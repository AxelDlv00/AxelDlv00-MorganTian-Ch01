import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Metric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Geodesic energy and first variation

This module records the variational contract used in Chapter 1.  The energy is
the source-normalized quantity

`E(gamma) = (1 / 2) * integral <gamma', gamma'>`.

The source is Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, the
energy/variation paragraph on pp. 41--43 (`morganTian2007`), with do Carmo,
Chapter 9, pp. 185--201 (`doCarmo1992`) as a cross-check.  Differentiation
under the integral is expressed using the pinned Mathlib
`ParametricIntervalIntegral` API and interval integration by parts.  The
canonical metric is always `Bundle.ContMDiffRiemannianMetric`, and the
canonical connection is `Connection.leviCivitaConnection`.

The pinned connection layer does not yet expose a covariant derivative along a
curve.  Accordingly, the first-variation declarations below make the
covariant-acceleration and test-field completeness witnesses explicit.  This
is the S18 handoff: no coordinate acceleration or competing geodesic predicate
is introduced here.  The slice proves the energy/length inequality and its
equality condition, but deliberately introduces no minimizer predicate; the
existence and identification of minimizers belong to S19.
-/

open Bundle Filter Function Manifold MeasureTheory Set
open scoped Bundle ContDiff ENNReal Interval Manifold RealInnerProductSpace Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Geodesic
namespace Variation

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Interval calculus -/

section RealCore

variable {f : ℝ → ℝ} {a b : ℝ}

private theorem integral_sub_const_sq (m : ℝ)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    (∫ t in a..b, (f t - m) ^ 2)
      = (∫ t in a..b, (f t) ^ 2) - 2 * m * (∫ t in a..b, f t) + m ^ 2 * (b - a) := by
  have hpt : ∀ t, (f t - m) ^ 2 = ((f t) ^ 2 - 2 * m * f t) + m ^ 2 := by
    intro t
    ring
  have hint1 : IntervalIntegrable (fun t => (f t) ^ 2 - 2 * m * f t) volume a b :=
    hf2.sub (hfi.const_mul (2 * m))
  have hint2 : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume a b :=
    intervalIntegrable_const
  calc
    (∫ t in a..b, (f t - m) ^ 2) =
        ∫ t in a..b, (((f t) ^ 2 - 2 * m * f t) + m ^ 2) := by
      simp_rw [hpt]
    _ = (∫ t in a..b, ((f t) ^ 2 - 2 * m * f t)) +
        ∫ _t in a..b, m ^ 2 := intervalIntegral.integral_add hint1 hint2
    _ = ((∫ t in a..b, (f t) ^ 2) - ∫ t in a..b, 2 * m * f t) +
        m ^ 2 * (b - a) := by
      rw [intervalIntegral.integral_sub hf2 (hfi.const_mul (2 * m)),
        intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring
    _ = (∫ t in a..b, (f t) ^ 2) - 2 * m * (∫ t in a..b, f t) +
        m ^ 2 * (b - a) := by
      rw [intervalIntegral.integral_const_mul]

private theorem intervalIntegrable_sub_const_sq (m : ℝ)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    IntervalIntegrable (fun t => (f t - m) ^ 2) volume a b := by
  have hpt : (fun t => (f t - m) ^ 2) =
      fun t => ((f t) ^ 2 - 2 * m * f t) + m ^ 2 := by
    funext t
    ring
  rw [hpt]
  exact (hf2.sub (hfi.const_mul (2 * m))).add intervalIntegrable_const

/-- The interval Cauchy--Schwarz inequality in the form used for energy
(Morgan--Tian, `morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9).

Only interval integrability is required, so this theorem also covers the
piecewise-smooth speed functions used by later comparison arguments. -/
theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (hab : a ≤ b)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hba : (0 : ℝ) < b - a := by linarith
  set L := ∫ t in a..b, f t with hL
  set m := L / (b - a) with hm
  have hexp := integral_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hnn : 0 ≤ ∫ t in a..b, (f t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => by positivity)
  rw [hexp] at hnn
  have hmL : m * (b - a) = L := by
    rw [hm]
    field_simp
  nlinarith [hnn, hmL, hba]

/-- Equality in `sq_intervalIntegral_le_mul_intervalIntegral_sq` is exactly
almost-everywhere constancy at the interval mean. -/
theorem sq_intervalIntegral_eq_iff_ae_eq_const (hab : a < b)
    (hfi : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) volume a b) :
    ((∫ t in a..b, f t) ^ 2 = (b - a) * ∫ t in a..b, (f t) ^ 2) ↔
      f =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ ((∫ t in a..b, f t) / (b - a)) := by
  have hab' : a ≤ b := hab.le
  have hba : (0 : ℝ) < b - a := by linarith
  set L := ∫ t in a..b, f t with hL
  set E := ∫ t in a..b, (f t) ^ 2 with hE
  set m := L / (b - a) with hm
  have hint : IntervalIntegrable (fun t => (f t - m) ^ 2) volume a b :=
    intervalIntegrable_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hexp := integral_sub_const_sq (f := f) (a := a) (b := b) m hfi hf2
  have hmL : m * (b - a) = L := by
    rw [hm]
    field_simp
  have hiff : (L ^ 2 = (b - a) * E) ↔
      (∫ t in a..b, (f t - m) ^ 2) = 0 := by
    rw [hexp]
    constructor <;> intro h <;> nlinarith [h, hmL, hba]
  rw [hiff, intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab'
      (Filter.Eventually.of_forall (fun _ => by positivity)) hint]
  constructor
  · intro h
    filter_upwards [h] with t ht
    have h0 : (f t - m) ^ 2 = 0 := ht
    have hsub : f t - m = 0 := by nlinarith [h0]
    have : f t = m := sub_eq_zero.mp hsub
    simpa [Function.const, hm] using this
  · intro h
    filter_upwards [h] with t ht
    have : f t = m := by
      simpa [Function.const, hm] using ht
    simp [this]

/-- Continuous-speed convenience form of the interval Cauchy--Schwarz
inequality. -/
theorem sq_intervalIntegral_le_mul_intervalIntegral_sq_of_continuousOn
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    (∫ t in a..b, f t) ^ 2 ≤ (b - a) * ∫ t in a..b, (f t) ^ 2 :=
  sq_intervalIntegral_le_mul_intervalIntegral_sq hab
    (hf.intervalIntegrable_of_Icc hab) ((hf.pow 2).intervalIntegrable_of_Icc hab)

end RealCore

/-! ## Canonical curve energy -/

section CurveEnergy

variable
  (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))

/-- The canonical velocity of a parameterized curve on an oriented interval.

The derivative is Mathlib's manifold derivative of the curve restricted to the
interval; no coordinate velocity is introduced. -/
noncomputable def velocity (gamma : ℝ → M) (a b t : ℝ) : TangentSpace I (gamma t) :=
  (mfderiv[Icc a b] gamma t) 1

/-- The squared speed measured by the supplied bundle metric. -/
noncomputable def speedSq (gamma : ℝ → M) (a b t : ℝ) : ℝ :=
  g.inner (gamma t) (velocity (I := I) gamma a b t) (velocity (I := I) gamma a b t)

/-- The nonnegative metric speed. -/
noncomputable def speed (gamma : ℝ → M) (a b t : ℝ) : ℝ :=
  Real.sqrt (speedSq (I := I) g gamma a b t)

/-- The energy of a curve on `[a,b]`, with the Morgan--Tian normalization from
Morgan--Tian (`morganTian2007`, pp. 41--43). -/
noncomputable def energy (gamma : ℝ → M) (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in a..b, speedSq (I := I) g gamma a b t

/-- The auxiliary real speed integral used for Cauchy--Schwarz.  It is not a
second manifold-length representation: `ofReal_curveLength_eq_pathELength`
below identifies it with Mathlib's canonical `Manifold.pathELength`. -/
noncomputable def curveLength (gamma : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, speed (I := I) g gamma a b t

/-- The metric square of a constant curve, exposing the canonical velocity
without introducing a coordinate derivative. -/
@[simp]
theorem speedSq_zero (gamma : ℝ → M) (a b t : ℝ) :
    speedSq (I := I) g (fun _ => gamma t) a b t =
      g.inner (gamma t) (velocity (I := I) (fun _ => gamma t) a b t)
        (velocity (I := I) (fun _ => gamma t) a b t) := rfl

/-- Positive definiteness of the supplied bundle metric. -/
theorem metric_inner_self_nonneg (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

/-- Nonnegativity of the canonical squared speed. -/
theorem speedSq_nonneg (gamma : ℝ → M) (a b t : ℝ) :
    0 ≤ speedSq (I := I) g gamma a b t := by
  exact metric_inner_self_nonneg (I := I) g (gamma t) (velocity (I := I) gamma a b t)

/-- Nonnegativity of the metric speed. -/
@[simp]
theorem speed_nonneg (gamma : ℝ → M) (a b t : ℝ) :
    0 ≤ speed (I := I) g gamma a b t :=
  Real.sqrt_nonneg _

/-- Squaring the nonnegative speed recovers the metric speed square. -/
theorem speed_sq (gamma : ℝ → M) (a b t : ℝ) :
    (speed (I := I) g gamma a b t) ^ 2 = speedSq (I := I) g gamma a b t := by
  exact Real.sq_sqrt (speedSq_nonneg (I := I) g gamma a b t)

/-- The scalar speed is the norm of the intrinsic tangent velocity for the
canonical metric bundle instance. -/
theorem speed_eq_norm_velocity (gamma : ℝ → M) (a b t : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    speed (I := I) g gamma a b t = ‖velocity (I := I) gamma a b t‖ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [speed, MorganTianLib.Ch01.norm_eq_sqrt_metric]
  rfl

/-- Unfolding the Morgan--Tian energy normalization. -/
theorem energy_eq_half_integral_speedSq (gamma : ℝ → M) (a b : ℝ) :
    energy (I := I) g gamma a b =
      (1 / 2 : ℝ) * ∫ t in a..b, speedSq (I := I) g gamma a b t := rfl

/-- The same normalization expressed using the scalar speed. -/
theorem energy_eq_half_integral_speed_sq (gamma : ℝ → M) (a b : ℝ) :
    energy (I := I) g gamma a b =
      (1 / 2 : ℝ) * ∫ t in a..b, (speed (I := I) g gamma a b t) ^ 2 := by
  simp_rw [speed_sq]
  rfl

/-- Unfolding the real speed-integral adapter used by the inequalities. -/
theorem curveLength_eq_integral_speed (gamma : ℝ → M) (a b : ℝ) :
    curveLength (I := I) g gamma a b =
      ∫ t in a..b, speed (I := I) g gamma a b t := rfl

/-! `curveLength` is the real-valued speed integral used by the
Cauchy--Schwarz lemmas.  The canonical manifold length is Mathlib's
`Manifold.pathELength`; the next declarations record the bridge without
installing a second length definition. -/

/-- On a nonnegative integrable speed, the real integral is exactly the
`ENNReal.ofReal` image of Mathlib's canonical `pathELength` integrand.  This
is the pinned `MeasureTheory.ofReal_integral_eq_lintegral_ofReal` bridge; the
metric-bundle instance is local and definitionally the supplied `g`. -/
theorem ofReal_curveLength_eq_pathELength_integral
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : IntervalIntegrable (speed (I := I) g gamma a b) volume a b) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (curveLength (I := I) g gamma a b) =
      ∫⁻ t in Icc a b, ‖(mfderiv[Icc a b] gamma t) 1‖ₑ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [curveLength, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hIoc : IntegrableOn (speed (I := I) g gamma a b) (Ioc a b) volume := by
    rw [← uIoc_of_le hab]
    exact (intervalIntegrable_iff.mp hs)
  have hIcc : IntegrableOn (speed (I := I) g gamma a b) (Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 hIoc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)]
      speed (I := I) g gamma a b :=
    Filter.Eventually.of_forall (fun t => speed_nonneg (I := I) g gamma a b t)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIcc hnonneg]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact (by
    simp only [enorm_eq_nnnorm]
    rw [ENNReal.coe_nnreal_eq]
    congr 1)

/-- The preceding bridge rewritten with Mathlib's canonical
`Manifold.pathELength` (`PathELength.lean`). -/
theorem ofReal_curveLength_eq_pathELength
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : IntervalIntegrable (speed (I := I) g gamma a b) volume a b) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (curveLength (I := I) g gamma a b) =
      Manifold.pathELength I gamma a b := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  exact ofReal_curveLength_eq_pathELength_integral (I := I) g gamma hab hs

/-- Energy is additive across adjacent intervals whenever its density is
integrable on the two pieces.  The interval argument in `velocity` is
deliberate: `mfderivWithin` can depend on the chosen closed interval at its
boundary.  Additivity therefore takes the compatibility equalities as
hypotheses instead of silently identifying different boundary derivatives. -/
theorem energy_add (gamma : ℝ → M) {a b c : ℝ} (_hab : a ≤ b) (_hbc : b ≤ c)
    {q : ℝ → ℝ}
    (h₁ : IntervalIntegrable q volume a b) (h₂ : IntervalIntegrable q volume b c)
    (hEq : ∀ t, speedSq (I := I) g gamma a c t = q t)
    (hEq₁ : ∀ t, speedSq (I := I) g gamma a b t = q t)
    (hEq₂ : ∀ t, speedSq (I := I) g gamma b c t = q t) :
    energy (I := I) g gamma a c =
      energy (I := I) g gamma a b + energy (I := I) g gamma b c := by
  simp only [energy]
  rw [show (fun t => speedSq (I := I) g gamma a c t) = q from funext hEq,
    show (fun t => speedSq (I := I) g gamma a b t) = q from funext hEq₁,
    show (fun t => speedSq (I := I) g gamma b c t) = q from funext hEq₂]
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
  ring

/-- Positivity is the metric part of the energy contract (Morgan--Tian,
`morganTian2007`, pp. 41--43).  The interval-integrability witness remains in
the signature even though Mathlib's totalized interval integral makes the
nonnegativity proof itself independent of it. -/
theorem energy_nonneg (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (_hint : IntervalIntegrable (fun t => speedSq (I := I) g gamma a b t) volume a b) :
    0 ≤ energy (I := I) g gamma a b := by
  rw [energy]
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun t ht => speedSq_nonneg (I := I) g gamma a b t)
  positivity

/-- Nonnegativity of the auxiliary real speed integral on an ordered interval.
The canonical manifold length is obtained from it through the `pathELength`
bridge above. -/
theorem curveLength_nonneg (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (_hint : IntervalIntegrable (speed (I := I) g gamma a b) volume a b) :
    0 ≤ curveLength (I := I) g gamma a b := by
  rw [curveLength]
  exact intervalIntegral.integral_nonneg hab
    (fun t _ => speed_nonneg (I := I) g gamma a b t)

/-- The interval energy/length inequality is the Cauchy--Schwarz step in
Morgan--Tian (`morganTian2007`, pp. 41--43) and do Carmo (`doCarmo1992`,
Ch. 9, Section 2). -/
theorem curveLength_sq_le_two_mul_interval_sub_mul_energy
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : IntervalIntegrable (speed (I := I) g gamma a b) volume a b)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma a b t) ^ 2) volume a b) :
    (curveLength (I := I) g gamma a b) ^ 2 ≤
      2 * (b - a) * energy (I := I) g gamma a b := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  have h := sq_intervalIntegral_le_mul_intervalIntegral_sq (f := speed (I := I) g gamma a b)
    hab hs hs2
  nlinarith

/-- The normalized `[0,1]` energy/length inequality (Morgan--Tian,
`morganTian2007`, pp. 41--43). -/
theorem curveLength_sq_le_two_mul_energy (gamma : ℝ → M)
    (hs : IntervalIntegrable (speed (I := I) g gamma 0 1) volume 0 1)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma 0 1 t) ^ 2) volume 0 1) :
    (curveLength (I := I) g gamma 0 1) ^ 2 ≤
      2 * energy (I := I) g gamma 0 1 := by
  simpa using curveLength_sq_le_two_mul_interval_sub_mul_energy
    (I := I) g gamma (a := 0) (b := 1) (by norm_num) hs hs2

/-- Equality in the energy/length inequality is exactly a.e. constant speed;
the pointwise upgrade below uses continuity (Morgan--Tian,
`morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9). -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : IntervalIntegrable (speed (I := I) g gamma a b) volume a b)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma a b t) ^ 2) volume a b) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      speed (I := I) g gamma a b =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  convert sq_intervalIntegral_eq_iff_ae_eq_const hab hs hs2 using 1
  all_goals ring_nf

/-! ### Regularity and the geodesic speed regression -/

/-- The explicit regularity package used by the interval energy statements.

The `CMDiff` field is the intrinsic `C¹` path hypothesis.  The two
`IntervalIntegrable` fields are kept separate because differentiation of the
energy uses the squared speed while the length inequality uses both speed and
its square. -/
structure CurveRegularity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Prop where
  interval_order : a ≤ b
  smoothOn : CMDiff[Icc a b] 1 gamma
  speed_integrable :
    IntervalIntegrable (speed (I := I) g gamma a b) volume a b
  speedSq_integrable :
    IntervalIntegrable
      (fun t => (speed (I := I) g gamma a b t) ^ 2) volume a b

/-- A smooth-speed version of the equality characterization. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_of_continuousOn
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma a b) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      speed (I := I) g gamma a b =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
  apply curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff (I := I) g gamma hab
  · exact hs.intervalIntegrable_of_Icc hab.le
  · exact (hs.pow 2).intervalIntegrable_of_Icc hab.le

/-- With continuous speed, equality in the energy/length inequality is
pointwise constant norm of the velocity (including the endpoint values). -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma a b) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma a b t = c := by
  have hbase := curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_of_continuousOn
    (I := I) g gamma hab hs
  constructor
  · intro heq
    have haeIoc := hbase.mp heq
    have haeIcc : speed (I := I) g gamma a b =ᵐ[volume.restrict (Icc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
      rw [Measure.restrict_congr_set (μ := volume) Ioc_ae_eq_Icc] at haeIoc
      exact haeIoc
    refine ⟨curveLength (I := I) g gamma a b / (b - a), ?_⟩
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne haeIcc hs continuousOn_const
  · rintro ⟨c, hc⟩
    rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
    have hEq : EqOn (speed (I := I) g gamma a b)
        (fun _ : ℝ => c) (uIcc a b) := by
      intro t ht
      exact hc t (by simpa [uIcc_of_le hab.le] using ht)
    have hEq2 : EqOn (fun t => (speed (I := I) g gamma a b t) ^ 2)
        (fun _ : ℝ => c ^ 2) (uIcc a b) := by
      intro t ht
      change (speed (I := I) g gamma a b t) ^ 2 = c ^ 2
      rw [hc t (by simpa [uIcc_of_le hab.le] using ht)]
    rw [intervalIntegral.integral_congr hEq,
      intervalIntegral.integral_congr hEq2,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    ring

/-- Continuous-speed equality characterization on a possibly degenerate
interval (Morgan--Tian, `morganTian2007`, pp. 41--43).  This is separated
from the positive-length theorem so its denominator remains visibly nonzero. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn_of_le
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn (speed (I := I) g gamma a b) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma a b t = c := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [sub_self, mul_zero, curveLength, intervalIntegral.integral_same,
      pow_two, energy]
    constructor
    · intro _
      refine ⟨speed (I := I) g gamma a a a, ?_⟩
      intro t ht
      have hta : t = a := by simpa using ht
      simp [hta]
    · intro _
      trivial
  · exact curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn
      (I := I) g gamma hlt hs

/-- A pointwise constant speed attains equality in the interval
energy/length inequality, including the degenerate interval case (Morgan--Tian,
`morganTian2007`, pp. 41--43). -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_of_const_speed
    (gamma : ℝ → M) {a b c : ℝ} (hab : a ≤ b)
    (hconst : ∀ t ∈ Icc a b, speed (I := I) g gamma a b t = c) :
    (curveLength (I := I) g gamma a b) ^ 2 =
      2 * (b - a) * energy (I := I) g gamma a b := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  have hEq : EqOn (speed (I := I) g gamma a b)
      (fun _ : ℝ => c) (uIcc a b) := by
    intro t ht
    exact hconst t (by simpa [uIcc_of_le hab] using ht)
  have hEq2 : EqOn (fun t => (speed (I := I) g gamma a b t) ^ 2)
      (fun _ : ℝ => c ^ 2) (uIcc a b) := by
    intro t ht
    change (speed (I := I) g gamma a b t) ^ 2 = c ^ 2
    rw [hconst t (by simpa [uIcc_of_le hab] using ht)]
  rw [intervalIntegral.integral_congr hEq,
    intervalIntegral.integral_congr hEq2,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  ring

/-- The same equality characterization stated literally as constancy of the
norm of the intrinsic velocity in the canonical metric bundle. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_const_norm_velocity
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma a b) (Icc a b)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b,
        ‖velocity (I := I) gamma a b t‖ = c := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hbase := curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn
    (I := I) g gamma hab hs
  constructor
  · intro h
    rcases hbase.mp h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma a b t] using hc t ht
  · rintro ⟨c, hc⟩
    apply hbase.mpr
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma a b t] using hc t ht

/-- A typed intrinsic acceleration contract.  The acceleration is intended to
be supplied by the S18 connection/geodesic producer; this module stores no
coordinate acceleration and does not define a competing geodesic predicate. -/
structure CovariantAccelerationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Type _ where
  acceleration : ∀ t, TangentSpace I (gamma t)
  speedSq_deriv : ∀ t ∈ uIcc a b,
    HasDerivAt (fun s => speedSq (I := I) g gamma a b s)
      (2 * g.inner (gamma t) (velocity (I := I) gamma a b t) (acceleration t)) t

section CanonicalConnection

variable [FiniteDimensional ℝ E]

/-- A global section agreeing with the curve velocity on the chosen interval.
It is the explicit adapter needed by Mathlib's bundled connection API. -/
structure VelocityExtension (gamma : ℝ → M) (a b : ℝ) : Type _ where
  field : ∀ x : M, TangentSpace I x
  agrees : ∀ t ∈ uIcc a b,
    field (gamma t) = velocity (I := I) gamma a b t

/-- Covariant differentiation of the supplied velocity section by the canonical
Levi--Civita connection.  The argument order is `∇_velocity velocity`. -/
noncomputable def canonicalAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b : ℝ}
    (X : VelocityExtension (I := I) gamma a b) (t : ℝ) :
    TangentSpace I (gamma t) :=
  Connection.leviCivitaConnection g X.field (gamma t)
    (velocity (I := I) gamma a b t)

/-- A covariant-acceleration package whose connection-side value is explicit. -/
structure CanonicalAccelerationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Type _ where
  extension : VelocityExtension (I := I) gamma a b
  acceleration : ∀ t, TangentSpace I (gamma t)
  acceleration_eq : ∀ t ∈ uIcc a b,
    acceleration t = canonicalAcceleration g extension t
  speedSq_deriv : ∀ t ∈ uIcc a b,
    HasDerivAt (fun s => speedSq (I := I) g gamma a b s)
      (2 * g.inner (gamma t) (velocity (I := I) gamma a b t) (acceleration t)) t

def CanonicalAccelerationData.toCovariant
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {gamma : ℝ → M} {a b : ℝ}
    (D : CanonicalAccelerationData g gamma a b) :
    CovariantAccelerationData g gamma a b where
  acceleration := D.acceleration
  speedSq_deriv := D.speedSq_deriv

end CanonicalConnection

/-- Zero covariant acceleration forces constant squared speed on the chosen
interval.  The proof is the fundamental theorem for interval integrals, with
the derivative order and endpoint orientation visible. -/
theorem speedSq_eq_of_zero_acceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (hzero : ∀ t ∈ uIcc a b, hacc.acceleration t = 0) :
    ∀ t₁ t₂, t₁ ∈ uIcc a b → t₂ ∈ uIcc a b →
      speedSq (I := I) g gamma a b t₁ = speedSq (I := I) g gamma a b t₂ := by
  intro t₁ t₂ ht₁ ht₂
  have hderiv : ∀ t ∈ uIcc t₁ t₂,
      HasDerivAt (fun s => speedSq (I := I) g gamma a b s) 0 t := by
    intro t ht
    have ht' : t ∈ uIcc a b := Set.uIcc_subset_uIcc ht₁ ht₂ ht
    simpa [hzero t ht'] using hacc.speedSq_deriv t ht'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume t₁ t₂)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
  linarith

/-- The same constant-speed conclusion through the canonical
Levi--Civita-connection adapter.  The adapter applies the bundled connection
to an explicitly supplied global velocity extension; it is not yet the S18
along-curve covariant-derivative producer. -/
theorem speedSq_eq_of_zero_canonical_acceleration
    [FiniteDimensional ℝ E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CanonicalAccelerationData g gamma a b)
    (hzero : ∀ t ∈ uIcc a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0) :
    ∀ t₁ t₂, t₁ ∈ uIcc a b → t₂ ∈ uIcc a b →
      speedSq (I := I) g gamma a b t₁ = speedSq (I := I) g gamma a b t₂ := by
  apply speedSq_eq_of_zero_acceleration (I := I) g gamma hacc.toCovariant
  intro t ht
  change hacc.acceleration t = 0
  rw [hacc.acceleration_eq t ht]
  exact hzero t ht

/-- Constant squared speed on an ordered interval implies constant speed. -/
theorem speed_eq_of_zero_acceleration_on_Icc
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (hab : a ≤ b) (hzero : ∀ t ∈ Icc a b, hacc.acceleration t = 0)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    speed (I := I) g gamma a b t₁ = speed (I := I) g gamma a b t₂ := by
  have hsq := speedSq_eq_of_zero_acceleration (I := I) g gamma hacc
    (fun t ht => hzero t (by simpa [uIcc_of_le hab] using ht))
    t₁ t₂ (by simpa [uIcc_of_le hab] using ht₁) (by simpa [uIcc_of_le hab] using ht₂)
  unfold speed
  rw [hsq]

/-- Constant speed through the canonical Levi--Civita acceleration adapter.
The premise is stated for `canonicalAcceleration`, rather than silently
reusing the arbitrary acceleration field in `CanonicalAccelerationData`. -/
theorem speed_eq_of_zero_canonical_acceleration_on_Icc
    [FiniteDimensional ℝ E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CanonicalAccelerationData g gamma a b)
    (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    speed (I := I) g gamma a b t₁ = speed (I := I) g gamma a b t₂ := by
  refine speed_eq_of_zero_acceleration_on_Icc (I := I) g gamma hacc.toCovariant hab ?_
      t₁ t₂ ht₁ ht₂
  intro t ht
  have htu : t ∈ uIcc a b := by
    simpa [uIcc_of_le hab] using ht
  change hacc.acceleration t = 0
  rw [hacc.acceleration_eq t htu]
  exact hzero t ht

/-- A zero-acceleration package supplies a single pointwise speed on the whole
ordered interval. -/
theorem exists_const_speed_of_zero_acceleration_on_Icc
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (hab : a ≤ b) (hzero : ∀ t ∈ Icc a b, hacc.acceleration t = 0) :
    ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma a b t = c := by
  refine ⟨speed (I := I) g gamma a b a, ?_⟩
  intro t ht
  exact speed_eq_of_zero_acceleration_on_Icc (I := I) g gamma hacc hab hzero
    t a ht (left_mem_Icc.2 hab)

/-- Existence of a constant speed through the canonical Levi--Civita
acceleration adapter. -/
theorem exists_const_speed_of_zero_canonical_acceleration_on_Icc
    [FiniteDimensional ℝ E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CanonicalAccelerationData g gamma a b)
    (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0) :
    ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma a b t = c := by
  refine ⟨speed (I := I) g gamma a b a, ?_⟩
  intro t ht
  exact speed_eq_of_zero_canonical_acceleration_on_Icc (I := I) g gamma hacc hab hzero
    t a ht (left_mem_Icc.2 hab)

/-- Constant-speed segment energy, including the degenerate interval case. -/
theorem energy_eq_half_interval_mul_of_speedSq_eq_const
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b c : ℝ} (hab : a ≤ b)
    (hconst : ∀ t ∈ Icc a b,
      speedSq (I := I) g gamma a b t = c ^ 2) :
    energy (I := I) g gamma a b = (1 / 2 : ℝ) * (b - a) * c ^ 2 := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g gamma a b)
      (fun _ : ℝ => c ^ 2) (uIcc a b) := by
    intro t ht
    exact hconst t (by simpa [uIcc_of_le hab] using ht)
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

/-- Density-level Euclidean straight-line regression: a constant velocity norm
has exactly the normalized energy `1/2 * interval length * speed²`.  This is
the flat affine model used to check the normalization without introducing a
second metric bundle. -/
theorem euclidean_straightLine_energy_density (a b v : ℝ) (_hab : a ≤ b) :
    (1 / 2 : ℝ) * (∫ _t in a..b, v ^ 2) =
      (1 / 2 : ℝ) * (b - a) * v ^ 2 := by
  rw [intervalIntegral.integral_const]
  ring

/-- Zero velocity gives zero energy. -/
theorem energy_eq_zero_of_velocity_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, velocity (I := I) gamma a b t = 0) :
    energy (I := I) g gamma a b = 0 := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g gamma a b)
      (fun _ : ℝ => (0 : ℝ)) (uIcc a b) := by
    intro t ht
    rw [speedSq]
    simp [hzero t (by simpa [uIcc_of_le hab] using ht)]
  rw [intervalIntegral.integral_congr hEq]
  simp

/-- Pointwise sign regression valid for a nonconstant metric as well as a
constant one: positive definiteness, not metric constancy, controls every
energy density. -/
theorem nonconstant_metric_sign_probe
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b t : ℝ) :
    0 ≤ g.inner (gamma t) (velocity (I := I) gamma a b t)
      (velocity (I := I) gamma a b t) :=
  speedSq_nonneg (I := I) g gamma a b t

/-- Strict positivity at a nonzero velocity, valid for a metric that varies
with the base point as well as for a constant Euclidean metric. -/
theorem metric_sign_probe_of_nonzero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b t : ℝ)
    (hv : velocity (I := I) gamma a b t ≠ 0) :
    0 < g.inner (gamma t) (velocity (I := I) gamma a b t)
      (velocity (I := I) gamma a b t) :=
  g.pos (gamma t) _ hv

/-! ### Reparameterization and variation contracts -/

/-- Positive affine reparameterization of a curve scales energy by its speed
factor.  `density_eq` is the manifold chain-rule witness: it is intentionally
visible because the current Mathlib connection layer has no along-curve
derivative producer. -/
theorem energy_affine_reparam_of_density
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma delta : ℝ → M} {a b alpha beta : ℝ} (_hab : a ≤ b) (_halpha : 0 < alpha)
    (density_eq : ∀ t ∈ uIcc a b,
      speedSq (I := I) g delta a b t =
        alpha ^ 2 * speedSq (I := I) g gamma
          (alpha * a + beta) (alpha * b + beta) (alpha * t + beta))
    (hgamma : Continuous
      (speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta))) :
    energy (I := I) g delta a b =
      alpha * energy (I := I) g gamma (alpha * a + beta) (alpha * b + beta) := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g delta a b)
      (fun t => alpha ^ 2 * speedSq (I := I) g gamma
        (alpha * a + beta) (alpha * b + beta) (alpha * t + beta)) (uIcc a b) := by
    intro t ht
    exact density_eq t ht
  have hchange :
      (∫ t in a..b,
        (speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta) ∘
          (fun x : ℝ => alpha * x + beta)) t * alpha) =
        ∫ t in alpha * a + beta..alpha * b + beta,
          speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta) t := by
    apply intervalIntegral.integral_comp_mul_deriv
    · intro x hx
      simpa [Function.comp_def] using
        (hasDerivAt_id x).const_mul alpha |>.add_const beta
    · exact continuousOn_const
    · exact hgamma
  have hscale :
      (∫ t in a..b, alpha ^ 2 *
        speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta)
          (alpha * t + beta)) =
        alpha * (∫ t in a..b,
          speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta)
            (alpha * t + beta) * alpha) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    ring
  rw [intervalIntegral.integral_congr hEq, hscale]
  have hchange' :
      (∫ t in a..b,
        speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta)
          (alpha * t + beta) * alpha) =
        ∫ t in alpha * a + beta..alpha * b + beta,
          speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta) t := by
    simpa [Function.comp_def] using hchange
  rw [hchange']
  ring

/-- Affine reparameterization with the curve-composition equality made
explicit.  The remaining `density_eq` field is the manifold chain-rule
witness; it is separated from the algebraic change-of-variables proof. -/
theorem energy_affine_reparam_of_composition
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma delta : ℝ → M} {a b alpha beta : ℝ} (_hab : a ≤ b) (_halpha : 0 < alpha)
    (hdelta : delta = gamma ∘ (fun t : ℝ => alpha * t + beta))
    (density_eq : ∀ t ∈ uIcc a b,
      speedSq (I := I) g (gamma ∘ (fun t : ℝ => alpha * t + beta)) a b t =
        alpha ^ 2 * speedSq (I := I) g gamma
          (alpha * a + beta) (alpha * b + beta) (alpha * t + beta))
    (hgamma : Continuous
      (speedSq (I := I) g gamma (alpha * a + beta) (alpha * b + beta))) :
    energy (I := I) g delta a b =
      alpha * energy (I := I) g gamma (alpha * a + beta) (alpha * b + beta) := by
  apply energy_affine_reparam_of_density (I := I) g _hab _halpha
    (fun t ht => ?_) hgamma
  rw [hdelta]
  exact density_eq t ht

/-- Mathlib's canonical path length is invariant under a monotone
differentiable reparameterization; this is the pinned
`Manifold.pathELength_comp_of_monotoneOn` contract. -/
theorem pathELength_comp_monotone
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} (hab : a ≤ b) {gamma : ℝ → M} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc a b)) (h'f : DifferentiableOn ℝ f (Icc a b))
    (hgamma : MDiff[Icc (f a) (f b)] gamma) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (gamma ∘ f) a b =
      Manifold.pathELength I gamma (f a) (f b) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_comp_of_monotoneOn hab hf h'f hgamma

/-! ### Smooth two-parameter variations -/

/-- A smooth two-parameter variation on `[a,b]` (Morgan--Tian,
`morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9, Sections 2--3).
The surface is defined on all of `ℝ × ℝ` so that `mfderiv` can form the
variational field; regularity and the zero slice are restricted to the compact
parameter rectangle. -/
structure SmoothVariation (gamma : ℝ → M) (a b epsilon : ℝ) : Type _ where
  family : ℝ → ℝ → M
  epsilon_pos : 0 < epsilon
  interval_order : a ≤ b
  surface_smooth :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry family)
      (Icc (-epsilon) epsilon ×ˢ Icc a b)
  zero_slice : ∀ t ∈ Icc a b, family 0 t = gamma t

/-- The base curve in the zero slice. -/
def baseCurve
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) : ℝ → M :=
  fun t => V.family 0 t

omit [IsManifold I ∞ M] in
/-- The base curve agrees with the prescribed curve on the variation interval. -/
theorem baseCurve_eq_gamma_on
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) :
    ∀ t ∈ Icc a b, baseCurve V t = gamma t := by
  intro t ht
  exact V.zero_slice t ht

/-- The variational vector field `∂F/∂s` at the zero slice. -/
noncomputable def variationalVectorField
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) (t : ℝ) :
    TangentSpace I (baseCurve V t) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun s => V.family s t) 0 1

/-- Energy as a function of the variation parameter. -/
noncomputable def variationEnergy
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) (s : ℝ) : ℝ :=
  energy (I := I) g (fun t => V.family s t) a b

/-- The zero slice has the prescribed curve energy.  The derivative congruence
uses Mathlib's `mfderivWithin_congr_of_mem`; endpoint equality alone would not
justify this identity because `velocity` is interval-restricted. -/
theorem variationEnergy_zero_eq_energy
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) :
    variationEnergy (I := I) g V 0 = energy (I := I) g gamma a b := by
  rw [variationEnergy, energy, energy]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc a b := by
    simpa [uIcc_of_le V.interval_order] using ht
  have hderiv := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, ℝ)) (I' := I)
    (f₁ := baseCurve V) (f := gamma) (s := Icc a b)
    (fun x hx => V.zero_slice x hx) ht'
  change speedSq (I := I) g (baseCurve V) a b t =
    speedSq (I := I) g gamma a b t
  rw [speedSq, velocity, hderiv, baseCurve_eq_gamma_on V t ht']
  rfl

/-- The metric pairing of the variational field and base velocity. -/
noncomputable def variationPairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) (t : ℝ) : ℝ :=
  g.inner (baseCurve V t) (variationalVectorField V t)
    (velocity (I := I) (baseCurve V) a b t)

/-- Pairing of a supplied covariant derivative with the base velocity. -/
noncomputable def covariantPairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon)
    (D : ∀ t, TangentSpace I (baseCurve V t)) (t : ℝ) : ℝ :=
  g.inner (baseCurve V t) (D t)
    (velocity (I := I) (baseCurve V) a b t)

/-- Pairing of the variational field with a supplied covariant acceleration. -/
noncomputable def accelerationPairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon)
    (A : ∀ t, TangentSpace I (baseCurve V t)) (t : ℝ) : ℝ :=
  g.inner (baseCurve V t) (variationalVectorField V t) (A t)

/-- Endpoint-fixed variations are those whose variational field vanishes at both
endpoints. -/
def EndpointVectorsZero
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) : Prop :=
  variationalVectorField V a = 0 ∧ variationalVectorField V b = 0

/-- Endpoint pairings vanish when the corresponding variational vector is zero. -/
theorem variationPairing_eq_zero_of_endpoint_vector_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon} {t : ℝ}
    (h : variationalVectorField V t = 0) :
    variationPairing (I := I) g V t = 0 := by
  simp [variationPairing, h]

omit [IsManifold I ∞ M] in
/-- Endpoint-fixed surface hypotheses imply the endpoint vector condition. -/
theorem endpointVectorsZero_of_fixed_endpoints
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon)
    (hleft : ∀ s, V.family s a = V.family 0 a)
    (hright : ∀ s, V.family s b = V.family 0 b) :
    EndpointVectorsZero (I := I) V := by
  constructor
  · have hfun : (fun s => V.family s a) = fun _ : ℝ => V.family 0 a := by
      funext s
      exact hleft s
    rw [variationalVectorField, hfun]
    simp [baseCurve]
    rfl

  · have hfun : (fun s => V.family s b) = fun _ : ℝ => V.family 0 b := by
      funext s
      exact hright s
    rw [variationalVectorField, hfun]
    simp [baseCurve]
    rfl

/-! ### Differentiation under the integral and first variation -/

/-- Pinned Mathlib differentiation-under-the-integral contract.

This wrapper keeps the measurable, integrable, dominated, and pointwise
`HasDerivAt` hypotheses in the public API.  It is the exact
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(`ParametricIntervalIntegral.lean`) used to construct the `energy_deriv`
field below. -/
theorem hasDerivAt_intervalIntegral_of_dominated_loc
    {F F' : ℝ → ℝ → ℝ} {a b x₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x : ℝ in 𝓝 x₀,
      AEStronglyMeasurable (F x) (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable (F x₀) volume a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀)
      (volume.restrict (uIoc a b)))
    {bound : ℝ → ℝ}
    (h_bound : ∀ᵐ t ∂volume, t ∈ uIoc a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound volume a b)
    (h_diff : ∀ᵐ t ∂volume, t ∈ uIoc a b → ∀ x ∈ s,
      HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) volume a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ :=
  intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff

/-- All analytic data needed for the intrinsic first variation (Morgan--Tian,
`morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9, Sections 2--3).

`energy_deriv_eq_integral` is where the preceding dominated-integral theorem,
metric compatibility, and the mixed-partial/connection bridge are supplied.
The factor `1/2` in the energy cancels the `2` from differentiating the
metric square, leaving the unhalved pairing below.
The fields are deliberately witnesses rather than axioms hidden in a theorem:
they expose exactly which regularity remains to be discharged by the S18
geodesic producer. -/
structure FirstVariationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) : Type _ where
  acceleration : ∀ t, TangentSpace I (baseCurve V t)
  covariantDerivative : ∀ t, TangentSpace I (baseCurve V t)
  energyDerivative : ℝ
  energy_deriv : HasDerivAt (variationEnergy (I := I) g V) energyDerivative 0
  energy_deriv_eq_integral :
    energyDerivative =
      ∫ t in a..b, covariantPairing (I := I) g V covariantDerivative t
  pairing_deriv : ∀ t ∈ uIcc a b,
    HasDerivAt (variationPairing (I := I) g V)
      (covariantPairing (I := I) g V covariantDerivative t +
        accelerationPairing (I := I) g V acceleration t) t
  covariant_pair_integrable :
    IntervalIntegrable
      (covariantPairing (I := I) g V covariantDerivative) volume a b
  acceleration_pair_integrable :
    IntervalIntegrable
      (accelerationPairing (I := I) g V acceleration) volume a b

/-- Full first variation formula, with both endpoint terms and the intrinsic
acceleration term.  The signs are `+` at `b`, `-` at `a`, and `-` for the
integrated covariant acceleration (Morgan--Tian, `morganTian2007`, pp. 41--43;
do Carmo, `doCarmo1992`, Ch. 9, Proposition 2.4).  The endpoint assembly uses
Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
-/
theorem firstEnergyVariation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) :
    HasDerivAt (variationEnergy (I := I) g V)
      (variationPairing (I := I) g V b - variationPairing (I := I) g V a -
        ∫ t in a..b, accelerationPairing (I := I) g V D.acceleration t) 0 := by
  have hsum : IntervalIntegrable
      (fun t => covariantPairing (I := I) g V D.covariantDerivative t +
        accelerationPairing (I := I) g V D.acceleration t) volume a b :=
    D.covariant_pair_integrable.add D.acceleration_pair_integrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => D.pairing_deriv t ht) hsum
  have hsplit := intervalIntegral.integral_add
    D.covariant_pair_integrable D.acceleration_pair_integrable
  have hsumEq :
      (∫ t in a..b, covariantPairing (I := I) g V D.covariantDerivative t) +
        ∫ t in a..b, accelerationPairing (I := I) g V D.acceleration t =
      variationPairing (I := I) g V b - variationPairing (I := I) g V a := by
    rw [← hsplit]
    exact hFTC
  have hvalue : D.energyDerivative =
      variationPairing (I := I) g V b - variationPairing (I := I) g V a -
        ∫ t in a..b, accelerationPairing (I := I) g V D.acceleration t := by
    rw [D.energy_deriv_eq_integral]
    linarith
  have hderiv := D.energy_deriv
  rw [hvalue] at hderiv
  exact hderiv

/-- The derivative form of `firstEnergyVariation`. -/
theorem firstEnergyVariation_deriv
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) :
    deriv (variationEnergy (I := I) g V) 0 =
      variationPairing (I := I) g V b - variationPairing (I := I) g V a -
        ∫ t in a..b, accelerationPairing (I := I) g V D.acceleration t :=
  (firstEnergyVariation (I := I) g D).deriv

/-- Endpoint-sign regression: when the integrated acceleration term vanishes,
the free-end derivative is `+` at `b` and `-` at `a`. -/
theorem firstEnergyVariation_endpoint_terms_of_zero_acceleration_integral
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V)
    (hacc : (∫ t in a..b,
      accelerationPairing (I := I) g V D.acceleration t) = 0) :
    deriv (variationEnergy (I := I) g V) 0 =
      variationPairing (I := I) g V b - variationPairing (I := I) g V a := by
  rw [firstEnergyVariation_deriv (I := I) g D, hacc]
  ring

/-- Fixed-endpoint specialization of the first variation formula. -/
theorem firstEnergyVariation_fixed_endpoints
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V)
    (hend : EndpointVectorsZero (I := I) V) :
    HasDerivAt (variationEnergy (I := I) g V)
      (-∫ t in a..b, accelerationPairing (I := I) g V D.acceleration t) 0 := by
  have h := firstEnergyVariation (I := I) g D
  have hleft := variationPairing_eq_zero_of_endpoint_vector_zero
    (I := I) g hend.1
  have hright := variationPairing_eq_zero_of_endpoint_vector_zero
    (I := I) g hend.2
  rw [hleft, hright] at h
  simpa using h

/-- A variation is energy-critical when its first derivative at the zero slice
vanishes. -/
def IsEnergyCritical
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) : Prop :=
  deriv (variationEnergy (I := I) g V) 0 = 0

/-- Under a `FirstVariationData` package, the totalized derivative predicate is
equivalent to vanishing of the supplied genuine derivative. -/
theorem isEnergyCritical_iff_energyDerivative_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) :
    IsEnergyCritical (I := I) g V ↔ D.energyDerivative = 0 := by
  have hderiv : deriv (variationEnergy (I := I) g V) 0 = D.energyDerivative :=
    D.energy_deriv.deriv
  constructor
  · intro h
    change deriv (variationEnergy (I := I) g V) 0 = 0 at h
    rw [hderiv] at h
    exact h
  · intro h
    change deriv (variationEnergy (I := I) g V) 0 = 0
    rw [hderiv, h]

/-- The intrinsic acceleration-zero predicate attached to a first-variation
data package.  Its interval and regularity hypotheses are explicit. -/
def IsZeroCovariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) : Prop :=
  ∀ t ∈ Icc a b, D.acceleration t = 0

/-- The S18/fundamental-lemma witness needed for the converse criticality
direction.  It is separated from `FirstVariationData` so a future S18 module
can supply it without changing the endpoint/sign contract here. -/
structure FixedEndpointCriticalityWitness
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon)
    (D : FirstVariationData (I := I) g V) : Prop where
  zero_of_critical :
    IsEnergyCritical (I := I) g V → IsZeroCovariantAcceleration (I := I) g D

/-- Zero intrinsic acceleration implies criticality for a fixed-endpoint
variation. -/
theorem isEnergyCritical_of_zero_covariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V)
    (hend : EndpointVectorsZero (I := I) V)
    (hzero : IsZeroCovariantAcceleration (I := I) g D) :
    IsEnergyCritical (I := I) g V := by
  have hderiv := firstEnergyVariation_fixed_endpoints (I := I) g D hend
  have hacc : (∫ t in a..b,
      accelerationPairing (I := I) g V D.acceleration t) = 0 := by
    have hEq : EqOn (fun t => accelerationPairing (I := I) g V D.acceleration t)
        (fun _ : ℝ => (0 : ℝ)) (uIcc a b) := by
      intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [uIcc_of_le V.interval_order] using ht
      simp [accelerationPairing, hzero t ht']
    rw [intervalIntegral.integral_congr hEq]
    simp
  rw [hacc] at hderiv
  simpa [IsEnergyCritical] using hderiv.deriv

/-- Under the explicit S18 test-field witness, criticality is equivalent to
vanishing intrinsic covariant acceleration. -/
theorem isEnergyCritical_iff_zero_covariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V)
    (hend : EndpointVectorsZero (I := I) V)
    (W : FixedEndpointCriticalityWitness (I := I) g V D) :
    IsEnergyCritical (I := I) g V ↔ IsZeroCovariantAcceleration (I := I) g D := by
  constructor
  · exact W.zero_of_critical
  · exact isEnergyCritical_of_zero_covariantAcceleration (I := I) g D hend

/-- All fixed-endpoint variations are critical, with the S18 producer made
explicit as an existential data/witness package.  Each quantified
`SmoothVariation` carries its own explicit `a ≤ b` field, so no reversed
interval is admitted by the family. -/
def AllFixedEndpointEnergyCritical
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Prop :=
  ∀ epsilon, ∀ V : SmoothVariation (I := I) gamma a b epsilon,
    EndpointVectorsZero (I := I) V → IsEnergyCritical (I := I) g V

/-- A family of first-variation/test-field witnesses for the all-variations
criticality statement. -/
structure AllVariationCriticalityWitness
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Prop where
  data : ∀ epsilon (V : SmoothVariation (I := I) gamma a b epsilon),
    EndpointVectorsZero (I := I) V →
      ∃ D : FirstVariationData (I := I) g V,
        FixedEndpointCriticalityWitness (I := I) g V D

/-- The all-variation formulation of the criticality/acceleration contract. -/
theorem allFixedEndpointEnergyCritical_iff_zero_covariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ}
    (C : AllVariationCriticalityWitness (I := I) g gamma a b) :
    AllFixedEndpointEnergyCritical (I := I) g gamma a b ↔
      ∀ epsilon (V : SmoothVariation (I := I) gamma a b epsilon),
        ∀ _hend : EndpointVectorsZero (I := I) V,
          ∃ D : FirstVariationData (I := I) g V,
            IsZeroCovariantAcceleration (I := I) g D := by
  constructor
  · intro h epsilon V hend
    rcases C.data epsilon V hend with ⟨D, W⟩
    exact ⟨D, W.zero_of_critical (h epsilon V hend)⟩
  · intro h epsilon V hend
    rcases h epsilon V hend with ⟨D, hzero⟩
    exact isEnergyCritical_of_zero_covariantAcceleration (I := I) g D hend hzero

end CurveEnergy

end Variation

/-! The primitive energy names are re-exported at the geodesic ownership
boundary.  The variation-specific contracts remain under `Geodesic.Variation`.
-/
export Variation (velocity speedSq speed energy curveLength speed_eq_norm_velocity)

end Geodesic
end Ch01
end MorganTianLib
