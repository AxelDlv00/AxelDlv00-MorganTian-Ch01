import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Metric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Geodesic energy and first variation

This module records the variational contract used in Chapter 1.  The energy is
the source-normalized quantity

`E(gamma) = (1 / 2) * integral <gamma', gamma'>`.

The source is Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, the
energy/variation paragraph on pp. 41--43 (`morganTian2007`), with do Carmo,
Chapter 9, pp. 185--201 (`doCarmo1992`) as a cross-check.  Differentiation
under the integral and interval integration by parts remain explicit
regularity witnesses in the first-variation data.  The
canonical metric is always `Bundle.ContMDiffRiemannianMetric`, and the
canonical connection is `Connection.leviCivitaConnection`.

The pinned connection layer does not yet expose a covariant derivative along a
curve.  Accordingly, `FirstVariationData` keeps the covariant-acceleration
field as an explicit, variation-local regularity witness.  The valid
zero-acceleration implication remains one-way; the converse from criticality
against *all* fixed-endpoint variations is deliberately deferred until S18 can
provide one curve-level acceleration field and the test-field realization
theorem.  No per-variation completeness witness or criticality equivalence is
exported here.  This is the S18 handoff: no coordinate acceleration or
competing geodesic predicate is introduced here.  The slice proves the
energy/length inequality and its equality condition, but deliberately
introduces no minimizer predicate; the existence and identification of
minimizers belong to S19.  The integral density uses unrestricted `mfderiv`;
the separate `velocityWithin` accessor retains the one-sided derivative needed
by endpoint terms.
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

/-- The canonical (unrestricted) velocity density of a parameterized curve.

This is the derivative used by the integral energy and length densities, in
the same form as Mathlib's `Manifold.pathELength`. -/
noncomputable def velocity (gamma : ℝ → M) (t : ℝ) : TangentSpace I (gamma t) :=
  (mfderiv 𝓘(ℝ, ℝ) I gamma t) 1

/-- The one-sided, interval-restricted velocity used for endpoint terms.

Its values can differ from `velocity` at interval endpoints; those values are
retained only where the first-variation boundary formula needs them. -/
noncomputable def velocityWithin (gamma : ℝ → M) (a b t : ℝ) : TangentSpace I (gamma t) :=
  (mfderiv[Icc a b] gamma t) 1

omit [IsManifold I ∞ M] in
/-- Away from the endpoints, the boundary-aware accessor agrees with the
canonical unrestricted velocity density. -/
theorem velocityWithin_eq_velocity_of_mem_Ioo
    {gamma : ℝ → M} {a b t : ℝ} (ht : t ∈ Ioo a b) :
    velocityWithin (I := I) gamma a b t = velocity (I := I) gamma t := by
  rw [velocityWithin, velocity, mfderivWithin_of_mem_nhds]
  exact Icc_mem_nhds ht.1 ht.2

/-- The squared speed density measured by the supplied bundle metric. -/
noncomputable def speedSq (gamma : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (gamma t) (velocity (I := I) gamma t) (velocity (I := I) gamma t)

/-- The nonnegative speed density. -/
noncomputable def speed (gamma : ℝ → M) (t : ℝ) : ℝ :=
  Real.sqrt (speedSq (I := I) g gamma t)

/-- The energy of a curve on `[a,b]`, with the Morgan--Tian normalization from
Morgan--Tian (`morganTian2007`, pp. 41--43). -/
noncomputable def energy (gamma : ℝ → M) (a b : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in a..b, speedSq (I := I) g gamma t

/-- The auxiliary real speed integral used for Cauchy--Schwarz.  It is not a
second manifold-length representation: `ofReal_curveLength_eq_pathELength`
below identifies it with Mathlib's canonical `Manifold.pathELength` when
`a ≤ b`; the totalized definition remains available for arbitrary endpoints. -/
noncomputable def curveLength (gamma : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, speed (I := I) g gamma t

omit [IsManifold I ∞ M] in
/-- A constant curve has zero unrestricted manifold velocity. -/
@[simp]
theorem velocity_const (x : M) (t : ℝ) :
    velocity (I := I) (fun _ : ℝ => x) t = 0 := by
  simp [velocity]

omit [IsManifold I ∞ M] in
/-- A constant curve has zero endpoint-restricted velocity as well. -/
@[simp]
theorem velocityWithin_const (x : M) (a b t : ℝ) :
    velocityWithin (I := I) (fun _ : ℝ => x) a b t = 0 := by
  rw [velocityWithin, mfderivWithin_const]
  simp

/-- The squared speed of a constant curve is zero.  This is the concrete
zero-velocity regression for the canonical metric energy. -/
@[simp]
theorem speedSq_zero (x : M) (t : ℝ) :
    speedSq (I := I) g (fun _ : ℝ => x) t = 0 := by
  simp only [speedSq, velocity_const]
  simp

/-- A constant curve has zero energy on every interval. -/
@[simp]
theorem energy_zero_of_const (x : M) (a b : ℝ) :
    energy (I := I) g (fun _ : ℝ => x) a b = 0 := by
  simp [energy]

/-- Positive definiteness of the supplied bundle metric. -/
theorem metric_inner_self_nonneg (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

/-- Nonnegativity of the canonical squared speed. -/
theorem speedSq_nonneg (gamma : ℝ → M) (t : ℝ) :
    0 ≤ speedSq (I := I) g gamma t := by
  exact metric_inner_self_nonneg (I := I) g (gamma t) (velocity (I := I) gamma t)

/-- Nonnegativity of the metric speed. -/
@[simp]
theorem speed_nonneg (gamma : ℝ → M) (t : ℝ) :
    0 ≤ speed (I := I) g gamma t :=
  Real.sqrt_nonneg _

/-- Squaring the nonnegative speed recovers the metric speed square. -/
theorem speed_sq (gamma : ℝ → M) (t : ℝ) :
    (speed (I := I) g gamma t) ^ 2 = speedSq (I := I) g gamma t := by
  exact Real.sq_sqrt (speedSq_nonneg (I := I) g gamma t)

/-- The scalar speed is the norm of the intrinsic tangent velocity for the
canonical metric bundle instance. -/
theorem speed_eq_norm_velocity (gamma : ℝ → M) (t : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    speed (I := I) g gamma t = ‖velocity (I := I) gamma t‖ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [speed, MorganTianLib.Ch01.norm_eq_sqrt_metric]
  rfl

/-- Unfolding the Morgan--Tian energy normalization. -/
theorem energy_eq_half_integral_speedSq (gamma : ℝ → M) (a b : ℝ) :
    energy (I := I) g gamma a b =
      (1 / 2 : ℝ) * ∫ t in a..b, speedSq (I := I) g gamma t := rfl

/-- The same normalization expressed using the scalar speed. -/
theorem energy_eq_half_integral_speed_sq (gamma : ℝ → M) (a b : ℝ) :
    energy (I := I) g gamma a b =
      (1 / 2 : ℝ) * ∫ t in a..b, (speed (I := I) g gamma t) ^ 2 := by
  simp_rw [speed_sq]
  rfl

/-- Unfolding the real speed-integral adapter used by the inequalities. -/
theorem curveLength_eq_integral_speed (gamma : ℝ → M) (a b : ℝ) :
    curveLength (I := I) g gamma a b =
      ∫ t in a..b, speed (I := I) g gamma t := rfl

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
    (hs : IntervalIntegrable (speed (I := I) g gamma) volume a b) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (curveLength (I := I) g gamma a b) =
      ∫⁻ t in Icc a b, ‖(mfderiv 𝓘(ℝ, ℝ) I gamma t) 1‖ₑ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [curveLength, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  have hIoc : IntegrableOn (speed (I := I) g gamma) (Ioc a b) volume := by
    rw [← uIoc_of_le hab]
    exact (intervalIntegrable_iff.mp hs)
  have hIcc : IntegrableOn (speed (I := I) g gamma) (Icc a b) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).2 hIoc
  have hnonneg : 0 ≤ᵐ[volume.restrict (Icc a b)]
      speed (I := I) g gamma :=
    Filter.Eventually.of_forall (fun t => speed_nonneg (I := I) g gamma t)
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
    (hs : IntervalIntegrable (speed (I := I) g gamma) volume a b) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (curveLength (I := I) g gamma a b) =
      Manifold.pathELength I gamma a b := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  exact ofReal_curveLength_eq_pathELength_integral (I := I) g gamma hab hs

/-- Energy is additive across adjacent intervals for the canonical
unrestricted density. Endpoint values of the separate `velocityWithin`
accessor are null for this integral and do not enter the API. -/
theorem energy_add (gamma : ℝ → M) {a b c : ℝ}
    (h₁ : IntervalIntegrable (speedSq (I := I) g gamma) volume a b)
    (h₂ : IntervalIntegrable (speedSq (I := I) g gamma) volume b c) :
    energy (I := I) g gamma a c =
      energy (I := I) g gamma a b + energy (I := I) g gamma b c := by
  simp only [energy]
  rw [← intervalIntegral.integral_add_adjacent_intervals h₁ h₂]
  ring

/-- Positivity follows from interval order and pointwise metric positivity;
Mathlib's totalized interval integral needs no separate integrability witness. -/
theorem energy_nonneg (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ energy (I := I) g gamma a b := by
  rw [energy]
  have h := intervalIntegral.integral_nonneg (μ := volume) hab
    (fun t ht => speedSq_nonneg (I := I) g gamma t)
  positivity

/-- Nonnegativity of the auxiliary real speed integral on an ordered interval.
The canonical manifold length is obtained from it through the `pathELength`
bridge above. -/
theorem curveLength_nonneg (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ curveLength (I := I) g gamma a b := by
  rw [curveLength]
  exact intervalIntegral.integral_nonneg hab
    (fun t _ => speed_nonneg (I := I) g gamma t)

/-- The interval energy/length inequality is the Cauchy--Schwarz step in
Morgan--Tian (`morganTian2007`, pp. 41--43) and do Carmo (`doCarmo1992`,
Ch. 9, Section 2). -/
theorem curveLength_sq_le_two_mul_interval_sub_mul_energy
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : IntervalIntegrable (speed (I := I) g gamma) volume a b)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma t) ^ 2) volume a b) :
    (curveLength (I := I) g gamma a b) ^ 2 ≤
      2 * (b - a) * energy (I := I) g gamma a b := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  have h := sq_intervalIntegral_le_mul_intervalIntegral_sq (f := speed (I := I) g gamma)
    hab hs hs2
  nlinarith

/-- The normalized `[0,1]` energy/length inequality (Morgan--Tian,
`morganTian2007`, pp. 41--43). -/
theorem curveLength_sq_le_two_mul_energy (gamma : ℝ → M)
    (hs : IntervalIntegrable (speed (I := I) g gamma) volume 0 1)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma t) ^ 2) volume 0 1) :
    (curveLength (I := I) g gamma 0 1) ^ 2 ≤
      2 * energy (I := I) g gamma 0 1 := by
  simpa using curveLength_sq_le_two_mul_interval_sub_mul_energy
    (I := I) g gamma (a := 0) (b := 1) (by norm_num) hs hs2

/-- Equality in the energy/length inequality is exactly a.e. constant speed;
the pointwise upgrade below uses continuity (Morgan--Tian,
`morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9). -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : IntervalIntegrable (speed (I := I) g gamma) volume a b)
    (hs2 : IntervalIntegrable
      (fun t => (speed (I := I) g gamma t) ^ 2) volume a b) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      speed (I := I) g gamma =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  convert sq_intervalIntegral_eq_iff_ae_eq_const hab hs hs2 using 1
  all_goals ring_nf

/-- A smooth-speed version of the equality characterization. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_of_continuousOn
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      speed (I := I) g gamma =ᵐ[volume.restrict (Ioc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
  apply curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff (I := I) g gamma hab
  · exact hs.intervalIntegrable_of_Icc hab.le
  · exact (hs.pow 2).intervalIntegrable_of_Icc hab.le

/-- With continuous speed, equality in the energy/length inequality is
pointwise constant norm of the velocity (including the endpoint values). -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma t = c := by
  have hbase := curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_of_continuousOn
    (I := I) g gamma hab hs
  constructor
  · intro heq
    have haeIoc := hbase.mp heq
    have haeIcc : speed (I := I) g gamma =ᵐ[volume.restrict (Icc a b)]
        Function.const ℝ (curveLength (I := I) g gamma a b / (b - a)) := by
      rw [Measure.restrict_congr_set (μ := volume) Ioc_ae_eq_Icc] at haeIoc
      exact haeIoc
    refine ⟨curveLength (I := I) g gamma a b / (b - a), ?_⟩
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne haeIcc hs continuousOn_const
  · rintro ⟨c, hc⟩
    rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
    have hEq : EqOn (speed (I := I) g gamma)
        (fun _ : ℝ => c) (uIcc a b) := by
      intro t ht
      exact hc t (by simpa [uIcc_of_le hab.le] using ht)
    have hEq2 : EqOn (fun t => (speed (I := I) g gamma t) ^ 2)
        (fun _ : ℝ => c ^ 2) (uIcc a b) := by
      intro t ht
      change (speed (I := I) g gamma t) ^ 2 = c ^ 2
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
    (hs : ContinuousOn (speed (I := I) g gamma) (Icc a b)) :
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma t = c := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp only [sub_self, mul_zero, curveLength, intervalIntegral.integral_same,
      pow_two, energy]
    constructor
    · intro _
      refine ⟨speed (I := I) g gamma a, ?_⟩
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
    (hconst : ∀ t ∈ Icc a b, speed (I := I) g gamma t = c) :
    (curveLength (I := I) g gamma a b) ^ 2 =
      2 * (b - a) * energy (I := I) g gamma a b := by
  rw [curveLength_eq_integral_speed, energy_eq_half_integral_speed_sq]
  have hEq : EqOn (speed (I := I) g gamma)
      (fun _ : ℝ => c) (uIcc a b) := by
    intro t ht
    exact hconst t (by simpa [uIcc_of_le hab] using ht)
  have hEq2 : EqOn (fun t => (speed (I := I) g gamma t) ^ 2)
      (fun _ : ℝ => c ^ 2) (uIcc a b) := by
    intro t ht
    change (speed (I := I) g gamma t) ^ 2 = c ^ 2
    rw [hconst t (by simpa [uIcc_of_le hab] using ht)]
  rw [intervalIntegral.integral_congr hEq,
    intervalIntegral.integral_congr hEq2,
    intervalIntegral.integral_const, intervalIntegral.integral_const]
  ring

/-- The same equality characterization stated literally as constancy of the
norm of the intrinsic velocity in the canonical metric bundle. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_const_norm_velocity
    (gamma : ℝ → M) {a b : ℝ} (hab : a < b)
    (hs : ContinuousOn (speed (I := I) g gamma) (Icc a b)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b,
        ‖velocity (I := I) gamma t‖ = c := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hbase := curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn
    (I := I) g gamma hab hs
  constructor
  · intro h
    rcases hbase.mp h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma t] using hc t ht
  · rintro ⟨c, hc⟩
    apply hbase.mpr
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma t] using hc t ht

/-- The same norm-velocity equality characterization, including a degenerate
interval.  The positive-length theorem above is retained separately so its
strict denominator hypothesis remains visible. -/
theorem curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_const_norm_velocity_of_le
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn (speed (I := I) g gamma) (Icc a b)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ((curveLength (I := I) g gamma a b) ^ 2 =
        2 * (b - a) * energy (I := I) g gamma a b) ↔
      ∃ c : ℝ, ∀ t ∈ Icc a b,
        ‖velocity (I := I) gamma t‖ = c := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hbase := curveLength_sq_eq_two_mul_interval_sub_mul_energy_iff_constOn_of_le
    (I := I) g gamma hab hs
  constructor
  · intro h
    rcases hbase.mp h with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma t] using hc t ht
  · rintro ⟨c, hc⟩
    apply hbase.mpr
    refine ⟨c, ?_⟩
    intro t ht
    simpa [speed_eq_norm_velocity (I := I) g gamma t] using hc t ht

/-- A typed, curve-level intrinsic acceleration contract.  Its acceleration is
indexed only by the base curve and interval, independently of any variation;
it is intended to be supplied by the S18 connection/geodesic producer.  This
module stores no coordinate acceleration and does not define a competing
geodesic predicate. -/
structure CovariantAccelerationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Type _ where
  acceleration : ∀ t, TangentSpace I (gamma t)
  speedSq_continuous :
    ContinuousOn (speedSq (I := I) g gamma) (Icc a b)
  speedSq_deriv : ∀ t ∈ Ioo a b,
    HasDerivAt (fun s => speedSq (I := I) g gamma s)
      (2 * g.inner (gamma t) (velocity (I := I) gamma t) (acceleration t)) t

section CanonicalConnection

variable [FiniteDimensional ℝ E]

/-- A differentiable global section agreeing with the curve velocity on the
chosen interval.  It is the explicit adapter needed by Mathlib's bundled
connection API.  This is an additional extension hypothesis, not an
along-curve derivative: it can be unavailable when a self-intersecting curve
has incompatible velocities at the same point. -/
structure VelocityExtension (gamma : ℝ → M) (a b : ℝ) : Type _ where
  field : ∀ x : M, TangentSpace I x
  mdifferentiable : MDiff (T% field)
  agrees : ∀ t ∈ uIcc a b,
    field (gamma t) = velocityWithin (I := I) gamma a b t

/-- Covariant differentiation of the supplied velocity section by the canonical
Levi--Civita connection.  The argument order is `∇_velocity velocity`. -/
noncomputable def canonicalAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b : ℝ}
    (X : VelocityExtension (I := I) gamma a b) (t : ℝ) :
    TangentSpace I (gamma t) :=
  Connection.leviCivitaConnection g X.field (gamma t)
    (velocityWithin (I := I) gamma a b t)

/-- A covariant-acceleration package whose connection-side value is explicit. -/
structure CanonicalAccelerationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Type _ where
  extension : VelocityExtension (I := I) gamma a b
  acceleration : ∀ t, TangentSpace I (gamma t)
  acceleration_eq : ∀ t ∈ uIcc a b,
    acceleration t = canonicalAcceleration g extension t
  speedSq_continuous :
    ContinuousOn (speedSq (I := I) g gamma) (Icc a b)
  speedSq_deriv : ∀ t ∈ Ioo a b,
    HasDerivAt (fun s => speedSq (I := I) g gamma s)
      (2 * g.inner (gamma t) (velocity (I := I) gamma t) (acceleration t)) t

/-- Forget the explicit Levi--Civita extension fields and retain the
acceleration and squared-speed derivative data as a generic
`CovariantAccelerationData` package.  This conversion does not create an
along-curve derivative producer. -/
def CanonicalAccelerationData.toCovariant
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {gamma : ℝ → M} {a b : ℝ}
    (D : CanonicalAccelerationData g gamma a b) :
    CovariantAccelerationData g gamma a b where
  acceleration := D.acceleration
  speedSq_continuous := D.speedSq_continuous
  speedSq_deriv := D.speedSq_deriv

end CanonicalConnection

/-- Zero covariant acceleration forces constant squared speed on the chosen
interval.  The proof is the fundamental theorem for interval integrals, with
the derivative order and endpoint orientation visible. -/
theorem speedSq_eq_of_zero_acceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (_hab : a ≤ b) (hzero : ∀ t ∈ Ioo a b, hacc.acceleration t = 0) :
    ∀ t₁ t₂, t₁ ∈ Icc a b → t₂ ∈ Icc a b →
      speedSq (I := I) g gamma t₁ = speedSq (I := I) g gamma t₂ := by
  intro t₁ t₂ ht₁ ht₂
  let lo := min t₁ t₂
  let hi := max t₁ t₂
  have hlo : lo ∈ Icc a b := by
    exact ⟨le_min ht₁.1 ht₂.1, (min_le_left _ _).trans ht₁.2⟩
  have hhi : hi ∈ Icc a b := by
    exact ⟨ht₁.1.trans (le_max_left _ _), max_le ht₁.2 ht₂.2⟩
  have hsub : Icc lo hi ⊆ Icc a b := by
    intro t ht
    exact ⟨hlo.1.trans ht.1, ht.2.trans hhi.2⟩
  have hderiv : ∀ t ∈ Ioo lo hi,
      HasDerivAt (fun s => speedSq (I := I) g gamma s) 0 t := by
    intro t ht
    have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_lt hlo.1 ht.1,
      lt_of_lt_of_le ht.2 hhi.2⟩
    simpa [hzero t ht'] using hacc.speedSq_deriv t ht'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    min_le_max (hacc.speedSq_continuous.mono hsub) hderiv
    (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (0 : ℝ)) volume lo hi)
  have hconst : speedSq (I := I) g gamma hi =
      speedSq (I := I) g gamma lo := by
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hftc
    linarith
  rcases le_total t₁ t₂ with h | h
  · simpa [lo, hi, min_eq_left h, max_eq_right h] using hconst.symm
  · simpa [lo, hi, min_eq_right h, max_eq_left h] using hconst

/-- The same constant-speed conclusion through the canonical
Levi--Civita-connection adapter.  The adapter applies the bundled connection
to an explicitly supplied global velocity extension; it is not yet the S18
along-curve covariant-derivative producer. -/
theorem speedSq_eq_of_zero_canonical_acceleration
    [FiniteDimensional ℝ E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CanonicalAccelerationData g gamma a b)
    (hab : a ≤ b) (hzero : ∀ t ∈ Ioo a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0) :
    ∀ t₁ t₂, t₁ ∈ Icc a b → t₂ ∈ Icc a b →
      speedSq (I := I) g gamma t₁ = speedSq (I := I) g gamma t₂ := by
  apply speedSq_eq_of_zero_acceleration (I := I) g gamma hacc.toCovariant hab
  intro t ht
  change hacc.acceleration t = 0
  have ht_u : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ht.1.le, ht.2.le⟩
  rw [hacc.acceleration_eq t ht_u]
  exact hzero t ht

/-- Constant squared speed on an ordered interval implies constant speed. -/
theorem speed_eq_of_zero_acceleration_on_Icc
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (hab : a ≤ b) (hzero : ∀ t ∈ Ioo a b, hacc.acceleration t = 0)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    speed (I := I) g gamma t₁ = speed (I := I) g gamma t₂ := by
  have hsq := speedSq_eq_of_zero_acceleration (I := I) g gamma hacc
    hab hzero t₁ t₂ ht₁ ht₂
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
    (hzero : ∀ t ∈ Ioo a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0)
    (t₁ t₂ : ℝ) (ht₁ : t₁ ∈ Icc a b) (ht₂ : t₂ ∈ Icc a b) :
    speed (I := I) g gamma t₁ = speed (I := I) g gamma t₂ := by
  refine speed_eq_of_zero_acceleration_on_Icc (I := I) g gamma hacc.toCovariant hab ?_
      t₁ t₂ ht₁ ht₂
  intro t ht
  change hacc.acceleration t = 0
  have ht_u : t ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ht.1.le, ht.2.le⟩
  rw [hacc.acceleration_eq t ht_u]
  exact hzero t ht

/-- A zero-acceleration package supplies a single pointwise speed on the whole
ordered interval. -/
theorem exists_const_speed_of_zero_acceleration_on_Icc
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hacc : CovariantAccelerationData g gamma a b)
    (hab : a ≤ b) (hzero : ∀ t ∈ Ioo a b, hacc.acceleration t = 0) :
    ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma t = c := by
  refine ⟨speed (I := I) g gamma a, ?_⟩
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
    (hzero : ∀ t ∈ Ioo a b,
      canonicalAcceleration (I := I) g hacc.extension t = 0) :
    ∃ c : ℝ, ∀ t ∈ Icc a b, speed (I := I) g gamma t = c := by
  refine ⟨speed (I := I) g gamma a, ?_⟩
  intro t ht
  exact speed_eq_of_zero_canonical_acceleration_on_Icc (I := I) g gamma hacc hab hzero
    t a ht (left_mem_Icc.2 hab)

/-- Constant-speed segment energy, including the degenerate interval case. -/
theorem energy_eq_half_interval_mul_of_speedSq_eq_const
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b c : ℝ} (hab : a ≤ b)
    (hconst : ∀ t ∈ Icc a b,
      speedSq (I := I) g gamma t = c ^ 2) :
    energy (I := I) g gamma a b = (1 / 2 : ℝ) * (b - a) * c ^ 2 := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g gamma)
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
private theorem euclidean_straightLine_energy_density (a b v : ℝ) (_hab : a ≤ b) :
    (1 / 2 : ℝ) * (∫ _t in a..b, v ^ 2) =
      (1 / 2 : ℝ) * (b - a) * v ^ 2 := by
  rw [intervalIntegral.integral_const]
  ring

/-! ### Concrete flat-model regression -/

/-- The canonical interval-restricted velocity of an affine real line is its
constant slope. -/
private theorem euclidean_straightLine_velocity (p v : ℝ) {a b t : ℝ}
    (hab : a < b) (ht : t ∈ Icc a b) :
    velocityWithin (I := 𝓘(ℝ, ℝ)) (fun s : ℝ => p + s * v) a b t = v := by
  rw [velocityWithin, mfderivWithin_eq_fderivWithin]
  change (fderivWithin ℝ (fun s : ℝ => p + s * v) (Icc a b) t) 1 = v
  have hd : HasDerivAt (fun s : ℝ => p + s * v) v t := by
    simpa using ((hasDerivAt_id t).mul_const v).const_add p
  rw [hd.hasFDerivAt.hasFDerivWithinAt.fderivWithin
    ((uniqueDiffOn_Icc hab).uniqueDiffWithinAt ht)]
  simp

private theorem euclidean_straightLine_velocity_unrestricted (p v t : ℝ) :
    velocity (I := 𝓘(ℝ, ℝ)) (fun s : ℝ => p + s * v) t = v := by
  rw [velocity, mfderiv_eq_fderiv]
  change (fderiv ℝ (fun s : ℝ => p + s * v) t) 1 = v
  have hd : HasDerivAt (fun s : ℝ => p + s * v) v t := by
    simpa using ((hasDerivAt_id t).mul_const v).const_add p
  rw [hd.hasFDerivAt.fderiv]
  simp

/-- The affine real line has the expected Euclidean squared speed. -/
private theorem euclidean_straightLine_speedSq (p v : ℝ) (t : ℝ) :
    let g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
        (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
      { riemannianMetricVectorSpace ℝ with
        contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le (by simp) }
    speedSq (I := 𝓘(ℝ, ℝ)) g (fun s : ℝ => p + s * v) t = v ^ 2 := by
  dsimp
  rw [speedSq, euclidean_straightLine_velocity_unrestricted p v t]
  change inner ℝ v v = v ^ 2
  simp

/-- The concrete Euclidean straight line has the normalized energy
`(1/2) * (b-a) * v^2`. -/
private theorem euclidean_straightLine_energy (p v : ℝ) {a b : ℝ} (_hab : a < b) :
    let g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
        (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
      { riemannianMetricVectorSpace ℝ with
        contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le (by simp) }
    energy (I := 𝓘(ℝ, ℝ)) g (fun s : ℝ => p + s * v) a b =
      (1 / 2 : ℝ) * (b - a) * v ^ 2 := by
  dsimp
  unfold energy
  have hEq : EqOn
      (speedSq (I := 𝓘(ℝ, ℝ))
        ({ riemannianMetricVectorSpace ℝ with
          contMDiff := (riemannianMetricVectorSpace ℝ).contMDiff.of_le (by simp) })
        (fun s : ℝ => p + s * v))
      (fun _ : ℝ => v ^ 2) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le _hab.le] at ht
    exact euclidean_straightLine_speedSq p v t
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const]
  simp [smul_eq_mul]
  ring

/-- Zero velocity gives zero energy. -/
theorem energy_eq_zero_of_velocity_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {a b : ℝ} (hab : a ≤ b)
    (hzero : ∀ t ∈ Icc a b, velocity (I := I) gamma t = 0) :
    energy (I := I) g gamma a b = 0 := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g gamma)
      (fun _ : ℝ => (0 : ℝ)) (uIcc a b) := by
    intro t ht
    rw [speedSq]
    simp [hzero t (by simpa [uIcc_of_le hab] using ht)]
  rw [intervalIntegral.integral_congr hEq]
  simp

/-- Pointwise sign regression valid for a nonconstant metric as well as a
constant one: positive definiteness, not metric constancy, controls every
energy density. -/
private theorem nonconstant_metric_sign_probe
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) :
    0 ≤ g.inner (gamma t) (velocity (I := I) gamma t)
      (velocity (I := I) gamma t) :=
  speedSq_nonneg (I := I) g gamma t

/-- Strict positivity at a nonzero velocity, valid for a metric that varies
with the base point as well as for a constant Euclidean metric. -/
private theorem metric_sign_probe_of_nonzero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ)
    (hv : velocity (I := I) gamma t ≠ 0) :
    0 < g.inner (gamma t) (velocity (I := I) gamma t)
      (velocity (I := I) gamma t) :=
  g.pos (gamma t) _ hv

/-! ### Reparameterization and variation contracts -/

/-- A density-scaling helper for a positive affine change of variables.
`density_eq` is the manifold chain-rule witness: it is intentionally visible
because the current Mathlib connection layer has no along-curve derivative
producer.  The composition hypothesis that identifies `delta` with the
reparameterized curve is supplied by
`energy_affine_reparam_of_composition`, not by this density-only theorem. -/
theorem energy_affine_reparam_of_density
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma delta : ℝ → M} {a b alpha beta : ℝ} (hab : a ≤ b) (halpha : 0 < alpha)
    (density_eq : ∀ t ∈ uIcc a b,
      speedSq (I := I) g delta t =
        alpha ^ 2 * speedSq (I := I) g gamma (alpha * t + beta))
    (hgamma : ContinuousOn
      (speedSq (I := I) g gamma)
      (Icc (alpha * a + beta) (alpha * b + beta))) :
    energy (I := I) g delta a b =
      alpha * energy (I := I) g gamma (alpha * a + beta) (alpha * b + beta) := by
  unfold energy
  have hEq : EqOn (speedSq (I := I) g delta)
      (fun t => alpha ^ 2 * speedSq (I := I) g gamma (alpha * t + beta))
      (uIcc a b) := by
    intro t ht
    exact density_eq t ht
  have hchange :
      (∫ t in a..b,
        (speedSq (I := I) g gamma ∘ (fun x : ℝ => alpha * x + beta)) t * alpha) =
        ∫ t in alpha * a + beta..alpha * b + beta,
          speedSq (I := I) g gamma t := by
    apply intervalIntegral.integral_comp_mul_deriv'
    · intro x hx
      simpa [Function.comp_def] using
        (hasDerivAt_id x).const_mul alpha |>.add_const beta
    · exact continuousOn_const
    · apply hgamma.mono
      rintro _ ⟨t, ht, rfl⟩
      rw [uIcc_of_le hab] at ht
      constructor <;> nlinarith [ht.1, ht.2, halpha]
  have hscale :
      (∫ t in a..b, alpha ^ 2 *
        speedSq (I := I) g gamma (alpha * t + beta)) =
        alpha * (∫ t in a..b,
          speedSq (I := I) g gamma (alpha * t + beta) * alpha) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
    ring
  rw [intervalIntegral.integral_congr hEq, hscale]
  have hchange' :
      (∫ t in a..b,
        speedSq (I := I) g gamma (alpha * t + beta) * alpha) =
        ∫ t in alpha * a + beta..alpha * b + beta,
          speedSq (I := I) g gamma t := by
    simpa [Function.comp_def] using hchange
  rw [hchange']
  ring

/-- Affine reparameterization with the curve-composition equality made
explicit.  The remaining `density_eq` field is the manifold chain-rule
witness; it is separated from the algebraic change-of-variables proof. -/
theorem energy_affine_reparam_of_composition
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma delta : ℝ → M} {a b alpha beta : ℝ} (hab : a ≤ b) (halpha : 0 < alpha)
    (hdelta : delta = gamma ∘ (fun t : ℝ => alpha * t + beta))
    (density_eq : ∀ t ∈ uIcc a b,
      speedSq (I := I) g (gamma ∘ (fun t : ℝ => alpha * t + beta)) t =
        alpha ^ 2 * speedSq (I := I) g gamma (alpha * t + beta))
    (hgamma : ContinuousOn
      (speedSq (I := I) g gamma)
      (Icc (alpha * a + beta) (alpha * b + beta))) :
    energy (I := I) g delta a b =
      alpha * energy (I := I) g gamma (alpha * a + beta) (alpha * b + beta) := by
  apply energy_affine_reparam_of_density (I := I) g hab halpha
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

omit [IsManifold I ∞ M] in
/-- Every parameter slice of a smooth variation is differentiable at the zero
slice, including the endpoints of the curve interval. -/
theorem SmoothVariation.mdifferentiableAt_parameterSlice
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) (t : ℝ)
    (ht : t ∈ Icc a b) :
    MDifferentiableAt 𝓘(ℝ, ℝ) I (fun s : ℝ => V.family s t) 0 := by
  have hrect : (0, t) ∈ Icc (-epsilon) epsilon ×ˢ Icc a b := by
    exact ⟨⟨by linarith [V.epsilon_pos], V.epsilon_pos.le⟩, ht⟩
  have hsurf := V.surface_smooth (0, t) hrect
  rw [modelWithCornersSelf_prod] at hsurf
  rw [← chartedSpaceSelf_prod] at hsurf
  have hwithin := ContMDiffWithinAt.curry_left (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ))
    (J := I) (f := V.family) (s := Icc (-epsilon) epsilon ×ˢ Icc a b)
    hsurf
  have hnhds : Icc (-epsilon) epsilon ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith [V.epsilon_pos]) V.epsilon_pos
  have hset : {x : ℝ | (x, t) ∈ Icc (-epsilon) epsilon ×ˢ Icc a b} =
      Icc (-epsilon) epsilon := by
    ext x
    simp [ht.1, ht.2]
  rw [hset] at hwithin
  exact (hwithin.contMDiffAt hnhds).mdifferentiableAt (by norm_num)

omit [IsManifold I ∞ M] in
/-- The manifold derivative used in `variationalVectorField` is the genuine
derivative of every parameter slice at the zero slice. -/
theorem SmoothVariation.hasMFDerivAt_parameterSlice
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) (t : ℝ)
    (ht : t ∈ Icc a b) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s : ℝ => V.family s t) 0
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ => V.family s t) 0) := by
  exact (V.mdifferentiableAt_parameterSlice t ht).hasMFDerivAt

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

/-- The variational vector field `∂F/∂s` at the zero slice.
`SmoothVariation.hasMFDerivAt_parameterSlice` records that this totalized
manifold derivative is genuine on the whole curve interval. -/
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

/-- The zero slice has the prescribed curve energy.  The unrestricted density
is compared on the open interval, where the zero-slice equality supplies the
needed neighborhood congruence; endpoint values are null for the integral. -/
theorem variationEnergy_zero_eq_energy
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) :
    variationEnergy (I := I) g V 0 = energy (I := I) g gamma a b := by
  rw [variationEnergy, energy, energy]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le V.interval_order
  intro t ht
  have hlocal : baseCurve V =ᶠ[𝓝 t] gamma := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with x hx
    exact V.zero_slice x hx
  change speedSq (I := I) g (baseCurve V) t =
    speedSq (I := I) g gamma t
  simp only [speedSq, velocity]
  rw [hlocal.mfderiv_eq, hlocal.self_of_nhds]

/-- The metric pairing of the variational field and base velocity. -/
noncomputable def variationPairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
  (V : SmoothVariation (I := I) gamma a b epsilon) (t : ℝ) : ℝ :=
  g.inner (baseCurve V t) (variationalVectorField V t)
    (velocityWithin (I := I) (baseCurve V) a b t)

/-- Pairing of a supplied covariant derivative with the base velocity. -/
noncomputable def covariantPairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
  (V : SmoothVariation (I := I) gamma a b epsilon)
    (D : ∀ t, TangentSpace I (baseCurve V t)) (t : ℝ) : ℝ :=
  g.inner (baseCurve V t) (D t)
    (velocity (I := I) (baseCurve V) t)

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
/-- Endpoint-fixed surface hypotheses on the declared parameter rectangle imply
the endpoint vector condition.  Only a neighborhood of the zero slice is
needed for the unrestricted `mfderiv` in `variationalVectorField`. -/
theorem endpointVectorsZero_of_fixed_endpoints
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon)
    (hleft : ∀ s ∈ Icc (-epsilon) epsilon, V.family s a = V.family 0 a)
    (hright : ∀ s ∈ Icc (-epsilon) epsilon, V.family s b = V.family 0 b) :
    EndpointVectorsZero (I := I) V := by
  have hnhds : Icc (-epsilon) epsilon ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith [V.epsilon_pos]) V.epsilon_pos
  constructor
  · have hfun : (fun s => V.family s a) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ : ℝ => V.family 0 a) :=
      Filter.eventually_of_mem hnhds hleft
    rw [variationalVectorField, hfun.mfderiv_eq]
    simp [baseCurve]
    rfl

  · have hfun : (fun s => V.family s b) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ : ℝ => V.family 0 b) :=
      Filter.eventually_of_mem hnhds hright
    rw [variationalVectorField, hfun.mfderiv_eq]
    simp [baseCurve]
    rfl

/-! ### Differentiation under the integral and first variation -/

/-- All analytic data needed for the intrinsic first variation (Morgan--Tian,
`morganTian2007`, pp. 41--43; do Carmo, `doCarmo1992`, Ch. 9, Sections 2--3).

`energy_deriv_eq_integral` is the supplied differentiation-under-the-integral,
metric-compatibility, and mixed-partial/connection bridge.
The factor `1/2` in the energy cancels the `2` from differentiating the
metric square, leaving the unhalved pairing below.
The fields are deliberately witnesses rather than axioms hidden in a theorem:
they expose exactly which regularity remains to be discharged by the S18
geodesic producer.  In particular, `acceleration` is local to this variation;
this structure does not claim that it is the single curve-level acceleration
used by the fundamental lemma. -/
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
  pairing_continuous :
    ContinuousOn (variationPairing (I := I) g V) (Icc a b)
  pairing_deriv : ∀ t ∈ Ioo a b,
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
Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, with
continuity on the closed interval and derivatives on its interior.
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
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    V.interval_order D.pairing_continuous (fun t ht => D.pairing_deriv t ht) hsum
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

/-- A variation is energy-critical when its energy has the genuine zero
derivative at the zero slice.  Using `HasDerivAt` avoids Mathlib's totalized
`deriv`, which would classify a nondifferentiable variation as critical. -/
def IsEnergyCritical
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    (V : SmoothVariation (I := I) gamma a b epsilon) : Prop :=
  HasDerivAt (variationEnergy (I := I) g V) 0 0

/-- Under a `FirstVariationData` package, genuine criticality is equivalent to
vanishing of the supplied derivative value. -/
theorem isEnergyCritical_iff_energyDerivative_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) :
    IsEnergyCritical (I := I) g V ↔ D.energyDerivative = 0 := by
  constructor
  · intro h
    exact D.energy_deriv.unique h
  · intro h
    change HasDerivAt (variationEnergy (I := I) g V) 0 0
    simpa [h] using D.energy_deriv

/-- The intrinsic acceleration-zero predicate on the open curve interior.
Endpoint acceleration values are deliberately excluded because the derivative
and interval-integral contracts are insensitive to null endpoint changes. -/
def IsZeroCovariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {a b epsilon : ℝ}
    {V : SmoothVariation (I := I) gamma a b epsilon}
    (D : FirstVariationData (I := I) g V) : Prop :=
  ∀ t ∈ Ioo a b, D.acceleration t = 0

/-- Zero intrinsic acceleration implies criticality for a fixed-endpoint
variation.  This is intentionally a one-way, variation-local statement: it
does not identify `D.acceleration` with the curve-level
`CovariantAccelerationData` used by the future S18 fundamental-lemma proof. -/
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
        (fun _ : ℝ => (0 : ℝ)) (Ioo a b) := by
      intro t ht
      simp [accelerationPairing, hzero t ht]
    rw [intervalIntegral.integral_congr_Ioo_of_le V.interval_order hEq]
    simp
  rw [hacc] at hderiv
  simpa [IsEnergyCritical] using hderiv

/-- The universal fixed-endpoint criticality premise used by the future
fundamental-lemma theorem.  This is only a premise: this module deliberately
does not assert a converse or identify a per-variation acceleration witness
with the curve-level `CovariantAccelerationData`.  The nonempty endpoint-fixed
variation premise prevents the universal statement from becoming vacuous for a
curve that admits no such variation. -/
def AllFixedEndpointEnergyCritical
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a b : ℝ) : Prop :=
  a ≤ b ∧
    (∃ epsilon, ∃ V : SmoothVariation (I := I) gamma a b epsilon,
      EndpointVectorsZero (I := I) V) ∧
    ∀ epsilon, ∀ V : SmoothVariation (I := I) gamma a b epsilon,
      EndpointVectorsZero (I := I) V → IsEnergyCritical (I := I) g V

end CurveEnergy

end Variation

/-! The primitive energy names are re-exported at the geodesic ownership
boundary.  The variation-specific contracts remain under `Geodesic.Variation`.
-/
export Variation (velocity velocityWithin speedSq speed energy curveLength speed_eq_norm_velocity)

end Geodesic
end Ch01
end MorganTianLib
