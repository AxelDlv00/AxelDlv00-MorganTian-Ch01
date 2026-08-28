/-
Copyright (c) 2026 Axel Dlv. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
-/
import MorganTianLib.Ch01.Connection.Christoffel
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Geodesics

This module is the Chapter 1 geodesic handoff.  It uses the canonical bundled
Levi--Civita connection from `Ch01.Connection` and gives a fixed-chart
second-order reduction together with its current-foot transport.  The local
IVP and uniqueness results are deliberately chart-local; moving-chart gluing,
the maximal interval, and smooth dependence on initial data are later F2 work.

In a chart `alpha`, the equation is

`u''^k + Gamma^k_ij (u) u'^i u'^j = 0`,

where `u = extChartAt I alpha ∘ gamma`.  The coefficient is obtained by
applying `Connection.leviCivitaConnection g` to the coordinate frame; hence the
lower slots and the sign are fixed by the bundled connection rather than by a
second connection facade.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Definition
1.17 and the coordinate/initial-value paragraph on printed p. 41 (`morganTian2007`).
-/

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace MorganTianLib
namespace Ch01
namespace Geodesic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Coordinates

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The coordinate coefficient extracted from Mathlib's bundled
Levi--Civita connection.  The first lower slot is the direction field and
the second is the differentiated field, so this is `Gamma^k_ij` in the
Morgan--Tian convention. -/
private noncomputable def chartConnectionCoeff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha q : M) (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  t.localFrame_coeff I b k q
    (Connection.leviCivitaConnection g (t.localFrame b j) q (t.localFrame b i q))

private theorem chartConnectionCoeff_contMDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (i j k : Fin (Module.finrank ℝ E)) {q : M}
    (hq : q ∈ (chartAt H alpha).source) :
    CMDiffAt ∞
      (chartConnectionCoeff (I := I) g alpha · i j k) q := by
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  have hbase : q ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hq
  have hframe (a : Fin (Module.finrank ℝ E)) :
      CMDiffAt ∞ (T% (t.localFrame b a)) q :=
    contMDiffAt_localFrame_of_mem (I := I) (n := ∞) (e := t) (b := b) a hbase
  have hcov : CMDiffAt ∞
      (T% (fun y ↦ Connection.leviCivitaConnection g (t.localFrame b j) y
        (t.localFrame b i y))) q :=
    Connection.contMDiffAt_leviCivitaConnection_apply g (hframe i) (hframe j)
  have hcoeff : CMDiffAt ∞
      ((LinearMap.piApply (t.localFrame_coeff I b k))
        (fun y ↦ Connection.leviCivitaConnection g (t.localFrame b j) y
          (t.localFrame b i y))) q :=
    contMDiffAt_localFrame_coeff b hbase hcov k
  exact hcoeff

/-- The Christoffel coefficient in the chart centred at `alpha`.

The first lower slot is the coordinate direction and the second is the
differentiated vector field, matching the argument order of Mathlib's
`CovariantDerivative` and Morgan--Tian's `Gamma^k_ij`. -/
private def chartChristoffel
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  chartConnectionCoeff (I := I) g alpha ((extChartAt I alpha).symm y) i j k

/-- Unfolding rule for the chart coefficient. -/
@[simp] private theorem chartChristoffel_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g alpha y i j k =
      chartConnectionCoeff (I := I) g alpha ((extChartAt I alpha).symm y) i j k := rfl

/-- Unfolded connection bridge for the public coefficient. -/
private theorem chartChristoffel_eq_leviCivita
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g alpha y i j k =
      let q := (extChartAt I alpha).symm y
      let t := trivializationAt E (TangentSpace I) alpha
      let b := Module.finBasis ℝ E
      t.localFrame_coeff I b k q
        (Connection.leviCivitaConnection g (t.localFrame b j) q
          (t.localFrame b i q)) := rfl

private theorem chartChristoffel_contDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I alpha).target) :
    ContDiffAt ℝ ∞ (chartChristoffel (I := I) g alpha · i j k) y := by
  have hytarget : y ∈ (extChartAt I alpha).target := interior_subset hy
  have hsymm : CMDiffAt ∞ (extChartAt I alpha).symm y :=
    (contMDiffWithinAt_extChartAt_symm_target alpha hytarget).contMDiffAt
      (mem_of_superset (isOpen_interior.mem_nhds hy) interior_subset)
  have hsource : (extChartAt I alpha).symm y ∈ (chartAt H alpha).source :=
    by simpa only [extChartAt_source (I := I)] using
      (extChartAt I alpha).map_target hytarget
  have hcoeff := chartConnectionCoeff_contMDiffAt (I := I) g alpha i j k hsource
  simpa only [chartChristoffel, Function.comp_def] using (hcoeff.comp y hsymm).contDiffAt

private def chartSpraySecond
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v : E) : E :=
  let b := Module.finBasis ℝ E
  ∑ k : Fin (Module.finrank ℝ E),
    (-∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (I := I) g alpha y i j k * b.repr v i * b.repr v j) • b k

/-- The canonical-connection contraction `Gamma(v,w)` in the chart centred at
`alpha`.

The first velocity supplies the direction (the first lower Christoffel slot),
and the second supplies the differentiated vector field.  This is the one
coordinate adapter intentionally shared with the local geodesic and Jacobi
certificates; the frame/coefficient implementation and compatibility aliases
above remain private. -/
def chartConnectionContraction
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) : E :=
  let b := Module.finBasis ℝ E
  let q := (extChartAt I alpha).symm y
  let t := trivializationAt E (TangentSpace I) alpha
  ∑ k : Fin (Module.finrank ℝ E),
    (∑ i : Fin (Module.finrank ℝ E),
      ∑ j : Fin (Module.finrank ℝ E),
        t.localFrame_coeff I b k q
          (Connection.leviCivitaConnection g (t.localFrame b j) q
            (t.localFrame b i q)) * b.repr v i * b.repr w j) • b k

/-- Internal alias retained only for the chart-spray proof. -/
private def chartChristoffelContraction
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) : E :=
  chartConnectionContraction (I := I) g alpha y v w

/-- The public Christoffel contraction is the canonical connection contraction.
-/
private theorem chartChristoffelContraction_eq_connection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) :
    chartChristoffelContraction (I := I) g alpha y v w =
      chartConnectionContraction (I := I) g alpha y v w := rfl

/-- The contraction used by the coordinate equation, expanded to the
canonical bundled connection.  This is the declaration-level bridge behind
the coordinate realization of `D_t (gamma')`. -/
private theorem chartChristoffelContraction_eq_leviCivita
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) :
    chartChristoffelContraction (I := I) g alpha y v w =
      let b := Module.finBasis ℝ E
      let q := (extChartAt I alpha).symm y
      let t := trivializationAt E (TangentSpace I) alpha
      ∑ k : Fin (Module.finrank ℝ E),
        (∑ i : Fin (Module.finrank ℝ E),
          ∑ j : Fin (Module.finrank ℝ E),
            t.localFrame_coeff I b k q
              (Connection.leviCivitaConnection g (t.localFrame b j) q
                (t.localFrame b i q)) * b.repr v i * b.repr w j) • b k := by
  rfl

private theorem chartSpraySecond_eq_neg_contraction
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v : E) :
    chartSpraySecond (I := I) g alpha y v =
      -chartChristoffelContraction (I := I) g alpha y v v := by
  simp only [chartSpraySecond, chartChristoffelContraction, chartConnectionContraction,
    Finset.sum_neg_distrib, neg_smul, chartChristoffel_eq_leviCivita]

/-- The first-order spray associated with the chart equation. -/
private def chartSpray
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) : E × E → E × E :=
  fun z => (z.2, chartSpraySecond (I := I) g alpha z.1 z.2)

private theorem chartSpray_contDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {y v : E} (hy : y ∈ interior (extChartAt I alpha).target) :
    ContDiffAt ℝ ∞ (chartSpray (I := I) g alpha) (y, v) := by
  classical
  let b := Module.finBasis ℝ E
  let c := fun i : Fin (Module.finrank ℝ E) =>
    (⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩ : E →L[ℝ] ℝ)
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      ContDiffAt ℝ ∞ (fun z : E × E => b.repr z.2 i) (y, v) := by
    convert (c i).contDiff.contDiffAt.comp (y, v) contDiffAt_snd using 1
    ext z
    rfl
  have hsecond : ContDiffAt ℝ ∞
      (fun z : E × E => chartSpraySecond (I := I) g alpha z.1 z.2) (y, v) := by
    simp only [chartSpraySecond]
    apply ContDiffAt.sum
    intro k _
    apply ContDiffAt.smul_const
    apply ContDiffAt.neg
    apply ContDiffAt.sum
    intro i _
    apply ContDiffAt.sum
    intro j _
    exact (((chartChristoffel_contDiffAt (I := I) g alpha i j k hy).comp
      (y, v) contDiffAt_fst).mul (hcoord i)).mul (hcoord j)
  exact contDiffAt_snd.prodMk hsecond

/-- The `E`-coordinate of a tangent vector in the chart trivialisation at `p`.

This is the velocity variable used by the local first-order spray. -/
def chartVelocityAt (p : M) (v : TangentSpace I p) : E :=
  (trivializationAt E (TangentSpace I) p (⟨p, v⟩ : TangentBundle I M)).2

/-- The chart reading of a curve. -/
def chartReading (alpha : M) (gamma : ℝ → M) : ℝ → E :=
  fun t => extChartAt I alpha (gamma t)

/-- The second-order regularity needed by the coordinate geodesic equation.

The eventual first-derivative clause is intentional: Mathlib's `deriv` is
totalized, so differentiability only at the base time would admit spurious
second derivatives. -/
def HasChartGeodesicRegularityAt (alpha : M) (gamma : ℝ → M) (t : ℝ) : Prop :=
  (∀ᶠ s in 𝓝 t, gamma s ∈ (chartAt H alpha).source) ∧
    HasDerivAt (chartReading (I := I) alpha gamma)
        (deriv (chartReading (I := I) alpha gamma) t) t ∧
      (∀ᶠ s in 𝓝 t, HasDerivAt (chartReading (I := I) alpha gamma)
        (deriv (chartReading (I := I) alpha gamma) s) s) ∧
      DifferentiableAt ℝ (deriv (chartReading (I := I) alpha gamma)) t

/-- The coordinate acceleration `u'' + Gamma(u',u')` in a fixed chart. -/
def chartAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) (t : ℝ) : E :=
  deriv (deriv (chartReading (I := I) alpha gamma)) t +
    chartConnectionContraction (I := I) g alpha
      (chartReading (I := I) alpha gamma t)
      (deriv (chartReading (I := I) alpha gamma) t)
      (deriv (chartReading (I := I) alpha gamma) t)

/-- The chart ODE at one time, in solved second-order form. -/
def HasChartGeodesicEquationAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) (t : ℝ) : Prop :=
  HasChartGeodesicRegularityAt (I := I) alpha gamma t ∧
    chartAcceleration (I := I) g alpha gamma t = 0

/-- The chart equation on a set of times. -/
def HasChartGeodesicEquationOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, gamma t ∈ (chartAt H alpha).source ∧
    HasChartGeodesicEquationAt (I := I) g alpha gamma t

/-- Restricting a chart equation to a smaller time set preserves the equation.

This is the local restriction compatibility used when a later maximal-domain
construction glues overlapping solutions. -/
theorem HasChartGeodesicEquationOn.mono
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) {s s' : Set ℝ} (hs : s' ⊆ s)
    (hgamma : HasChartGeodesicEquationOn (I := I) g alpha gamma s) :
    HasChartGeodesicEquationOn (I := I) g alpha gamma s' := by
  intro t ht
  exact hgamma t (hs ht)

/-- Local existence for prescribed position and velocity in the canonical
chart.  The interval is deliberately returned as a symmetric open interval;
the intrinsic maximal-domain construction belongs to the next geodesic slice.

The velocity is represented in the chart trivialisation by `chartVelocityAt`.
The only analytic completeness input is `[CompleteSpace E]`; boundarylessness
is supplied separately by `exists_localChartGeodesicAt_boundaryless`.  The
returned curve is continuous at every time in the displayed interval. -/
theorem exists_localChartGeodesicAt [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt γ t) := by
  let y₀ : E := extChartAt I p p
  let w₀ : E := chartVelocityAt (I := I) p v
  have hy₀ : y₀ ∈ interior (extChartAt I p).target := by
    exact (I.isInteriorPoint_iff).mp hp
  have hspray : ContDiffAt ℝ 1 (chartSpray (I := I) g p) (y₀, w₀) :=
    (chartSpray_contDiffAt (I := I) g p hy₀).of_le (by norm_num)
  obtain ⟨ζ, hζ₀, ε, hε, hζ⟩ :=
    hspray.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hzero : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith
  have hζzero := hζ 0 hzero
  have hζpos₀ : HasDerivAt (fun s => (ζ s).1) w₀ 0 := by
    have h := (hζzero.hasFDerivAt.fst).hasDerivAt
    simpa [chartSpray, w₀, hζ₀] using h
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), (ζ s).1 ∈ interior (extChartAt I p).target := by
    have hmem : (ζ 0).1 ∈ interior (extChartAt I p).target := by
      simpa only [hζ₀, y₀] using hy₀
    exact hζpos₀.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hmem)
  obtain ⟨δ, hδ, hδmem⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let ε' := min ε δ
  have hε' : 0 < ε' := lt_min hε hδ
  have hsub (t : ℝ) (ht : t ∈ Ioo (-ε') ε') : t ∈ Ioo (-ε) ε := by
    have hεmin : ε' ≤ ε := min_le_left ε δ
    constructor
    · exact lt_of_le_of_lt (neg_le_neg hεmin) ht.1
    · exact lt_of_lt_of_le ht.2 hεmin
  have htarget (t : ℝ) (ht : t ∈ Ioo (-ε') ε') :
      (ζ t).1 ∈ interior (extChartAt I p).target := by
    have hδmin : ε' ≤ δ := min_le_right ε δ
    apply hδmem t
    rw [Real.ball_eq_Ioo]
    constructor
    · linarith [ht.1, hδmin]
    · linarith [ht.2, hδmin]
  let γ : ℝ → M := (extChartAt I p).symm ∘ fun t => (ζ t).1
  have hread (t : ℝ) (ht : t ∈ Ioo (-ε') ε') :
      chartReading (I := I) p γ t = (ζ t).1 := by
    dsimp [chartReading, γ]
    exact (extChartAt I p).right_inv (interior_subset (htarget t ht))
  have hγ₀ : γ 0 = p := by
    dsimp [γ]
    rw [hζ₀]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hread_deriv₀ :
      HasDerivAt (chartReading (I := I) p γ) w₀ 0 := by
    have heq : chartReading (I := I) p γ =ᶠ[𝓝 (0 : ℝ)] fun s => (ζ s).1 := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hε') hε'] with s hs
      exact hread s hs
    exact hζpos₀.congr_of_eventuallyEq heq
  refine ⟨ε', hε', γ, hγ₀, hread_deriv₀, ?_, ?_⟩
  intro t ht
  have ht0 := hsub t ht
  have hstate := hζ t (by simpa [sub_eq_add_neg] using ht0)
  have hpos : HasDerivAt (fun s => (ζ s).1) ((ζ t).2) t := by
    simpa [chartSpray] using (hstate.hasFDerivAt.fst).hasDerivAt
  have hvel : HasDerivAt (fun s => (ζ s).2)
      (chartSpraySecond (I := I) g p (ζ t).1 (ζ t).2) t := by
    simpa [chartSpray] using (hstate.hasFDerivAt.snd).hasDerivAt
  have heq : chartReading (I := I) p γ =ᶠ[𝓝 t] fun s => (ζ s).1 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hread s hs
  have hread_deriv : HasDerivAt (chartReading (I := I) p γ) ((ζ t).2) t :=
    hpos.congr_of_eventuallyEq heq
  have hderiv_eq : deriv (chartReading (I := I) p γ) =ᶠ[𝓝 t]
      (fun s => (ζ s).2) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hps := hζ s (by simpa [sub_eq_add_neg] using hsub s hs)
    have hp : HasDerivAt (fun r => (ζ r).1) ((ζ s).2) s := by
      simpa [chartSpray] using (hps.hasFDerivAt.fst).hasDerivAt
    have hread_s := hp.congr_of_eventuallyEq (by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
      exact hread r hr)
    exact hread_s.deriv
  have hsecond : HasDerivAt (deriv (chartReading (I := I) p γ))
      (chartSpraySecond (I := I) g p (ζ t).1 (ζ t).2) t :=
    hvel.congr_of_eventuallyEq hderiv_eq
  have hsource : ∀ᶠ s in 𝓝 t, γ s ∈ (chartAt H p).source := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    simpa only [γ, Function.comp_apply, extChartAt_source (I := I)] using
      (extChartAt I p).map_target (interior_subset (htarget s hs))
  refine ⟨?_, ?_⟩
  · simpa only [γ, Function.comp_apply, extChartAt_source (I := I)] using
      (extChartAt I p).map_target (interior_subset (htarget t ht))
  · refine ⟨?_, ?_⟩
    · refine ⟨hsource, hread_deriv.congr_deriv hread_deriv.deriv.symm, ?_, ?_⟩
      · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        have hps := hζ s (by simpa [sub_eq_add_neg] using hsub s hs)
        have hp : HasDerivAt (fun r => (ζ r).1) ((ζ s).2) s := by
          simpa [chartSpray] using (hps.hasFDerivAt.fst).hasDerivAt
        have hr := hp.congr_of_eventuallyEq (by
          filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
          exact hread r hr)
        exact hr.congr_deriv hr.deriv.symm
      · exact hvel.differentiableAt.congr_of_eventuallyEq hderiv_eq
    · rw [chartAcceleration, hsecond.deriv]
      rw [chartSpraySecond_eq_neg_contraction]
      rw [hread t ht, hread_deriv.deriv]
      rw [chartChristoffelContraction_eq_connection]
      abel
  · intro t ht
    have ht0 := hsub t ht
    have hstate := hζ t (by simpa [sub_eq_add_neg] using ht0)
    have hpos : HasDerivAt (fun s => (ζ s).1) ((ζ t).2) t := by
      simpa [chartSpray] using (hstate.hasFDerivAt.fst).hasDerivAt
    have hsymm : ContinuousAt (extChartAt I p).symm ((ζ t).1) :=
      continuousAt_extChartAt_symm'' (interior_subset (htarget t ht))
    have hζcont : ContinuousAt ζ t := hstate.continuousAt
    have hcomp := hsymm.comp (continuousAt_fst : ContinuousAt Prod.fst (ζ t))
    have hfinal := hcomp.comp hζcont
    simpa [γ, Function.comp_def] using hfinal

/-- The first-order state `(u,u')` associated with a chart reading. -/
def chartState (alpha : M) (gamma : ℝ → M) : ℝ → E × E :=
  fun t => (chartReading (I := I) alpha gamma t,
    deriv (chartReading (I := I) alpha gamma) t)

/-- Local uniqueness for chart geodesics, expressed through the first-order
state equation.  The hypotheses quantify the equation on a neighbourhood;
this is the exact local uniqueness contract supplied by the ODE library. -/
theorem chartGeodesic_eventuallyEq_of_equation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) {gamma gamma' : ℝ → M} {t : ℝ}
    (hgamma₀ : HasChartGeodesicEquationAt (I := I) g p gamma t)
    (hgamma'₀ : HasChartGeodesicEquationAt (I := I) g p gamma' t)
    (hgamma : ∀ᶠ s in 𝓝 t,
      HasChartGeodesicEquationAt (I := I) g p gamma s)
    (hgamma' : ∀ᶠ s in 𝓝 t,
      HasChartGeodesicEquationAt (I := I) g p gamma' s)
    (hy : chartReading (I := I) p gamma t ∈ interior (extChartAt I p).target)
    (hstate : chartState (I := I) p gamma t = chartState (I := I) p gamma' t) :
    chartReading (I := I) p gamma =ᶠ[𝓝 t]
      chartReading (I := I) p gamma' := by
  let z : ℝ → E × E := chartState (I := I) p gamma
  let z' : ℝ → E × E := chartState (I := I) p gamma'
  have hode (q : ℝ → M)
      (hq : ∀ᶠ s in 𝓝 t, HasChartGeodesicEquationAt (I := I) g p q s) :
      ∀ᶠ s in 𝓝 t,
        HasDerivAt (chartState (I := I) p q)
          (chartSpray (I := I) g p (chartState (I := I) p q s)) s := by
    filter_upwards [hq] with s hs
    have hfirst := hs.1.2.1
    have hsecond := hs.1.2.2.2.hasDerivAt
    have heq : deriv (deriv (chartReading (I := I) p q)) s =
        chartSpraySecond (I := I) g p
          (chartReading (I := I) p q s)
          (deriv (chartReading (I := I) p q) s) := by
      rw [chartSpraySecond_eq_neg_contraction]
      exact eq_neg_of_add_eq_zero_left hs.2
    have hsecond' := hsecond.congr_deriv heq
    exact hfirst.prodMk hsecond'
  have hz : ∀ᶠ s in 𝓝 t,
      HasDerivAt z (chartSpray (I := I) g p (z s)) s := by
    simpa only [z] using hode gamma hgamma
  have hz' : ∀ᶠ s in 𝓝 t,
      HasDerivAt z' (chartSpray (I := I) g p (z' s)) s := by
    simpa only [z'] using hode gamma' hgamma'
  have hzcont : ContinuousAt z t := by
    exact (hgamma₀.1.2.1.continuousAt.prodMk hgamma₀.1.2.2.2.continuousAt)
  have hz'cont : ContinuousAt z' t := by
    exact (hgamma'₀.1.2.1.continuousAt.prodMk hgamma'₀.1.2.2.2.continuousAt)
  have hspray : ContDiffAt ℝ 1 (chartSpray (I := I) g p) (z t) := by
    simpa only [z, chartState] using
      (chartSpray_contDiffAt (I := I) g p hy).of_le (by norm_num)
  obtain ⟨K, U, hU, hK⟩ := hspray.exists_lipschitzOnWith
  have hzU : ∀ᶠ s in 𝓝 t, z s ∈ U := hzcont.preimage_mem_nhds hU
  have hstatez : z t = z' t := by simpa only [z, z'] using hstate
  have hz'U : ∀ᶠ s in 𝓝 t, z' s ∈ U := by
    have hU' : U ∈ 𝓝 (z' t) := by simpa only [hstatez] using hU
    exact hz'cont.preimage_mem_nhds hU'
  have huniq := ODE_solution_unique_of_eventually
    (v := fun _ : ℝ => chartSpray (I := I) g p)
    (s := fun _ : ℝ => U) (K := K)
    (Filter.Eventually.of_forall fun _ => hK)
    (hz.and hzU) (hz'.and hz'U) hstate
  filter_upwards [huniq] with s hs
  have hfirst := congrArg Prod.fst hs
  simpa only [z, z', chartState, Function.comp_apply] using hfirst

/-- Two local chart geodesics with the same prescribed position and velocity
agree near the initial time.

The conclusion is equality of the manifold-valued curves, not merely equality
of their chart readings.  No completeness or separation assumption is needed
for this local uniqueness statement. -/
theorem localChartGeodesic_eventuallyEq_of_initial_data
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p)
    {gamma gamma' : ℝ → M}
    (hgamma0 : gamma 0 = p) (hgamma'0 : gamma' 0 = p)
    (hvel : HasDerivAt (chartReading (I := I) p gamma)
      (chartVelocityAt (I := I) p v) 0)
    (hvel' : HasDerivAt (chartReading (I := I) p gamma')
      (chartVelocityAt (I := I) p v) 0)
    (hgamma : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasChartGeodesicEquationAt (I := I) g p gamma s)
    (hgamma' : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasChartGeodesicEquationAt (I := I) g p gamma' s) :
    gamma =ᶠ[𝓝 (0 : ℝ)] gamma' := by
  have hgammaAt := hgamma.self_of_nhds
  have hgamma'At := hgamma'.self_of_nhds
  have hstate : chartState (I := I) p gamma 0 = chartState (I := I) p gamma' 0 := by
    apply Prod.ext
    · simp only [chartState, chartReading, hgamma0, hgamma'0]
    · simp only [chartState]
      rw [hvel.deriv, hvel'.deriv]
  have hy : chartReading (I := I) p gamma 0 ∈
      interior (extChartAt I p).target := by
    simpa only [chartReading, hgamma0] using (I.isInteriorPoint_iff).mp hp
  have hread := chartGeodesic_eventuallyEq_of_equation (I := I) g p
    hgammaAt hgamma'At hgamma hgamma' hy hstate
  have hsource : ∀ᶠ s in 𝓝 (0 : ℝ), gamma s ∈ (extChartAt I p).source := by
    filter_upwards [hgamma] with s hs
    simpa only [extChartAt_source (I := I)] using hs.1.1.self_of_nhds
  have hsource' : ∀ᶠ s in 𝓝 (0 : ℝ), gamma' s ∈ (extChartAt I p).source := by
    filter_upwards [hgamma'] with s hs
    simpa only [extChartAt_source (I := I)] using hs.1.1.self_of_nhds
  filter_upwards [hread, hsource, hsource'] with s hs hsgamma hsgamma'
  apply (extChartAt I p).injOn hsgamma hsgamma'
  simpa only [chartReading] using hs

/-- The Christoffel contraction vanishes on two zero velocities. -/
@[simp] private theorem chartChristoffelContraction_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) :
    chartChristoffelContraction (I := I) g alpha y 0 0 = 0 := by
  classical
  simp [chartChristoffelContraction, chartConnectionContraction]

/-- The canonical connection contraction vanishes on two zero velocities. -/
@[simp] theorem chartConnectionContraction_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) :
    chartConnectionContraction (I := I) g alpha y 0 0 = 0 := by
  classical
  simp [chartConnectionContraction]

/-- Boundaryless wrapper for `exists_localChartGeodesicAt`. -/
theorem exists_localChartGeodesicAt_boundaryless [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt γ t) :=
  exists_localChartGeodesicAt g p v BoundarylessManifold.isInteriorPoint

/-- Covariant acceleration `D_t (gamma')`, read in the canonical chart at the
current foot and transported back to the tangent fibre.

The connection term is evaluated with
  `Connection.leviCivitaConnection g`; this is the coordinate realization of
  the canonical connection and introduces neither a second connection nor an
  implicit metric. -/
def covariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) : TangentSpace I (gamma t) :=
  (trivializationAt E (TangentSpace I) (gamma t)).symmL ℝ (gamma t)
    (chartAcceleration (I := I) g (gamma t) gamma t)

/-- A curve is geodesic at `t` when it has the required second-order
regularity and its Levi--Civita covariant acceleration vanishes. -/
def IsGeodesicAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) : Prop :=
  gamma t ∈ (chartAt H (gamma t)).source ∧
    ContinuousAt gamma t ∧
    HasChartGeodesicRegularityAt (I := I) (gamma t) gamma t ∧
    covariantAcceleration (I := I) g gamma t = 0

/-- The intrinsic geodesic predicate for the explicit metric `g`.

This is Morgan--Tian Definition 1.17: `D_t (gamma') = 0` for the canonical
Levi--Civita connection. -/
def IsGeodesic
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) : Prop :=
  ∀ t, IsGeodesicAt (I := I) g gamma t

/-! ## Interval-level intrinsic predicate -/

/-- The moving-foot geodesic predicate restricted to a set of times.

This small interval contract belongs to the local geodesic layer.  The
Hopf--Rinow module consumes it, but does not own it: keeping the predicate here
lets lower-level Jacobi and variation consumers depend on `Geodesic` without
pulling in completeness or minimizer interfaces. -/
def IsGeodesicOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsGeodesicAt (I := I) g gamma t

/-- Restricting an interval geodesic certificate to a smaller time set. -/
theorem isGeodesicOn_mono
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {s s' : Set ℝ} (hs : s' ⊆ s)
    (hgamma : IsGeodesicOn (I := I) g gamma s) :
    IsGeodesicOn (I := I) g gamma s' := by
  intro t ht
  exact hgamma t (hs ht)

/-- Restriction to `Set.univ` recovers the global geodesic predicate. -/
@[simp]
theorem isGeodesicOn_univ_iff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) :
    IsGeodesicOn (I := I) g gamma (Set.univ : Set ℝ) ↔
      IsGeodesic (I := I) g gamma := by
  constructor
  · intro h t
    exact h t (Set.mem_univ t)
  · intro h t _
    exact h t

/-- Constant curves are geodesics; this is the zero-velocity regression for
the canonical coordinate equation. -/
theorem isGeodesic_const
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    IsGeodesic g (fun _ : ℝ => p) := by
  classical
  rw [IsGeodesic]
  intro t
  have hconst (s : ℝ) :
      HasDerivAt (chartReading (I := I) p (fun _ : ℝ => p)) 0 s := by
    change HasDerivAt (fun _ : ℝ => extChartAt I p p) 0 s
    exact hasDerivAt_const (x := s) (c := extChartAt I p p)
  have hderiv : deriv (chartReading (I := I) p (fun _ : ℝ => p)) =
      (fun _ : ℝ => (0 : E)) := by
    funext s
    exact (hconst s).deriv
  have hfirst (s : ℝ) :
      HasDerivAt (chartReading (I := I) p (fun _ : ℝ => p))
        (deriv (chartReading (I := I) p (fun _ : ℝ => p)) s) s :=
    (hconst s).congr_deriv (hconst s).deriv.symm
  have hsecond : deriv (deriv (chartReading (I := I) p (fun _ : ℝ => p))) t = 0 := by
    rw [hderiv]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only using (mem_chart_source H p)
  · exact continuousAt_const
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa only using (mem_chart_source H p))
    · exact hfirst t
    · filter_upwards [] with s
      exact hfirst s
    · change DifferentiableAt ℝ
        (deriv (chartReading (I := I) p (fun _ : ℝ => p))) t
      rw [hderiv]
      exact differentiableAt_const (c := (0 : E))
  · change covariantAcceleration (I := I) g (fun _ : ℝ => p) t = 0
    rw [covariantAcceleration, chartAcceleration, hsecond, hderiv]
    simp only [chartConnectionContraction_zero, add_zero, map_zero]

/-- The intrinsic equation at a time is equivalent to the Morgan--Tian
coordinate equation in the chart centred at the foot. -/
theorem isGeodesicAt_iff_chartEquation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) :
    IsGeodesicAt (I := I) g gamma t ↔
      gamma t ∈ (chartAt H (gamma t)).source ∧
        ContinuousAt gamma t ∧
        HasChartGeodesicEquationAt (I := I) g (gamma t) gamma t := by
  let e := trivializationAt E (TangentSpace I) (gamma t)
  have hbase : gamma t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' (gamma t)
  constructor
  · rintro ⟨hsource, hcont, hreg, hzero⟩
    refine ⟨hsource, hcont, hreg, ?_⟩
    have h := congrArg (e.continuousLinearMapAt ℝ (gamma t)) hzero
    simpa only [covariantAcceleration, e, e.continuousLinearMapAt_symmL hbase,
      map_zero] using h
  · rintro ⟨hsource, hcont, hreg, hzero⟩
    refine ⟨hsource, hcont, hreg, ?_⟩
    simp only [covariantAcceleration, hzero, map_zero]

/-- Coordinate form of Morgan--Tian's geodesic equation,
`u''^k + Gamma^k_ij u'^i u'^j = 0`. -/
theorem isGeodesicAt_iff_coordinate_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) :
    IsGeodesicAt (I := I) g gamma t ↔
      gamma t ∈ (chartAt H (gamma t)).source ∧
      ContinuousAt gamma t ∧
      HasChartGeodesicRegularityAt (I := I) (gamma t) gamma t ∧
      deriv (deriv (chartReading (I := I) (gamma t) gamma)) t +
        chartConnectionContraction (I := I) g (gamma t)
          (chartReading (I := I) (gamma t) gamma t)
          (deriv (chartReading (I := I) (gamma t) gamma) t)
          (deriv (chartReading (I := I) (gamma t) gamma) t) = 0 := by
  rw [isGeodesicAt_iff_chartEquation]
  rfl

end Coordinates

end Geodesic
end Ch01
end MorganTianLib
