import MorganTianLib.Ch01.Connection.Christoffel
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue

/-!
# Geodesics

This module is the Chapter 1 geodesic handoff.  It uses the canonical bundled
Levi--Civita connection from `Ch01.Connection` and gives the fixed-chart
second-order reduction together with the local initial-value contract.  The
maximal-domain definitions below are deliberately a domain substrate: their
canonical curve and the chart-transition/gluing argument are separate pieces
of the S18 construction.  Smooth dependence on initial data is likewise left
to the parameter-flow slice: the pinned Mathlib ODE API supplies time
smoothness and local uniqueness, but no joint smooth-flow theorem.

The overlap kinematics include the second-order chain rule for the moving
transition derivative.  This is the calculus input for the Christoffel
transformation law; that metric-dependent identity and the resulting gluing
remain separate S18 work.  The Euclidean model regression at the end of the
module checks the coefficient and affine straight-line branches concretely.
The local equation also has affine parameter-transport and set-relative
restriction lemmas (including translation and time reversal); these are
algebraic reparameterization facts and do not assert the pending global
maximal-flow construction.

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
noncomputable def chartConnectionCoeff
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
def chartChristoffel
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) : ℝ :=
  chartConnectionCoeff (I := I) g alpha ((extChartAt I alpha).symm y) i j k

/-- Unfolding rule for the chart coefficient. -/
@[simp] theorem chartChristoffel_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (I := I) g alpha y i j k =
      chartConnectionCoeff (I := I) g alpha ((extChartAt I alpha).symm y) i j k := rfl

/-- Unfolded connection bridge for the public coefficient. -/
theorem chartChristoffel_eq_leviCivita
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

/-- The Christoffel contraction `Gamma(v,w)` in the chart centred at `alpha`.

The first velocity supplies the direction (the first lower Christoffel slot),
and the second supplies the differentiated vector field. -/
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

/-- The public contraction notation for the Christoffel coefficients. -/
def chartChristoffelContraction
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) : E :=
  chartConnectionContraction (I := I) g alpha y v w

/-- The public Christoffel contraction is the canonical connection contraction.
-/
theorem chartChristoffelContraction_eq_connection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y v w : E) :
    chartChristoffelContraction (I := I) g alpha y v w =
      chartConnectionContraction (I := I) g alpha y v w := rfl

/-- The contraction used by the coordinate equation, expanded to the
canonical bundled connection.  This is the declaration-level bridge behind
the coordinate realization of `D_t (gamma')`. -/
theorem chartChristoffelContraction_eq_leviCivita
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

/-! ### Algebraic transport of the coordinate equation -/

/-- The canonical connection contraction is quadratic in a repeated velocity:
`Gamma(a v, a v) = a^2 Gamma(v, v)`.  This is the algebraic ingredient needed
for affine reparameterization of the geodesic equation.  The statement uses
the same bundled `leviCivitaConnection` as the coordinate equation above; it
does not introduce a second connection representation.  Compare the affine
reparameterization step in do Carmo, Chapter 3, and Morgan--Tian's geodesic
equation (Definition 1.17, `morganTian2007`). -/
theorem chartConnectionContraction_smul_smul
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (a : ℝ) (v y : E) :
    chartConnectionContraction (I := I) g alpha y (a • v) (a • v) =
      (a * a) • chartConnectionContraction (I := I) g alpha y v v := by
  classical
  unfold chartConnectionContraction
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hi_smul : ((Module.finBasis ℝ E).repr (a • v)) i =
      a * ((Module.finBasis ℝ E).repr v i) := by
    rw [map_smul]
    rfl
  have hj_smul : ((Module.finBasis ℝ E).repr (a • v)) j =
      a * ((Module.finBasis ℝ E).repr v j) := by
    rw [map_smul]
    rfl
  rw [hi_smul, hj_smul]
  ring_nf

/-- The public Christoffel spelling of the quadratic contraction law. -/
theorem chartChristoffelContraction_smul_smul
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (a : ℝ) (v y : E) :
    chartChristoffelContraction (I := I) g alpha y (a • v) (a • v) =
      (a * a) • chartChristoffelContraction (I := I) g alpha y v v := by
  exact chartConnectionContraction_smul_smul (I := I) g alpha a v y

/-- Ordered-basis regression for the Christoffel contraction.

The first basis argument is the direction slot and the second is the
differentiated-field slot.  Keeping this projection theorem public makes a
swapped-lower-index implementation observable even though the final geodesic
specialization contracts both slots with the same velocity. -/
theorem chartChristoffelContraction_basis_repr
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) (i j k : Fin (Module.finrank ℝ E)) :
    (Module.finBasis ℝ E).repr
        (chartChristoffelContraction (I := I) g alpha y
          (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)) k =
      chartChristoffel (I := I) g alpha y i j k := by
  classical
  rw [chartChristoffelContraction_eq_connection]
  simp [chartConnectionContraction, chartChristoffel, chartConnectionCoeff,
    Module.Basis.repr_self, Finsupp.single_apply]

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

private theorem chartSpray_contDiffOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
  ContDiffOn ℝ ∞ (chartSpray (I := I) g alpha)
      (interior (extChartAt I alpha).target ×ˢ (Set.univ : Set E)) := by
  intro z hz
  exact (chartSpray_contDiffAt (I := I) g alpha hz.1).contDiffWithinAt

/-! The next declarations are deliberately private.  They lift the fixed-chart
spray to the tangent bundle on one chart, which is the first-order ODE used by
the integral-curve API.  A global spray still requires the missing
fixed-to-moving-chart transition theorem, so no chart-dependent field is part
of the source-facing geodesic contract. -/

private def chartSprayDomain (alpha : M) : Set (TangentBundle I M) :=
  (Bundle.TotalSpace.proj : TangentBundle I M → M) ⁻¹' (chartAt H alpha).source

private def chartSprayState (alpha : M) (p : TangentBundle I M) : E × E :=
  (extChartAt I alpha p.proj,
    (trivializationAt E (TangentSpace I) alpha p).2)

private def chartSpraySection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (p : TangentBundle I M) : TangentSpace I.tangent p :=
  (trivializationAt (E × E) (TangentSpace I.tangent)
      (⟨alpha, (0 : E)⟩ : TangentBundle I M)).symmL ℝ p
    (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p))

omit [FiniteDimensional ℝ E] in
private theorem chartSprayState_eq_extChartAt (alpha : M) (p : TangentBundle I M) :
    chartSprayState (I := I) alpha p =
      extChartAt I.tangent (⟨alpha, (0 : E)⟩ : TangentBundle I M) p := by
  rw [FiberBundle.extChartAt]
  simp only [chartSprayState, PartialEquiv.trans_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem chartSprayState_contMDiffOn (alpha : M) :
    ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
      (chartSprayState (I := I) alpha) (chartSprayDomain (I := I) alpha) := by
  rw [show chartSprayState (I := I) alpha =
      extChartAt I.tangent (⟨alpha, (0 : E)⟩ : TangentBundle I M) from
      funext (chartSprayState_eq_extChartAt (I := I) alpha)]
  have hs :
      (chartAt (ModelProd H E) (⟨alpha, (0 : E)⟩ : TangentBundle I M)).source =
        chartSprayDomain (I := I) alpha := by
    ext p
    rw [TangentBundle.mem_chart_source_iff]
    rfl
  rw [← hs]
  exact contMDiffOn_extChartAt

omit [FiniteDimensional ℝ E] in
private theorem chartSprayState_mapsTo_interior [BoundarylessManifold I M]
    (alpha : M) :
    MapsTo (chartSprayState (I := I) alpha)
      (chartSprayDomain (I := I) alpha)
      (interior (extChartAt I alpha).target ×ˢ (Set.univ : Set E)) := by
  intro p hp
  have hproj : p.proj ∈ (chartAt H alpha).source := hp
  have hy : extChartAt I alpha p.proj ∈ (extChartAt I alpha).target := by
    exact (extChartAt I alpha).map_source
      (by simpa only [extChartAt_source (I := I)] using hproj)
  have htarget : extChartAt I alpha p.proj ∈ interior (extChartAt I alpha).target := by
    let q : M := (extChartAt I alpha).symm (extChartAt I alpha p.proj)
    have hqsrc : q ∈ (chartAt H alpha).source := by
      change (extChartAt I alpha).symm (extChartAt I alpha p.proj) ∈
        (chartAt H alpha).source
      simpa only [extChartAt_source (I := I)] using
        (extChartAt I alpha).map_target hy
    have hqint : I.IsInteriorPoint q := BoundarylessManifold.isInteriorPoint
    have hcoord : (extChartAt I alpha) q ∈ interior (extChartAt I alpha).target :=
      (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (e := chartAt H alpha) (chart_mem_atlas H alpha) hqsrc).mp hqint
    change (extChartAt I alpha) ((extChartAt I alpha).symm
      (extChartAt I alpha p.proj)) ∈ interior (extChartAt I alpha).target at hcoord
    rw [(extChartAt I alpha).right_inv hy] at hcoord
    exact hcoord
  exact ⟨htarget, Set.mem_univ _⟩

private theorem chartSpraySection_contMDiffOn
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
    ContMDiffOn I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, chartSpraySection (I := I) g alpha p⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (chartSprayDomain (I := I) alpha) := by
  classical
  let e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨alpha, (0 : E)⟩ : TangentBundle I M)
  letI : MemTrivializationAtlas e :=
    ⟨FiberBundle.trivialization_mem_atlas (E × E) (TangentSpace I.tangent) _⟩
  have hdomain : chartSprayDomain (I := I) alpha = e.baseSet := by
    unfold chartSprayDomain e
    ext p
    rw [Set.mem_preimage,
      TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨alpha, (0 : E)⟩ : TangentBundle I M)]
    exact (TangentBundle.mem_chart_source_iff (I := I) (M := M) p
      (⟨alpha, (0 : E)⟩ : TangentBundle I M)).symm
  have hMapsTo :
      MapsTo
        (fun p : TangentBundle I M =>
          (⟨p, chartSpraySection (I := I) g alpha p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (chartSprayDomain (I := I) alpha) e.source := by
    intro p hp
    rw [Trivialization.source_eq]
    rw [← hdomain]
    exact hp
  rw [e.contMDiffOn_iff (IM := I.tangent) (IB := I.tangent)
    (n := (∞ : WithTop ℕ∞)) hMapsTo]
  refine ⟨?_, ?_⟩
  · change ContMDiffOn I.tangent I.tangent ∞
      (fun x : TangentBundle I M => x) (chartSprayDomain (I := I) alpha)
    exact contMDiffOn_id
  · have heq : ∀ p ∈ chartSprayDomain (I := I) alpha,
        (e (⟨p, chartSpraySection (I := I) g alpha p⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 =
          chartSpray (I := I) g alpha
            (chartSprayState (I := I) alpha p) := by
      intro p hp
      have hp' : p ∈ e.baseSet := by rw [← hdomain]; exact hp
      unfold chartSpraySection
      rw [Trivialization.symmL_apply _ hp']
      change (e (⟨p, e.symm p
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p))⟩)).2 = _
      exact congrArg Prod.snd (e.apply_mk_symm hp'
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p)))
    have hcomp :
        ContMDiffOn I.tangent 𝓘(ℝ, E × E) ∞
          (fun p => chartSpray (I := I) g alpha
            (chartSprayState (I := I) alpha p))
          (chartSprayDomain (I := I) alpha) :=
      (chartSpray_contDiffOn (I := I) g alpha).contMDiffOn.comp
        (chartSprayState_contMDiffOn (I := I) alpha)
        (chartSprayState_mapsTo_interior (I := I) alpha)
    exact hcomp.congr heq

/-! The global section smoothness lemma above is convenient on a boundaryless
manifold, but a local IVP only needs the prescribed base point to be interior.
The following private lemmas retain that weaker point-local contract. -/

omit [FiniteDimensional ℝ E] in
private theorem tangent_isInteriorPoint_of_base
    {p : TangentBundle I M} (hp : I.IsInteriorPoint p.proj) :
    I.tangent.IsInteriorPoint p := by
  rw [ModelWithCorners.isInteriorPoint_iff]
  rw [show extChartAt I.tangent p =
      extChartAt I.tangent (⟨p.proj, (0 : E)⟩ : TangentBundle I M) from rfl]
  rw [FiberBundle.extChartAt_target]
  rw [FiberBundle.extChartAt]
  simp only [PartialEquiv.trans_apply, PartialEquiv.prod_coe,
    PartialEquiv.refl_coe]
  have hbase :
      (extChartAt I p.proj).target ∩
          (extChartAt I p.proj).symm ⁻¹'
            (trivializationAt E (TangentSpace I) p.proj).baseSet =
        (extChartAt I p.proj).target := by
    refine inter_eq_left.mpr ?_
    intro y hy
    rw [mem_preimage, TangentBundle.trivializationAt_baseSet, ← extChartAt_source I]
    exact (extChartAt I p.proj).map_target hy
  rw [hbase, interior_prod_eq, interior_univ, mem_prod]
  constructor
  · have hfst :
        ((trivializationAt E (TangentSpace I) p.proj).toPartialEquiv p).1 = p.proj := by
      rfl
    rw [hfst]
    exact (ModelWithCorners.isInteriorPoint_iff.mp hp)
  · trivial

omit [FiniteDimensional ℝ E] in
private theorem chartSprayState_mem_interior_of_base
    {alpha : M} {p : TangentBundle I M}
    (hpbase : I.IsInteriorPoint p.proj)
    (hp : p ∈ chartSprayDomain (I := I) alpha) :
    chartSprayState (I := I) alpha p ∈
      interior (extChartAt I alpha).target ×ˢ (Set.univ : Set E) := by
  have hproj : p.proj ∈ (chartAt H alpha).source := hp
  have hcoord :
      (extChartAt I alpha) p.proj ∈ interior (extChartAt I alpha).target :=
    (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (e := chartAt H alpha) (chart_mem_atlas H alpha) hproj).mp hpbase
  change (extChartAt I alpha) p.proj ∈ interior (extChartAt I alpha).target ∧
    (trivializationAt E (TangentSpace I) alpha p).2 ∈ (Set.univ : Set E)
  exact ⟨hcoord, Set.mem_univ _⟩

private theorem chartSpraySection_contMDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {p : TangentBundle I M}
    (hpbase : I.IsInteriorPoint p.proj)
    (hp : p ∈ chartSprayDomain (I := I) alpha) :
    ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, chartSpraySection (I := I) g alpha p⟩ :
          TangentBundle I.tangent (TangentBundle I M))) p := by
  classical
  let e := trivializationAt (E × E) (TangentSpace I.tangent)
    (⟨alpha, (0 : E)⟩ : TangentBundle I M)
  letI : MemTrivializationAtlas e :=
    ⟨FiberBundle.trivialization_mem_atlas (E × E) (TangentSpace I.tangent) _⟩
  have hdomain : chartSprayDomain (I := I) alpha = e.baseSet := by
    unfold chartSprayDomain e
    ext q
    rw [Set.mem_preimage,
      TangentBundle.trivializationAt_baseSet (I := I.tangent)
        (M := TangentBundle I M) (⟨alpha, (0 : E)⟩ : TangentBundle I M)]
    exact (TangentBundle.mem_chart_source_iff (I := I) (M := M) q
      (⟨alpha, (0 : E)⟩ : TangentBundle I M)).symm
  have hMapsTo :
      MapsTo
        (fun q : TangentBundle I M =>
          (⟨q, chartSpraySection (I := I) g alpha q⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (chartSprayDomain (I := I) alpha) e.source := by
    intro q hq
    rw [Trivialization.source_eq, ← hdomain]
    exact hq
  have hp_source :
      (⟨p, chartSpraySection (I := I) g alpha p⟩ :
        TangentBundle I.tangent (TangentBundle I M)) ∈ e.source := hMapsTo hp
  rw [Bundle.Trivialization.contMDiffAt_iff (e := e)
    (B := TangentBundle I M) (F := E × E) (M := TangentBundle I M)
    (E := TangentSpace I.tangent) (IM := I.tangent) (IB := I.tangent)
    (n := (∞ : WithTop ℕ∞)) hp_source]
  refine ⟨?_, ?_⟩
  · change ContMDiffAt I.tangent I.tangent ∞
      (fun q : TangentBundle I M => q) p
    exact contMDiffAt_id
  · have hopen : IsOpen (chartSprayDomain (I := I) alpha) := by
      exact (chartAt H alpha).open_source.preimage
        (FiberBundle.continuous_proj E (TangentSpace I))
    have hstate :
        ContMDiffAt I.tangent 𝓘(ℝ, E × E) ∞
          (chartSprayState (I := I) alpha) p :=
      (chartSprayState_contMDiffOn (I := I) alpha).contMDiffAt
        (hopen.mem_nhds hp)
    have htarget := chartSprayState_mem_interior_of_base (I := I)
      hpbase hp
    have hspray :
        ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E × E) ∞
          (chartSpray (I := I) g alpha)
          (chartSprayState (I := I) alpha p) :=
      (chartSpray_contDiffAt (I := I) g alpha htarget.1).contMDiffAt
    have hcomp : ContMDiffAt I.tangent 𝓘(ℝ, E × E) ∞
        (fun q : TangentBundle I M =>
          chartSpray (I := I) g alpha (chartSprayState (I := I) alpha q)) p := by
      simpa [Function.comp_def] using hspray.comp p hstate
    have heq :
        (e (⟨p, chartSpraySection (I := I) g alpha p⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 =
          chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p) := by
      have hp' : p ∈ e.baseSet := by rw [← hdomain]; exact hp
      unfold chartSpraySection
      rw [Trivialization.symmL_apply _ hp']
      change (e (⟨p, e.symm p
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p))⟩)).2 = _
      exact congrArg Prod.snd (e.apply_mk_symm hp'
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha p)))
    have heq' : ∀ᶠ q in 𝓝 p,
        (e (⟨q, chartSpraySection (I := I) g alpha q⟩ :
          TangentBundle I.tangent (TangentBundle I M))).2 =
          chartSpray (I := I) g alpha (chartSprayState (I := I) alpha q) := by
      filter_upwards [hopen.mem_nhds hp] with q hq
      have hq' : q ∈ e.baseSet := by rw [← hdomain]; exact hq
      unfold chartSpraySection
      rw [Trivialization.symmL_apply _ hq']
      change (e (⟨q, e.symm q
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha q))⟩)).2 = _
      exact congrArg Prod.snd (e.apply_mk_symm hq'
        (chartSpray (I := I) g alpha (chartSprayState (I := I) alpha q)))
    apply hcomp.congr_of_eventuallyEq
    exact heq'

private theorem exists_chartSpraySection_integralCurveAt [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {p : TangentBundle I M}
    (hpbase : I.IsInteriorPoint p.proj)
    (hp : p ∈ chartSprayDomain (I := I) alpha) :
    ∃ gamma : ℝ → TangentBundle I M, gamma 0 = p ∧
      IsMIntegralCurveAt gamma
        (fun q : TangentBundle I M => chartSpraySection (I := I) g alpha q) 0 := by
  have hv := chartSpraySection_contMDiffAt (I := I) g alpha hpbase hp
  obtain ⟨gamma, hg, hcurve⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt
      (I := I.tangent) (M := TangentBundle I M) (t₀ := 0) (x₀ := p)
      (v := fun q : TangentBundle I M => chartSpraySection (I := I) g alpha q)
      (hv.of_le (by norm_num)) (tangent_isInteriorPoint_of_base (I := I) hpbase)
  exact ⟨gamma, hg, hcurve⟩

/-- The `E`-coordinate of a tangent vector in the chart trivialisation at `p`.

This is the velocity variable used by the local first-order spray. -/
def chartVelocityAt (p : M) (v : TangentSpace I p) : E :=
  (trivializationAt E (TangentSpace I) p (⟨p, v⟩ : TangentBundle I M)).2

/-- The model-space velocity coordinates of a tangent vector at `p`, read in
the chart centred at `alpha`.  `chartVelocityAt` is the special case
`alpha = p`; this two-point form is needed when comparing overlapping local
geodesic equations. -/
def chartVelocityInChart (alpha p : M) (v : TangentSpace I p) : E :=
  (trivializationAt E (TangentSpace I) alpha (⟨p, v⟩ : TangentBundle I M)).2

omit [FiniteDimensional ℝ E] in
@[simp] theorem chartVelocityInChart_self (p : M) (v : TangentSpace I p) :
    chartVelocityInChart (I := I) p p v = chartVelocityAt (I := I) p v := rfl

/-- The chart reading of a curve. -/
def chartReading (alpha : M) (gamma : ℝ → M) : ℝ → E :=
  fun t => extChartAt I alpha (gamma t)

/-! ## Chart-transition kinematics

The fixed-chart spray is anchored at one point, while the intrinsic predicate
uses the chart centred at the moving foot.  The following declarations expose
the kinematic part of that change of coordinates.  They deliberately stop
before the metric-dependent Christoffel transformation law: that law is the
remaining gluing theorem for this S18 slice.
-/

/-- The extended-coordinate transition from the `alpha` chart to the `beta`
chart.  Outside the overlap the extended charts are totalized by Mathlib; all
derivative statements below carry an explicit source/interior hypothesis. -/
def geodesicChartTransition (alpha beta : M) : E → E :=
  (extChartAt I beta) ∘ (extChartAt I alpha).symm

/-- The overlap source of `geodesicChartTransition`, written in `alpha`
coordinates. -/
def geodesicChartTransitionSource (alpha beta : M) : Set E :=
  ((extChartAt I alpha).symm ≫ extChartAt I beta).source

private def geodesicChartFrameMap (alpha p : M) : E →L[ℝ] TangentSpace I p :=
  (trivializationAt E (TangentSpace I) alpha).symmL ℝ p

omit [FiniteDimensional ℝ E] in
private theorem geodesicChartFrameMap_eq_comp {alpha beta p : M}
    (hα : p ∈ (chartAt H alpha).source)
    (hβ : p ∈ (chartAt H beta).source) :
    geodesicChartFrameMap (I := I) alpha p =
      (geodesicChartFrameMap (I := I) beta p).comp
        (tangentCoordChange I alpha beta p) := by
  have hα' : p ∈ (extChartAt I alpha).source := by
    simpa only [extChartAt_source] using hα
  have hβ' : p ∈ (extChartAt I beta).source := by
    simpa only [extChartAt_source] using hβ
  rw [geodesicChartFrameMap, geodesicChartFrameMap,
    TangentBundle.symmL_trivializationAt_eq_core hα,
    TangentBundle.symmL_trivializationAt_eq_core hβ]
  ext u
  exact (tangentCoordChange_comp (I := I) (w := alpha) (x := beta) (y := p)
    (z := p) (v := u) ⟨⟨hα', hβ'⟩, mem_extChartAt_source p⟩).symm

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
@[simp] theorem geodesicChartTransition_apply (alpha beta : M) (y : E) :
    geodesicChartTransition (I := I) alpha beta y =
      extChartAt I beta ((extChartAt I alpha).symm y) := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
theorem geodesicChartTransitionSource_eq (alpha beta : M) :
    geodesicChartTransitionSource (I := I) alpha beta =
      (extChartAt I alpha).target ∩
        (extChartAt I alpha).symm ⁻¹' (chartAt H beta).source := by
  unfold geodesicChartTransitionSource
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, extChartAt_source]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- A common chart point gives a coordinate point in the transition source. -/
theorem geodesicChartTransition_mem {alpha beta x : M}
    (hα : x ∈ (chartAt H alpha).source)
    (hβ : x ∈ (chartAt H beta).source) :
    extChartAt I alpha x ∈ geodesicChartTransitionSource (I := I) alpha beta := by
  rw [geodesicChartTransitionSource_eq (I := I)]
  refine ⟨?_, ?_⟩
  · exact (extChartAt I alpha).map_source (by
      simpa only [extChartAt_source] using hα)
  · rw [mem_preimage,
      (extChartAt I alpha).left_inv (by simpa only [extChartAt_source] using hα)]
    simpa only [extChartAt_source] using hβ

omit [FiniteDimensional ℝ E] in
private theorem geodesicChartTransition_range_mem_nhds {alpha x : M}
    (hα : x ∈ (chartAt H alpha).source) (hx : I.IsInteriorPoint x) :
    Set.range I ∈ 𝓝 (extChartAt I alpha x) := by
  have hcoordInterior : extChartAt I alpha x ∈ interior (Set.range I) := by
    exact OpenPartialHomeomorph.interior_extend_target_subset_interior_range
        (chartAt H alpha)
      ((ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := I)
        (n := (∞ : ℕ∞ω)) (x := x) (e := chartAt H alpha) (by simp)
        (chart_mem_atlas H alpha) hα).mp hx)
  exact mem_nhds_iff.mpr
    ⟨interior (Set.range I), interior_subset, isOpen_interior, hcoordInterior⟩

omit [FiniteDimensional ℝ E] in
/-- On an interior common chart point, the transition is smooth as a full
map `E → E`.  The interior hypothesis is point-local and does not install a
stronger model-wide boundaryless instance. -/
theorem geodesicChartTransition_contDiffAt {alpha beta x : M}
    (hα : x ∈ (chartAt H alpha).source)
    (hβ : x ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint x) :
    ContDiffAt ℝ ∞ (geodesicChartTransition (I := I) alpha beta)
      (extChartAt I alpha x) := by
  have hwithin := contDiffWithinAt_ext_coord_change (I := I)
    (n := (∞ : ℕ∞ω)) beta alpha
      (geodesicChartTransition_mem (I := I) hα hβ)
  exact (by
    simpa only [geodesicChartTransition] using
      hwithin.contDiffAt
        (geodesicChartTransition_range_mem_nhds (I := I) hα hx))

omit [FiniteDimensional ℝ E] in
/-- The first derivative of the transition is Mathlib's tangent-coordinate
change at the common foot. -/
theorem geodesicChartTransition_hasFDerivAt {alpha beta x : M}
    (hα : x ∈ (chartAt H alpha).source)
    (hβ : x ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint x) :
    HasFDerivAt (geodesicChartTransition (I := I) alpha beta)
      (tangentCoordChange I alpha beta x) (extChartAt I alpha x) := by
  have hsource : x ∈ (extChartAt I alpha).source := by
    simpa only [extChartAt_source] using hα
  have hwithin := hasFDerivWithinAt_tangentCoordChange (I := I)
    (x := alpha) (y := beta) (z := x)
      ⟨hsource, by simpa only [extChartAt_source] using hβ⟩
  have hfull := hwithin.hasFDerivAt
    (geodesicChartTransition_range_mem_nhds (I := I) hα hx)
  simpa only [geodesicChartTransition] using hfull

omit [FiniteDimensional ℝ E] in
/-- The full Frechet derivative of the transition, in a form convenient for
the second-order chain rule. -/
theorem geodesicChartTransition_fderiv {alpha beta x : M}
    (hα : x ∈ (chartAt H alpha).source)
    (hβ : x ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint x) :
    fderiv ℝ (geodesicChartTransition (I := I) alpha beta)
        (extChartAt I alpha x) = tangentCoordChange I alpha beta x :=
  (geodesicChartTransition_hasFDerivAt (I := I) hα hβ hx).fderiv

omit [FiniteDimensional ℝ E] in
/-- The moving transition derivative is itself differentiable on an interior
common point.  Its derivative is the second Frechet derivative of the
transition, with no Christoffel or metric identity hidden in the statement. -/
theorem geodesicChartTransition_hasFDerivAt_fderiv {alpha beta x : M}
    (hα : x ∈ (chartAt H alpha).source)
    (hβ : x ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint x) :
    HasFDerivAt
      (fderiv ℝ (geodesicChartTransition (I := I) alpha beta))
      (fderiv ℝ (fderiv ℝ (geodesicChartTransition (I := I) alpha beta))
        (extChartAt I alpha x))
      (extChartAt I alpha x) := by
  have hcont := geodesicChartTransition_contDiffAt (I := I) hα hβ hx
  have hcont₁ : ContDiffAt ℝ 1
      (fderiv ℝ (geodesicChartTransition (I := I) alpha beta))
      (extChartAt I alpha x) :=
    hcont.fderiv_right (WithTop.coe_le_coe.2 le_top)
  exact (hcont₁.differentiableAt one_ne_zero).hasFDerivAt

omit [FiniteDimensional ℝ E] in
/-- Applying the second derivative of an overlapping chart transition to a
curve velocity gives the inhomogeneous term in the second-order chain rule.

The theorem is deliberately expressed for the `alpha` chart reading.  It
uses only the transition's source/interior hypotheses and the two ordinary
time derivatives of that reading; no Christoffel transformation or metric
coherence is built into the statement.  The order of the two terms follows
`HasDerivAt.clm_apply`: `D²τ(u') u' + Dτ(u'')`.

Source anchor: Morgan--Tian, Definition 1.17 and the coordinate/initial-value
paragraph on printed p. 41 (`morganTian2007`). -/
theorem chartReading_transition_deriv_fderiv_apply_hasDerivAt
    {alpha beta : M} {gamma : ℝ → M} {t : ℝ}
    (hα : gamma t ∈ (chartAt H alpha).source)
    (hβ : gamma t ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint (gamma t))
    (hfirst : HasDerivAt (chartReading (I := I) alpha gamma)
      (deriv (chartReading (I := I) alpha gamma) t) t)
    (hsecond : HasDerivAt (deriv (chartReading (I := I) alpha gamma))
      (deriv (deriv (chartReading (I := I) alpha gamma)) t) t) :
    HasDerivAt
      (fun s ↦
        (fderiv ℝ (geodesicChartTransition (I := I) alpha beta)
          (chartReading (I := I) alpha gamma s))
          (deriv (chartReading (I := I) alpha gamma) s))
      (fderiv ℝ (fderiv ℝ (geodesicChartTransition (I := I) alpha beta))
          (chartReading (I := I) alpha gamma t)
          (deriv (chartReading (I := I) alpha gamma) t)
          (deriv (chartReading (I := I) alpha gamma) t)
        + fderiv ℝ (geodesicChartTransition (I := I) alpha beta)
          (chartReading (I := I) alpha gamma t)
          (deriv (deriv (chartReading (I := I) alpha gamma)) t)) t := by
  have hτ₂ := geodesicChartTransition_hasFDerivAt_fderiv
    (I := I) hα hβ hx
  have hc : HasDerivAt
      (fun s ↦ fderiv ℝ (geodesicChartTransition (I := I) alpha beta)
        (chartReading (I := I) alpha gamma s))
      (fderiv ℝ (fderiv ℝ (geodesicChartTransition (I := I) alpha beta))
        (chartReading (I := I) alpha gamma t)
        (deriv (chartReading (I := I) alpha gamma) t)) t := by
    simpa [Function.comp_def, chartReading] using
      hτ₂.comp_hasDerivAt t hfirst
  have happly := hc.clm_apply hsecond
  simpa only [add_comm] using happly

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- On a neighbourhood where a curve remains in two chart sources, its two
chart readings are related by the transition map. -/
theorem chartReading_transition_eventuallyEq {alpha beta : M}
    {gamma : ℝ → M} {t : ℝ}
    (hcont : ContinuousAt gamma t)
    (hα : gamma t ∈ (chartAt H alpha).source)
    (hβ : gamma t ∈ (chartAt H beta).source) :
    chartReading (I := I) beta gamma =ᶠ[𝓝 t]
      geodesicChartTransition (I := I) alpha beta ∘
        chartReading (I := I) alpha gamma := by
  have hmem : ∀ᶠ s in 𝓝 t,
      gamma s ∈ (chartAt H alpha).source ∧ gamma s ∈ (chartAt H beta).source := by
    have hn : (chartAt H alpha).source ∩ (chartAt H beta).source ∈ 𝓝 (gamma t) :=
      ((chartAt H alpha).open_source.inter (chartAt H beta).open_source).mem_nhds
        ⟨hα, hβ⟩
    exact hcont.preimage_mem_nhds hn
  filter_upwards [hmem] with s hs
  change extChartAt I beta (gamma s) = _
  unfold geodesicChartTransition chartReading
  change extChartAt I beta (gamma s) =
    extChartAt I beta ((extChartAt I alpha).symm
      (extChartAt I alpha (gamma s)))
  rw [(extChartAt I alpha).left_inv
    (by simpa only [extChartAt_source] using hs.1)]

omit [FiniteDimensional ℝ E] in
/-- First-order chain rule for chart readings on an interior common point. -/
theorem chartReading_transition_hasDerivAt {alpha beta : M}
    {gamma : ℝ → M} {t : ℝ} {v : E}
    (hcont : ContinuousAt gamma t)
    (hα : gamma t ∈ (chartAt H alpha).source)
    (hβ : gamma t ∈ (chartAt H beta).source)
    (hx : I.IsInteriorPoint (gamma t))
    (hfirst : HasDerivAt (chartReading (I := I) alpha gamma) v t) :
    HasDerivAt (chartReading (I := I) beta gamma)
      (tangentCoordChange I alpha beta (gamma t) v) t := by
  have hT := geodesicChartTransition_hasFDerivAt (I := I) hα hβ hx
  have hcomp := hT.comp_hasDerivAt t hfirst
  exact hcomp.congr_of_eventuallyEq
    (chartReading_transition_eventuallyEq (I := I) hcont hα hβ)

omit [FiniteDimensional ℝ E] in
/-- Velocity coordinates read in two overlapping charts are related by the
tangent-coordinate change at the common foot.  This is the zeroth/first-order
kinematic input to the still-open Christoffel transformation law. -/
theorem chartVelocityInChart_transition {alpha beta p : M}
    (hα : p ∈ (chartAt H alpha).source)
    (hβ : p ∈ (chartAt H beta).source)
    (v : TangentSpace I p) :
    chartVelocityInChart (I := I) beta p v =
      tangentCoordChange I alpha beta p
        (chartVelocityInChart (I := I) alpha p v) := by
  let a : E := chartVelocityInChart (I := I) alpha p v
  let b : E := chartVelocityInChart (I := I) beta p v
  have ha : geodesicChartFrameMap (I := I) alpha p a = v := by
    dsimp [geodesicChartFrameMap, a, chartVelocityInChart]
    rw [Trivialization.symmL_apply _ hα]
    exact (trivializationAt E (TangentSpace I) alpha).symm_apply_apply_mk hα v
  have hb : geodesicChartFrameMap (I := I) beta p b = v := by
    dsimp [geodesicChartFrameMap, b, chartVelocityInChart]
    rw [Trivialization.symmL_apply _ hβ]
    exact (trivializationAt E (TangentSpace I) beta).symm_apply_apply_mk hβ v
  have hframe := geodesicChartFrameMap_eq_comp (I := I) hα hβ
  have heq := congrArg (fun f : E →L[ℝ] TangentSpace I p => f a) hframe
  rw [ha, ContinuousLinearMap.comp_apply] at heq
  have htan : v = geodesicChartFrameMap (I := I) beta p
      (tangentCoordChange I alpha beta p a) := by
    exact heq
  have hsymm := congrArg
    (fun z : TangentSpace I p =>
      (trivializationAt E (TangentSpace I) beta).continuousLinearMapAt ℝ p z) htan
  change (trivializationAt E (TangentSpace I) beta
      (⟨p, v⟩ : TangentBundle I M)).2 =
    tangentCoordChange I alpha beta p
      ((trivializationAt E (TangentSpace I) alpha
        (⟨p, v⟩ : TangentBundle I M)).2)
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) beta) hβ,
    ← Trivialization.continuousLinearMapAt_apply_of_mem ℝ
      (trivializationAt E (TangentSpace I) alpha) hα]
  calc
    _ = (trivializationAt E (TangentSpace I) beta).continuousLinearMapAt ℝ p
        ((trivializationAt E (TangentSpace I) beta).symmL ℝ p
          (tangentCoordChange I alpha beta p a)) := hsymm
    _ = tangentCoordChange I alpha beta p a :=
      Trivialization.continuousLinearMapAt_symmL
        (trivializationAt E (TangentSpace I) beta) hβ _
    _ = tangentCoordChange I alpha beta p
        ((trivializationAt E (TangentSpace I) alpha).continuousLinearMapAt ℝ p v) := by
      congr 1
      simp [a, chartVelocityInChart,
        Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) alpha) hα]

/-- The second-order regularity needed by the coordinate geodesic equation.

The eventual first-derivative clause is intentional: Mathlib's `deriv` is
totalized, so differentiability only at the base time could permit spurious
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
    chartChristoffelContraction (I := I) g alpha
      (chartReading (I := I) alpha gamma t)
      (deriv (chartReading (I := I) alpha gamma) t)
      (deriv (chartReading (I := I) alpha gamma) t)

/-- Solved-form sign regression for the coordinate ODE.  The spray uses the
negative Christoffel contraction, so the unsolved equation is exactly
`u'' = -Gamma(u',u')`. -/
theorem chartAcceleration_eq_zero_iff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) (t : ℝ) :
    chartAcceleration (I := I) g alpha gamma t = 0 ↔
      deriv (deriv (chartReading (I := I) alpha gamma)) t =
        -chartChristoffelContraction (I := I) g alpha
          (chartReading (I := I) alpha gamma t)
          (deriv (chartReading (I := I) alpha gamma) t)
          (deriv (chartReading (I := I) alpha gamma) t) := by
  unfold chartAcceleration
  constructor
  · exact eq_neg_of_add_eq_zero_left
  · intro h
    rw [h]
    simp

/-- Coordinate straight-line regression.  Whenever the Christoffel
contraction vanishes along an affine chart path, its coordinate acceleration
vanishes identically.  A concrete Euclidean metric instantiation can use this
lemma without introducing a second metric representation. -/
theorem chartAcceleration_affine_of_zero_contraction
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {a b : E}
    (hread : ∀ t : ℝ, chartReading (I := I) alpha gamma t = a + t • b)
    (hcontraction : ∀ t : ℝ,
      chartChristoffelContraction (I := I) g alpha (a + t • b) b b = 0) :
    ∀ t, chartAcceleration (I := I) g alpha gamma t = 0 := by
  have hu : chartReading (I := I) alpha gamma = fun t : ℝ => a + t • b := by
    funext t
    exact hread t
  have hfirst : deriv (fun t : ℝ => a + t • b) = fun _ => b := by
    funext t
    simpa [Pi.add_apply, Function.id_def] using
      ((hasDerivAt_const (x := t) (c := a)).add
        ((hasDerivAt_id t).smul_const b)).deriv
  have hsecond : deriv (deriv (fun t : ℝ => a + t • b)) = fun _ => 0 := by
    rw [hfirst]
    funext t
    exact (hasDerivAt_const (x := t) (c := b)).deriv
  intro t
  rw [chartAcceleration, hu]
  rw [hsecond, hfirst]
  simp [hcontraction]

/-- The chart ODE at one time, in solved second-order form.

Source anchor: Morgan--Tian, Definition 1.17 and the coordinate paragraph on
printed p. 41 (`morganTian2007`). -/
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
returned curve is continuous at every time in the displayed interval.

Source anchor: Morgan--Tian, Definition 1.17 and the coordinate/initial-value
paragraph on printed p. 41 (`morganTian2007`). -/
theorem exists_localChartGeodesicAt [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p γ t ∈ interior (extChartAt I p).target) ∧
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
  refine ⟨ε', hε', γ, hγ₀, hread_deriv₀, ?_, ?_, ?_⟩
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
    simpa only [hread t ht] using htarget t ht
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

/- The two private lemmas below identify the fixed-chart second-order equation
   with the first-order spray equation.  This is a fixed-chart equivalence only:
   moving-foot transport still requires the pending Christoffel transition law. -/
private theorem hasDerivAt_chartState_of_equation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {t : ℝ}
    (hgamma : HasChartGeodesicEquationAt (I := I) g alpha gamma t) :
    HasDerivAt (chartState (I := I) alpha gamma)
      (chartSpray (I := I) g alpha (chartState (I := I) alpha gamma t)) t := by
  have hfirst := hgamma.1.2.1
  have hsecond := hgamma.1.2.2.2.hasDerivAt
  have hacc : deriv (deriv (chartReading (I := I) alpha gamma)) t =
      chartSpraySecond (I := I) g alpha
        (chartReading (I := I) alpha gamma t)
        (deriv (chartReading (I := I) alpha gamma) t) := by
    rw [chartSpraySecond_eq_neg_contraction]
    exact eq_neg_of_add_eq_zero_left hgamma.2
  have hsecond' := hsecond.congr_deriv hacc
  change HasDerivAt
    (fun s => (chartReading (I := I) alpha gamma s,
      deriv (chartReading (I := I) alpha gamma) s))
    (deriv (chartReading (I := I) alpha gamma) t,
      chartSpraySecond (I := I) g alpha
        (chartReading (I := I) alpha gamma t)
        (deriv (chartReading (I := I) alpha gamma) t)) t
  exact hfirst.prodMk hsecond'

private theorem chartEquation_of_hasDerivAt_chartState
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {t : ℝ}
    (hreg : HasChartGeodesicRegularityAt (I := I) alpha gamma t)
    (hstate : HasDerivAt (chartState (I := I) alpha gamma)
      (chartSpray (I := I) g alpha
        (chartState (I := I) alpha gamma t)) t) :
    HasChartGeodesicEquationAt (I := I) g alpha gamma t := by
  refine ⟨hreg, ?_⟩
  have hsecond : HasDerivAt (deriv (chartReading (I := I) alpha gamma))
      (chartSpraySecond (I := I) g alpha
        (chartReading (I := I) alpha gamma t)
        (deriv (chartReading (I := I) alpha gamma) t)) t := by
    have h := (hstate.hasFDerivAt.snd).hasDerivAt
    simpa [chartState, chartSpray, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply] using h
  rw [chartAcceleration, hsecond.deriv]
  rw [chartSpraySecond_eq_neg_contraction]
  simp

private theorem hasDerivAt_chartState_iff_chartEquation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {t : ℝ}
    (hreg : HasChartGeodesicRegularityAt (I := I) alpha gamma t) :
    HasDerivAt (chartState (I := I) alpha gamma)
        (chartSpray (I := I) g alpha
          (chartState (I := I) alpha gamma t)) t ↔
      HasChartGeodesicEquationAt (I := I) g alpha gamma t := by
  constructor
  · exact chartEquation_of_hasDerivAt_chartState (I := I) g alpha hreg
  · intro h
    exact hasDerivAt_chartState_of_equation (I := I) g alpha h

omit [FiniteDimensional ℝ E] in
private theorem contDiffOn_of_hasDerivAt_ode
    {F : E × E → E × E} {z : ℝ → E × E} {s : Set ℝ} {U : Set (E × E)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F U)
    (hmem : ∀ t ∈ s, z t ∈ U)
    (hode : ∀ t ∈ s, HasDerivAt z (F (z t)) t) (n : ℕ) :
    ContDiffOn ℝ n z s := by
  have hzcont : ContinuousOn z s := fun t ht =>
    (hode t ht).continuousAt.continuousWithinAt
  induction n with
  | zero => exact contDiffOn_zero.mpr hzcont
  | succ n ih =>
    have hdiff : DifferentiableOn ℝ z s := fun t ht =>
      (hode t ht).differentiableAt.differentiableWithinAt
    have hFn : ContDiffOn ℝ n F U := contDiffOn_infty.mp hF n
    have hcomp : ContDiffOn ℝ n (F ∘ z) s := hFn.comp ih hmem
    have hderiv : ContDiffOn ℝ n (deriv z) s := hcomp.congr (fun t ht => by
      simpa [Function.comp_apply] using (hode t ht).deriv)
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_deriv_of_isOpen hs).2
    refine ⟨hdiff, ?_, hderiv⟩
    simp

/-- Smoothness bootstrap for a fixed-chart geodesic equation.

The local spray is smooth on the chart target.  A solution of its first-order
state equation is therefore `C^n` on every open time set on which the chart
equation is asserted.  This is the regularity theorem used by the eventual
moving-chart/maximal-domain construction; it does not claim smooth dependence
on initial data. -/
theorem contDiffOn_chartState_of_chartEquationOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (hinterior : ∀ t ∈ s,
      chartReading (I := I) alpha gamma t ∈ interior (extChartAt I alpha).target)
    (hgamma : HasChartGeodesicEquationOn (I := I) g alpha gamma s) (n : ℕ) :
    ContDiffOn ℝ n (chartState (I := I) alpha gamma) s := by
  let U : Set (E × E) := interior (extChartAt I alpha).target ×ˢ (Set.univ : Set E)
  have hmem : ∀ t ∈ s, chartState (I := I) alpha gamma t ∈ U := by
    intro t ht
    exact ⟨hinterior t ht, Set.mem_univ _⟩
  have hode : ∀ t ∈ s, HasDerivAt (chartState (I := I) alpha gamma)
      (chartSpray (I := I) g alpha (chartState (I := I) alpha gamma t)) t := by
    intro t ht
    exact hasDerivAt_chartState_of_equation (I := I) g alpha (hgamma t ht).2
  exact contDiffOn_of_hasDerivAt_ode hs
    (chartSpray_contDiffOn (I := I) g alpha) hmem hode n

/-- The chart reading of a fixed-chart geodesic equation is smooth to every
finite order on its open time domain. -/
theorem contDiffOn_chartReading_of_chartEquationOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {gamma : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (hinterior : ∀ t ∈ s,
      chartReading (I := I) alpha gamma t ∈ interior (extChartAt I alpha).target)
    (hgamma : HasChartGeodesicEquationOn (I := I) g alpha gamma s) (n : ℕ) :
    ContDiffOn ℝ n (chartReading (I := I) alpha gamma) s :=
  (contDiffOn_chartState_of_chartEquationOn (I := I) g alpha hs hinterior hgamma n).fst

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
@[simp] theorem chartChristoffelContraction_zero
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
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p γ t ∈ interior (extChartAt I p).target) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt γ t) :=
  exists_localChartGeodesicAt g p v BoundarylessManifold.isInteriorPoint

/-- The point-local IVP together with the full fixed-chart smoothness witness.

This strengthens `exists_localChartGeodesicAt` without changing its chart-local
contract.  The moving-chart transport needed to turn this witness into a
canonical maximal intrinsic solution remains a separate S18 obligation. -/
theorem exists_localChartGeodesicAt_smooth [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p γ t ∈ interior (extChartAt I p).target) ∧
      ContDiffOn ℝ ∞ (chartReading (I := I) p γ) (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt γ t) := by
  obtain ⟨ε, hε, γ, hγ₀, hvel, hγ, hinterior, hcont⟩ :=
    exists_localChartGeodesicAt (I := I) g p v hp
  have hsmooth : ContDiffOn ℝ ∞ (chartReading (I := I) p γ) (Ioo (-ε) ε) :=
    contDiffOn_infty.mpr (fun n =>
      contDiffOn_chartReading_of_chartEquationOn (I := I) g p isOpen_Ioo hinterior hγ n)
  exact ⟨ε, hε, γ, hγ₀, hvel, hγ, hinterior, hsmooth, hcont⟩

/-- Boundaryless wrapper for `exists_localChartGeodesicAt_smooth`. -/
theorem exists_localChartGeodesicAt_smooth_boundaryless [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p γ t ∈ interior (extChartAt I p).target) ∧
      ContDiffOn ℝ ∞ (chartReading (I := I) p γ) (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt γ t) :=
  exists_localChartGeodesicAt_smooth g p v BoundarylessManifold.isInteriorPoint

/-! ## Local connection contract

The following declarations package the moving-foot coordinate representative
of the covariant acceleration.  The coefficient term is
`chartChristoffelContraction`, whose definition expands the single bundled
connection `Connection.leviCivitaConnection g`.  They are a local source-facing
contract: chart independence and the fixed-chart to moving-foot transition are
not claimed until the pending Christoffel transformation law is supplied.
-/

/-- The acceleration of a curve, represented in the tangent fibre at its
current foot by the chart representative used in this module.  The Christoffel
term is obtained from the canonical bundled Levi--Civita connection through
`chartChristoffelContraction`; no connection or metric structure is introduced
by this definition.  Independence from the chosen chart is a later theorem. -/
def connectionAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) : TangentSpace I (gamma t) :=
    (trivializationAt E (TangentSpace I) (gamma t)).symmL ℝ (gamma t)
    (deriv (deriv (chartReading (I := I) (gamma t) gamma)) t +
      chartChristoffelContraction (I := I) g (gamma t)
        (chartReading (I := I) (gamma t) gamma t)
        (deriv (chartReading (I := I) (gamma t) gamma) t)
        (deriv (chartReading (I := I) (gamma t) gamma) t))

/- The old name is retained as a compatibility spelling for the local chart
   handoff.  All new statements use `connectionAcceleration`. -/
abbrev covariantAcceleration
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) : TangentSpace I (gamma t) :=
  connectionAcceleration (I := I) (E := E) g gamma t

/-- Declaration-level expansion of the connection term in the intrinsic
acceleration.  In particular, the first lower Christoffel slot is the curve
velocity and the second is the differentiated velocity. -/
theorem connectionAcceleration_eq_leviCivita
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) :
    connectionAcceleration (I := I) g gamma t =
      (trivializationAt E (TangentSpace I) (gamma t)).symmL ℝ (gamma t)
        (deriv (deriv (chartReading (I := I) (gamma t) gamma)) t +
          chartChristoffelContraction (I := I) g (gamma t)
            (chartReading (I := I) (gamma t) gamma t)
            (deriv (chartReading (I := I) (gamma t) gamma) t)
            (deriv (chartReading (I := I) (gamma t) gamma) t)) := by
  rfl

/-- Local vanishing-acceleration contract at a time.  The source and
regularity clauses are part of the curve contract; the final equality is the
canonical Levi--Civita coordinate representative in the moving-foot chart.
The intrinsic chart-independence theorem is deferred to the transition-law
slice. -/
def HasCovariantAccelerationAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) (A : TangentSpace I (gamma t)) : Prop :=
  gamma t ∈ (chartAt H (gamma t)).source ∧
    ContinuousAt gamma t ∧
    HasChartGeodesicRegularityAt (I := I) (gamma t) gamma t ∧
    connectionAcceleration (I := I) g gamma t = A

/-- A curve satisfies the local geodesic contract at `t` when it has the
required second-order regularity and the selected Levi--Civita coordinate
representative vanishes.  The chart-independent `D_t (gamma')` equivalence is
not asserted by this slice.

Source anchor: Morgan--Tian, Definition 1.17, printed p. 41
(`morganTian2007`). -/
def IsGeodesicAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ) : Prop :=
  HasCovariantAccelerationAt (I := I) g gamma t 0

/-- The intrinsic geodesic equation at every time of a totalized curve.

This low-level predicate is useful when an ODE theorem already supplies the
curve regularity separately.  The source-facing curve contract is
`IsGeodesicOn`, which also carries continuity on its asserted domain. -/
def isGeodesic
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) : Prop :=
  Continuous gamma ∧ ∀ t, IsGeodesicAt (I := I) g gamma t

/-- The open-interval form of the geodesic predicate.

`IsGeodesicAt` carries the local chart regularity and the vanishing
Levi--Civita acceleration.  Relativising it to a time set keeps the curve
defined on all of `ℝ` (as Mathlib's integral-curve predicates do), while the
continuity conjunct prevents a bare pointwise equation from being mistaken
for a curve. -/
def IsGeodesicEquationOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsGeodesicAt (I := I) g gamma t

/-- Morgan--Tian's open-domain geodesic curve contract: continuity on the
asserted time set and the intrinsic vanishing-acceleration equation. -/
def IsGeodesicOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  ContinuousOn gamma s ∧ IsGeodesicEquationOn (I := I) g gamma s

/-- Compatibility spelling for the source-facing curve contract. -/
def IsGeodesicCurveOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  IsGeodesicOn (I := I) g gamma s

/-- Restriction of the curve-level geodesic contract. -/
theorem IsGeodesicCurveOn.mono
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {s s' : Set ℝ} (hs : s' ⊆ s)
    (hgamma : IsGeodesicCurveOn (I := I) g gamma s) :
    IsGeodesicCurveOn (I := I) g gamma s' := by
  exact ⟨hgamma.1.mono hs, fun t ht => hgamma.2 t (hs ht)⟩

/-- A geodesic curve contract remains true after restricting its time domain. -/
theorem IsGeodesicOn.mono
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) {s s' : Set ℝ} (hs : s' ⊆ s)
  (hgamma : IsGeodesicOn (I := I) g gamma s) :
    IsGeodesicOn (I := I) g gamma s' := by
  exact ⟨hgamma.1.mono hs, fun t ht => hgamma.2 t (hs ht)⟩

/-- The global predicate is exactly the open-domain predicate on `univ`. -/
theorem isGeodesic_iff_isGeodesicOn_univ
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) :
    isGeodesic (I := I) g gamma ↔ IsGeodesicOn (I := I) g gamma (Set.univ : Set ℝ) := by
  constructor
  · rintro ⟨hcont, heq⟩
    exact ⟨hcont.continuousOn, fun t _ => heq t⟩
  · rintro ⟨hcont, heq⟩
    have hcont' : Continuous gamma := by
      rw [← continuousOn_univ]
      exact hcont
    exact ⟨hcont', fun t => heq t (Set.mem_univ _)⟩

/-- A geodesic solution on a (possibly still local) open time domain.

The curve is totalized outside `domain`, but all geometric assertions are
restricted to `domain`; this prevents an incomplete solution from being
silently represented by a globally smooth junk extension.

Source anchor: Morgan--Tian, Definition 1.17 and the local IVP paragraph,
printed p. 41 (`morganTian2007`). -/
structure GeodesicSolution
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) where
  domain : Set ℝ
  isOpen_domain : IsOpen domain
  isPreconnected_domain : IsPreconnected domain
  zero_mem_domain : (0 : ℝ) ∈ domain
  curve : ℝ → M
  initial_position : curve 0 = p
  initial_velocity :
    HasDerivAt (chartReading (I := I) p curve) (chartVelocityAt (I := I) p v) 0
  chart_smooth : ContDiffOn ℝ ∞ (chartReading (I := I) p curve) domain
  equation : IsGeodesicCurveOn (I := I) g curve domain

/-- The union of the domains of all currently supplied geodesic solutions with
the same initial data.  This is only a domain substrate: without the
overlap-uniqueness/gluing theorem it does not yet carry a canonical curve. -/
def maximalGeodesicDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} : Set ℝ :=
  ⋃ S : GeodesicSolution (I := I) g p v, S.domain

theorem maximalGeodesicDomain_isOpen
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} :
    IsOpen (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  unfold maximalGeodesicDomain
  exact isOpen_iUnion (fun S => S.isOpen_domain)

theorem maximalGeodesicDomain_isPreconnected
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hS : Nonempty (GeodesicSolution (I := I) g p v)) :
    IsPreconnected (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  unfold maximalGeodesicDomain
  obtain ⟨S₀⟩ := hS
  apply isPreconnected_iUnion
  · refine ⟨0, ?_⟩
    simp only [mem_iInter]
    intro S
    exact S.zero_mem_domain
  · intro S
    exact S.isPreconnected_domain

/-- The maximal domain has the order-theoretic interval property.

On `ℝ`, `OrdConnected` is the canonical order formulation of an interval.  We
keep the topological `IsPreconnected` theorem above as the construction
lemma, and expose this form for continuation and endpoint arguments. -/
theorem maximalGeodesicDomain_ordConnected
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hS : Nonempty (GeodesicSolution (I := I) g p v)) :
    (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)).OrdConnected := by
  exact (maximalGeodesicDomain_isPreconnected (I := I) (g := g) (p := p)
    (v := v) hS).ordConnected

/-- Every supplied solution domain is an order interval as well. -/
theorem GeodesicSolution.domain_ordConnected
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (S : GeodesicSolution (I := I) g p v) : S.domain.OrdConnected := by
  exact S.isPreconnected_domain.ordConnected

theorem zero_mem_maximalGeodesicDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hS : Nonempty (GeodesicSolution (I := I) g p v)) :
    (0 : ℝ) ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) := by
  obtain ⟨S⟩ := hS
  exact mem_iUnion_of_mem S S.zero_mem_domain

theorem subset_maximalGeodesicDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (S : GeodesicSolution (I := I) g p v) :
    S.domain ⊆ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) := by
  exact subset_iUnion (fun T : GeodesicSolution (I := I) g p v => T.domain) S

/-- Restricting a solution to a smaller open domain containing the initial time.

The underlying totalized curve is unchanged, so the initial data is preserved;
only the set on which the equation is asserted is narrowed. -/
def GeodesicSolution.restrict
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (S : GeodesicSolution (I := I) g p v)
    {s : Set ℝ} (hs : IsOpen s) (hpre : IsPreconnected s) (h0 : (0 : ℝ) ∈ s)
    (hsub : s ⊆ S.domain) : GeodesicSolution (I := I) g p v := by
  exact
    { domain := s
      isOpen_domain := hs
      isPreconnected_domain := hpre
      zero_mem_domain := h0
      curve := S.curve
      initial_position := S.initial_position
      initial_velocity := S.initial_velocity
      chart_smooth := S.chart_smooth.mono hsub
      equation := IsGeodesicCurveOn.mono g S.curve hsub S.equation }

/-- The maximality contract for a future canonical solution constructor.

It quantifies over every open-interval solution with the same initial data and
requires its domain to be contained in the selected domain.  This predicate is
kept separate from the domain union because constructing a canonical witness
requires the moving-chart gluing and continuation argument recorded in S18. -/
def IsMaximalGeodesicSolution
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (S : GeodesicSolution (I := I) g p v) : Prop :=
  ∀ {s : Set ℝ} {gamma : ℝ → M},
    IsOpen s → IsPreconnected s → (0 : ℝ) ∈ s → gamma 0 = p →
    HasDerivAt (chartReading (I := I) p gamma) (chartVelocityAt (I := I) p v) 0 →
    IsGeodesicCurveOn (I := I) g gamma s →
    s ⊆ S.domain

/-- The raw maximality contract contains every bundled solution domain.

This adapter is intentionally proved from the existing extension predicate:
the bundled solution fields supply all of its hypotheses.  It is the bridge
that makes `IsMaximalGeodesicSolution` and `maximalGeodesicDomain` refer to the
same family, while retaining the stronger raw-curve extension interface for
future continuation arguments. -/
theorem IsMaximalGeodesicSolution.domain_subset
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    {S : GeodesicSolution (I := I) g p v}
    (hmax : IsMaximalGeodesicSolution (I := I) (g := g) (p := p) (v := v) S)
    (T : GeodesicSolution (I := I) g p v) :
    T.domain ⊆ S.domain := by
  intro t ht
  exact hmax T.isOpen_domain T.isPreconnected_domain T.zero_mem_domain
    T.initial_position T.initial_velocity T.equation ht

/-- A bundled maximal solution has exactly the union maximal domain.

The reverse inclusion is the substantive direction: it follows by applying
the raw extension predicate to each bundled solution selected by membership in
the union. -/
theorem IsMaximalGeodesicSolution.domain_eq_maximalGeodesicDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    {S : GeodesicSolution (I := I) g p v}
    (hmax : IsMaximalGeodesicSolution (I := I) (g := g) (p := p) (v := v) S) :
    S.domain = maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) := by
  apply Set.Subset.antisymm
  · exact subset_maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) S
  · intro t ht
    change t ∈ ⋃ T : GeodesicSolution (I := I) g p v, T.domain at ht
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp ht
    exact hmax.domain_subset T hT

/-!
### Domain witnesses and compatibility

The following declarations make the set-theoretic part of the maximal
interval construction explicit.  A member of the union is selected only after
its time has been supplied as a proof, so the totalized representative is
deterministic.  The agreement theorem is intentionally conditional on the
overlap-compatibility hypothesis; it is the exact interface needed by the
future chart-transition/gluing proof and does not assert that compatibility is
already available here.
-/

/-- A solution witness whose open domain contains `t`.

This is the witness form of the union used in `maximalGeodesicDomain`.  The
source is Morgan--Tian, Definition 1.17 and the coordinate initial-value
paragraph (printed p. 41); no maximality or completeness claim is hidden in
the predicate. -/
def MaximalGeodesicWitness
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (t : ℝ) : Prop :=
  ∃ S : GeodesicSolution (I := I) g p v, t ∈ S.domain

theorem mem_maximalGeodesicDomain_iff
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} {t : ℝ} :
    t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) ↔
      MaximalGeodesicWitness (I := I) (g := g) (p := p) (v := v) t := by
  simp only [maximalGeodesicDomain, MaximalGeodesicWitness, mem_iUnion]

/-- Select the solution witnessing membership of `t` in the maximal domain. -/
noncomputable def maximalGeodesicSolutionAt
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) :
    GeodesicSolution (I := I) g p v :=
  Classical.choose ((mem_maximalGeodesicDomain_iff (I := I) (g := g)
    (p := p) (v := v) (t := t)).mp ht)

theorem maximalGeodesicSolutionAt_mem
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) :
    t ∈ (maximalGeodesicSolutionAt (I := I) (g := g) (p := p) (v := v) ht).domain := by
  exact Classical.choose_spec ((mem_maximalGeodesicDomain_iff (I := I) (g := g)
    (p := p) (v := v) (t := t)).mp ht)

/-- A totalized value obtained by choosing a solution at each time in the
maximal domain.  Values outside the domain are the initial position. -/
noncomputable def maximalGeodesicCurve
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (t : ℝ) : M :=
  by
    classical
    exact if ht : t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) then
      (maximalGeodesicSolutionAt (I := I) (g := g) (p := p) (v := v) ht).curve t
    else p

theorem maximalGeodesicCurve_of_mem
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) t =
      (maximalGeodesicSolutionAt (I := I) (g := g) (p := p) (v := v) ht).curve t := by
  simp only [maximalGeodesicCurve, dif_pos ht]

theorem maximalGeodesicCurve_of_not_mem
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} {t : ℝ}
    (ht : t ∉ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) t = p := by
  simp only [maximalGeodesicCurve, dif_neg ht]

/-- At the initial time, a nonempty solution family already determines the
initial position.  This does not require overlap compatibility because every
selected witness carries the same `initial_position` field. -/
theorem maximalGeodesicCurve_zero_of_nonempty
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hS : Nonempty (GeodesicSolution (I := I) g p v)) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) 0 = p := by
  have h0 : (0 : ℝ) ∈ maximalGeodesicDomain (I := I) (g := g)
      (p := p) (v := v) := zero_mem_maximalGeodesicDomain (I := I) (g := g)
        (p := p) (v := v) hS
  rw [maximalGeodesicCurve_of_mem h0]
  exact (maximalGeodesicSolutionAt (I := I) (g := g) (p := p) (v := v) h0).initial_position

/-- Pairwise overlap compatibility for the supplied solution family.

For two solutions `S` and `T`, the curves must agree on the intersection of
their domains.  The condition is the gluing premise, not a theorem: it is to
be discharged by the moving-chart uniqueness argument in the continuation
slice. -/
def GeodesicSolutionsCompatible
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} : Prop :=
  ∀ S T : GeodesicSolution (I := I) g p v,
    EqOn S.curve T.curve (S.domain ∩ T.domain)

theorem maximalGeodesicCurve_agrees
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v))
    (S : GeodesicSolution (I := I) g p v) {t : ℝ} (ht : t ∈ S.domain) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) t = S.curve t := by
  have htm : t ∈ maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) :=
    subset_maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) S ht
  rw [maximalGeodesicCurve_of_mem htm]
  exact hcompat (maximalGeodesicSolutionAt (I := I) (g := g) (p := p) (v := v) htm) S
    ⟨maximalGeodesicSolutionAt_mem (I := I) (g := g) (p := p) (v := v) htm, ht⟩

/-- On the domain of a supplied solution, the selected maximal representative
agrees on a whole neighbourhood, not just at one time.  Openness of the
solution domain is what upgrades pointwise overlap compatibility to the germ
equality required by derivative and smoothness transfer. -/
theorem maximalGeodesicCurve_eventuallyEq_of_mem
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v))
    (S : GeodesicSolution (I := I) g p v) {t : ℝ} (ht : t ∈ S.domain) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) =ᶠ[𝓝 t] S.curve := by
  filter_upwards [S.isOpen_domain.mem_nhds ht] with s hs
  exact maximalGeodesicCurve_agrees hcompat S hs

theorem maximalGeodesicCurve_zero
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hS : Nonempty (GeodesicSolution (I := I) g p v))
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v)) :
    maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) 0 = p := by
  obtain ⟨S⟩ := hS
  rw [maximalGeodesicCurve_agrees hcompat S S.zero_mem_domain]
  exact S.initial_position

theorem maximalGeodesicDomain_eq_univ_of_global_solution
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (S : GeodesicSolution (I := I) g p v) (hdom : S.domain = (Set.univ : Set ℝ)) :
    maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) = Set.univ := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro t ht
    apply subset_maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) S
    rw [hdom]
    exact Set.mem_univ t

/-- A time set has an unbounded lifetime when it is unbounded in both time
directions.  This keeps the two endpoint directions explicit instead of
encoding an unbounded maximal interval as an opaque predicate. -/
def HasUnboundedLifetime (s : Set ℝ) : Prop :=
  ¬BddAbove s ∧ ¬BddBelow s

theorem hasUnboundedLifetime_univ :
    HasUnboundedLifetime (Set.univ : Set ℝ) := by
  constructor
  · rintro ⟨a, ha⟩
    have h := ha (Set.mem_univ (a + 1))
    linarith
  · rintro ⟨a, ha⟩
    have h := ha (Set.mem_univ (a - 1))
    linarith

theorem maximalGeodesicDomain_hasUnboundedLifetime_of_global_solution
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (S : GeodesicSolution (I := I) g p v) (hdom : S.domain = (Set.univ : Set ℝ)) :
    HasUnboundedLifetime
      (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  rw [maximalGeodesicDomain_eq_univ_of_global_solution S hdom]
  exact hasUnboundedLifetime_univ

theorem restrict_domain_subset_maximalGeodesicDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (S : GeodesicSolution (I := I) g p v)
    {s : Set ℝ} (hs : IsOpen s) (hpre : IsPreconnected s) (h0 : (0 : ℝ) ∈ s)
    (hsub : s ⊆ S.domain) :
    (S.restrict hs hpre h0 hsub).domain ⊆
      maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) := by
  exact subset_maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)
    (S.restrict hs hpre h0 hsub)

/-! ### Conditional canonical-union transfer

The next lemmas isolate the analytic part of the maximal-interval
construction.  They are conditional on the explicit overlap premise above:
the missing metric Christoffel transformation theorem is still the producer
that must establish that premise for arbitrary initial data. -/

/-- The restriction operation preserves the data which identify a solution.

This is a small API regression, but it is useful when a continuation proof
shrinks a solution to an overlap interval. -/
theorem GeodesicSolution.restrict_data
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p} (S : GeodesicSolution (I := I) g p v)
    {s : Set ℝ} (hs : IsOpen s) (hpre : IsPreconnected s) (h0 : (0 : ℝ) ∈ s)
    (hsub : s ⊆ S.domain) :
    (S.restrict hs hpre h0 hsub).domain = s ∧
      (S.restrict hs hpre h0 hsub).curve = S.curve ∧
      (S.restrict hs hpre h0 hsub).initial_position = S.initial_position ∧
      (S.restrict hs hpre h0 hsub).initial_velocity = S.initial_velocity := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The chosen representative is continuous on the union of compatible
solution domains.  Openness of each witness domain upgrades pointwise
agreement to the germ equality required by continuity. -/
theorem maximalGeodesicCurve_continuousOn_of_compatible
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v)) :
    ContinuousOn
      (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v))
      (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  intro t ht
  obtain ⟨S, htS⟩ :=
    (mem_maximalGeodesicDomain_iff (I := I) (g := g) (p := p) (v := v)
      (t := t)).mp ht
  have hScont : ContinuousAt S.curve t :=
    S.equation.1.continuousAt (S.isOpen_domain.mem_nhds htS)
  have heq :
      maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) =ᶠ[𝓝 t]
        S.curve :=
    maximalGeodesicCurve_eventuallyEq_of_mem hcompat S htS
  exact (hScont.congr_of_eventuallyEq heq).continuousWithinAt

/-- The chart reading of the chosen representative is smooth on the union of
compatible solution domains. -/
theorem maximalGeodesicCurve_chartSmoothOn_of_compatible
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v)) :
    ContDiffOn ℝ ∞
      (chartReading (I := I) p
        (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v)))
      (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  intro t ht
  obtain ⟨S, htS⟩ :=
    (mem_maximalGeodesicDomain_iff (I := I) (g := g) (p := p) (v := v)
      (t := t)).mp ht
  have hSdiff : ContDiffAt ℝ ∞
      (chartReading (I := I) p S.curve) t :=
    S.chart_smooth.contDiffAt (S.isOpen_domain.mem_nhds htS)
  have heqCurve :
      maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) =ᶠ[𝓝 t]
        S.curve :=
    maximalGeodesicCurve_eventuallyEq_of_mem hcompat S htS
  have heqRead :
      chartReading (I := I) p
          (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v)) =ᶠ[𝓝 t]
        chartReading (I := I) p S.curve := by
    filter_upwards [heqCurve] with s hs
    simpa only [chartReading] using congrArg (extChartAt I p) hs
  exact (hSdiff.congr_of_eventuallyEq heqRead).contDiffWithinAt

/-- A nonzero Christoffel contraction cannot be cancelled by the wrong sign.

This reusable obstruction is the algebraic core of the nonconstant-metric sign
probe: an eventual concrete metric instantiation supplies the displayed
nonzero contraction and second derivative, while this theorem rules out the
reversed `u'' - Γ(u',u')` equation.  The instantiation itself remains a later
coordinate-regression obligation. -/
theorem chartAcceleration_sign_regression
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (t : ℝ)
    (hsecond : deriv (deriv (chartReading (I := I) (gamma t) gamma)) t =
      chartChristoffelContraction (I := I) g (gamma t)
        (chartReading (I := I) (gamma t) gamma t)
        (deriv (chartReading (I := I) (gamma t) gamma) t)
        (deriv (chartReading (I := I) (gamma t) gamma) t))
    (hnonzero : chartChristoffelContraction (I := I) g (gamma t)
        (chartReading (I := I) (gamma t) gamma t)
        (deriv (chartReading (I := I) (gamma t) gamma) t)
        (deriv (chartReading (I := I) (gamma t) gamma) t) ≠ 0) :
    chartAcceleration (I := I) g (gamma t) gamma t ≠ 0 := by
  intro hzero
  have hcancel := (chartAcceleration_eq_zero_iff (I := I) g (gamma t) gamma t).mp hzero
  have heq :
      chartChristoffelContraction (I := I) g (gamma t)
          (chartReading (I := I) (gamma t) gamma t)
          (deriv (chartReading (I := I) (gamma t) gamma) t)
          (deriv (chartReading (I := I) (gamma t) gamma) t) =
        -chartChristoffelContraction (I := I) g (gamma t)
          (chartReading (I := I) (gamma t) gamma t)
          (deriv (chartReading (I := I) (gamma t) gamma) t)
          (deriv (chartReading (I := I) (gamma t) gamma) t) := by
    calc
      _ = deriv (deriv (chartReading (I := I) (gamma t) gamma)) t := hsecond.symm
      _ = -_ := hcancel
  apply hnonzero
  have htwo : (2 : ℝ) •
      chartChristoffelContraction (I := I) g (gamma t)
        (chartReading (I := I) (gamma t) gamma t)
        (deriv (chartReading (I := I) (gamma t) gamma) t)
        (deriv (chartReading (I := I) (gamma t) gamma) t) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr heq
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Constant curves are geodesics; this is the zero-velocity regression for
the canonical coordinate equation. -/
theorem isGeodesic_const
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    isGeodesic g (fun _ : ℝ => p) := by
  classical
  refine ⟨continuous_const, ?_⟩
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
  · change connectionAcceleration (I := I) g (fun _ : ℝ => p) t = 0
    rw [connectionAcceleration, hsecond, hderiv]
    simp only [chartChristoffelContraction_zero, add_zero, map_zero]

/-- Concrete model regression for the zero-velocity case.

On an inner-product vector space, Mathlib's canonical
`riemannianMetricVectorSpace` supplies the Euclidean metric.  Its bundled
smoothness is analytic (`ω`), so the record update below exposes the same
metric at the `∞` regularity used by this module.  The resulting constant
curve is geodesic by the intrinsic coordinate contract; this is deliberately
the bounded zero-velocity probe, not a claim about the nonzero straight-line
Christoffel calculation.
-/
theorem isGeodesic_const_riemannianMetricVectorSpace
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (p : F) :
    isGeodesic (I := 𝓘(ℝ, F)) (M := F)
      ({ riemannianMetricVectorSpace F with
          contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top })
      (fun _ : ℝ => p) := by
  let g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (TangentSpace 𝓘(ℝ, F)) :=
    { riemannianMetricVectorSpace F with
        contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }
  exact isGeodesic_const (I := 𝓘(ℝ, F)) g p

/-! ### Euclidean straight-line coefficient regression

The following calculation is intentionally concrete.  It unfolds the
canonical Euclidean metric through `Connection.christoffel_formula`, rather
than postulating a flat connection, and checks the flat branch of the chart
equation against the bundled connection.  A nonconstant metric is still
needed to distinguish sign and lower-slot conventions. -/

/-- The canonical Euclidean metric has zero Christoffel coefficients in every
model-space chart.  The proof keeps the bundled metric and
`Connection.leviCivitaConnection` as the only geometric data.

This is the coordinate probe corresponding to Morgan--Tian's equation (1.1)
and Definition 1.17 (`morganTian2007`).  Since all coefficients vanish in
the flat model, this regression does not by itself distinguish a reversed
Christoffel sign or swapped lower slots. -/
theorem chartConnectionCoeff_riemannianMetricVectorSpace_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (alpha q : F) (i j k : Fin (Module.finrank ℝ F)) :
    chartConnectionCoeff (I := 𝓘(ℝ, F))
      ({ riemannianMetricVectorSpace F with
          contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top })
      alpha q i j k = 0 := by
  let g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (TangentSpace 𝓘(ℝ, F)) :=
    { riemannianMetricVectorSpace F with
        contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }
  let t := trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha
  let b := Module.finBasis ℝ F
  have hq : q ∈ (chartAt F alpha).source := by simp
  have hi : (𝓘(ℝ, F)).IsInteriorPoint q :=
    BoundarylessManifold.isInteriorPoint
  have hderiv' (a c r : Fin (Module.finrank ℝ F)) :
      fderiv ℝ
          (fun y : F =>
            g.inner ((extChartAt 𝓘(ℝ, F) alpha).symm y)
              ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
                (Module.finBasis ℝ F) a ((extChartAt 𝓘(ℝ, F) alpha).symm y))
              ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
                (Module.finBasis ℝ F) c ((extChartAt 𝓘(ℝ, F) alpha).symm y)))
          ((extChartAt 𝓘(ℝ, F) alpha) q) (Module.finBasis ℝ F r) = 0 := by
    have hh : (fun y : F =>
        g.inner ((extChartAt 𝓘(ℝ, F) alpha).symm y)
          ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
            (Module.finBasis ℝ F) a ((extChartAt 𝓘(ℝ, F) alpha).symm y))
          ((trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
            (Module.finBasis ℝ F) c ((extChartAt 𝓘(ℝ, F) alpha).symm y))) =
      (fun _ : F => inner ℝ ((Module.finBasis ℝ F) a)
        ((Module.finBasis ℝ F) c)) := by
      funext y
      have hfa : (trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
            (Module.finBasis ℝ F) a ((extChartAt 𝓘(ℝ, F) alpha).symm y) =
            (Module.finBasis ℝ F) a := by
        have hx : ((extChartAt 𝓘(ℝ, F) alpha).symm y) ∈
            (trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).baseSet := by simp
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
        simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
        rw [Bundle.Trivialization.linearEquivAt_symm_apply]
        rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hx]
        rw [TangentBundle.symmL_model_space]
        unfold TangentSpace
        rfl
      have hfc : (trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).localFrame
            (Module.finBasis ℝ F) c ((extChartAt 𝓘(ℝ, F) alpha).symm y) =
            (Module.finBasis ℝ F) c := by
        have hx : ((extChartAt 𝓘(ℝ, F) alpha).symm y) ∈
            (trivializationAt F (TangentSpace 𝓘(ℝ, F)) alpha).baseSet := by simp
        rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet _ _ hx]
        simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
        rw [Bundle.Trivialization.linearEquivAt_symm_apply]
        rw [← Bundle.Trivialization.symmL_apply (R := ℝ) _ hx]
        rw [TangentBundle.symmL_model_space]
        unfold TangentSpace
        rfl
      rw [hfa, hfc]
      rfl
    rw [hh]
    simp
  have hf := Connection.christoffel_formula
    (I := 𝓘(ℝ, F)) g (alpha := alpha) (p := q) hq hi i j k
  dsimp only at hf
  simp only [hderiv'] at hf
  have hleft :
      (t.basisAt b (by simp [t])).repr
          (Connection.leviCivitaConnection g
            (t.localFrame b j) q (t.localFrame b i q)) k = 0 := by
    simpa only [t, b, zero_add, add_zero, sub_zero, mul_zero,
      Finset.sum_const_zero] using hf
  rw [chartConnectionCoeff]
  have hbase : q ∈ t.baseSet := by simp [t]
  rw [Bundle.Trivialization.localFrame_coeff_apply_of_mem_baseSet
    (I := 𝓘(ℝ, F)) t b hbase
    (fun x => Connection.leviCivitaConnection g
      (t.localFrame b j) x (t.localFrame b i x)) k]
  exact hleft

/-- The Euclidean Christoffel contraction is zero for arbitrary two
velocities, not only for the repeated zero velocity. -/
theorem chartChristoffelContraction_riemannianMetricVectorSpace_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (alpha y v w : F) :
    chartChristoffelContraction (I := 𝓘(ℝ, F))
      ({ riemannianMetricVectorSpace F with
          contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top })
      alpha y v w = 0 := by
  let g : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (TangentSpace 𝓘(ℝ, F)) :=
    { riemannianMetricVectorSpace F with
        contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }
  let b := Module.finBasis ℝ F
  let q := (extChartAt (𝓘(ℝ, F)) alpha).symm y
  let t := trivializationAt F (TangentSpace (𝓘(ℝ, F))) alpha
  change ∑ k, (∑ i, ∑ j,
      chartConnectionCoeff (I := 𝓘(ℝ, F)) g alpha q i j k *
        b.repr v i * b.repr w j) • b k = 0
  have hcoeff (i j k : Fin (Module.finrank ℝ F)) :
      chartConnectionCoeff (I := 𝓘(ℝ, F)) g alpha q i j k = 0 := by
    exact chartConnectionCoeff_riemannianMetricVectorSpace_zero
      (alpha := alpha) (q := q) i j k
  simp_rw [hcoeff]
  simp

/-- An affine Euclidean chart path has zero coordinate acceleration.  In
particular, the theorem covers nonzero velocities and is a concrete
straight-line regression for the flat branch of the Morgan--Tian equation. -/
theorem chartAcceleration_affine_riemannianMetricVectorSpace_zero
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (alpha a v : F) :
    ∀ t : ℝ,
    chartAcceleration (I := 𝓘(ℝ, F))
      ({ riemannianMetricVectorSpace F with
          contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top })
      alpha (fun s : ℝ => a + s • v) t = 0 := by
  intro t
  apply chartAcceleration_affine_of_zero_contraction
    (I := 𝓘(ℝ, F))
    (g := ({ riemannianMetricVectorSpace F with
      contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }))
    (alpha := alpha) (gamma := fun s : ℝ => a + s • v)
    (a := a) (b := v)
  · intro s
    simp [chartReading]
  · intro s
    exact chartChristoffelContraction_riemannianMetricVectorSpace_zero
      (alpha := alpha) (y := a + s • v) (v := v) (w := v)

/-! ### Global zero-velocity solution regression

The general nonempty maximal-domain witness still needs the fixed-to-moving
Christoffel law.  The constant curve is independent of that law, however, and
therefore supplies a useful canonical boundary case for the domain substrate.
-/

/-- The constant curve gives a global intrinsic solution for zero initial
velocity.  This is a genuine `GeodesicSolution` witness on `Set.univ`, not a
pointwise equation or a chosen totalized representative.

Source anchor: Morgan--Tian, Definition 1.17 and the coordinate/initial-value
paragraph on printed p. 41 (`morganTian2007`). -/
noncomputable def geodesicSolution_zero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) : GeodesicSolution (I := I) g p (0 : TangentSpace I p) := by
  let gamma : ℝ → M := fun _ ↦ p
  have hconst : HasDerivAt (chartReading (I := I) p gamma) 0 0 := by
    change HasDerivAt (fun _ : ℝ ↦ extChartAt I p p) 0 0
    exact hasDerivAt_const (x := (0 : ℝ)) (c := extChartAt I p p)
  have hcurve : IsGeodesicCurveOn (I := I) g gamma (Set.univ : Set ℝ) := by
    exact (isGeodesic_iff_isGeodesicOn_univ (I := I) g gamma).mp
      (isGeodesic_const (I := I) g p)
  refine ⟨Set.univ, isOpen_univ, isPreconnected_univ, Set.mem_univ 0,
    gamma, rfl, ?_, ?_, hcurve⟩
  · have hvzero : chartVelocityAt (I := I) p
        (0 : TangentSpace I p) = 0 := by
      unfold chartVelocityAt
      rw [TangentBundle.trivializationAt_apply]
      exact map_zero _
    simpa [gamma, hvzero] using hconst
  · change ContDiffOn ℝ ∞ (fun _ : ℝ ↦ extChartAt I p p) (Set.univ : Set ℝ)
    exact contDiffOn_const

/-- A nonempty global solution witness for zero initial velocity. -/
theorem nonempty_geodesicSolution_zero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    Nonempty (GeodesicSolution (I := I) g p (0 : TangentSpace I p)) :=
  ⟨geodesicSolution_zero_velocity (I := I) g p⟩

@[simp] theorem geodesicSolution_zero_velocity_domain
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    (geodesicSolution_zero_velocity (I := I) g p).domain = (Set.univ : Set ℝ) := rfl

/-- The maximal domain is all of time for the zero-velocity regression. -/
theorem maximalGeodesicDomain_zero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    maximalGeodesicDomain (I := I) (g := g) (p := p)
      (v := (0 : TangentSpace I p)) = (Set.univ : Set ℝ) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · intro t ht
    let S := geodesicSolution_zero_velocity (I := I) g p
    apply subset_maximalGeodesicDomain (I := I) (g := g) (p := p)
      (v := (0 : TangentSpace I p)) S
    rw [geodesicSolution_zero_velocity_domain (I := I) g p]
    exact ht

/-- The zero-velocity maximal-domain regression has an unbounded lifetime. -/
theorem maximalGeodesicDomain_zero_velocity_hasUnboundedLifetime
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    HasUnboundedLifetime
      (maximalGeodesicDomain (I := I) (g := g) (p := p)
        (v := (0 : TangentSpace I p))) := by
  rw [maximalGeodesicDomain_zero_velocity (I := I) g p]
  exact hasUnboundedLifetime_univ

/-- The local geodesic contract is equivalent to the Morgan--Tian coordinate
equation in the chart centred at the foot.  This is an unfolding in the same
chart, not the fixed-chart to moving-foot invariance theorem. -/
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
    simpa [chartAcceleration, chartChristoffelContraction, connectionAcceleration, e,
      e.continuousLinearMapAt_symmL hbase, map_zero] using h
  · rintro ⟨hsource, hcont, hreg, hzero⟩
    refine ⟨hsource, hcont, hreg, ?_⟩
    have hacc : deriv (deriv (chartReading (I := I) (gamma t) gamma)) t +
        chartChristoffelContraction (I := I) g (gamma t)
          (chartReading (I := I) (gamma t) gamma t)
          (deriv (chartReading (I := I) (gamma t) gamma) t)
          (deriv (chartReading (I := I) (gamma t) gamma) t) = 0 := by
      simpa [chartAcceleration, chartChristoffelContraction] using hzero
    rw [connectionAcceleration, hacc, map_zero]

/-! ### Initial-time intrinsic regression

At the prescribed initial time, the chart used by the local IVP is already the
chart centred at the curve's foot.  This small bridge is therefore available
without a chart-transition theorem; transferring the equation to later moving
charts remains a separate S18 obligation. -/

/-- A fixed-chart equation at the initial foot is the intrinsic equation at
time zero.  The equality `gamma 0 = p` identifies the prescribed IVP chart
with the current-foot chart in `isGeodesicAt_iff_chartEquation`. -/
theorem isGeodesicAt_zero_of_chartEquationAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {p : M} {gamma : ℝ → M}
    (hposition : gamma 0 = p)
    (hcontinuous : ContinuousAt gamma 0)
    (hequation : HasChartGeodesicEquationAt (I := I) g p gamma 0) :
    IsGeodesicAt (I := I) g gamma 0 := by
  subst p
  rw [isGeodesicAt_iff_chartEquation]
  exact ⟨mem_chart_source H (gamma 0), hcontinuous, hequation⟩

/-- The point-local IVP witness also satisfies the intrinsic geodesic equation
at its prescribed initial time.  The theorem deliberately retains the fixed
chart equation and all local target/continuity witnesses for downstream
consumers. -/
theorem exists_localChartGeodesicAt_with_intrinsic_zero [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p) :
    ∃ ε > (0 : ℝ), ∃ gamma : ℝ → M,
      gamma 0 = p ∧
      HasDerivAt (chartReading (I := I) p gamma) (chartVelocityAt (I := I) p v) 0 ∧
      IsGeodesicAt (I := I) g gamma 0 ∧
      HasChartGeodesicEquationOn (I := I) g p gamma (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p gamma t ∈ interior (extChartAt I p).target) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt gamma t) := by
  obtain ⟨ε, hε, gamma, hposition, hvelocity, hequation, hinterior, hcontinuous⟩ :=
    exists_localChartGeodesicAt (I := I) g p v hp
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := by
    constructor <;> linarith
  have hinitial : IsGeodesicAt (I := I) g gamma 0 :=
    isGeodesicAt_zero_of_chartEquationAt (I := I) g hposition
      (hcontinuous 0 hzero) (hequation 0 hzero).2
  exact ⟨ε, hε, gamma, hposition, hvelocity, hinitial, hequation, hinterior,
    hcontinuous⟩

/-- Boundaryless wrapper for
`exists_localChartGeodesicAt_with_intrinsic_zero`. -/
theorem exists_localChartGeodesicAt_with_intrinsic_zero_boundaryless
    [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) :
    ∃ ε > (0 : ℝ), ∃ gamma : ℝ → M,
      gamma 0 = p ∧
      HasDerivAt (chartReading (I := I) p gamma) (chartVelocityAt (I := I) p v) 0 ∧
      IsGeodesicAt (I := I) g gamma 0 ∧
      HasChartGeodesicEquationOn (I := I) g p gamma (Ioo (-ε) ε) ∧
      (∀ t ∈ Ioo (-ε) ε,
        chartReading (I := I) p gamma t ∈ interior (extChartAt I p).target) ∧
      (∀ t ∈ Ioo (-ε) ε, ContinuousAt gamma t) :=
  exists_localChartGeodesicAt_with_intrinsic_zero (I := I) g p v
    BoundarylessManifold.isInteriorPoint

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
        chartChristoffelContraction (I := I) g (gamma t)
          (chartReading (I := I) (gamma t) gamma t)
          (deriv (chartReading (I := I) (gamma t) gamma) t)
          (deriv (chartReading (I := I) (gamma t) gamma) t) = 0 := by
  rw [isGeodesicAt_iff_chartEquation]
  rfl

/-! ### Affine reparameterization

The following transport is purely local in the chosen chart.  It records the
homogeneity needed by restriction, translation, and time-reversal arguments;
it does not use, or conceal, the still-pending moving-chart Christoffel
transformation law. -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Second-order chart regularity is preserved by an affine change of time.

The derivative is transported as
`(u ∘ (s ↦ a * s + c))' = a • (u' ∘ (s ↦ a * s + c))`.
Keeping this lemma separate makes the totalized-derivative side condition
explicit when later modules restrict or translate a geodesic. -/
theorem HasChartGeodesicRegularityAt.comp_affine
    (alpha : M) (gamma : ℝ → M) (a c t : ℝ)
    (h : HasChartGeodesicRegularityAt (I := I) alpha gamma (a * t + c)) :
    HasChartGeodesicRegularityAt (I := I) alpha
      (fun s ↦ gamma (a * s + c)) t := by
  rcases h with ⟨hsrc, hfirst, hev, hdiff⟩
  let φ : ℝ → ℝ := fun s ↦ a * s + c
  let u : ℝ → E := chartReading (I := I) alpha gamma
  let u' : ℝ → E := chartReading (I := I) alpha (fun s ↦ gamma (φ s))
  have hφcont : Continuous φ := by
    dsimp [φ]
    exact (continuous_const.mul continuous_id).add continuous_const
  have hφt : Tendsto φ (𝓝 t) (𝓝 (φ t)) :=
    hφcont.continuousAt.tendsto
  have hφderiv (s : ℝ) : HasDerivAt φ a s := by
    dsimp [φ]
    simpa only [mul_comm] using (hasDerivAt_const_mul a).add_const c
  have hu' : u' = u ∘ φ := by
    funext s
    rfl
  have hderiv_comp (s : ℝ) : deriv u' s = a • deriv u (φ s) := by
    rw [hu']
    calc
      deriv (u ∘ φ) s = deriv (fun r ↦ u (a * r + c)) s := by rfl
      _ = a • deriv (fun z ↦ u (z + c)) (a * s) := by
        exact deriv_comp_mul_left a (fun z ↦ u (z + c)) s
      _ = a • deriv u (a * s + c) := by
        rw [deriv_comp_add_const]
      _ = a • deriv u (φ s) := by rfl
  have hsrc' : ∀ᶠ s in 𝓝 t,
      (fun r ↦ gamma (φ r)) s ∈ (chartAt H alpha).source := by
    exact hφt.eventually hsrc
  have hfirst' : HasDerivAt u' (deriv u' t) t := by
    have hc := hfirst.scomp t (hφderiv t)
    have hc' : HasDerivAt u' (a • deriv u (φ t)) t := by
      simpa only [u', u, hu', Function.comp_def] using hc
    exact hc'.congr_deriv (hderiv_comp t).symm
  have hev' : ∀ᶠ s in 𝓝 t, HasDerivAt u' (deriv u' s) s := by
    have hev0 := hφt.eventually hev
    filter_upwards [hev0] with s hs
    have hc := hs.scomp s (hφderiv s)
    have hc' : HasDerivAt u' (a • deriv u (φ s)) s := by
      simpa only [u', u, hu', Function.comp_def] using hc
    exact hc'.congr_deriv (hderiv_comp s).symm
  have hdiff' : DifferentiableAt ℝ (deriv u') t := by
    rw [hu'] at hderiv_comp
    have hcomp : DifferentiableAt ℝ (deriv u ∘ φ) t :=
      hdiff.comp t (hφderiv t).differentiableAt
    have hsmul := hcomp.const_smul a
    rw [show deriv u' = fun s ↦ a • deriv u (φ s) by
      funext s; exact hderiv_comp s]
    have hfun : (a • (deriv u ∘ φ)) =
        (fun s ↦ a • deriv u (φ s)) := by
      funext s
      rfl
    rw [← hfun]
    exact hsmul
  exact ⟨hsrc', hfirst', hev', hdiff'⟩

/-- The fixed-chart geodesic equation is invariant under affine time change.

The acceleration and the connection contraction both acquire the common
factor `a * a`; the zero equation therefore transfers even when `a = 0`.
This is the homogeneity step used by restriction and time-translation
adapters. -/
theorem HasChartGeodesicEquationAt.comp_affine
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (gamma : ℝ → M) (a c t : ℝ)
    (h : HasChartGeodesicEquationAt (I := I) g alpha gamma (a * t + c)) :
    HasChartGeodesicEquationAt (I := I) g alpha
      (fun s ↦ gamma (a * s + c)) t := by
  rcases h with ⟨hreg, hzero⟩
  let φ : ℝ → ℝ := fun s ↦ a * s + c
  let u : ℝ → E := chartReading (I := I) alpha gamma
  let u' : ℝ → E := chartReading (I := I) alpha (fun s ↦ gamma (φ s))
  have hφcont : Continuous φ := by
    dsimp [φ]
    exact (continuous_const.mul continuous_id).add continuous_const
  have hφderiv (s : ℝ) : HasDerivAt φ a s := by
    dsimp [φ]
    simpa only [mul_comm] using (hasDerivAt_const_mul a).add_const c
  have hu' : u' = u ∘ φ := by
    funext s
    rfl
  have hderiv_comp (s : ℝ) : deriv u' s = a • deriv u (φ s) := by
    rw [hu']
    calc
      deriv (u ∘ φ) s = deriv (fun r ↦ u (a * r + c)) s := by rfl
      _ = a • deriv (fun z ↦ u (z + c)) (a * s) := by
        exact deriv_comp_mul_left a (fun z ↦ u (z + c)) s
      _ = a • deriv u (a * s + c) := by
        rw [deriv_comp_add_const]
      _ = a • deriv u (φ s) := by rfl
  have hsecond : HasDerivAt (deriv u')
      ((a * a) • deriv (deriv u) (φ t)) t := by
    have hbase := hreg.2.2.2
    have hcomp := hbase.hasDerivAt.scomp t (hφderiv t)
    have hsmul := HasDerivAt.const_smul a hcomp
    have hfun : (a • (deriv u ∘ φ)) =
        (fun s ↦ a • deriv u (φ s)) := by
      funext s
      rfl
    have hsmul' : HasDerivAt (fun s ↦ a • deriv u (φ s))
        (a • (a • deriv (deriv u) (φ t))) t := by
      rw [← hfun]
      exact hsmul
    have heq : deriv u' =ᶠ[𝓝 t] (fun s ↦ a • deriv u (φ s)) :=
      Filter.Eventually.of_forall (fun s ↦ hderiv_comp s)
    have hsmul'' := hsmul'.congr_of_eventuallyEq heq
    have hval : a • (a • deriv (deriv u) (φ t)) =
        (a * a) • deriv (deriv u) (φ t) := by
      rw [smul_smul]
    exact hsmul''.congr_deriv hval
  have hreg' := HasChartGeodesicRegularityAt.comp_affine
    (I := I) alpha gamma a c t hreg
  refine ⟨hreg', ?_⟩
  change deriv (deriv u') t +
      chartChristoffelContraction (I := I) g alpha (u' t)
        (deriv u' t) (deriv u' t) = 0
  rw [hsecond.deriv, hderiv_comp t]
  have hut : u' t = u (φ t) := by
    rw [hu']
    rfl
  rw [hut, chartChristoffelContraction_smul_smul]
  have hzero' : deriv (deriv u) (φ t) +
      chartChristoffelContraction (I := I) g alpha (u (φ t))
        (deriv u (φ t)) (deriv u (φ t)) = 0 := by
    simpa only [chartAcceleration, chartChristoffelContraction, u, φ] using hzero
  rw [← smul_add, hzero', smul_zero]

/-- The moving-foot geodesic predicate is invariant under affine time change.
This point-local bridge uses the same current-foot chart on both sides. -/
theorem IsGeodesicAt.comp_affine
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (a c t : ℝ)
    (h : IsGeodesicAt (I := I) g gamma (a * t + c)) :
    IsGeodesicAt (I := I) g (fun s ↦ gamma (a * s + c)) t := by
  have hbase := (isGeodesicAt_iff_chartEquation (I := I) g gamma
    (a * t + c)).mp h
  rcases hbase with ⟨hsource, hcont, heq⟩
  apply (isGeodesicAt_iff_chartEquation (I := I) g
    (fun s ↦ gamma (a * s + c)) t).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact hsource
  · have hphi : Continuous (fun s : ℝ ↦ a * s + c) := by
      exact (continuous_const.mul continuous_id).add continuous_const
    have hphi_at : ContinuousAt (fun s : ℝ ↦ a * s + c) t :=
      hphi.continuousAt
    have hc : ContinuousAt (gamma ∘ (fun s : ℝ ↦ a * s + c)) t :=
      ContinuousAt.comp (f := fun s : ℝ ↦ a * s + c) (g := gamma)
        (x := t) hcont hphi_at
    simpa only [Function.comp_def] using hc
  · exact HasChartGeodesicEquationAt.comp_affine (I := I) g
      (gamma (a * t + c)) gamma a c t heq

/-- A global geodesic remains global after affine reparameterization. -/
theorem isGeodesic_comp_affine
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (h : isGeodesic (I := I) g gamma) (a c : ℝ) :
    isGeodesic (I := I) g (fun s ↦ gamma (a * s + c)) := by
  refine ⟨?_, ?_⟩
  · exact h.1.comp ((continuous_const.mul continuous_id).add continuous_const)
  · intro t
    exact IsGeodesicAt.comp_affine (I := I) g gamma a c t (h.2 (a * t + c))

/-- Time translation is the unit-slope instance of affine transport. -/
theorem isGeodesic_comp_add
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (h : isGeodesic (I := I) g gamma) (c : ℝ) :
    isGeodesic (I := I) g (fun s ↦ gamma (s + c)) := by
  simpa only [one_mul] using isGeodesic_comp_affine (I := I) g gamma h 1 c

/-- Time reversal is the slope `-1` instance of affine transport. -/
theorem isGeodesic_comp_neg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (h : isGeodesic (I := I) g gamma) :
    isGeodesic (I := I) g (fun s ↦ gamma (-s)) := by
  simpa only [neg_mul, one_mul, zero_add, add_zero, neg_one_mul] using
    isGeodesic_comp_affine (I := I) g gamma h (-1) 0

/-- Velocity rescaling is the zero-offset instance of affine transport. -/
theorem isGeodesic_comp_mul_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (h : isGeodesic (I := I) g gamma) (a : ℝ) :
    isGeodesic (I := I) g (fun s ↦ gamma (a * s)) := by
  simpa only [add_zero] using isGeodesic_comp_affine (I := I) g gamma h a 0

/-- A geodesic contract on a time set pulls back along an affine parameter
change.  The domain is kept as the literal preimage, so no endpoint or
injectivity convention is hidden in the transport. -/
theorem IsGeodesicOn.comp_affine
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : IsGeodesicOn (I := I) g gamma s) (a c : ℝ) :
    IsGeodesicOn (I := I) g (fun t ↦ gamma (a * t + c))
      ((fun t : ℝ ↦ a * t + c) ⁻¹' s) := by
  let φ : ℝ → ℝ := fun t ↦ a * t + c
  have hφ : Continuous φ := by
    dsimp [φ]
    exact (continuous_const.mul continuous_id).add continuous_const
  refine ⟨?_, ?_⟩
  · have hcomp : ContinuousOn (gamma ∘ φ) (φ ⁻¹' s) :=
      h.1.comp hφ.continuousOn (fun t ht ↦ ht)
    simpa only [Function.comp_def, φ] using hcomp
  · intro t ht
    apply IsGeodesicAt.comp_affine (I := I) g gamma a c t
    exact h.2 (a * t + c) ht

/-- Set-relative time translation, with its exact pulled-back lifetime. -/
theorem IsGeodesicOn.comp_add
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : IsGeodesicOn (I := I) g gamma s) (c : ℝ) :
    IsGeodesicOn (I := I) g (fun t ↦ gamma (t + c))
      ((fun t : ℝ ↦ t + c) ⁻¹' s) := by
  simpa only [one_mul] using IsGeodesicOn.comp_affine (I := I) g gamma s h 1 c

/-- Set-relative time reversal, with its exact pulled-back lifetime. -/
theorem IsGeodesicOn.comp_neg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : IsGeodesicOn (I := I) g gamma s) :
    IsGeodesicOn (I := I) g (fun t ↦ gamma (-t))
      ((fun t : ℝ ↦ -t) ⁻¹' s) := by
  simpa only [neg_mul, one_mul, zero_add, add_zero, neg_one_mul] using
    IsGeodesicOn.comp_affine (I := I) g gamma s h (-1) 0

/-! ### Equation congruence and conditional maximal curve

The next congruence lemmas are purely local calculus.  They deliberately do
not assert that two coordinate representatives satisfy the same equation on
an overlap: the metric Christoffel transformation law is the separate S18
input which supplies the overlap compatibility premise. -/

/-- An eventual equality of two curves transports the local geodesic contract.

The proof keeps the totalized `deriv` regularity clauses explicit.  In
particular, the eventual equality is lifted once more with
`Filter.EventuallyEq.eventuallyEq_nhds` before transferring the eventual
first-derivative clause. -/
theorem isGeodesicAt_congr_of_eventuallyEq
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {gamma₁ gamma₂ : ℝ → M} {t : ℝ}
    (hev : gamma₂ =ᶠ[𝓝 t] gamma₁)
    (h : IsGeodesicAt (I := I) g gamma₁ t) :
    IsGeodesicAt (I := I) g gamma₂ t := by
  rw [isGeodesicAt_iff_chartEquation] at h ⊢
  obtain ⟨hsource, hcont, hreg, hacc⟩ := h
  have hpt : gamma₂ t = gamma₁ t := hev.self_of_nhds
  rw [hpt]
  have hloc :
      chartReading (I := I) (gamma₁ t) gamma₁ =ᶠ[𝓝 t]
        chartReading (I := I) (gamma₁ t) gamma₂ := by
    filter_upwards [hev] with s hs
    show extChartAt I (gamma₁ t) (gamma₁ s) =
      extChartAt I (gamma₁ t) (gamma₂ s)
    rw [hs]
  have hderiv :
      deriv (chartReading (I := I) (gamma₁ t) gamma₁) =ᶠ[𝓝 t]
        deriv (chartReading (I := I) (gamma₁ t) gamma₂) := hloc.deriv
  refine ⟨hsource, hcont.congr_of_eventuallyEq hev, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · filter_upwards [hreg.1, hev] with s hs hγ
      rwa [hγ]
    · exact (hreg.2.1.congr_of_eventuallyEq hloc.symm).congr_deriv hloc.deriv_eq
    · filter_upwards [hreg.2.2.1, hloc.eventuallyEq_nhds, hderiv]
        with s hs hlocs hds
      rw [← hds]
      exact hs.congr_of_eventuallyEq hlocs.symm
    · exact hreg.2.2.2.congr_of_eventuallyEq hderiv.symm
  · have h0 := hloc.self_of_nhds
    have h1 := hloc.deriv_eq
    have h2 := hloc.deriv.deriv_eq
    simpa [chartAcceleration, h0, h1, h2] using hacc

/-- A geodesic equation on an open interval is invariant under an eventual
equality supplied on that interval. -/
theorem IsGeodesicOn.congr_of_eqOn
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {gamma₁ gamma₂ : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (heq : Set.EqOn gamma₁ gamma₂ s)
    (h : IsGeodesicOn (I := I) g gamma₁ s) :
    IsGeodesicOn (I := I) g gamma₂ s := by
  refine ⟨h.1.congr heq.symm, ?_⟩
  intro t ht
  apply isGeodesicAt_congr_of_eventuallyEq (I := I) (g := g)
    (t := t) ?_ (h.2 t ht)
  exact (heq.eventuallyEq_of_mem (hs.mem_nhds ht)).symm

/-- Under pairwise overlap compatibility, the canonical union representative
satisfies the intrinsic equation on its union domain.  The theorem is
conditional because proving `hcompat` is precisely the pending Christoffel
transition/gluing argument. -/
theorem maximalGeodesicCurve_isGeodesicOn_of_compatible
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v)) :
    IsGeodesicOn (I := I) g
      (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v))
      (maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) := by
  refine ⟨maximalGeodesicCurve_continuousOn_of_compatible hcompat, ?_⟩
  intro t ht
  obtain ⟨S, htS⟩ :=
    (mem_maximalGeodesicDomain_iff (I := I) (g := g) (p := p) (v := v)
      (t := t)).mp ht
  have heq : Set.EqOn
      (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v))
      S.curve S.domain := by
    intro s hs
    exact maximalGeodesicCurve_agrees hcompat S hs
  exact (IsGeodesicOn.congr_of_eqOn (I := I) (g := g)
    S.isOpen_domain heq.symm S.equation).2 t htS

/-- A compatible nonempty solution family has a bundled solution on the full
union domain.  This packages the canonical curve, its initial data, and the
conditional equation/smoothness transfer without claiming the still-missing
arbitrary-data compatibility theorem. -/
theorem exists_maximalGeodesicSolution_of_compatible
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    (S₀ : GeodesicSolution (I := I) g p v)
    (hcompat : GeodesicSolutionsCompatible (I := I) (g := g) (p := p) (v := v)) :
    ∃ Smax : GeodesicSolution (I := I) g p v,
      Smax.domain = maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) ∧
      Smax.curve = maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) := by
  let hS : Nonempty (GeodesicSolution (I := I) g p v) := ⟨S₀⟩
  have hzero :
      maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) 0 = p :=
    maximalGeodesicCurve_zero hS hcompat
  have hvel :
      HasDerivAt
        (chartReading (I := I) p
          (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v)))
        (chartVelocityAt (I := I) p v) 0 := by
    have heqCurve :
        maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v) =ᶠ[𝓝 (0 : ℝ)]
          S₀.curve :=
      maximalGeodesicCurve_eventuallyEq_of_mem hcompat S₀ S₀.zero_mem_domain
    have heqRead :
        chartReading (I := I) p
            (maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v)) =ᶠ[𝓝 (0 : ℝ)]
          chartReading (I := I) p S₀.curve := by
      filter_upwards [heqCurve] with s hs
      simpa only [chartReading] using congrArg (extChartAt I p) hs
    exact S₀.initial_velocity.congr_of_eventuallyEq heqRead
  have hsmooth := maximalGeodesicCurve_chartSmoothOn_of_compatible hcompat
  have hequation := maximalGeodesicCurve_isGeodesicOn_of_compatible hcompat
  refine ⟨{
    domain := maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)
    isOpen_domain := maximalGeodesicDomain_isOpen (I := I) (g := g) (p := p) (v := v)
    isPreconnected_domain := maximalGeodesicDomain_isPreconnected
      (I := I) (g := g) (p := p) (v := v) hS
    zero_mem_domain := zero_mem_maximalGeodesicDomain
      (I := I) (g := g) (p := p) (v := v) hS
    curve := maximalGeodesicCurve (I := I) (g := g) (p := p) (v := v)
    initial_position := hzero
    initial_velocity := hvel
    chart_smooth := hsmooth
    equation := hequation
  }, rfl, rfl⟩

/-- A bundled solution whose domain is the compatible union extends every
other bundled solution with the same initial data.  This is the precise
interval-maximality statement available from the union construction; the raw
curve extension predicate `IsMaximalGeodesicSolution` additionally asks for
regularity data on an arbitrary totalized curve and remains a later theorem. -/
theorem GeodesicSolution.domain_subset_of_maximalDomain
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {p : M} {v : TangentSpace I p}
    {S : GeodesicSolution (I := I) g p v}
    (hdom : S.domain = maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v)) :
    ∀ T : GeodesicSolution (I := I) g p v, T.domain ⊆ S.domain := by
  intro T
  rw [hdom]
  exact subset_maximalGeodesicDomain (I := I) (g := g) (p := p) (v := v) T

omit [FiniteDimensional ℝ E] in
/-- The chart velocity of the zero tangent vector is zero.  This is the
initial-data normalization used by the constant-curve regression below. -/
@[simp] theorem chartVelocityAt_zero
    (p : M) :
    chartVelocityAt (I := I) p (0 : TangentSpace I p) = 0 := by
  unfold chartVelocityAt
  rw [TangentBundle.trivializationAt_apply]
  exact map_zero _

/-- Zero initial velocity selects the constant solution locally.  This is the
ODE model regression: it combines the prescribed chart velocity, the constant
curve equation, and local uniqueness rather than merely checking that a
constant curve satisfies the equation. -/
theorem localChartGeodesic_eventuallyEq_const_of_zero_velocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (hp : I.IsInteriorPoint p) {gamma : ℝ → M}
    (hgamma0 : gamma 0 = p)
    (hvel : HasDerivAt (chartReading (I := I) p gamma)
      (chartVelocityAt (I := I) p (0 : TangentSpace I p)) 0)
    (hgamma : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasChartGeodesicEquationAt (I := I) g p gamma s) :
    gamma =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => p) := by
  apply localChartGeodesic_eventuallyEq_of_initial_data (I := I) g p 0 hp
    hgamma0 rfl hvel
  · rw [chartVelocityAt_zero]
    change HasDerivAt (fun _ : ℝ => extChartAt I p p) 0 0
    exact hasDerivAt_const (x := (0 : ℝ)) (c := extChartAt I p p)
  · exact hgamma
  · filter_upwards [] with s
    have hconst : IsGeodesicAt (I := I) g (fun _ : ℝ => p) s :=
      (isGeodesic_const (I := I) g p).2 s
    exact (isGeodesicAt_iff_chartEquation (I := I) g (fun _ : ℝ => p) s).mp hconst |>.2.2

end Coordinates

end Geodesic
end Ch01
end MorganTianLib
