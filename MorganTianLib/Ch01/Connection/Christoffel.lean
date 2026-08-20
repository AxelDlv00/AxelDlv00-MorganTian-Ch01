import MorganTianLib.Ch01.Connection
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Christoffel coordinates for the Levi--Civita connection

This module identifies the chart coefficients of
`Connection.leviCivitaConnection g` with Morgan--Tian equation (1.1),

`Gamma^k_ij = (1 / 2) * g^{kl} * (partial_i g_lj + partial_j g_il - partial_l g_ij)`.

The coordinate frame and its Gram matrix are proof data only.  The exported
theorem keeps the explicit smooth metric and the canonical bundled connection
visible, so it does not introduce a second affine connection or metric.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, equation (1.1),
printed p. 36.  Cross-checks: do Carmo (1992), Chapter 2, pp. 44--51, and Lee
(2018), Chapter 5.
-/

noncomputable section

open Bundle FiberBundle Filter Function Manifold Matrix Set VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace MorganTianLib
namespace Ch01
namespace Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private noncomputable def chartFrame [IsManifold I ∞ M] (alpha : M)
    (i : Fin (Module.finrank ℝ E)) (q : M) : TangentSpace I q :=
  (trivializationAt E (TangentSpace I) alpha).localFrame (Module.finBasis ℝ E) i q

private def chartMetricComponent [IsManifold I ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (a b : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  let q := (extChartAt I alpha).symm y
  g.inner q (chartFrame (I := I) alpha a q) (chartFrame (I := I) alpha b q)

private lemma chartMetricComponent_symm [IsManifold I ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (a b : Fin (Module.finrank ℝ E)) :
    chartMetricComponent (I := I) g alpha a b = chartMetricComponent (I := I) g alpha b a := by
  funext y
  exact g.symm _ _ _

private lemma chartFrame_mdifferentiableAt [IsManifold I ∞ M]
    (alpha : M) (i : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (chartFrame (I := I) alpha i)) p := by
  exact (contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
    (e := trivializationAt E (TangentSpace I) alpha) (b := Module.finBasis ℝ E) i
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hp)).mdifferentiableAt (by simp)

private lemma mfderiv_extChartAt_chartFrame [IsManifold I ∞ M]
    (alpha : M) (i : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I alpha) p
        (chartFrame (I := I) alpha i p) =
      (Module.finBasis ℝ E) i := by
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hp]
  change t.continuousLinearMapAt ℝ p (t.localFrame b i p) = b i
  rw [t.localFrame_apply_of_mem_baseSet b hbase]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply, t.linearEquivAt_symm_apply]
  rw [← t.symmL_apply (R := ℝ) hbase]
  exact t.continuousLinearMapAt_symmL hbase (b i)

omit [FiniteDimensional ℝ E] in
private lemma mlieBracket_const_const (c d : E) :
    VectorField.mlieBracket 𝓘(ℝ, E)
      (fun _ : E => c) (fun _ : E => d) = 0 := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  funext x
  show fderiv ℝ (fun _ : E => d) x ((fun _ : E => c) x) -
      fderiv ℝ (fun _ : E => c) x ((fun _ : E => d) x) = 0
  rw [fderiv_fun_const, fderiv_fun_const]
  simp

private lemma chartFrame_eventuallyEq_mpullback [IsManifold I ∞ M]
    (alpha : M) (i : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    chartFrame (I := I) alpha i =ᶠ[nhds p]
      VectorField.mpullback I 𝓘(ℝ, E) (extChartAt I alpha)
        (fun _ => (Module.finBasis ℝ E) i) := by
  have hopen : IsOpen (chartAt H alpha).source := (chartAt H alpha).open_source
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hqsrc : q ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source]
  rw [VectorField.mpullback_apply]
  exact (((isInvertible_mfderiv_extChartAt hqsrc).inverse_apply_eq).mpr
    (mfderiv_extChartAt_chartFrame (I := I) alpha i hq).symm).symm

private lemma mlieBracket_chartFrame_eq_zero [IsManifold I ∞ M]
    (alpha : M) (a b : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    VectorField.mlieBracket I (chartFrame (I := I) alpha a)
      (chartFrame (I := I) alpha b) p = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [Filter.EventuallyEq.mlieBracket_vectorField_eq
      (chartFrame_eventuallyEq_mpullback (I := I) alpha a hp)
      (chartFrame_eventuallyEq_mpullback (I := I) alpha b hp)]
  have hsrc_nhds : (chartAt H alpha).source ∈ nhds p :=
    (chartAt H alpha).open_source.mem_nhds hp
  have hphi : ContMDiffAt I 𝓘(ℝ, E) ∞
      (extChartAt I alpha) p :=
    (contMDiffOn_extChartAt (I := I) (x := alpha) (n := ∞)).contMDiffAt hsrc_nhds
  have hV : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) a) :
        TangentBundle 𝓘(ℝ, E) E))
      (extChartAt I alpha p) := by
    apply (show ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) a) :
        TangentBundle 𝓘(ℝ, E) E)) (extChartAt I alpha p) by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩).mdifferentiableAt
    simp
  have hW : MDifferentiableAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) b) :
        TangentBundle 𝓘(ℝ, E) E))
      (extChartAt I alpha p) := by
    apply (show ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (TotalSpace.mk' E x ((Module.finBasis ℝ E) b) :
        TangentBundle 𝓘(ℝ, E) E)) (extChartAt I alpha p) by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩).mdifferentiableAt
    simp
  have hn : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  rw [← VectorField.mpullback_mlieBracket hV hW hphi hn]
  rw [mlieBracket_const_const, VectorField.mpullback_zero, Pi.zero_apply]

private lemma fderiv_chartMetricComponent_eq_mvfderiv [IsManifold I ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (a b r : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartMetricComponent (I := I) g alpha a b) (extChartAt I alpha p)
        ((Module.finBasis ℝ E) r) =
      d% (fun q => g.inner q (chartFrame (I := I) alpha a q)
        (chartFrame (I := I) alpha b q)) p (chartFrame (I := I) alpha r p) := by
  let phi := extChartAt I alpha
  let metricComponent : M → ℝ := fun q =>
    g.inner q (chartFrame (I := I) alpha a q) (chartFrame (I := I) alpha b q)
  have hsource : p ∈ phi.source := by
    simpa only [phi, extChartAt_source] using hp
  have hy : phi p ∈ phi.target := phi.map_source hsource
  have hyInterior : phi p ∈ interior phi.target := by
    exact (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas H alpha) hp).mp hinterior
  have htarget : phi.target ∈ nhds (phi p) :=
    mem_interior_iff_mem_nhds.mp hyInterior
  have hinv : MDifferentiableAt 𝓘(ℝ, E) I phi.symm (phi p) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := I) (n := ∞) alpha hy).contMDiffAt
      htarget).mdifferentiableAt (by simp)
  have hbase : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hp
  have hframeA : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (chartFrame (I := I) alpha a)) p :=
    contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := trivializationAt E (TangentSpace I) alpha) (b := Module.finBasis ℝ E) a hbase
  have hframeB : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (chartFrame (I := I) alpha b)) p :=
    contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := trivializationAt E (TangentSpace I) alpha) (b := Module.finBasis ℝ E) b hbase
  have hmetric : MDifferentiableAt I 𝓘(ℝ, ℝ) metricComponent p := by
    have hmetricSmooth : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ metricComponent p := by
      have h := g.contMDiff.contMDiffAt.clm_bundle_apply₂ hframeA hframeB
      simp only [contMDiffAt_totalSpace] at h
      simpa [metricComponent] using h.2
    exact hmetricSmooth.mdifferentiableAt (by simp)
  have hleft : phi.symm (phi p) = p := phi.left_inv hsource
  have hmetricAtInv : MDifferentiableAt I 𝓘(ℝ, ℝ) metricComponent (phi.symm (phi p)) := by
    simpa only [hleft] using hmetric
  have hcoord : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (chartMetricComponent (I := I) g alpha a b) (phi p) := by
    change MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (metricComponent ∘ phi.symm) (phi p)
    exact hmetricAtInv.comp (phi p) hinv
  have heq : metricComponent =ᶠ[nhds p]
      chartMetricComponent (I := I) g alpha a b ∘ phi := by
    filter_upwards [(chartAt H alpha).open_source.mem_nhds hp] with q hq
    have hqsource : q ∈ phi.source := by
      simpa only [phi, extChartAt_source] using hq
    simp only [metricComponent, chartMetricComponent, Function.comp_apply, phi]
    rw [(extChartAt I alpha).left_inv hqsource]
  symm
  change (d% metricComponent p) (chartFrame (I := I) alpha r p) = _
  simp only [mvfderiv]
  rw [heq.mfderiv_eq, mfderiv_comp p hcoord (mdifferentiableAt_extChartAt hp)]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (chartMetricComponent (I := I) g alpha a b) (phi p)
        (mfderiv I 𝓘(ℝ, E) phi p (chartFrame (I := I) alpha r p)) = _
  rw [mfderiv_extChartAt_chartFrame (I := I) alpha r hp, mfderiv_eq_fderiv]
  rfl

private lemma leviCivita_inner_chartFrame_eq [IsManifold I ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j l : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (leviCivitaConnection g (chartFrame (I := I) alpha j) p
        (chartFrame (I := I) alpha i p)) (chartFrame (I := I) alpha l p) =
      (fderiv ℝ (chartMetricComponent (I := I) g alpha l j) (extChartAt I alpha p)
          ((Module.finBasis ℝ E) i) +
        fderiv ℝ (chartMetricComponent (I := I) g alpha i l) (extChartAt I alpha p)
          ((Module.finBasis ℝ E) j) -
        fderiv ℝ (chartMetricComponent (I := I) g alpha i j) (extChartAt I alpha p)
          ((Module.finBasis ℝ E) l)) / 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfield (a : Fin (Module.finrank ℝ E)) :
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (chartFrame (I := I) alpha a)) p :=
    chartFrame_mdifferentiableAt (I := I) alpha a hp
  rw [leviCivitaConnection_koszul g (hfield i) (hfield j) (hfield l)]
  rw [mlieBracket_chartFrame_eq_zero (I := I) alpha j l hp,
    mlieBracket_chartFrame_eq_zero (I := I) alpha l i hp,
    mlieBracket_chartFrame_eq_zero (I := I) alpha i j hp]
  simp only [inner_zero_right, add_zero, sub_zero]
  change
    ((d% (fun q => g.inner q (chartFrame (I := I) alpha j q)
          (chartFrame (I := I) alpha l q)) p) (chartFrame (I := I) alpha i p) +
        (d% (fun q => g.inner q (chartFrame (I := I) alpha l q)
          (chartFrame (I := I) alpha i q)) p) (chartFrame (I := I) alpha j p) -
        (d% (fun q => g.inner q (chartFrame (I := I) alpha i q)
          (chartFrame (I := I) alpha j q)) p) (chartFrame (I := I) alpha l p)) / 2 = _
  rw [← fderiv_chartMetricComponent_eq_mvfderiv (I := I) g hp hinterior j l i,
    ← fderiv_chartMetricComponent_eq_mvfderiv (I := I) g hp hinterior l i j,
    ← fderiv_chartMetricComponent_eq_mvfderiv (I := I) g hp hinterior i j l,
    chartMetricComponent_symm (I := I) g alpha j l,
    chartMetricComponent_symm (I := I) g alpha l i]

/-- The chart-coordinate Christoffel formula for the canonical bundled
Levi--Civita connection (Morgan--Tian equation (1.1)).

At an interior point `p` of the source of the chart centered at `alpha`, the
left side is the `k`-th chart coefficient of `nabla_(partial_i) partial_j`.
The matrix on the right is the inverse Gram matrix `g^{kl}`, and every
derivative is the ordinary Frechet derivative of the pulled-back metric
component in the indicated chart-basis direction. -/
theorem christoffel_formula [IsManifold I ∞ M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j k : Fin (Module.finrank ℝ E)) :
    let t := trivializationAt E (TangentSpace I) alpha
    let b := Module.finBasis ℝ E
    let e := t.localFrame b
    let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun a b => g.inner p (e a p) (e b p)
    let gij (a b : Fin (Module.finrank ℝ E)) (y : E) :=
      let q := (extChartAt I alpha).symm y
      g.inner q (e a q) (e b q)
    (t.basisAt b (by
      change p ∈ (chartAt H alpha).source
      exact hp)).repr
        (leviCivitaConnection g (e j) p (e i p)) k =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        G⁻¹ k l *
          (fderiv ℝ (gij l j) (extChartAt I alpha p) (b i) +
            fderiv ℝ (gij i l) (extChartAt I alpha p) (b j) -
            fderiv ℝ (gij i j) (extChartAt I alpha p) (b l)) := by
  classical
  dsimp only
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  let e := t.localFrame b
  let bp := t.basisAt b hbase
  let v := leviCivitaConnection g (e j) p (e i p)
  let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun a b => g.inner p (e a p) (e b p)
  let D : Fin (Module.finrank ℝ E) → ℝ := fun l =>
    fderiv ℝ (chartMetricComponent (I := I) g alpha l j) (extChartAt I alpha p) (b i) +
      fderiv ℝ (chartMetricComponent (I := I) g alpha i l) (extChartAt I alpha p) (b j) -
      fderiv ℝ (chartMetricComponent (I := I) g alpha i j) (extChartAt I alpha p) (b l)
  change bp.repr v k = (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * D l
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have he (a : Fin (Module.finrank ℝ E)) : e a p = bp a := by
    exact t.localFrame_apply_of_mem_baseSet b hbase
  have hfirst (l : Fin (Module.finrank ℝ E)) :
      inner ℝ v (e l p) = D l / 2 := by
    change
      inner ℝ (leviCivitaConnection g (chartFrame (I := I) alpha j) p
          (chartFrame (I := I) alpha i p)) (chartFrame (I := I) alpha l p) =
        (fderiv ℝ (chartMetricComponent (I := I) g alpha l j)
              (extChartAt I alpha p) (Module.finBasis ℝ E i) +
            fderiv ℝ (chartMetricComponent (I := I) g alpha i l)
              (extChartAt I alpha p) (Module.finBasis ℝ E j) -
            fderiv ℝ (chartMetricComponent (I := I) g alpha i j)
              (extChartAt I alpha p) (Module.finBasis ℝ E l)) / 2
    exact leviCivita_inner_chartFrame_eq (I := I) g hp hinterior i j l
  let c : Fin (Module.finrank ℝ E) → ℝ := bp.repr v
  have hsystem : G.mulVec c = fun l => D l / 2 := by
    funext l
    change (∑ a, G l a * c a) = D l / 2
    calc
      ∑ a, G l a * c a =
          ∑ a, c a * inner ℝ (bp a) (bp l) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← he a, ← he l]
        change g.inner p (e l p) (e a p) * c a =
          c a * g.inner p (e a p) (e l p)
        rw [g.symm]
        ring
      _ = inner ℝ (∑ a, c a • bp a) (bp l) := by
        simp only [sum_inner, inner_smul_left, RCLike.conj_to_real]
      _ = inner ℝ v (bp l) := by
        simp only [c]
        rw [bp.sum_repr]
      _ = inner ℝ v (e l p) := by rw [he l]
      _ = D l / 2 := hfirst l
  have hG : G = Matrix.gram ℝ (fun a => bp a) := by
    ext a d
    simp only [G, Matrix.gram_apply]
    rw [← he a, ← he d]
    rfl
  have hdet : G.det ≠ 0 := by
    rw [hG, Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact bp.linearIndependent
  letI : Invertible G := Matrix.invertibleOfIsUnitDet G (isUnit_iff_ne_zero.mpr hdet)
  have hinv : G⁻¹.mulVec (fun l => D l / 2) = c :=
    Matrix.inv_mulVec_eq_vec hsystem.symm
  have hk := congrFun hinv k
  change c k = _
  rw [← hk]
  change (∑ l, G⁻¹ k l * (D l / 2)) = (1 / 2 : ℝ) * ∑ l, G⁻¹ k l * D l
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end Connection
end Ch01
end MorganTianLib
