import MorganTianLib.Ch01.Volume
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Chart densities and Euclidean change of variables

This module supplies the local chart measure toolkit for Chapter 1.
For a smooth Riemannian metric it constructs the Gram density of a chart,
proves its smoothness, positivity, square-root determinant formula, and overlap
law, and proves that coordinate nullity is independent of the chosen chart.

The inner-product Gram-density and Jacobian sections use Mathlib's
basis-independent `LinearMap.normDet` directly. The generic chart-transition
and normalized change-of-variables sections use Mathlib's determinant and
absolute-determinant APIs, with C1 manifold charts where tangent derivatives
are used. Their critical-value and area statements are direct specializations of
Mathlib's
`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`,
`MeasureTheory.measurable_image_of_fderivWithin`,
`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`,
and `MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` to
`μHE[finrank ℝ E]`, with the same Hausdorff normalization convention used by
`riemannianVolume`.

The exported norm-determinant formulas are the canonical same-dimensional
Riemannian Jacobian API: coordinate determinants occur only as theorems about
`LinearMap.normDet`, never as a second Jacobian definition.

The pinned Mathlib API does not yet identify the Hausdorff measure of the
Riemannian path metric with this chart density. Accordingly, this module does
not define another global measure and does not assert the unavailable local
chart-density formula. The normalization used by the exported formulas is
the canonical `riemannianVolume` choice recorded in `Volume.lean`.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
the volume discussion on pp. 45--50 (bibliography key `morganTian2007`).
-/

noncomputable section

open Bundle Manifold Matrix
open scoped Bundle ContDiff Manifold MeasureTheory RealInnerProductSpace

namespace MorganTianLib
namespace Ch01

/-! ## Generic chart frame and transition -/

section ChartFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The chart trivialization identifies the model space with the tangent fibre at `p`.
It is a linear equivalence when `p` belongs to the chart source. -/
noncomputable def chartFrameMap (alpha p : M) :
    E →L[ℝ] TangentSpace I p :=
  (trivializationAt E (TangentSpace I) alpha).symmL ℝ p

/-- On a chart overlap, the first chart frame is the second chart frame composed with
Mathlib's tangent coordinate change. -/
theorem chartFrameMap_eq_comp_tangentCoordChange
    (alpha beta : M) {p : M} (hpalpha : p ∈ (chartAt H alpha).source)
    (hpbeta : p ∈ (chartAt H beta).source) :
    chartFrameMap (I := I) alpha p =
      (chartFrameMap (I := I) beta p).comp (tangentCoordChange I alpha beta p) := by
  have hpalpha' : p ∈ (extChartAt I alpha).source := by
    simpa only [extChartAt_source] using hpalpha
  have hpbeta' : p ∈ (extChartAt I beta).source := by
    simpa only [extChartAt_source] using hpbeta
  rw [chartFrameMap, chartFrameMap,
    TangentBundle.symmL_trivializationAt_eq_core hpalpha,
    TangentBundle.symmL_trivializationAt_eq_core hpbeta]
  ext v
  exact (tangentCoordChange_comp (I := I) (w := alpha) (x := beta) (y := p)
    (z := p) (v := v) ⟨⟨hpalpha', hpbeta'⟩, mem_extChartAt_source p⟩).symm

end ChartFrame

/-! ## Chart Gram density -/

section GramDensity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Gram matrix of the chart coordinate frame in the standard orthonormal basis of
the model inner-product space. The empty matrix is retained when `finrank ℝ E = 0`. -/
noncomputable def chartGramMatrix
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha p : M) : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Matrix.gram ℝ (fun i =>
    chartFrameMap (I := I) alpha p (stdOrthonormalBasis ℝ E i))

/-- The basis-independent chart density, defined as the norm determinant of the chart
frame map. This is nonnegative without a chart-source hypothesis. -/
noncomputable def chartDensityAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha p : M) : ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (chartFrameMap (I := I) alpha p).normDet

/-- The square of the chart density is the determinant of its Gram matrix. -/
theorem chartDensityAt_sq
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha p : M) :
    chartDensityAt (I := I) g alpha p ^ 2 =
      (chartGramMatrix (I := I) g alpha p).det := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (chartFrameMap (I := I) alpha p).normDet_sq_eq_det_gram
    (stdOrthonormalBasis ℝ E)

/-- The chart density is exactly the square root of the Gram determinant. -/
theorem chartDensityAt_eq_sqrt_det
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha p : M) :
    chartDensityAt (I := I) g alpha p =
      Real.sqrt (chartGramMatrix (I := I) g alpha p).det := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← chartDensityAt_sq]
  exact (Real.sqrt_sq (by
    exact LinearMap.normDet_nonneg _)).symm

/-- The chart density is strictly positive at every point in the chart source, including
the zero-dimensional case. -/
theorem chartDensityAt_pos
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {p : M} (hp : p ∈ (chartAt H alpha).source) :
    0 < chartDensityAt (I := I) g alpha p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [chartDensityAt]
  let t := trivializationAt E (TangentSpace I) alpha
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  let e := t.continuousLinearEquivAt ℝ p hbase
  have hinj : Function.Injective (chartFrameMap (I := I) alpha p) := by
    rw [chartFrameMap, ← t.symm_continuousLinearEquivAt_eq' hbase]
    exact e.symm.injective
  have hne : (chartFrameMap (I := I) alpha p).normDet ≠ 0 := by
    intro hzero
    exact ((chartFrameMap (I := I) alpha p).normDet_eq_zero_iff_ker_ne_bot.mp hzero)
      (LinearMap.ker_eq_bot.mpr hinj)
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) hne.symm

/-- The Gram determinant is strictly positive at points in the chart source. -/
theorem chartGramMatrix_det_pos
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {p : M} (hp : p ∈ (chartAt H alpha).source) :
    0 < (chartGramMatrix (I := I) g alpha p).det := by
  rw [← chartDensityAt_sq]
  exact sq_pos_of_pos (chartDensityAt_pos (I := I) g alpha hp)

/-- The density overlap law. The transition Jacobian is Mathlib's basis-independent
`LinearMap.normDet`. -/
theorem chartDensityAt_transition
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha beta : M) {p : M} (hpalpha : p ∈ (chartAt H alpha).source)
    (hpbeta : p ∈ (chartAt H beta).source) :
    chartDensityAt (I := I) g alpha p =
    chartDensityAt (I := I) g beta p *
        (tangentCoordChange I alpha beta p).normDet := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [chartDensityAt, chartDensityAt,
    chartFrameMap_eq_comp_tangentCoordChange alpha beta hpalpha hpbeta]
  rw [ContinuousLinearMap.toLinearMap_comp,
    LinearMap.normDet_comp_of_finrank_eq _ _ rfl]

/-- Coordinate form of the density overlap law, obtained from the primary `normDet`
statement by Mathlib's absolute-determinant identity. -/
theorem chartDensityAt_transition_abs_det
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha beta : M) {p : M} (hpalpha : p ∈ (chartAt H alpha).source)
    (hpbeta : p ∈ (chartAt H beta).source) :
    chartDensityAt (I := I) g alpha p =
      chartDensityAt (I := I) g beta p *
        |LinearMap.det (tangentCoordChange I alpha beta p : E →ₗ[ℝ] E)| := by
  rw [chartDensityAt_transition g alpha beta hpalpha hpbeta]
  congr 1
  exact LinearMap.normDet_eq_abs_det _

/-- The determinant form of the Gram-matrix overlap law. It is stated without a
positive-dimension assumption, so the empty determinant remains `1`. -/
theorem chartGramMatrix_det_transition
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha beta : M) {p : M} (hpalpha : p ∈ (chartAt H alpha).source)
    (hpbeta : p ∈ (chartAt H beta).source) :
    (chartGramMatrix (I := I) g alpha p).det =
      (chartGramMatrix (I := I) g beta p).det *
        LinearMap.det (tangentCoordChange I alpha beta p : E →ₗ[ℝ] E) ^ 2 := by
  rw [← chartDensityAt_sq, ← chartDensityAt_sq,
    chartDensityAt_transition g alpha beta hpalpha hpbeta, mul_pow]
  congr 1
  rw [LinearMap.normDet_eq_abs_det
    (tangentCoordChange I alpha beta p).toLinearMap]
  exact sq_abs _

/-- The chart density as a function of model coordinates. Values outside the exact chart
target are irrelevant; all regularity and positivity theorems restrict to that target. -/
noncomputable def chartVolumeDensity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) : ℝ :=
  chartDensityAt (I := I) g alpha ((extChartAt I alpha).symm y)

/-- The coordinate density is the familiar `sqrt (det (g_ij))`, with no normalization
factor omitted. -/
theorem chartVolumeDensity_eq_sqrt_det
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) :
    chartVolumeDensity (I := I) g alpha y =
      Real.sqrt (chartGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y)).det :=
  chartDensityAt_eq_sqrt_det (I := I) g alpha _

/-- The coordinate density is strictly positive on the exact extended-chart target. -/
theorem chartVolumeDensity_pos
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    0 < chartVolumeDensity (I := I) g alpha y := by
  apply chartDensityAt_pos (I := I) (H := H) g alpha
  simpa only [extChartAt_source] using (extChartAt I alpha).map_target hy

/-- In dimension zero the coordinate density is `1`, as required by the empty-product
normalization of `LinearMap.normDet`. -/
@[simp]
theorem chartVolumeDensity_of_subsingleton [Subsingleton E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (y : E) : chartVolumeDensity (I := I) g alpha y = 1 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact LinearMap.normDet_of_subsingleton
    (chartFrameMap (I := I) alpha ((extChartAt I alpha).symm y)).toLinearMap

/-- Coordinate form of the density overlap law on the exact source and target points. -/
theorem chartVolumeDensity_transition
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha beta : M) {y : E} (hy : y ∈ (extChartAt I alpha).target)
    (hbeta : (extChartAt I alpha).symm y ∈ (chartAt H beta).source) :
    chartVolumeDensity (I := I) g alpha y =
      chartVolumeDensity (I := I) g beta
          ((extChartAt I beta) ((extChartAt I alpha).symm y)) *
        |LinearMap.det
          (tangentCoordChange I alpha beta ((extChartAt I alpha).symm y) : E →ₗ[ℝ] E)| := by
  let p := (extChartAt I alpha).symm y
  have hpalpha : p ∈ (chartAt H alpha).source := by
    simpa only [p, extChartAt_source] using (extChartAt I alpha).map_target hy
  have hpbeta' : p ∈ (extChartAt I beta).source := by
    simpa only [extChartAt_source] using hbeta
  rw [chartVolumeDensity,
    chartDensityAt_transition_abs_det g alpha beta hpalpha hbeta]
  simp only [p, chartVolumeDensity, (extChartAt I beta).left_inv hpbeta']

end GramDensity

/-! ## Chart sets and transitions -/

section ChartSets

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The coordinate representative of a manifold set in a chart. The preimage form makes
measurability available without first proving a separate image theorem. -/
def chartPreimage (alpha : M) (s : Set M) : Set E :=
  (extChartAt I alpha).symm ⁻¹' s ∩ (extChartAt I alpha).target

/-- A chart representative lies in the exact extended-chart target. -/
theorem chartPreimage_subset_target (alpha : M) (s : Set M) :
    chartPreimage (I := I) alpha s ⊆ (extChartAt I alpha).target :=
  Set.inter_subset_right

/-- A Borel manifold set has a measurable coordinate representative on a boundaryless
model, where the extended-chart target is open. -/
theorem measurableSet_chartPreimage
    [I.Boundaryless] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M]
    (alpha : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage (I := I) alpha s) := by
  have htgt : MeasurableSet (extChartAt I alpha).target :=
    (isOpen_extChartAt_target alpha).measurableSet
  have hcont : Continuous ((extChartAt I alpha).target.restrict
      (extChartAt I alpha).symm) :=
    (continuousOn_extChartAt_symm alpha).restrict
  have hsub : MeasurableSet
      (((extChartAt I alpha).target.restrict (extChartAt I alpha).symm) ⁻¹' s) :=
    hcont.measurable hs
  have himg := htgt.subtype_image hsub
  convert himg using 1
  ext y
  simp only [chartPreimage, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image,
    Subtype.exists, Set.restrict_apply]
  constructor
  · rintro ⟨hys, hyt⟩
    exact ⟨y, hyt, hys, rfl⟩
  · rintro ⟨z, hzt, hzs, rfl⟩
    exact ⟨hzs, hzt⟩

/-- The coordinate transition from the `alpha` chart to the `beta` chart. -/
def chartTransition (alpha beta : M) : E → E :=
  (extChartAt I beta) ∘ (extChartAt I alpha).symm

/-- If `s` lies in both chart sources, the coordinate transition maps its `alpha`
representative exactly onto its `beta` representative. -/
theorem chartTransition_image_chartPreimage
    (alpha beta : M) {s : Set M}
    (hsalpha : s ⊆ (extChartAt I alpha).source)
    (hsbeta : s ⊆ (extChartAt I beta).source) :
    chartTransition (I := I) alpha beta '' chartPreimage (I := I) alpha s =
      chartPreimage (I := I) beta s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hys, hyt⟩ := hy
    have hleft : (extChartAt I beta).symm (chartTransition (I := I) alpha beta y) =
        (extChartAt I alpha).symm y := by
      exact (extChartAt I beta).left_inv (hsbeta hys)
    refine ⟨?_, (extChartAt I beta).map_source (hsbeta hys)⟩
    show (extChartAt I beta).symm (chartTransition (I := I) alpha beta y) ∈ s
    rw [hleft]
    exact hys
  · intro z hz
    obtain ⟨hzs, hzt⟩ := hz
    let y := (extChartAt I alpha) ((extChartAt I beta).symm z)
    have hyalpha : (extChartAt I beta).symm z ∈ (extChartAt I alpha).source :=
      hsalpha hzs
    have hybeta : (extChartAt I beta).symm z ∈ (extChartAt I beta).source :=
      hsbeta hzs
    refine ⟨y, ⟨?_, (extChartAt I alpha).map_source hyalpha⟩, ?_⟩
    · show (extChartAt I alpha).symm y ∈ s
      change (extChartAt I alpha).symm
        ((extChartAt I alpha) ((extChartAt I beta).symm z)) ∈ s
      rw [(extChartAt I alpha).left_inv hyalpha]
      exact hzs
    · simp only [chartTransition, Function.comp_apply, y,
        (extChartAt I alpha).left_inv hyalpha, (extChartAt I beta).right_inv hzt]

end ChartSets

section ChartTransitionDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The derivative of a chart transition is Mathlib's `tangentCoordChange` on the exact
coordinate representative of a set contained in the overlap. -/
theorem hasFDerivWithinAt_chartTransition
    (alpha beta : M) {s : Set M}
    (hsalpha : s ⊆ (extChartAt I alpha).source)
    (hsbeta : s ⊆ (extChartAt I beta).source)
    {y : E} (hy : y ∈ chartPreimage (I := I) alpha s) :
    HasFDerivWithinAt (chartTransition (I := I) alpha beta)
      (tangentCoordChange I alpha beta ((extChartAt I alpha).symm y))
      (chartPreimage (I := I) alpha s) y := by
  obtain ⟨hys, hyt⟩ := hy
  have hp : (extChartAt I alpha).symm y ∈
      (extChartAt I alpha).source ∩ (extChartAt I beta).source :=
    ⟨hsalpha hys, hsbeta hys⟩
  have hd := hasFDerivWithinAt_tangentCoordChange (I := I) hp
  rw [(extChartAt I alpha).right_inv hyt] at hd
  exact hd.mono ((chartPreimage_subset_target (I := I) alpha s).trans
    (extChartAt_target_subset_range alpha))

/-- A chart transition is differentiable on the coordinate representative of any set in
the overlap. -/
theorem differentiableOn_chartTransition
    (alpha beta : M) {s : Set M}
    (hsalpha : s ⊆ (extChartAt I alpha).source)
    (hsbeta : s ⊆ (extChartAt I beta).source) :
    DifferentiableOn ℝ (chartTransition (I := I) alpha beta)
      (chartPreimage (I := I) alpha s) := fun _ hy ↦
  (hasFDerivWithinAt_chartTransition (I := I) alpha beta hsalpha hsbeta hy).differentiableWithinAt

end ChartTransitionDerivative

section GramDensityRegularity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private noncomputable def chartFrame (alpha : M)
    (i : Fin (Module.finrank ℝ E)) (p : M) : TangentSpace I p :=
  (trivializationAt E (TangentSpace I) alpha).localFrame
    (stdOrthonormalBasis ℝ E).toBasis i p

private def chartGramComponent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  let p := (extChartAt I alpha).symm y
  g.inner p (chartFrame (I := I) alpha i p) (chartFrame (I := I) alpha j p)

private theorem chartFrame_eq_chartFrameMap
    (alpha : M) {p : M} (hp : p ∈ (chartAt H alpha).source)
    (i : Fin (Module.finrank ℝ E)) :
    chartFrame (I := I) alpha i p =
      chartFrameMap (I := I) alpha p (stdOrthonormalBasis ℝ E i) := by
  let t := trivializationAt E (TangentSpace I) alpha
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  rw [chartFrame, t.localFrame_apply_of_mem_baseSet
    (stdOrthonormalBasis ℝ E).toBasis hbase]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    t.linearEquivAt_symm_apply]
  rw [← t.symmL_apply (R := ℝ) hbase]
  rfl

private theorem chartGramComponent_contDiffWithinAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    ContDiffWithinAt ℝ ∞ (chartGramComponent (I := I) g alpha i j)
      (extChartAt I alpha).target y := by
  let phi := extChartAt I alpha
  let p := phi.symm y
  let metricComponent : M → ℝ := fun q =>
    g.inner q (chartFrame (I := I) alpha i q) (chartFrame (I := I) alpha j q)
  have hp : p ∈ (chartAt H alpha).source := by
    simpa only [p, phi, extChartAt_source] using (extChartAt I alpha).map_target hy
  have hbase : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hp
  have hframeI : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (chartFrame (I := I) alpha i)) p :=
    contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := trivializationAt E (TangentSpace I) alpha)
      (b := (stdOrthonormalBasis ℝ E).toBasis) i hbase
  have hframeJ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (chartFrame (I := I) alpha j)) p :=
    contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := trivializationAt E (TangentSpace I) alpha)
      (b := (stdOrthonormalBasis ℝ E).toBasis) j hbase
  have hmetric : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ metricComponent p := by
    have h := g.contMDiff.contMDiffAt.clm_bundle_apply₂ hframeI hframeJ
    simp only [contMDiffAt_totalSpace] at h
    simpa [metricComponent] using h.2
  have hinv : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ phi.symm phi.target y := by
    simpa only [phi] using
      contMDiffWithinAt_extChartAt_symm_target (I := I) (n := ∞) alpha hy
  rw [← contMDiffWithinAt_iff_contDiffWithinAt]
  change ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
    (metricComponent ∘ phi.symm) phi.target y
  exact hmetric.comp_contMDiffWithinAt y hinv

private theorem chartGramMatrix_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y) i j =
      chartGramComponent (I := I) g alpha i j y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let p := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    simpa only [p, extChartAt_source] using (extChartAt I alpha).map_target hy
  change g.inner p
    (chartFrameMap (I := I) alpha p (stdOrthonormalBasis ℝ E i))
    (chartFrameMap (I := I) alpha p (stdOrthonormalBasis ℝ E j)) = _
  rw [← chartFrame_eq_chartFrameMap alpha hp i,
    ← chartFrame_eq_chartFrameMap alpha hp j]
  rfl

private theorem chartGramDet_contDiffWithinAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    ContDiffWithinAt ℝ ∞
      (fun z ↦ (chartGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm z)).det)
      (extChartAt I alpha).target y := by
  simp only [Matrix.det_apply']
  apply ContDiffWithinAt.sum
  intro sigma _
  apply contDiffWithinAt_const.mul
  apply contDiffWithinAt_prod
  intro i _
  exact (chartGramComponent_contDiffWithinAt (I := I) g alpha (sigma i) i hy).congr
    (fun z hz ↦ chartGramMatrix_apply (I := I) g alpha (sigma i) i hz)
    (chartGramMatrix_apply (I := I) g alpha (sigma i) i hy)

/-- The coordinate density is smooth on the exact extended-chart target. The proof expands
the finite determinant and therefore also covers dimension zero. -/
theorem contDiffOn_chartVolumeDensity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
    ContDiffOn ℝ ∞ (chartVolumeDensity (I := I) g alpha)
      (extChartAt I alpha).target := by
  intro y hy
  have hdet := chartGramDet_contDiffWithinAt (I := I) g alpha hy
  have hdet_ne :
      (chartGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y)).det ≠ 0 := by
    rw [← chartDensityAt_sq]
    exact pow_ne_zero 2 (ne_of_gt (chartVolumeDensity_pos (I := I) g alpha hy))
  have heq : chartVolumeDensity (I := I) g alpha = fun z ↦
      Real.sqrt (chartGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm z)).det := by
    funext z
    exact chartDensityAt_eq_sqrt_det (I := I) g alpha _
  rw [heq]
  exact hdet.sqrt hdet_ne

/-- The coordinate density is continuous on the exact extended-chart target. -/
theorem continuousOn_chartVolumeDensity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
    ContinuousOn (chartVolumeDensity (I := I) g alpha)
      (extChartAt I alpha).target :=
  (contDiffOn_chartVolumeDensity (I := I) g alpha).continuousOn

/-- The chart density extended by zero outside the exact chart target. -/
noncomputable def chartVolumeDensityExtension
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) : E → ℝ :=
  by
    classical
    exact Set.piecewise (extChartAt I alpha).target
      (chartVolumeDensity (I := I) g alpha) 0

/-- On a boundaryless model, the zero extension of the chart density is Borel measurable. -/
theorem measurable_chartVolumeDensityExtension
    [I.Boundaryless] [MeasurableSpace E] [BorelSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
    Measurable (chartVolumeDensityExtension (I := I) g alpha) := by
  classical
  simpa only [chartVolumeDensityExtension] using
    (ContinuousOn.measurable_piecewise
    (continuousOn_chartVolumeDensity (I := I) g alpha)
    continuous_zero.continuousOn
    (isOpen_extChartAt_target alpha).measurableSet)

/-- The measurable extension agrees with the chart density on the exact chart target. -/
theorem chartVolumeDensityExtension_eq_on_target
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    chartVolumeDensityExtension (I := I) g alpha y =
      chartVolumeDensity (I := I) g alpha y := by
  classical
  rw [chartVolumeDensityExtension]
  exact Set.piecewise_eq_of_mem _ _ _ hy

/-- On a boundaryless model, the smooth chart density is almost-everywhere measurable for
the restricted, Euclidean-normalized measure `μHE[finrank ℝ E]` on the chart target. -/
theorem aemeasurable_chartVolumeDensity
    [I.Boundaryless] [MeasurableSpace E] [BorelSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha : M) :
    AEMeasurable (chartVolumeDensity (I := I) g alpha)
      ((μHE[Module.finrank ℝ E] : MeasureTheory.Measure E).restrict
        (extChartAt I alpha).target) :=
  (contDiffOn_chartVolumeDensity (I := I) g alpha).continuousOn.aemeasurable
    (isOpen_extChartAt_target alpha).measurableSet

end GramDensityRegularity

/-! ## The canonical norm-determinant Jacobian -/

section NormDetJacobian

variable
  {U V W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

omit [FiniteDimensional ℝ V] in
/-- `LinearMap.normDet` agrees with the absolute coordinate determinant for any
orthonormal bases of equal finite cardinality. -/
theorem normDet_continuousLinearMap_eq_abs_det_toMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : U →L[ℝ] V) (bU : OrthonormalBasis ι ℝ U)
    (bV : OrthonormalBasis ι ℝ V) :
    A.toLinearMap.normDet =
      |(A.toLinearMap.toMatrix bU.toBasis bV.toBasis).det| := by
  simpa only [Real.norm_eq_abs] using
    LinearMap.normDet_eq_norm_det_toMatrix A.toLinearMap bU bV

/-- The same-dimensional composition law in the continuous-linear-map spelling
used by chart derivatives. -/
theorem normDet_continuousLinearMap_comp
    (A : V →L[ℝ] W) (B : U →L[ℝ] V)
    (h : Module.finrank ℝ U = Module.finrank ℝ V) :
    (A.comp B).toLinearMap.normDet =
      A.toLinearMap.normDet * B.toLinearMap.normDet := by
  change (A.toLinearMap.comp B.toLinearMap).normDet = _
  exact LinearMap.normDet_comp_of_finrank_eq B.toLinearMap A.toLinearMap h

omit [FiniteDimensional ℝ V] in
/-- A continuous linear equivalence has a strictly positive canonical Jacobian. -/
theorem normDet_continuousLinearEquiv_pos (A : U ≃L[ℝ] V) :
    0 < A.toLinearMap.normDet := by
  have hne : A.toLinearMap.normDet ≠ 0 :=
    ((LinearMap.normDet_ne_zero_tfae A.toLinearMap).out 0 4).mpr A.injective
  exact lt_of_le_of_ne (LinearMap.normDet_nonneg _) hne.symm

/-- The canonical Jacobians of a continuous linear equivalence and its inverse
are reciprocal, with no choice of bases in the statement. -/
theorem normDet_continuousLinearEquiv_mul_symm
    (A : U ≃L[ℝ] V) :
    A.toLinearMap.normDet * A.symm.toLinearMap.normDet = 1 := by
  calc
    A.toLinearMap.normDet * A.symm.toLinearMap.normDet =
        A.symm.toLinearMap.normDet * A.toLinearMap.normDet := mul_comm _ _
    _ = (A.symm.toLinearMap.comp A.toLinearMap).normDet := by
      rw [LinearMap.normDet_comp_of_finrank_eq A.toLinearMap A.symm.toLinearMap
        A.toLinearEquiv.finrank_eq]
    _ = 1 := by simp

/-- The identity continuous linear map has canonical Jacobian one. -/
@[simp] theorem normDet_continuousLinearMap_id :
    (ContinuousLinearMap.id ℝ U).toLinearMap.normDet = 1 := by
  simp

omit [FiniteDimensional ℝ V] in
/-- Scaling a continuous linear map scales its canonical Jacobian by the
absolute scalar to the source dimension. -/
theorem normDet_continuousLinearMap_smul (c : ℝ) (A : U →L[ℝ] V) :
    (c • A).toLinearMap.normDet =
      |c| ^ Module.finrank ℝ U * A.toLinearMap.normDet := by
  change (c • A.toLinearMap).normDet = _
  simpa only [Real.norm_eq_abs] using LinearMap.normDet_smul A.toLinearMap c

omit [FiniteDimensional ℝ V] in
/-- A map out of a zero-dimensional source has canonical Jacobian one. -/
@[simp] theorem normDet_continuousLinearMap_of_subsingleton [Subsingleton U]
    (A : U →L[ℝ] V) :
    A.toLinearMap.normDet = 1 := by
  exact LinearMap.normDet_of_subsingleton A.toLinearMap

/-- The real scalar case is the one-dimensional regression for the preceding
scaling law. -/
@[simp]
theorem normDet_real_smul_id (c : ℝ) :
    (c • (ContinuousLinearMap.id ℝ ℝ)).toLinearMap.normDet = |c| := by
  simp

end NormDetJacobian

section ChangeOfVariables

open MeasureTheory Set
open scoped ENNReal MeasureTheory

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- An image of a measurable source set is measurable under Mathlib's
within-derivative and injectivity hypotheses. This result is kept separate
from all measure-zero conclusions. -/
theorem measurableSet_image_of_hasFDerivWithinAt
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) :
    MeasurableSet (f '' s) :=
  MeasureTheory.measurable_image_of_fderivWithin hs hf' hf

/-- A differentiable map sends a `μHE[finrank ℝ E]`-null set to a null set. Neither
source measurability nor injectivity is required by Mathlib's theorem. -/
theorem euclideanHausdorffMeasure_image_eq_zero
    {s : Set E} {f : E → E} (hf : DifferentiableOn ℝ f s)
    (hs : μHE[Module.finrank ℝ E] s = 0) :
    μHE[Module.finrank ℝ E] (f '' s) = 0 :=
  MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
    μHE[Module.finrank ℝ E] hf hs

/-- Equidimensional Sard wrapper: the image of a set on which the supplied derivative has
zero determinant is `μHE[finrank ℝ E]`-null. No measurability assumption is hidden. -/
theorem criticalValues_euclideanHausdorffMeasure_zero
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, (f' x).det = 0) :
    μHE[Module.finrank ℝ E] (f '' s) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    μHE[Module.finrank ℝ E] hf'
  intro x hx
  exact hcrit x hx

/-- Injective change of variables for nonnegative integrals against the pinned
Euclidean-normalized measure. The hypotheses are exactly those consumed by Mathlib's API. -/
theorem euclideanHausdorffMeasure_lintegral_image_eq_lintegral_abs_det_mul
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) (q : E → ℝ≥0∞) :
    ∫⁻ y in f '' s, q y ∂μHE[Module.finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * q (f x)
        ∂μHE[Module.finrank ℝ E] := by
  simpa only using
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      μHE[Module.finrank ℝ E] hs hf' hf q

/-- The corresponding area formula for the measure of an injective image. -/
theorem euclideanHausdorffMeasure_image_eq_lintegral_abs_det
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det|
        ∂μHE[Module.finrank ℝ E] := by
  symm
  simpa only using
    MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
      μHE[Module.finrank ℝ E] hs hf' hf

/-- Coordinate nullity is independent of the chart on an overlap. This is an equivalence
of measure-zero statements only; use `measurableSet_chartPreimage` separately for measurability. -/
theorem chartPreimage_euclideanHausdorffMeasure_zero_iff
    (alpha beta : M) {s : Set M}
    (hsalpha : s ⊆ (extChartAt I alpha).source)
    (hsbeta : s ⊆ (extChartAt I beta).source) :
    μHE[Module.finrank ℝ E] (chartPreimage (I := I) alpha s) = 0 ↔
      μHE[Module.finrank ℝ E] (chartPreimage (I := I) beta s) = 0 := by
  constructor
  · intro halpha
    rw [← chartTransition_image_chartPreimage (I := I) alpha beta hsalpha hsbeta]
    exact euclideanHausdorffMeasure_image_eq_zero
      (differentiableOn_chartTransition (I := I) alpha beta hsalpha hsbeta) halpha
  · intro hbeta
    rw [← chartTransition_image_chartPreimage (I := I) beta alpha hsbeta hsalpha]
    exact euclideanHausdorffMeasure_image_eq_zero
      (differentiableOn_chartTransition (I := I) beta alpha hsbeta hsalpha) hbeta

end ChangeOfVariables

/-! ## Norm-determinant change of variables -/

section NormDetChangeOfVariables

open MeasureTheory Set
open scoped ENNReal MeasureTheory

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Equidimensional Sard in the canonical Jacobian language. The conclusion is
measure-zero, while image measurability remains the separate theorem
`measurableSet_image_of_hasFDerivWithinAt`. -/
theorem criticalValues_euclideanHausdorffMeasure_zero_of_normDet
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hcrit : ∀ x ∈ s, (f' x).toLinearMap.normDet = 0) :
    μHE[Module.finrank ℝ E] (f '' s) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    μHE[Module.finrank ℝ E] hf'
  intro x hx
  have hdet : |(f' x).det| = 0 := by
    simpa only [LinearMap.normDet_eq_abs_det] using hcrit x hx
  exact abs_eq_zero.mp hdet

/-- Injective change of variables for nonnegative integrals, with the
basis-independent `LinearMap.normDet` as Jacobian. The hypotheses are exactly
those consumed by Mathlib's pinned API. -/
theorem lintegral_image_eq_lintegral_normDet_mul
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) (q : E → ℝ≥0∞) :
    ∫⁻ y in f '' s, q y ∂μHE[Module.finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet) * q (f x)
        ∂μHE[Module.finrank ℝ E] := by
  simpa only [LinearMap.normDet_eq_abs_det] using
    MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
      μHE[Module.finrank ℝ E] hs hf' hf q

/-- The corresponding injective area formula for the pinned
Euclidean-normalized Hausdorff measure. -/
theorem euclideanHausdorffMeasure_image_eq_lintegral_normDet
    {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : Set.InjOn f s) :
    μHE[Module.finrank ℝ E] (f '' s) =
      ∫⁻ x in s, ENNReal.ofReal ((f' x).toLinearMap.normDet)
        ∂μHE[Module.finrank ℝ E] := by
  symm
  simpa only [LinearMap.normDet_eq_abs_det] using
    MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image
      μHE[Module.finrank ℝ E] hs hf' hf

end NormDetChangeOfVariables

/-! ## Chart transition in the canonical Jacobian language -/

section ChartNormDetTransition

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-density overlap law with Mathlib's canonical norm determinant.
The absolute-determinant version is a corollary via
`LinearMap.normDet_eq_abs_det`. -/
theorem chartVolumeDensity_transition_normDet
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (alpha beta : M) {y : E} (hy : y ∈ (extChartAt I alpha).target)
    (hbeta : (extChartAt I alpha).symm y ∈ (chartAt H beta).source) :
    chartVolumeDensity (I := I) g alpha y =
      chartVolumeDensity (I := I) g beta
          ((extChartAt I beta) ((extChartAt I alpha).symm y)) *
        (tangentCoordChange I alpha beta ((extChartAt I alpha).symm y)).normDet := by
  simpa only [LinearMap.normDet_eq_abs_det] using
    chartVolumeDensity_transition (I := I) g alpha beta hy hbeta

end ChartNormDetTransition

end Ch01
end MorganTianLib
