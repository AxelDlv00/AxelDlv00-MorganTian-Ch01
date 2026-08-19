import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Chapter 1 Riemannian metric coherence

This module installs an explicit smooth tangent metric through Mathlib's scoped
`Bundle.RiemannianBundle` interface and records the resulting coherence facts.
There is no project-owned metric type: public statements use
`Bundle.ContMDiffRiemannianMetric` and `Manifold.riemannianEDist` directly.

The extended Riemannian distance induces the original manifold topology.  This
module also records the source-facing notion of a smooth path on `[0, 1]` and
its finite piecewise-smooth closure, whose length is the sum of Mathlib
`pathELength`s.  On a preconnected manifold the distance is finite: the
points reachable by finite piecewise-smooth paths form a nonempty clopen set,
using smooth inverse-chart segments locally.  Only the separating
extended-metric constructor needs `T3Space`; only the finiteness and
real-distance results need `PreconnectedSpace`.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
Definition 1.1 and the metric-ball discussion on p. 35.
-/

open Bundle Filter Manifold Set
open scoped Bundle ContDiff ENNReal Topology

namespace MorganTianLib
namespace Ch01

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Scoped bundle installation -/

/-- Installing `g.toRiemannianMetric` gives the intended smooth Riemannian
bundle predicate at the same regularity. -/
theorem contMDiffRiemannianBundle
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  infer_instance

/-- Installing `g.toRiemannianMetric` gives the continuous Riemannian bundle
predicate used by the path-length and distance constructions. -/
theorem continuousRiemannianBundle
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩

/-- The fibre inner product installed through `Bundle.RiemannianBundle` is
definitionally the bilinear form of the explicit metric. -/
theorem inner_eq_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ v w = g.inner x v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rfl

/-- The fibre norm is the norm induced by the explicit metric inner product. -/
theorem norm_eq_sqrt_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (v : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖v‖ = Real.sqrt (g.inner x v v) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner]
  rfl

/-- The norm topology installed on a tangent fibre is the fibre's pre-existing
topology.  This is the topology-preserving branch of Mathlib's bundled metric
construction, stated explicitly to rule out a second tangent-fibre topology. -/
theorem tangent_topology_eq_norm_topology
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (inferInstance : TopologicalSpace (TangentSpace I x)) =
      (inferInstance :
        NormedAddCommGroup (TangentSpace I x)).toMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rfl

/-! ## Smooth and piecewise-smooth paths -/

/-- A source-facing smooth path from `x` to `y`.

This structure models the smooth paths used to define distance in the paragraph
following Morgan--Tian, Definition 1.1, p. 35.  The Lean encoding uses a map on
all of `ℝ`, fixes its endpoints at `0` and `1`, and requires `CMDiff` regularity
on `[0, 1]`.  Values outside that interval do not enter either the regularity
condition or the length. -/
structure SmoothPath (I : ModelWithCorners ℝ E H) (x y : M) where
  /-- The underlying map, defined on all of `ℝ` so it can be passed directly to
  `Manifold.pathELength`. -/
  toFun : ℝ → M
  /-- The path starts at `x`. -/
  source_eq : toFun 0 = x
  /-- The path ends at `y`. -/
  target_eq : toFun 1 = y
  /-- The path is smooth on its parameter interval. -/
  smoothOn : CMDiff[Set.Icc 0 1] ∞ toFun

namespace SmoothPath

omit [IsManifold I ∞ M] in
instance {x y : M} : FunLike (SmoothPath I x y) ℝ M where
  coe p := p.toFun
  coe_injective p q h := by
    cases p
    cases q
    congr

omit [IsManifold I ∞ M] in
@[ext]
protected theorem ext {x y : M} {p q : SmoothPath I x y}
    (h : (p : ℝ → M) = q) : p = q :=
  DFunLike.coe_injective h

variable {x y : M} (p : SmoothPath I x y)

omit [IsManifold I ∞ M] in
/-- A smooth path takes the prescribed value at the source endpoint. -/
@[simp]
protected theorem source : p 0 = x :=
  p.source_eq

omit [IsManifold I ∞ M] in
/-- A smooth path takes the prescribed value at the target endpoint. -/
@[simp]
protected theorem target : p 1 = y :=
  p.target_eq

/-- The extended length of a smooth path, measured by Mathlib's canonical
Riemannian path-length functional on `[0, 1]`. -/
noncomputable def eLength [∀ x : M, ENorm (TangentSpace I x)] {x y : M}
    (p : SmoothPath I x y) : ℝ≥0∞ :=
  Manifold.pathELength I p 0 1

/-- The constant smooth path. -/
def refl (x : M) : SmoothPath I x x where
  toFun := fun _ ↦ x
  source_eq := rfl
  target_eq := rfl
  smoothOn := contMDiffOn_const

omit [IsManifold I ∞ M] in
/-- A constant smooth path has zero length. -/
@[simp]
theorem eLength_refl
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] (x : M) :
    (refl (I := I) x).eLength = 0 := by
  change Manifold.pathELength I (fun _ : ℝ ↦ x) 0 1 = 0
  simp [Manifold.pathELength_eq_lintegral_mfderiv_Icc]

/-- Reverse the orientation of a smooth path. -/
def reverse {x y : M} (p : SmoothPath I x y) : SmoothPath I y x where
  toFun := p ∘ fun t : ℝ ↦ 1 - t
  source_eq := by simp
  target_eq := by simp
  smoothOn := by
    apply p.smoothOn.comp
    · rw [contMDiffOn_iff_contDiffOn]
      fun_prop
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]

omit [IsManifold I ∞ M] in
/-- Reversing a smooth path preserves its Riemannian length. -/
@[simp]
theorem eLength_reverse [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y : M} (p : SmoothPath I x y) :
    p.reverse.eLength = p.eLength := by
  change Manifold.pathELength I (p ∘ fun t : ℝ ↦ 1 - t) 0 1 =
    Manifold.pathELength I p 0 1
  rw [Manifold.pathELength_comp_of_antitoneOn zero_le_one]
  · norm_num
  · intro a _ b _ hab
    dsimp
    linarith
  · fun_prop
  · simpa only [sub_self, sub_zero, show (p : ℝ → M) = p.toFun from rfl] using
      p.smoothOn.mdifferentiableOn (by simp)

end SmoothPath

/-- A finite piecewise-smooth path, represented as a typed list of smooth
segments.  Every segment uses `[0, 1]`; the endpoint indices in `cons` require
successive segments to meet exactly. -/
inductive PiecewiseSmoothPath (I : ModelWithCorners ℝ E H) : M → M → Type _
  /-- The empty path at a point. -/
  | nil (x : M) : PiecewiseSmoothPath I x x
  /-- Prepend one smooth segment to a finite piecewise-smooth path. -/
  | cons {x y z : M} (head : SmoothPath I x y) (tail : PiecewiseSmoothPath I y z) :
      PiecewiseSmoothPath I x z

namespace SmoothPath

/-- Regard one smooth path as a one-segment piecewise-smooth path. -/
def toPiecewise {x y : M} (p : SmoothPath I x y) : PiecewiseSmoothPath I x y :=
  .cons p (.nil _)

end SmoothPath

namespace PiecewiseSmoothPath

/-- Concatenate two finite piecewise-smooth paths. -/
def append {x y z : M} :
    PiecewiseSmoothPath I x y → PiecewiseSmoothPath I y z → PiecewiseSmoothPath I x z
  | .nil _, q => q
  | .cons head tail, q => .cons head (tail.append q)

/-- Reverse the first path into an accumulator with the same source. -/
def reverseAux {x y z : M} :
    PiecewiseSmoothPath I x y → PiecewiseSmoothPath I x z → PiecewiseSmoothPath I y z
  | .nil _, q => q
  | .cons head tail, q => tail.reverseAux (.cons head.reverse q)

/-- Reverse every segment and their order. -/
def reverse {x y : M} (p : PiecewiseSmoothPath I x y) : PiecewiseSmoothPath I y x :=
  p.reverseAux (.nil _)

/-- The length of a finite piecewise-smooth path is the sum of the canonical
`Manifold.pathELength` of its segments. -/
noncomputable def eLength [∀ x : M, ENorm (TangentSpace I x)] {x y : M} :
    PiecewiseSmoothPath I x y → ℝ≥0∞
  | .nil _ => 0
  | .cons head tail => head.eLength + tail.eLength

omit [IsManifold I ∞ M] in
/-- Length is additive under concatenation of finite piecewise-smooth paths. -/
@[simp]
theorem eLength_append [∀ x : M, ENorm (TangentSpace I x)]
    {x y z : M} (p : PiecewiseSmoothPath I x y) (q : PiecewiseSmoothPath I y z) :
    (p.append q).eLength = p.eLength + q.eLength := by
  induction p with
  | nil => simp [append, eLength]
  | cons head tail ih => simp [append, eLength, ih, add_assoc]

omit [IsManifold I ∞ M] in
/-- A smooth path and its one-segment piecewise form have the same length. -/
@[simp]
theorem eLength_toPiecewise [∀ x : M, ENorm (TangentSpace I x)]
    {x y : M} (p : SmoothPath I x y) :
    p.toPiecewise.eLength = p.eLength := by
  simp [SmoothPath.toPiecewise, eLength]

omit [IsManifold I ∞ M] in
/-- Reversing into an accumulator adds the lengths of the input paths. -/
@[simp]
theorem eLength_reverseAux
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y z : M} (p : PiecewiseSmoothPath I x y) (q : PiecewiseSmoothPath I x z) :
    (p.reverseAux q).eLength = p.eLength + q.eLength := by
  induction p with
  | nil => simp [reverseAux, eLength]
  | cons head tail ih =>
      simp [reverseAux, eLength, ih, add_comm, add_left_comm]

omit [IsManifold I ∞ M] in
/-- Reversing all segments preserves the total piecewise-smooth length. -/
@[simp]
theorem eLength_reverse
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y : M} (p : PiecewiseSmoothPath I x y) :
    p.reverse.eLength = p.eLength := by
  simp [reverse, eLength]

omit [IsManifold I ∞ M] in
/-- Mathlib's `C^1` Riemannian distance is at most the length of every finite
piecewise-smooth path with the same endpoints. -/
theorem riemannianEDist_le_eLength
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y : M} (p : PiecewiseSmoothPath I x y) :
    Manifold.riemannianEDist I x y ≤ p.eLength := by
  induction p with
  | nil x => simp [eLength, Manifold.riemannianEDist_self]
  | @cons x y z head tail ih =>
      exact Manifold.riemannianEDist_triangle.trans
        (add_le_add
          (Manifold.riemannianEDist_le_pathELength
            (head.smoothOn.of_le (by simp)) head.source head.target zero_le_one)
          ih)

end PiecewiseSmoothPath

/-! ### Source-facing length infima -/

/-- The infimum of lengths of smooth paths from `x` to `y`.

This is an auxiliary value used only to state correspondence with
`Manifold.riemannianEDist`; it does not install another ambient distance or
metric structure. -/
noncomputable def smoothPathEDist
    (I : ModelWithCorners ℝ E H) [∀ x : M, ENorm (TangentSpace I x)] (x y : M) : ℝ≥0∞ :=
  ⨅ p : SmoothPath I x y, p.eLength

/-- The infimum of the summed lengths of finite piecewise-smooth paths from
`x` to `y`.  The empty infimum is `∞`. -/
noncomputable def piecewiseSmoothPathEDist
    (I : ModelWithCorners ℝ E H) [∀ x : M, ENorm (TangentSpace I x)] (x y : M) : ℝ≥0∞ :=
  ⨅ p : PiecewiseSmoothPath I x y, p.eLength

omit [IsManifold I ∞ M] in
/-- Allowing finitely many smooth pieces can only decrease the smooth-path
length infimum. -/
theorem piecewiseSmoothPathEDist_le_smoothPathEDist
    [∀ x : M, ENorm (TangentSpace I x)] (x y : M) :
    piecewiseSmoothPathEDist I x y ≤ smoothPathEDist I x y := by
  rw [smoothPathEDist]
  refine le_iInf fun p ↦ ?_
  exact iInf_le_of_le p.toPiecewise (PiecewiseSmoothPath.eLength_toPiecewise p).le

omit [IsManifold I ∞ M] in
/-- The canonical Mathlib `C^1` distance is bounded above by the
piecewise-smooth path-length infimum. -/
theorem riemannianEDist_le_piecewiseSmoothPathEDist
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)] (x y : M) :
    Manifold.riemannianEDist I x y ≤ piecewiseSmoothPathEDist I x y := by
  rw [piecewiseSmoothPathEDist]
  exact le_iInf fun p ↦ p.riemannianEDist_le_eLength

omit [IsManifold I ∞ M] in
/-- In particular, the canonical Mathlib `C^1` distance is bounded above by
the infimum over paths smooth on `[0, 1]`. -/
theorem riemannianEDist_le_smoothPathEDist
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)] (x y : M) :
    Manifold.riemannianEDist I x y ≤ smoothPathEDist I x y :=
  (riemannianEDist_le_piecewiseSmoothPathEDist x y).trans
    (piecewiseSmoothPathEDist_le_smoothPathEDist x y)

omit [IsManifold I ∞ M] in
/-- The smooth-path length infimum vanishes on the diagonal. -/
@[simp]
theorem smoothPathEDist_self
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] (x : M) :
    smoothPathEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le (fun p : SmoothPath I x x ↦ p.eLength) (SmoothPath.refl x)).trans_eq
    (SmoothPath.eLength_refl x)

omit [IsManifold I ∞ M] in
/-- The piecewise-smooth path-length infimum vanishes on the diagonal. -/
@[simp]
theorem piecewiseSmoothPathEDist_self
    [∀ x : M, ENorm (TangentSpace I x)] (x : M) :
    piecewiseSmoothPathEDist I x x = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le (fun p : PiecewiseSmoothPath I x x ↦ p.eLength) (.nil x)).trans_eq rfl

/-! ### Local smooth chart segments -/

set_option backward.isDefEq.respectTransparency false in
/-- Every point has a neighborhood whose points are joined to it by smooth
paths of finite Riemannian length.

The path is the inverse-chart image of an affine segment.  The convexity of a
model-with-corners range keeps the segment in the chart, while a local bound on
the inverse chart derivative gives the finite-length estimate. -/
theorem eventually_exists_smoothPath_eLength_lt_top
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)] (x : M) :
    ∀ᶠ y in 𝓝 x, ∃ p : SmoothPath I x y, p.eLength < ⊤ := by
  letI (z : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  letI (z : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) z) :=
    normedSpaceTangentSpaceVectorSpace z
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with
    ⟨C, C_pos, hC⟩
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      Metric.ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    Metric.mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  have hgood :
      (extChartAt I x) ⁻¹' (Metric.ball (extChartAt I x x) r ∩ range I) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ r_pos)
  filter_upwards [hgood, chart_source_mem_nhds H x] with y hy hysource
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x x) (extChartAt I x y)
  let γ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
      {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset (by simp [r_pos]) hy
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] ∞ η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have γ_smooth : CMDiff[Icc 0 1] ∞ γ :=
    (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
  let p : SmoothPath I x y :=
    { toFun := γ
      source_eq := by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
      target_eq := by simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, hysource]
      smoothOn := γ_smooth }
  refine ⟨p, ?_⟩
  change Manifold.pathELength I γ 0 1 < ⊤
  have hlength :
      Manifold.pathELength I γ 0 1 ≤
        C * edist (extChartAt I x x) (extChartAt I x y) := by
    rw [← lintegral_fderiv_lineMap_eq_edist,
      Manifold.pathELength_eq_lintegral_mfderivWithin_Icc,
      ← MeasureTheory.lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    apply MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
    have hderiv : mfderiv[Icc 0 1] γ t =
        (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L
          (mfderiv[Icc 0 1] η t) := by
      apply mfderivWithin_comp
      · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
      · exact η_smooth.mdifferentiableOn (by simp) t ht
      · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
      · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
        exact uniqueDiffOn_Icc zero_lt_one t ht
    have hderiv_apply : mfderiv[Icc 0 1] γ t 1 =
        (mfderiv[range I] (extChartAt I x).symm (η t))
          (mfderiv[Icc 0 1] η t 1) := congr($hderiv 1)
    rw [hderiv_apply]
    apply (ContinuousLinearMap.le_opENorm _ _).trans
    gcongr
    · exact (hη.2 ht).le
    · simp only [mfderivWithin_eq_fderivWithin]
      exact le_of_eq rfl
  exact hlength.trans_lt
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (edist_lt_top _ _))

/-- Any two points of a preconnected manifold are joined by a finite
piecewise-smooth path of finite Riemannian length.

This upgrades the regularity of `exists_contMDiff_path` without adding
finite-dimensionality, completeness, boundarylessness, or separation
assumptions. -/
theorem exists_piecewiseSmooth_path [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ p : PiecewiseSmoothPath I x y, p.eLength < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  let s : Set M :=
    {z | ∃ p : PiecewiseSmoothPath I x z, p.eLength < ⊤}
  have hs_open : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    change ∃ p : PiecewiseSmoothPath I x z, p.eLength < ⊤ at hz
    rcases hz with ⟨p, hp⟩
    filter_upwards [eventually_exists_smoothPath_eLength_lt_top (I := I) z] with w hw
    rcases hw with ⟨q, hq⟩
    change ∃ p : PiecewiseSmoothPath I x w, p.eLength < ⊤
    refine ⟨p.append q.toPiecewise, ?_⟩
    rw [PiecewiseSmoothPath.eLength_append, PiecewiseSmoothPath.eLength_toPiecewise]
    exact ENNReal.add_lt_top.2 ⟨hp, hq⟩
  have hs_compl_open : IsOpen sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    change ¬∃ p : PiecewiseSmoothPath I x z, p.eLength < ⊤ at hz
    filter_upwards [eventually_exists_smoothPath_eLength_lt_top (I := I) z] with w hw
    rcases hw with ⟨q, hq⟩
    change ¬∃ p : PiecewiseSmoothPath I x w, p.eLength < ⊤
    intro hw_reachable
    rcases hw_reachable with ⟨p, hp⟩
    apply hz
    refine ⟨p.append q.reverse.toPiecewise, ?_⟩
    rw [PiecewiseSmoothPath.eLength_append, PiecewiseSmoothPath.eLength_toPiecewise,
      SmoothPath.eLength_reverse]
    exact ENNReal.add_lt_top.2 ⟨hp, hq⟩
  have hs_clopen : IsClopen s := ⟨isOpen_compl_iff.mp hs_compl_open, hs_open⟩
  have hs_nonempty : s.Nonempty := by
    refine ⟨x, ?_⟩
    change ∃ p : PiecewiseSmoothPath I x x, p.eLength < ⊤
    exact ⟨.nil x, by simp [PiecewiseSmoothPath.eLength]⟩
  have hs_univ : s = Set.univ := hs_clopen.eq_univ hs_nonempty
  have hy : y ∈ s := by rw [hs_univ]; exact Set.mem_univ y
  exact hy

/-- On a preconnected manifold the auxiliary piecewise-smooth path-length
infimum is finite, under the same assumption boundary as
`riemannianEDist_lt_top`. -/
theorem piecewiseSmoothPathEDist_lt_top [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    piecewiseSmoothPathEDist I x y < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rcases exists_piecewiseSmooth_path g x y with ⟨p, hp⟩
  exact (iInf_le (fun q : PiecewiseSmoothPath I x y ↦ q.eLength) p).trans_lt hp

/-! ## Extended and finite Riemannian distance -/

/-- On a preconnected manifold, the Riemannian extended distance associated to
an explicit smooth metric is finite.  No separation, dimension, boundary, or
completeness hypothesis is needed.

The finite piecewise-smooth witness supplied by
`exists_piecewiseSmooth_path` bounds the canonical `C^1` infimum. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I x y < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rcases exists_piecewiseSmooth_path g x y with ⟨p, hp⟩
  exact p.riemannianEDist_le_eLength.trans_lt hp

/-- Any two points of a preconnected manifold are joined by a `C^1` path of
finite Riemannian length.  This is the path witness underlying
`riemannianEDist_lt_top`, not a path-connectedness assumption. -/
theorem exists_contMDiff_path [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Set.Icc 0 1] 1 γ ∧
      Manifold.pathELength I γ 0 1 < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  exact Manifold.exists_lt_of_riemannianEDist_lt (riemannianEDist_lt_top g x y)

/-- Under Mathlib's topology-preserving extended-metric constructor, ambient
`edist` is exactly the Riemannian path-length infimum. -/
theorem edist_eq_riemannianEDist [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    edist x y = Manifold.riemannianEDist I x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  rfl

/-- The topology carried by the Riemannian extended metric is definitionally
the original manifold topology. -/
theorem topology_eq_riemannianEMetric [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    let h : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    (inferInstance : TopologicalSpace M) = h.toUniformSpace.toTopologicalSpace := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  rfl

/-- After the preconnectedness finiteness proof, ambient `dist` is the real
part of the Riemannian extended distance. -/
theorem dist_eq_riemannianEDist_toReal [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    dist x y = (Manifold.riemannianEDist I x y).toReal := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  rfl

/-- A `Metric.ball` for the finite Riemannian metric is exactly the real
Riemannian-distance sublevel set used in Chapter 1. -/
theorem metric_ball_eq_riemannianEDist [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (r : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    Metric.ball x r = {y | (Manifold.riemannianEDist I x y).toReal < r} := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  ext y
  simp only [Metric.mem_ball, Set.mem_setOf_eq]
  rw [dist_comm]
  rfl

end Ch01
end MorganTianLib
