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
`pathELength`s.  Quantitative inverse-chart replacements, a compact monotone
subdivision, and endpoint-flat concatenation prove that both source-facing
length infima equal Mathlib's canonical `C^1` infimum.  On a preconnected
manifold the distance is finite: the points reachable by finite
piecewise-smooth paths form a nonempty clopen set, using smooth inverse-chart
segments locally.  Only the separating extended-metric constructor needs
`T3Space`; only the finiteness and real-distance results need
`PreconnectedSpace`.

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

/-- A smooth monotone parameter that is constant near both endpoints of
`[0, 1]`. -/
private noncomputable def endpointFlatParameter (t : ℝ) : ℝ :=
  Real.smoothTransition (3 * t - 1)

@[simp]
private theorem endpointFlatParameter_zero : endpointFlatParameter 0 = 0 := by
  rw [endpointFlatParameter, Real.smoothTransition.zero_iff_nonpos]
  norm_num

@[simp]
private theorem endpointFlatParameter_one : endpointFlatParameter 1 = 1 := by
  rw [endpointFlatParameter, Real.smoothTransition.eq_one_iff_one_le]
  norm_num

private theorem contDiff_endpointFlatParameter :
    ContDiff ℝ ∞ endpointFlatParameter := by
  change ContDiff ℝ ∞ (fun t : ℝ ↦ Real.smoothTransition (3 * t - 1))
  fun_prop

private theorem monotone_endpointFlatParameter : Monotone endpointFlatParameter := by
  intro a b hab
  change Real.smoothTransition (3 * a - 1) ≤ Real.smoothTransition (3 * b - 1)
  apply Real.smoothTransition.monotone
  linarith

/-- Reparameterize a smooth path so that it is constant near both endpoints. -/
noncomputable def endpointFlat {x y : M} (p : SmoothPath I x y) : SmoothPath I x y where
  toFun := p ∘ endpointFlatParameter
  source_eq := by simpa only [Function.comp_apply, endpointFlatParameter_zero] using p.source
  target_eq := by simpa only [Function.comp_apply, endpointFlatParameter_one] using p.target
  smoothOn := by
    apply p.smoothOn.comp
    · rw [contMDiffOn_iff_contDiffOn]
      exact contDiff_endpointFlatParameter.contDiffOn
    · intro t _
      exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [IsManifold I ∞ M] in
/-- The endpoint-flat reparameterization is smooth on all of `ℝ`. -/
theorem contMDiff_endpointFlat {x y : M} (p : SmoothPath I x y) :
    CMDiff ∞ p.endpointFlat := by
  rw [← contMDiffOn_univ]
  apply p.smoothOn.comp
  · rw [contMDiffOn_iff_contDiffOn]
    exact contDiff_endpointFlatParameter.contDiffOn
  · intro t _
    exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

omit [IsManifold I ∞ M] in
/-- Endpoint flattening preserves Riemannian length. -/
@[simp]
theorem eLength_endpointFlat
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y : M} (p : SmoothPath I x y) :
    p.endpointFlat.eLength = p.eLength := by
  change Manifold.pathELength I (p ∘ endpointFlatParameter) 0 1 =
    Manifold.pathELength I p 0 1
  calc
    _ = Manifold.pathELength I p (endpointFlatParameter 0) (endpointFlatParameter 1) := by
      apply Manifold.pathELength_comp_of_monotoneOn zero_le_one
      · exact monotone_endpointFlatParameter.monotoneOn _
      · exact (contDiff_endpointFlatParameter.differentiable (by simp)).differentiableOn
      · simpa only [endpointFlatParameter_zero, endpointFlatParameter_one,
          show (p : ℝ → M) = p.toFun from rfl] using
          p.smoothOn.mdifferentiableOn (by simp)
    _ = _ := by rw [endpointFlatParameter_zero, endpointFlatParameter_one]

private noncomputable def appendLeft {x y : M} (p : SmoothPath I x y) : ℝ → M :=
  p.endpointFlat ∘ fun t ↦ 2 * t

private noncomputable def appendRight {y z : M} (q : SmoothPath I y z) : ℝ → M :=
  q.endpointFlat ∘ fun t ↦ 2 * t - 1

private noncomputable def appendFunction {x y z : M}
    (p : SmoothPath I x y) (q : SmoothPath I y z) : ℝ → M :=
  piecewise (Iic (1 / 2 : ℝ)) (appendLeft p) (appendRight q)

/-- Smoothly concatenate two paths after flattening their common endpoint. -/
noncomputable def append {x y z : M} (p : SmoothPath I x y) (q : SmoothPath I y z) :
    SmoothPath I x z := by
  have hf : CMDiff ∞ (appendLeft p) := p.contMDiff_endpointFlat.comp (by
    rw [contMDiff_iff_contDiff]
    fun_prop)
  have hg : CMDiff ∞ (appendRight q) := q.contMDiff_endpointFlat.comp (by
    rw [contMDiff_iff_contDiff]
    fun_prop)
  have hfg : appendLeft p =ᶠ[𝓝 (1 / 2 : ℝ)] appendRight q := by
    filter_upwards [Ioo_mem_nhds (show (1 / 3 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) < 2 / 3 by norm_num)] with t ht
    have hp_param : endpointFlatParameter (2 * t) = 1 := by
      rw [endpointFlatParameter, Real.smoothTransition.eq_one_iff_one_le]
      linarith [ht.1]
    have hq_param : endpointFlatParameter (2 * t - 1) = 0 := by
      rw [endpointFlatParameter, Real.smoothTransition.zero_iff_nonpos]
      linarith [ht.2]
    change p (endpointFlatParameter (2 * t)) = q (endpointFlatParameter (2 * t - 1))
    simp only [hp_param, hq_param, p.target, q.source]
  exact
    { toFun := appendFunction p q
      source_eq := by
        rw [appendFunction, Set.piecewise_eq_of_mem _ _ _ (by norm_num)]
        simp [appendLeft, endpointFlat]
      target_eq := by
        rw [appendFunction, Set.piecewise_eq_of_notMem _ _ _ (by norm_num)]
        change q (endpointFlatParameter (2 * 1 - 1)) = z
        convert q.target using 1
        norm_num
      smoothOn := (ContMDiff.piecewise_Iic hf hg hfg).contMDiffOn }

omit [IsManifold I ∞ M] in
private theorem append_apply_of_le {x y z : M} (p : SmoothPath I x y)
    (q : SmoothPath I y z) {t : ℝ} (ht : t ≤ 1 / 2) :
    p.append q t = p.endpointFlat (2 * t) := by
  change appendFunction p q t = _
  rw [appendFunction, Set.piecewise_eq_of_mem (s := Iic (1 / 2 : ℝ))
    (f := appendLeft p) (g := appendRight q) ht]
  rfl

omit [IsManifold I ∞ M] in
private theorem append_apply_of_lt {x y z : M} (p : SmoothPath I x y)
    (q : SmoothPath I y z) {t : ℝ} (ht : 1 / 2 < t) :
    p.append q t = q.endpointFlat (2 * t - 1) := by
  change appendFunction p q t = _
  rw [appendFunction, Set.piecewise_eq_of_notMem (s := Iic (1 / 2 : ℝ))
    (f := appendLeft p) (g := appendRight q) (by
      simpa only [mem_Iic] using not_le_of_gt ht)]
  rfl

omit [IsManifold I ∞ M] in
/-- Smooth concatenation adds the lengths of the two paths. -/
@[simp]
theorem eLength_append
    [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
    {x y z : M} (p : SmoothPath I x y) (q : SmoothPath I y z) :
    (p.append q).eLength = p.eLength + q.eLength := by
  have hleft :
      Manifold.pathELength I (p.endpointFlat ∘ fun t : ℝ ↦ 2 * t) 0 (1 / 2) =
        p.eLength := by
    calc
      _ = Manifold.pathELength I p.endpointFlat (2 * 0) (2 * (1 / 2)) := by
        apply Manifold.pathELength_comp_of_monotoneOn (by norm_num)
        · intro a _ b _ hab
          dsimp
          linarith
        · fun_prop
        · norm_num
          exact (p.contMDiff_endpointFlat.mdifferentiable (by simp)).mdifferentiableOn
      _ = p.endpointFlat.eLength := by norm_num [eLength]
      _ = p.eLength := p.eLength_endpointFlat
  have hright :
      Manifold.pathELength I (q.endpointFlat ∘ fun t : ℝ ↦ 2 * t - 1) (1 / 2) 1 =
        q.eLength := by
    calc
      _ = Manifold.pathELength I q.endpointFlat (2 * (1 / 2) - 1) (2 * 1 - 1) := by
        apply Manifold.pathELength_comp_of_monotoneOn (by norm_num)
        · intro a _ b _ hab
          dsimp
          linarith
        · fun_prop
        · norm_num
          exact (q.contMDiff_endpointFlat.mdifferentiable (by simp)).mdifferentiableOn
      _ = q.endpointFlat.eLength := by norm_num [eLength]
      _ = q.eLength := q.eLength_endpointFlat
  change Manifold.pathELength I (appendFunction p q) 0 1 = p.eLength + q.eLength
  calc
    _ = Manifold.pathELength I (appendFunction p q) 0 (1 / 2) +
        Manifold.pathELength I (appendFunction p q) (1 / 2) 1 :=
      (Manifold.pathELength_add (I := I) (γ := appendFunction p q)
        (by norm_num) (by norm_num)).symm
    _ = Manifold.pathELength I (p.endpointFlat ∘ fun t : ℝ ↦ 2 * t) 0 (1 / 2) +
        Manifold.pathELength I (q.endpointFlat ∘ fun t : ℝ ↦ 2 * t - 1) (1 / 2) 1 := by
      congr 1
      · apply Manifold.pathELength_congr
        intro t ht
        exact append_apply_of_le p q ht.2
      · apply Manifold.pathELength_congr_Ioo
        intro t ht
        exact append_apply_of_lt p q ht.1
    _ = _ := by rw [hleft, hright]

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

/-- Change the endpoint indices of a piecewise-smooth path along equalities. -/
def cast {x x' y y' : M} (hx : x = x') (hy : y = y')
    (p : PiecewiseSmoothPath I x y) : PiecewiseSmoothPath I x' y' := by
  subst x'
  subst y'
  exact p

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
/-- The empty piecewise-smooth path has zero length. -/
@[simp]
theorem eLength_nil [∀ x : M, ENorm (TangentSpace I x)] (x : M) :
    (PiecewiseSmoothPath.nil (I := I) x).eLength = 0 := rfl

omit [IsManifold I ∞ M] in
/-- Changing endpoint indices does not change piecewise-smooth path length. -/
@[simp]
theorem eLength_cast [∀ x : M, ENorm (TangentSpace I x)]
    {x x' y y' : M} (hx : x = x') (hy : y = y') (p : PiecewiseSmoothPath I x y) :
    (p.cast hx hy).eLength = p.eLength := by
  subst x'
  subst y'
  rfl

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

/-! A finite piecewise path can be flattened to one smooth path.  The
endpoint-flat reparameterization makes each join constant on a neighborhood,
so this operation preserves both endpoint data and total length. -/

/-- Flatten a finite piecewise-smooth path to a single smooth path. -/
noncomputable def toSmooth :
    {x y : M} → PiecewiseSmoothPath I x y → SmoothPath I x y
  | _, _, .nil x => SmoothPath.refl x
  | _, _, .cons head tail => head.append (toSmooth tail)

omit [IsManifold I ∞ M] in
/-- Flattening preserves the piecewise-smooth length. -/
@[simp]
theorem eLength_toSmooth
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    {x y : M} (p : PiecewiseSmoothPath I x y) :
    (p.toSmooth).eLength = p.eLength := by
  induction p with
  | nil x =>
      change (SmoothPath.refl (I := I) x).eLength = 0
      exact SmoothPath.eLength_refl (I := I) x
  | cons head tail ih =>
      change (head.append tail.toSmooth).eLength = head.eLength + tail.eLength
      rw [SmoothPath.eLength_append, ih]

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
/-- Flattening finite smooth pieces shows that allowing joins does not lower
the canonical smooth-path length infimum. -/
theorem smoothPathEDist_le_piecewiseSmoothPathEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] (x y : M) :
    smoothPathEDist I x y ≤ piecewiseSmoothPathEDist I x y := by
  rw [smoothPathEDist, piecewiseSmoothPathEDist]
  refine le_iInf fun p ↦ ?_
  exact iInf_le_of_le p.toSmooth (PiecewiseSmoothPath.eLength_toSmooth p).le

omit [IsManifold I ∞ M] in
/-- The smooth and finite piecewise-smooth path-length infima agree. -/
theorem smoothPathEDist_eq_piecewiseSmoothPathEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] (x y : M) :
    smoothPathEDist I x y = piecewiseSmoothPathEDist I x y :=
  le_antisymm (smoothPathEDist_le_piecewiseSmoothPathEDist x y)
    (piecewiseSmoothPathEDist_le_smoothPathEDist x y)

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

set_option backward.isDefEq.respectTransparency false in
/-- Near every point, a `C^1` subpath can be replaced by a smooth chart
segment with arbitrarily small multiplicative loss in length.

More precisely, for every `r > 1` there is a neighborhood `U` of `x` such
that a `C^1` path whose image lies in `U` admits a smooth endpoint-preserving
replacement of length at most `r ^ 2` times its own length.  The two factors
come from transporting tangent vectors to the fibre at `x` and back.  This is
the local quantitative input for the piecewise-smooth approximation of the
`C^1` competitors in `Manifold.riemannianEDist`.

No finite-dimensionality or completeness hypothesis is needed: the
fundamental-theorem estimate used below passes through the completion of the
fixed tangent fibre internally. -/
theorem eventually_exists_smoothPath_eLength_le_pathELength
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    (x : M) {r : ℝ} (hr : 1 < r) :
    ∃ U ∈ 𝓝 x, ∀ ⦃a b : ℝ⦄ (_hab : a ≤ b) ⦃γ : ℝ → M⦄,
      CMDiff[Set.Icc a b] 1 γ → MapsTo γ (Set.Icc a b) U →
        ∃ p : SmoothPath I (γ a) (γ b),
          p.eLength ≤ (ENNReal.ofReal r) ^ 2 * Manifold.pathELength I γ a b := by
  classical
  let T := trivializationAt E (TangentSpace I) x
  let L := T.symmL ℝ x
  have hto : ∀ᶠ y in 𝓝 x,
      ‖L ∘L T.continuousLinearMapAt ℝ y‖ < r :=
    eventually_norm_symmL_trivializationAt_self_comp_lt
      E (TangentSpace I) x hr
  have hfrom : ∀ᶠ y in 𝓝 x,
      ‖T.symmL ℝ y ∘L T.continuousLinearMapAt ℝ x‖ < r :=
    eventually_norm_symmL_trivializationAt_comp_self_lt
      E (TangentSpace I) x hr
  have htransport : ∀ᶠ y in 𝓝 x,
      ‖L ∘L T.continuousLinearMapAt ℝ y‖ < r ∧
        ‖T.symmL ℝ y ∘L T.continuousLinearMapAt ℝ x‖ < r :=
    hto.and hfrom
  have htransport_chart : ∀ᶠ z in 𝓝 (extChartAt I x x),
      ‖L ∘L T.continuousLinearMapAt ℝ ((extChartAt I x).symm z)‖ < r ∧
        ‖T.symmL ℝ ((extChartAt I x).symm z) ∘L
          T.continuousLinearMapAt ℝ x‖ < r :=
    by
      have htransport' : ∀ᶠ y in 𝓝 ((extChartAt I x).symm (extChartAt I x x)),
          ‖L ∘L T.continuousLinearMapAt ℝ y‖ < r ∧
            ‖T.symmL ℝ y ∘L T.continuousLinearMapAt ℝ x‖ < r := by
        simpa using htransport
      exact (continuousAt_extChartAt_symm (I := I) x).eventually htransport'
  have htransport_chart' : ∀ᶠ z in 𝓝[range I] (extChartAt I x x),
      ‖L ∘L T.continuousLinearMapAt ℝ ((extChartAt I x).symm z)‖ < r ∧
        ‖T.symmL ℝ ((extChartAt I x).symm z) ∘L
          T.continuousLinearMapAt ℝ x‖ < r :=
    Filter.Eventually.filter_mono inf_le_left htransport_chart
  obtain ⟨ρ, ρ_pos, hρ⟩ : ∃ ρ > 0,
      Metric.ball (extChartAt I x x) ρ ∩ range I ⊆ (extChartAt I x).target ∩
        {z | ‖L ∘L T.continuousLinearMapAt ℝ ((extChartAt I x).symm z)‖ < r ∧
          ‖T.symmL ℝ ((extChartAt I x).symm z) ∘L
            T.continuousLinearMapAt ℝ x‖ < r} := by
    apply Metric.mem_nhdsWithin_iff.1
    exact inter_mem (extChartAt_target_mem_nhdsWithin x) htransport_chart'
  let U := (extChartAt I x) ⁻¹' (Metric.ball (extChartAt I x x) ρ ∩ range I) ∩
    (chartAt H x).source
  have hU : U ∈ 𝓝 x := by
    apply inter_mem _ (chart_source_mem_nhds H x)
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ ρ_pos)
  refine ⟨U, hU, ?_⟩
  intro a b hab γ hγ hγU
  rcases hab.eq_or_lt with rfl | hab
  · refine ⟨SmoothPath.refl (I := I) (γ a), ?_⟩
    simp
  have haU : γ a ∈ U := hγU ⟨le_rfl, hab.le⟩
  have hbU : γ b ∈ U := hγU ⟨hab.le, le_rfl⟩
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x (γ a))
    (extChartAt I x (γ b))
  let σ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
      {z | ‖L ∘L T.continuousLinearMapAt ℝ ((extChartAt I x).symm z)‖ < r ∧
        ‖T.symmL ℝ ((extChartAt I x).symm z) ∘L
          T.continuousLinearMapAt ℝ x‖ < r}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hρ
    apply ((convex_ball _ _).inter I.convex_range).segment_subset
    · exact haU.1
    · exact hbU.1
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] ∞ η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have σ_smooth : CMDiff[Icc 0 1] ∞ σ :=
    (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
  let p : SmoothPath I (γ a) (γ b) :=
    { toFun := σ
      source_eq := by
        simp [σ, η, ContinuousAffineMap.coe_lineMap_eq, haU.2]
      target_eq := by
        simp [σ, η, ContinuousAffineMap.coe_lineMap_eq, hbU.2]
      smoothOn := σ_smooth }
  refine ⟨p, ?_⟩
  let e : ℝ → TangentSpace I x := fun t ↦ L (extChartAt I x (γ t))
  have hγsource : MapsTo γ (Icc a b) (chartAt H x).source :=
    fun t ht ↦ (hγU ht).2
  have hchartγ : CMDiff[Icc a b] 1 ((extChartAt I x) ∘ γ) :=
    (contMDiffOn_extChartAt (I := I) (x := x)).comp hγ hγsource
  have e_contDiff : ContDiffOn ℝ 1 e (Icc a b) := by
    apply L.contDiff.comp_contDiffOn hchartγ.contDiffOn
  have e_deriv (t : ℝ) (ht : t ∈ Icc a b) :
      derivWithin e (Icc a b) t =
        (L ∘L T.continuousLinearMapAt ℝ (γ t)) (mfderiv[Icc a b] γ t 1) := by
    have hunique : UniqueDiffWithinAt ℝ (Icc a b) t :=
      uniqueDiffOn_Icc hab t ht
    have huniqueM : UniqueMDiffAt[Icc a b] t := by
      rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact hunique
    have hγdiff : MDiffAt[Icc a b] γ t :=
      hγ.mdifferentiableOn one_ne_zero t ht
    have hchartderiv : mfderiv[Icc a b] ((extChartAt I x) ∘ γ) t =
        T.continuousLinearMapAt ℝ (γ t) ∘L mfderiv[Icc a b] γ t := by
      rw [TangentBundle.continuousLinearMapAt_trivializationAt (hγsource ht)]
      convert mfderivWithin_comp t
        (mdifferentiableAt_extChartAt (I := I) (hγsource ht)) hγdiff
        (fun _ _ ↦ Set.mem_univ _) huniqueM using 1
      simp only [mfderivWithin_univ]
    have hqdiff : DifferentiableWithinAt ℝ ((extChartAt I x) ∘ γ) (Icc a b) t := by
      rw [← mdifferentiableWithinAt_iff_differentiableWithinAt]
      exact hchartγ.mdifferentiableOn one_ne_zero t ht
    have hederiv : fderivWithin ℝ (L ∘ ((extChartAt I x) ∘ γ)) (Icc a b) t =
        L ∘L fderivWithin ℝ ((extChartAt I x) ∘ γ) (Icc a b) t :=
      (L.hasFDerivAt.comp_hasFDerivWithinAt t hqdiff.hasFDerivWithinAt).fderivWithin hunique
    change derivWithin (L ∘ ((extChartAt I x) ∘ γ)) (Icc a b) t = _
    rw [← fderivWithin_derivWithin, hederiv, ← mfderivWithin_eq_fderivWithin,
      hchartderiv]
    rfl
  have fixedChord_le :
      ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ ≤
        ENNReal.ofReal r * Manifold.pathELength I γ a b := by
    calc
      ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ = ‖e b - e a‖ₑ := by
        simp only [e, map_sub]
      _ ≤ ∫⁻ t in Icc a b, ‖derivWithin e (Icc a b) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc e_contDiff hab.le
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal r * ‖mfderiv[Icc a b] γ t 1‖ₑ := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [e_deriv t ht]
        have hop : ‖L ∘L T.continuousLinearMapAt ℝ (γ t)‖ ≤ r := by
          have ht' := (hρ (hγU ht).1).2.1
          have ht_source : γ t ∈ (extChartAt I x).source := by
            simpa only [extChartAt_source] using hγsource ht
          rw [(extChartAt I x).left_inv ht_source] at ht'
          exact ht'.le
        rw [← ofReal_norm]
        calc
          ENNReal.ofReal ‖(L ∘L T.continuousLinearMapAt ℝ (γ t))
              (mfderiv[Icc a b] γ t 1)‖ ≤
              ENNReal.ofReal (‖L ∘L T.continuousLinearMapAt ℝ (γ t)‖ *
                ‖mfderiv[Icc a b] γ t 1‖) :=
            ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
          _ ≤ ENNReal.ofReal (r * ‖mfderiv[Icc a b] γ t 1‖) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
          _ = ENNReal.ofReal r * ‖mfderiv[Icc a b] γ t 1‖ₑ := by
            rw [ENNReal.ofReal_mul (le_trans zero_le_one hr.le), ofReal_norm]
      _ = ENNReal.ofReal r * Manifold.pathELength I γ a b := by
        rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  have map_symmL_self (v : E) : T.continuousLinearMapAt ℝ x (L v) = v := by
    dsimp only [T, L]
    set_option backward.isDefEq.respectTransparency true in
      have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
        FiberBundle.mem_baseSet_trivializationAt' x
      simp only [Trivialization.continuousLinearMapAt_apply]
      convert
        ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x
          hx).apply_symm_apply v
      simp [Trivialization.coe_continuousLinearEquivAt_eq _ hx]
  have chordPath_le : Manifold.pathELength I σ 0 1 ≤
      ENNReal.ofReal r *
        ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ := by
    rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
    calc
      (∫⁻ t in Icc (0 : ℝ) 1, ‖mfderiv[Icc 0 1] σ t 1‖ₑ) ≤
          ∫⁻ _t in Icc (0 : ℝ) 1,
            ENNReal.ofReal r *
              ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ := by
        apply MeasureTheory.setLIntegral_mono' measurableSet_Icc
        intro t ht
        have hderiv : mfderiv[Icc 0 1] σ t =
            (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L
              (mfderiv[Icc 0 1] η t) := by
          apply mfderivWithin_comp
          · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
          · exact η_smooth.mdifferentiableOn (by simp) t ht
          · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        have hinvsource : (extChartAt I x).symm (η t) ∈ (chartAt H x).source := by
          have hsource : (extChartAt I x).symm (η t) ∈ (extChartAt I x).source :=
            (extChartAt I x).map_target (hη.1 ht)
          simpa only [extChartAt_source] using hsource
        have hηderiv : mfderiv[Icc 0 1] η t 1 =
            extChartAt I x (γ b) - extChartAt I x (γ a) := by
          simp only [mfderivWithin_eq_fderivWithin]
          rw [fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one t ht)
            (ContinuousAffineMap.differentiableAt _)]
          rw [ContinuousAffineMap.fderiv]
          change (η.toAffineMap.linear : ℝ → E) 1 = _
          rw [show η.toAffineMap = AffineMap.lineMap
            (extChartAt I x (γ a)) (extChartAt I x (γ b)) by rfl,
            AffineMap.lineMap_linear]
          simp
        have hinv : mfderiv[range I] (extChartAt I x).symm (η t) =
            T.symmL ℝ ((extChartAt I x).symm (η t)) := by
          rw [TangentBundle.symmL_trivializationAt hinvsource,
            (extChartAt I x).right_inv (hη.1 ht)]
        have hderiv_apply := congr($hderiv 1)
        rw [ContinuousLinearMap.comp_apply, hηderiv] at hderiv_apply
        let A := T.symmL ℝ ((extChartAt I x).symm (η t)) ∘L
          T.continuousLinearMapAt ℝ x
        let v := L (extChartAt I x (γ b) - extChartAt I x (γ a))
        have hAv : T.symmL ℝ ((extChartAt I x).symm (η t))
            (extChartAt I x (γ b) - extChartAt I x (γ a)) = A v := by
          set_option backward.isDefEq.respectTransparency true in
            dsimp only [A, v]
            rw [ContinuousLinearMap.comp_apply, map_symmL_self]
        have hAv' : (mfderiv[range I] (extChartAt I x).symm (η t))
            (extChartAt I x (γ b) - extChartAt I x (γ a)) = A v := by
          set_option backward.isDefEq.respectTransparency true in
            rw [hinv]
            exact hAv
        rw [hderiv_apply, hAv', ← ofReal_norm]
        have hop : ‖A‖ ≤ r := (hη.2 ht).2.le
        calc
          ENNReal.ofReal ‖A v‖ ≤ ENNReal.ofReal (‖A‖ * ‖v‖) :=
            ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
          _ ≤ ENNReal.ofReal (r * ‖v‖) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_right hop (norm_nonneg _)
          _ = ENNReal.ofReal r * ‖v‖ₑ := by
            rw [ENNReal.ofReal_mul (le_trans zero_le_one hr.le), ofReal_norm]
      _ = ENNReal.ofReal r *
          ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ := by
        simp
  calc
    p.eLength ≤ ENNReal.ofReal r *
        ‖L (extChartAt I x (γ b) - extChartAt I x (γ a))‖ₑ := chordPath_le
    _ ≤ ENNReal.ofReal r *
        (ENNReal.ofReal r * Manifold.pathELength I γ a b) :=
      mul_le_mul_right fixedChord_le _
    _ = ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ a b := by
      simp only [pow_two, mul_assoc]

/-- A `C^1` path on `[0, 1]` admits an endpoint-preserving finite
piecewise-smooth replacement with arbitrarily small multiplicative length
loss.

The proof covers the compact parameter interval by the inverse images of the
quantitative chart neighborhoods, refines that cover to a monotone finite
subdivision, and concatenates the local smooth replacements. -/
theorem exists_piecewiseSmoothPath_eLength_le_pathELength
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ) {r : ℝ} (hr : 1 < r) :
    ∃ p : PiecewiseSmoothPath I (γ 0) (γ 1),
      p.eLength ≤ ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ 0 1 := by
  classical
  choose U hU hreplace using fun z : Icc (0 : ℝ) 1 ↦
    eventually_exists_smoothPath_eLength_le_pathELength (I := I) (γ z) hr
  let γ' : Icc (0 : ℝ) 1 → M := fun z ↦ γ z
  have hγ' : Continuous γ' := hγ.continuousOn.restrict
  let c : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) :=
    fun z ↦ γ' ⁻¹' interior (U z)
  have hc_open : ∀ z, IsOpen (c z) := fun z ↦ isOpen_interior.preimage hγ'
  have hc_cover : univ ⊆ ⋃ z, c z := by
    intro z _
    apply mem_iUnion.2
    refine ⟨z, ?_⟩
    change γ' z ∈ interior (U z)
    exact mem_interior_iff_mem_nhds.2 (hU z)
  obtain ⟨t, ht_zero, ht_mono, ⟨m, hm⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  have segment (n : ℕ) :
      ∃ q : SmoothPath I (γ (t n)) (γ (t (n + 1))),
        q.eLength ≤ ENNReal.ofReal r ^ 2 *
          Manifold.pathELength I γ (t n) (t (n + 1)) := by
    rcases ht_cover n with ⟨z, hz⟩
    have htn : (t n : ℝ) ≤ t (n + 1) := ht_mono (Nat.le_succ n)
    apply hreplace z htn
    · apply hγ.mono
      intro s hs
      exact ⟨(t n).2.1.trans hs.1, hs.2.trans (t (n + 1)).2.2⟩
    · intro s hs
      have hs_unit : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(t n).2.1.trans hs.1, hs.2.trans (t (n + 1)).2.2⟩
      have hs_subtype : (⟨s, hs_unit⟩ : Icc (0 : ℝ) 1) ∈ Icc (t n) (t (n + 1)) :=
        hs
      have hs_cover := hz hs_subtype
      change γ s ∈ interior (U z) at hs_cover
      exact interior_subset hs_cover
  choose q hq using segment
  let p : (n : ℕ) → PiecewiseSmoothPath I (γ (t 0)) (γ (t n)) :=
    fun n ↦ Nat.rec (PiecewiseSmoothPath.nil (I := I) (γ (t 0)))
      (fun n p ↦ p.append (q n).toPiecewise) n
  have hp (n : ℕ) : (p n).eLength ≤ ENNReal.ofReal r ^ 2 *
      Manifold.pathELength I γ (t 0) (t n) := by
    induction n with
    | zero => simp [p]
    | succ n ih =>
        have h0n : (t 0 : ℝ) ≤ t n := ht_mono (Nat.zero_le n)
        have hnn : (t n : ℝ) ≤ t (n + 1) := ht_mono (Nat.le_succ n)
        rw [show p (n + 1) = (p n).append (q n).toPiecewise by rfl,
          PiecewiseSmoothPath.eLength_append, PiecewiseSmoothPath.eLength_toPiecewise]
        calc
          (p n).eLength + (q n).eLength ≤
              ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ (t 0) (t n) +
                ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ (t n) (t (n + 1)) :=
            add_le_add ih (hq n)
          _ = ENNReal.ofReal r ^ 2 *
              (Manifold.pathELength I γ (t 0) (t n) +
                Manifold.pathELength I γ (t n) (t (n + 1))) := by
            rw [mul_add]
          _ = ENNReal.ofReal r ^ 2 *
              Manifold.pathELength I γ (t 0) (t (n + 1)) := by
            rw [Manifold.pathELength_add h0n hnn]
  have ht_m : t m = 1 := hm m le_rfl
  have ht_zero_real : (t 0 : ℝ) = 0 := congrArg Subtype.val ht_zero
  have ht_m_real : (t m : ℝ) = 1 := congrArg Subtype.val ht_m
  have hγ_zero : γ (t 0) = γ 0 := congrArg γ ht_zero_real
  have hγ_m : γ (t m) = γ 1 := congrArg γ ht_m_real
  refine ⟨(p m).cast hγ_zero hγ_m, ?_⟩
  rw [PiecewiseSmoothPath.eLength_cast]
  simpa only [ht_zero_real, ht_m_real] using hp m

/-- A `C^1` path on `[0, 1]` admits an endpoint-preserving smooth replacement
with arbitrarily small multiplicative length loss. -/
theorem exists_smoothPath_eLength_le_pathELength
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ) {r : ℝ} (hr : 1 < r) :
    ∃ p : SmoothPath I (γ 0) (γ 1),
      p.eLength ≤ ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ 0 1 := by
  rcases exists_piecewiseSmoothPath_eLength_le_pathELength (I := I) hγ hr with ⟨p, hp⟩
  exact ⟨p.toSmooth, (PiecewiseSmoothPath.eLength_toSmooth p).le.trans hp⟩

private theorem le_of_forall_ofReal_sq_mul_le {a b : ℝ≥0∞}
    (h : ∀ r : ℝ, 1 < r → a ≤ ENNReal.ofReal r ^ 2 * b) : a ≤ b := by
  let r : ℕ → ℝ := fun n ↦ 1 + 1 / (n + 1)
  have hr : Tendsto r atTop (𝓝 1) := by
    have hzero : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [r] using tendsto_const_nhds.add hzero
  have hof : Tendsto (fun n ↦ ENNReal.ofReal (r n)) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal hr
  have hfactor : Tendsto (fun n ↦ ENNReal.ofReal (r n) ^ 2) atTop (𝓝 1) := by
    convert ENNReal.Tendsto.mul hof (Or.inl one_ne_zero) hof (Or.inl one_ne_zero) using 1 <;>
      simp [pow_two]
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (r n) ^ 2 * b) atTop (𝓝 b) := by
    simpa using ENNReal.Tendsto.mul_const hfactor (Or.inl one_ne_zero)
  apply ge_of_tendsto' hlim
  intro n
  apply h
  dsimp [r]
  have : 0 < (1 : ℝ) / (n + 1) := by positivity
  linarith

/-- The piecewise-smooth length infimum is bounded by every `C^1` competitor
on `[0, 1]` with the same endpoints. -/
theorem piecewiseSmoothPathEDist_le_pathELength
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {x y : M} {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ)
    (hγ_zero : γ 0 = x) (hγ_one : γ 1 = y) :
    piecewiseSmoothPathEDist I x y ≤ Manifold.pathELength I γ 0 1 := by
  apply le_of_forall_ofReal_sq_mul_le
  intro r hr
  rcases exists_piecewiseSmoothPath_eLength_le_pathELength (I := I) hγ hr with ⟨p, hp⟩
  let q := p.cast hγ_zero hγ_one
  calc
    piecewiseSmoothPathEDist I x y ≤ q.eLength := by
      exact iInf_le (fun q : PiecewiseSmoothPath I x y ↦ q.eLength) q
    _ = p.eLength := PiecewiseSmoothPath.eLength_cast _ _ _
    _ ≤ ENNReal.ofReal r ^ 2 * Manifold.pathELength I γ 0 1 := hp

/-- The smooth-path length infimum is bounded by every `C^1` competitor on
`[0, 1]` with the same endpoints. -/
theorem smoothPathEDist_le_pathELength
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    {x y : M} {γ : ℝ → M} (hγ : CMDiff[Icc 0 1] 1 γ)
    (hγ_zero : γ 0 = x) (hγ_one : γ 1 = y) :
    smoothPathEDist I x y ≤ Manifold.pathELength I γ 0 1 :=
  (smoothPathEDist_le_piecewiseSmoothPathEDist x y).trans
    (piecewiseSmoothPathEDist_le_pathELength hγ hγ_zero hγ_one)

/-- The source-facing piecewise-smooth path-length infimum is no larger than
Mathlib's canonical `C^1` Riemannian extended distance. -/
theorem piecewiseSmoothPathEDist_le_riemannianEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)] (x y : M) :
    piecewiseSmoothPathEDist I x y ≤ Manifold.riemannianEDist I x y := by
  rw [Manifold.riemannianEDist]
  apply le_iInf
  intro γ
  apply le_iInf
  intro hγ
  let η : ℝ → M := γ ∘ projIcc 0 1 zero_le_one
  have hη : CMDiff[Icc 0 1] 1 η := contMDiffOn_comp_projIcc_iff.2 hγ
  calc
    piecewiseSmoothPathEDist I x y ≤ Manifold.pathELength I η 0 1 :=
      piecewiseSmoothPathEDist_le_pathELength hη (by simp [η]) (by simp [η])
    _ = ∫⁻ t, ‖mfderiv% γ t 1‖ₑ :=
      Manifold.lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc.symm

/-- The source-facing smooth-path length infimum is no larger than Mathlib's
canonical `C^1` Riemannian extended distance. -/
theorem smoothPathEDist_le_riemannianEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)] (x y : M) :
    smoothPathEDist I x y ≤ Manifold.riemannianEDist I x y :=
  (smoothPathEDist_le_piecewiseSmoothPathEDist x y).trans
    (piecewiseSmoothPathEDist_le_riemannianEDist x y)

/-- Morgan--Tian's infimum over finite piecewise-smooth paths agrees with
Mathlib's canonical `C^1` Riemannian extended distance. -/
theorem piecewiseSmoothPathEDist_eq_riemannianEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)] (x y : M) :
    piecewiseSmoothPathEDist I x y = Manifold.riemannianEDist I x y :=
  le_antisymm (piecewiseSmoothPathEDist_le_riemannianEDist x y)
    (riemannianEDist_le_piecewiseSmoothPathEDist x y)

/-- Morgan--Tian's smooth-path length infimum agrees with Mathlib's canonical
`C^1` Riemannian extended distance. -/
theorem smoothPathEDist_eq_riemannianEDist
    [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)] (x y : M) :
    smoothPathEDist I x y = Manifold.riemannianEDist I x y :=
  (smoothPathEDist_eq_piecewiseSmoothPathEDist x y).trans
    (piecewiseSmoothPathEDist_eq_riemannianEDist x y)

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
