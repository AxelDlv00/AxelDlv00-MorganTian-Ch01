import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Tactic.LinearCombination

/-!
# The scalar bracket commutator

This leaf supplies the local second-derivative commutator used by the metric
curvature-symmetry proof.  It is derived from the manifold Lie-bracket product
rules and Jacobi identity, with no coordinate curvature facade.  The resulting
statement is an analytic adapter for `Curvature.Symmetries`, not a second
connection or curvature definition.

The sign and derivative-slot convention follows Morgan--Tian Claim 1.5,
`morganTian2007`, printed pp. 37--38.  The bundled covariant-derivative and
Lie-bracket APIs are the pinned Mathlib interfaces used by this proof.
-/

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature
namespace ScalarCommutator

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-- Smoothness at a point for a tangent-bundle vector field. -/
abbrev SmoothAt (X : (x : M) → TangentSpace I x) (p : M) : Prop :=
  ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% X) p

/- The finite-dimensional hypothesis is not needed for this local conversion. -/
omit [FiniteDimensional ℝ EM] in
/-- A smooth section is differentiable on a neighborhood of the base point. -/
lemma smoothAt_eventually_mdifferentiableAt
    {X : (x : M) → TangentSpace I x} {p : M} (hX : SmoothAt X p) :
    ∀ᶠ q in 𝓝 p, MDiffAt (T% X) q := by
  have hX1 := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact ENat.LEInfty.out)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hX1
  exact hn.mono fun q hq => hq.mdifferentiableAt one_ne_zero

omit [FiniteDimensional ℝ EM] in
/-- A smooth scalar is differentiable on a neighborhood of the base point. -/
lemma scalarAt_eventually_mdifferentiableAt
    {f : M → ℝ} {p : M} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p) :
    ∀ᶠ q in 𝓝 p, MDiffAt f q := by
  have hf1 := hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact ENat.LEInfty.out)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hf1
  exact hn.mono fun q hq => hq.mdifferentiableAt one_ne_zero

/-- The Lie bracket of two smooth local vector fields is smooth locally. -/
lemma mlieBracket_smoothAt
    {A B : (x : M) → TangentSpace I x} {p : M}
    (hA : SmoothAt A p) (hB : SmoothAt B p) :
    SmoothAt (VectorField.mlieBracket I A B) p := by
  letI : CompleteSpace EM := FiniteDimensional.complete ℝ EM
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  letI : IsManifold I ((↑(⊤ : ℕ∞) : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hmn : minSmoothness ℝ ((↑(⊤ : ℕ∞) : ℕ∞ω) + 1) ≤
      (↑(⊤ : ℕ∞) : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    simp
  exact ContMDiffAt.mlieBracket_vectorField (m := (⊤ : ℕ∞))
    (n := (⊤ : ℕ∞)) hA hB hmn

omit [FiniteDimensional ℝ EM] in
/-- Applying a manifold derivative to a smooth tangent field preserves local
smoothness. -/
lemma contMDiffAt_mvfderiv_apply_along
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {X : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ∞ f p) (hX : SmoothAt X p) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => d% f y (X y)) p := by
  have hsection : ContMDiffAt I (I.prod 𝓘(ℝ, EM →L[ℝ] F)) ∞
      (fun y => Bundle.TotalSpace.mk' (EM →L[ℝ] F)
        (E := fun y : M => TangentSpace I y →L[ℝ] F) y (d% f y)) p := by
    letI : ChartedSpace (ModelProd H (EM →L[ℝ] F))
        (Bundle.TotalSpace (EM →L[ℝ] F)
          (fun y : M => TangentSpace I y →L[ℝ] F)) :=
      FiberBundle.chartedSpace
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    convert hf.mfderiv_const (m := ∞) (by simp) using 1
    ext y v
    simp [mvfderiv, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl
  have h := hsection.clm_bundle_apply hX
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

/-- Jacobi and the bracket product rule cancel the scalar second-derivative
commutator after testing against any smooth tangent field. -/
lemma scalar_bracket_commutator_mul_at
    {f : M → ℝ} {X Y V : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hV : SmoothAt V p) :
    (((d% (fun q => d% f q (Y q)) p) (X p) -
        (d% (fun q => d% f q (X q)) p) (Y p) -
        (d% f p) (VectorField.mlieBracket I X Y p)) • V p) = 0 := by
  letI : CompleteSpace EM := FiniteDimensional.complete ℝ EM
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  letI : IsManifold I ((↑(⊤ : ℕ∞) : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  letI : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  let a : M → ℝ := fun q => d% f q (Y q)
  let b : M → ℝ := fun q => d% f q (X q)
  let XY : (x : M) → TangentSpace I x := VectorField.mlieBracket I X Y
  let XV : (x : M) → TangentSpace I x := VectorField.mlieBracket I X V
  let YV : (x : M) → TangentSpace I x := VectorField.mlieBracket I Y V
  let X_YV : (x : M) → TangentSpace I x := VectorField.mlieBracket I X YV
  let Y_XV : (x : M) → TangentSpace I x := VectorField.mlieBracket I Y XV
  let XY_V : (x : M) → TangentSpace I x := VectorField.mlieBracket I XY V
  have ha_s : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ a p := by
    exact contMDiffAt_mvfderiv_apply_along (hf) hY
  have hb_s : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ b p := by
    exact contMDiffAt_mvfderiv_apply_along (hf) hX
  have hXY_s : SmoothAt XY p := mlieBracket_smoothAt hX hY
  have hXV_s : SmoothAt XV p := mlieBracket_smoothAt hX hV
  have hYV_s : SmoothAt YV p := mlieBracket_smoothAt hY hV
  have hX_YV_s : SmoothAt X_YV p := mlieBracket_smoothAt hX hYV_s
  have hY_XV_s : SmoothAt Y_XV p := mlieBracket_smoothAt hY hXV_s
  have hXY_V_s : SmoothAt XY_V p := mlieBracket_smoothAt hXY_s hV
  have ha : MDiffAt a p := ha_s.mdifferentiableAt (by simp)
  have hb : MDiffAt b p := hb_s.mdifferentiableAt (by simp)
  have hf' : MDiffAt f p := hf.mdifferentiableAt (by simp)
  have hXp : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hYp : MDiffAt (T% Y) p := hY.mdifferentiableAt (by simp)
  have hVp : MDiffAt (T% V) p := hV.mdifferentiableAt (by simp)
  have hXYp : MDiffAt (T% XY) p := hXY_s.mdifferentiableAt (by simp)
  have hXVp : MDiffAt (T% XV) p := hXV_s.mdifferentiableAt (by simp)
  have hYVp : MDiffAt (T% YV) p := hYV_s.mdifferentiableAt (by simp)
  have hfaV : MDiffAt (T% (a • V)) p := ha.smul_section hVp
  have hfbV : MDiffAt (T% (b • V)) p := hb.smul_section hVp
  have hfa : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ a p := ha_s
  have hfb : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ b p := hb_s
  have hYf_ev : ∀ᶠ q in 𝓝 p,
      VectorField.mlieBracket I Y (f • V) q =
        a q • V q + f q • YV q := by
    filter_upwards [scalarAt_eventually_mdifferentiableAt hf,
      smoothAt_eventually_mdifferentiableAt hV] with q hfq hVq
    have hq := VectorField.mlieBracket_smul_right (I := I)
      (V := Y) (W := V) (f := f) (x := q) hfq hVq
    simpa [a, YV, mvfderiv] using hq
  have hXf_ev : ∀ᶠ q in 𝓝 p,
      VectorField.mlieBracket I X (f • V) q =
        b q • V q + f q • XV q := by
    filter_upwards [scalarAt_eventually_mdifferentiableAt hf,
      smoothAt_eventually_mdifferentiableAt hV] with q hfq hVq
    have hq := VectorField.mlieBracket_smul_right (I := I)
      (V := X) (W := V) (f := f) (x := q) hfq hVq
    simpa [b, XV, mvfderiv] using hq
  have hYf := (EventuallyEq.rfl : X =ᶠ[𝓝 p] X).mlieBracket_vectorField_eq hYf_ev
  have hXf := (EventuallyEq.rfl : Y =ᶠ[𝓝 p] Y).mlieBracket_vectorField_eq hXf_ev
  have hYf_arg : (fun x => a x • V x + f x • YV x) = a • V + f • YV := by
    funext q
    rfl
  have hXf_arg : (fun x => b x • V x + f x • XV x) = b • V + f • XV := by
    funext q
    rfl
  rw [hYf_arg] at hYf
  rw [hXf_arg] at hXf
  have hYf' := hYf
  have hXf' := hXf
  have hLadd := VectorField.mlieBracket_add_right (I := I) (V := X)
      (W := a • V) (W₁ := f • YV) (x := p) hfaV
      ((hf'.smul_section hYVp))
  have hRadd := VectorField.mlieBracket_add_right (I := I) (V := Y)
      (W := b • V) (W₁ := f • XV) (x := p) hfbV
      ((hf'.smul_section hXVp))
  have hLa := VectorField.mlieBracket_smul_right (I := I)
      (V := X) (W := V) (f := a) (x := p) ha hVp
  have hLb := VectorField.mlieBracket_smul_right (I := I)
      (V := Y) (W := V) (f := b) (x := p) hb hVp
  have hLf := VectorField.mlieBracket_smul_right (I := I)
      (V := X) (W := YV) (f := f) (x := p) hf' hYVp
  have hRf := VectorField.mlieBracket_smul_right (I := I)
      (V := Y) (W := XV) (f := f) (x := p) hf' hXVp
  have hbr := VectorField.mlieBracket_smul_right (I := I)
      (V := XY) (W := V) (f := f) (x := p) hf' hVp
  have hL : VectorField.mlieBracket I X (VectorField.mlieBracket I Y (f • V)) p =
      (d% a p) (X p) • V p + a p • XV p +
        (d% f p) (X p) • YV p + f p • X_YV p := by
    rw [hYf', hLadd, hLa, hLf]
    simp only [XV, YV, X_YV]
    module
  have hR : VectorField.mlieBracket I Y (VectorField.mlieBracket I X (f • V)) p =
      (d% b p) (Y p) • V p + b p • YV p +
        (d% f p) (Y p) • XV p + f p • Y_XV p := by
    rw [hXf', hRadd, hLb, hRf]
    simp only [XV, YV, Y_XV]
    module
  have hXYf : VectorField.mlieBracket I XY (f • V) p =
      (d% f p) (XY p) • V p + f p • XY_V p := hbr
  have hJf := VectorField.leibniz_identity_mlieBracket_apply
      (I := I) (𝕜 := ℝ) (M := M) (x := p)
      (hX.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
      (hY.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
      ((hf.smul_section hV).of_le
        (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
  have hJ := VectorField.leibniz_identity_mlieBracket_apply
      (I := I) (𝕜 := ℝ) (M := M) (x := p)
      (hX.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
      (hY.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
      (hV.of_le (by rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.LEInfty.out))
  have hJ' := hJf
  rw [hL, hXYf, hR] at hJ'
  have hJacV : X_YV p = XY_V p + Y_XV p := by
    exact hJ
  rw [hJacV] at hJ'
  dsimp [a, b] at hJ'
  simp only [smul_add] at hJ'
  have hcoef :
      ((d% a p) (X p) - (d% b p) (Y p) -
        (d% f p) (XY p)) • V p = 0 := by
    linear_combination (norm := module) hJ'
  simpa [a, b, XY] using hcoef

/-! Extract the scalar coefficient by testing against a local extension.  This is
the pointwise bridge needed when no globally smooth tangent section is available. -/
/-- A nonzero local extension extracts the scalar coefficient from the tested
vector identity. -/
lemma scalar_bracket_commutator_extend_at
    [Nontrivial EM]
    {f : M → ℝ} {X Y : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) :
    (d% (fun q => d% f q (Y q)) p) (X p) -
        (d% (fun q => d% f q (X q)) p) (Y p) =
      (d% f p) (VectorField.mlieBracket I X Y p) := by
  let t := trivializationAt EM (TangentSpace I) p
  have htp : p ∈ t.baseSet := by
    exact FiberBundle.mem_baseSet_trivializationAt' p
  let e : EM := Classical.choose (exists_ne (0 : EM))
  have he0 : e ≠ 0 := Classical.choose_spec (exists_ne (0 : EM))
  let v : TangentSpace I p := (t.linearEquivAt ℝ p htp).symm e
  have hv0 : v ≠ 0 := by
    intro hv
    have he : e = 0 := by
      calc
        e = (t.linearEquivAt ℝ p htp) v := by
          change e = (t.linearEquivAt ℝ p htp)
            ((t.linearEquivAt ℝ p htp).symm e)
          exact (t.linearEquivAt ℝ p htp).apply_symm_apply e |>.symm
        _ = (t.linearEquivAt ℝ p htp) 0 :=
          congrArg (t.linearEquivAt ℝ p htp) hv
        _ = 0 := map_zero _
    exact he0 he
  let V : (x : M) → TangentSpace I x := FiberBundle.extend EM v
  have hV : SmoothAt V p := by
    exact FiberBundle.contMDiffAt_extend I EM v
  have hmul := scalar_bracket_commutator_mul_at (p := p) hf hX hY hV
  have hmul' :
      ((d% (fun q => d% f q (Y q)) p) (X p) -
        (d% (fun q => d% f q (X q)) p) (Y p) -
        (d% f p) (VectorField.mlieBracket I X Y p)) • v = 0 := by
    simpa [V] using hmul
  have hscalar :
      ((d% (fun q => d% f q (Y q)) p) (X p) -
        (d% (fun q => d% f q (X q)) p) (Y p) -
        (d% f p) (VectorField.mlieBracket I X Y p)) = 0 := by
    exact (smul_eq_zero.mp hmul').resolve_right hv0
  exact sub_eq_zero.mp hscalar

/-! The extension argument is dimension-generic: in dimension zero, all tangent
fibers are trivial; otherwise a nonzero local extension extracts the coefficient. -/
omit [FiniteDimensional ℝ EM] in
/-- In a zero-dimensional model, every tangent fibre is subsingleton. -/
lemma tangent_eq_zero_of_subsingleton
    (hEM : Subsingleton EM) {q : M} (v : TangentSpace I q) : v = 0 := by
  let t := trivializationAt EM (TangentSpace I) q
  have hq : q ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' q
  apply (t.linearEquivAt ℝ q hq).injective
  exact hEM.elim _ _

/-- The manifold scalar bracket commutator, including the zero-dimensional
case. -/
lemma scalar_bracket_commutator_at
    {f : M → ℝ} {X Y : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) :
    (d% (fun q => d% f q (Y q)) p) (X p) -
        (d% (fun q => d% f q (X q)) p) (Y p) =
      (d% f p) (VectorField.mlieBracket I X Y p) := by
  rcases subsingleton_or_nontrivial EM with hEM | hEM
  · letI : Subsingleton EM := hEM
    have hXp : X p = 0 := tangent_eq_zero_of_subsingleton hEM _
    have hYp : Y p = 0 := tangent_eq_zero_of_subsingleton hEM _
    have hbp : VectorField.mlieBracket I X Y p = 0 :=
      tangent_eq_zero_of_subsingleton hEM _
    rw [hXp, hYp, hbp]
    simp
  · letI : Nontrivial EM := hEM
    exact scalar_bracket_commutator_extend_at hf hX hY

end ScalarCommutator
end Curvature
end Ch01
end MorganTianLib
