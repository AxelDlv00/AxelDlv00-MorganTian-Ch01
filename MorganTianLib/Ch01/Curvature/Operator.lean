import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic.FinCases
import MorganTianLib.Ch01.Curvature.Sectional

/-!
# The curvature operator on the exterior square

This is the fibrewise operator layer of Morgan--Tian Definition 1.7
(`morganTian2007`).  It uses only the pinned Mathlib universal property for
`⋀[ℝ]^2`; in particular, no unproved inner-product instance is installed on
the exterior power.  The metric bivector pairing is exposed as a symmetric
bilinear form and its decomposable-wedge evaluation is the normalization
`g(X,Z)g(Y,W)-g(X,W)g(Y,Z)`.

The construction is independent of coordinates and of the manifold producer.
The selected-extension tangent operator facade is kept in the direct-only
`Curvature.OperatorProvisional` module, with an explicit algebraic-curvature
witness; it is not imported here or by the stable intrinsic layer.

The normalization and positivity direction cross-check Morgan--Tian
Definition 1.7 (`morganTian2007`) and the algebraic curvature-form treatments
in do Carmo, Chapter 4 (`doCarmo1992`), and Petersen, Chapter 3
(`petersen2016`).  The only exterior-power facts used are the pinned
`LinearAlgebra.ExteriorPower.Basic` declarations
`exteriorPower.ιMulti`, `exteriorPower.alternatingMapLinearEquiv`, and
`exteriorPower.linearMap_ext`.
-/

noncomputable section

open exteriorPower
open Matrix Module
open scoped Matrix RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Curvature

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Alternating maps and the operator -/

/-- Turn an antisymmetric bilinear map into the alternating map on `Fin 2`.
This is the small bridge needed by `alternatingMapLinearEquiv`. -/
def bilinToAlt2 {N : Type*} [AddCommGroup N] [Module ℝ N]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] N)
    (hanti : ∀ x y, b x y = -b y x) :
    V [⋀^Fin 2]→ₗ[ℝ] N where
  toFun v := b (v 0) (v 1)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    have hzero : ∀ w : V, b w w = 0 := by
      intro w
      have h := hanti w w
      have h2 : (2 : ℝ) • b w w = 0 := by
        rw [two_smul]
        nth_rewrite 1 [h]
        exact neg_add_cancel _
      rcases smul_eq_zero.mp h2 with h0 | h0
      · exact absurd h0 (by norm_num)
      · exact h0
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hne | exact hij | exact hij.symm
    show b (v 0) (v 1) = 0
    rw [h01]
    exact hzero _

/-- Evaluation of the two-vector alternating bridge at a coordinate vector. -/
@[simp] theorem bilinToAlt2_apply {N : Type*} [AddCommGroup N] [Module ℝ N]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] N)
    (hanti : ∀ x y, b x y = -b y x) (v : Fin 2 → V) :
    bilinToAlt2 b hanti v = b (v 0) (v 1) := rfl

variable {B : V → V → V → V → ℝ}

/-- The last-pair bilinear map obtained by fixing the first curvature pair. -/
def curvBilinInner (hB : IsAlgebraicCurvature B) (x y : V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => B x y z w)
    (fun z₁ z₂ w => hB.add_third x y z₁ z₂ w)
    (fun c z w => by
      rw [hB.smul_third c x y z w, smul_eq_mul])
    (fun z w₁ w₂ => hB.add_fourth x y z w₁ w₂)
    (fun c z w => by
      rw [hB.smul_fourth c x y z w, smul_eq_mul])

/-- Evaluation of `curvBilinInner` recovers the original curvature form. -/
@[simp] theorem curvBilinInner_apply (hB : IsAlgebraicCurvature B)
    (x y z w : V) : curvBilinInner hB x y z w = B x y z w := rfl

/-- The alternating functional on the second exterior-square argument. -/
def curvInnerAlt (hB : IsAlgebraicCurvature B) (x y : V) :
    V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  bilinToAlt2 (curvBilinInner hB x y)
    (fun z w => hB.antisymm_last x y z w)

/-- Additivity of the alternating functional in its first fixed vector. -/
theorem curvInnerAlt_add_left (hB : IsAlgebraicCurvature B)
    (x₁ x₂ y : V) :
    curvInnerAlt hB (x₁ + x₂) y = curvInnerAlt hB x₁ y + curvInnerAlt hB x₂ y := by
  ext v
  simp [curvInnerAlt, curvBilinInner, hB.add_left]

/-- Homogeneity of the alternating functional in its first fixed vector. -/
theorem curvInnerAlt_smul_left (hB : IsAlgebraicCurvature B)
    (c : ℝ) (x y : V) :
    curvInnerAlt hB (c • x) y = c • curvInnerAlt hB x y := by
  ext v
  simp [curvInnerAlt, curvBilinInner, hB.smul_left]

/-- Additivity of the alternating functional in its second fixed vector. -/
theorem curvInnerAlt_add_right (hB : IsAlgebraicCurvature B)
    (x y₁ y₂ : V) :
    curvInnerAlt hB x (y₁ + y₂) = curvInnerAlt hB x y₁ + curvInnerAlt hB x y₂ := by
  ext v
  simp [curvInnerAlt, curvBilinInner, hB.add_second]

/-- Homogeneity of the alternating functional in its second fixed vector. -/
theorem curvInnerAlt_smul_right (hB : IsAlgebraicCurvature B)
    (c : ℝ) (x y : V) :
    curvInnerAlt hB x (c • y) = c • curvInnerAlt hB x y := by
  ext v
  simp [curvInnerAlt, curvBilinInner, hB.smul_second]

/-- First-pair antisymmetry of the alternating functional. -/
theorem curvInnerAlt_antisymm (hB : IsAlgebraicCurvature B) (x y : V) :
    curvInnerAlt hB x y = -curvInnerAlt hB y x := by
  ext v
  change B x y (v 0) (v 1) = -B y x (v 0) (v 1)
  exact hB.antisymm_first x y (v 0) (v 1)

/-- The bilinear map in the first exterior-square argument. -/
def curvBilinOuter (hB : IsAlgebraicCurvature B) :
    V →ₗ[ℝ] V →ₗ[ℝ] (⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => alternatingMapLinearEquiv (curvInnerAlt hB x y))
    (fun x₁ x₂ y => by
      rw [curvInnerAlt_add_left hB, map_add])
    (fun c x y => by
      rw [curvInnerAlt_smul_left hB, map_smul])
    (fun x y₁ y₂ => by
      rw [curvInnerAlt_add_right hB, map_add])
    (fun c x y => by
      rw [curvInnerAlt_smul_right hB, map_smul])

/-- Evaluation equation for the outer bilinear map. -/
@[simp] theorem curvBilinOuter_apply (hB : IsAlgebraicCurvature B)
    (x y : V) :
    curvBilinOuter hB x y = alternatingMapLinearEquiv (curvInnerAlt hB x y) := rfl

/-- The curvature operator `Rm` as a bilinear form on `⋀[ℝ]^2 V`, built via
the pinned `ExteriorPower.alternatingMapLinearEquiv` universal property
(Morgan--Tian Definition 1.7, `morganTian2007`). -/
def curvatureOperator (hB : IsAlgebraicCurvature B) :
    (⋀[ℝ]^2 V) →ₗ[ℝ] (⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :=
  alternatingMapLinearEquiv
    (bilinToAlt2 (curvBilinOuter hB)
      (fun x y => by
        rw [curvBilinOuter_apply hB x y, curvBilinOuter_apply hB y x,
          curvInnerAlt_antisymm hB x y, map_neg]))

/-- The operator evaluates to the original `(0,4)` form on decomposable
wedge generators. -/
@[simp] theorem curvatureOperator_ιMulti (hB : IsAlgebraicCurvature B)
    (x y z w : V) :
    curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, w]) = B x y z w := by
  rw [curvatureOperator, alternatingMapLinearEquiv_apply_ιMulti, bilinToAlt2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, curvBilinOuter_apply,
    alternatingMapLinearEquiv_apply_ιMulti, curvInnerAlt, bilinToAlt2_apply,
    curvBilinInner_apply]

/-- Pair symmetry of the curvature operator, proved on the decomposable
generators of the exterior power and extended by `exteriorPower.linearMap_ext`. -/
theorem curvatureOperator_symm (hB : IsAlgebraicCurvature B)
    (φ ψ : ⋀[ℝ]^2 V) :
    curvatureOperator hB φ ψ = curvatureOperator hB ψ φ := by
  have hgen : ∀ a b : Fin 2 → V,
      curvatureOperator hB (ιMulti ℝ 2 a) (ιMulti ℝ 2 b) =
        curvatureOperator hB (ιMulti ℝ 2 b) (ιMulti ℝ 2 a) := by
    intro a b
    have ha : a = ![a 0, a 1] := by
      ext i
      fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by
      ext i
      fin_cases i <;> rfl
    rw [ha, hb, curvatureOperator_ιMulti, curvatureOperator_ιMulti,
      hB.pair_swap]
  have hflip : curvatureOperator hB = (curvatureOperator hB).flip := by
    ext a b
    simpa [LinearMap.flip_apply] using hgen a b
  rw [show curvatureOperator hB φ ψ = (curvatureOperator hB).flip φ ψ from
      LinearMap.congr_fun (LinearMap.congr_fun hflip φ) ψ,
    LinearMap.flip_apply]

/-- The operator quadratic form on a decomposable wedge is the diagonal
curvature component. -/
theorem curvatureOperator_wedge_self (hB : IsAlgebraicCurvature B)
    (x y : V) :
    curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y]) = B x y x y :=
  curvatureOperator_ιMulti hB x y x y

/-- Sectional curvature is the operator quadratic form divided by the Gram
determinant. -/
theorem sectionalCurvature_eq_curvatureOperator
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {B : W → W → W → W → ℝ} (hB : IsAlgebraicCurvature B) (x y : W) :
    sectionalCurvature B x y =
      curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y]) /
        wedgeSq x y := by
  unfold sectionalCurvature
  rw [curvatureOperator_wedge_self hB]

/-! ### The metric normalization and positivity -/

/-- The metric wedge pairing regarded as a bilinear form on the exterior
square. -/
def wedgeInnerOperator {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] :
    (⋀[ℝ]^2 W) →ₗ[ℝ] (⋀[ℝ]^2 W →ₗ[ℝ] ℝ) :=
  curvatureOperator (isAlgebraicCurvature_wedgeInner (W := W))

/-- Decomposable evaluation of the metric wedge bilinear form. -/
@[simp] theorem wedgeInnerOperator_ιMulti
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (x y z w : W) :
    wedgeInnerOperator (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, w]) =
      wedgeInner x y z w := by
  exact curvatureOperator_ιMulti (isAlgebraicCurvature_wedgeInner (W := W)) x y z w

/-- Symmetry of the metric wedge bilinear form. -/
theorem wedgeInnerOperator_symm
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (phi psi : ⋀[ℝ]^2 W) :
    wedgeInnerOperator phi psi = wedgeInnerOperator psi phi := by
  exact curvatureOperator_symm
    (isAlgebraicCurvature_wedgeInner (W := W)) phi psi

/-- Nonnegativity of the metric wedge form on decomposable self-pairs. -/
theorem wedgeInnerOperator_wedge_self_nonneg
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  (x y : W) :
    0 ≤ wedgeInnerOperator (ιMulti ℝ 2 ![x, y])
      (ιMulti ℝ 2 ![x, y]) := by
  rw [wedgeInnerOperator_ιMulti, wedgeInner_self]
  exact wedgeSq_nonneg x y

/-- Nonnegative curvature operator, expressed as nonnegativity of the induced
bilinear form on every exterior-square argument. -/
def HasNonnegativeCurvatureOperator (hB : IsAlgebraicCurvature B) : Prop :=
  ∀ φ : ⋀[ℝ]^2 V, 0 ≤ curvatureOperator hB φ φ

/-- Positive curvature operator.  The implication to sectional positivity below
retains explicit nonzero-generator and nonzero-Gram hypotheses because the
pinned Basic exterior-power API has no wedge/nondegeneracy equivalence. -/
def HasPositiveCurvatureOperator (hB : IsAlgebraicCurvature B) : Prop :=
  ∀ φ : ⋀[ℝ]^2 V, φ ≠ 0 → 0 < curvatureOperator hB φ φ

/-- A nonnegative curvature operator gives nonnegative sectional curvature,
with the zero-Gram case handled by Lean's quotient convention. -/
theorem sectionalCurvature_nonneg_of_hasNonnegativeCurvatureOperator
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {B : W → W → W → W → ℝ} (hB : IsAlgebraicCurvature B)
    (h : HasNonnegativeCurvatureOperator hB) (x y : W) :
    0 ≤ sectionalCurvature B x y := by
  rw [sectionalCurvature_eq_curvatureOperator hB]
  exact div_nonneg (h _) (wedgeSq_nonneg x y)

/-- A positive curvature operator gives positive sectional curvature when the
decomposable generator and its Gram determinant are explicitly nonzero. -/
theorem sectionalCurvature_pos_of_hasPositiveCurvatureOperator
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {B : W → W → W → W → ℝ} (hB : IsAlgebraicCurvature B)
    (h : HasPositiveCurvatureOperator hB) {x y : W}
    (hφ : ιMulti ℝ 2 ![x, y] ≠ 0) (hw : wedgeSq x y ≠ 0) :
    0 < sectionalCurvature B x y := by
  rw [sectionalCurvature_eq_curvatureOperator hB]
  exact div_pos (h _ hφ) ((wedgeSq_nonneg x y).lt_of_ne (Ne.symm hw))

/-! ### Model and low-dimensional regressions -/

/-- Decomposable evaluation of the constant-curvature model operator. -/
theorem modelCurvatureOperator_ιMulti
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (lam : ℝ) (x y z w : W) :
    curvatureOperator (isAlgebraicCurvature_modelCurvature4 (W := W) lam)
        (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, w]) =
      modelCurvature4 lam x y z w := by
  exact curvatureOperator_ιMulti
    (isAlgebraicCurvature_modelCurvature4 (W := W) lam) x y z w

/-- The model operator's quadratic value on a decomposable wedge. -/
theorem modelCurvatureOperator_wedge_self
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (lam : ℝ) (x y : W) :
    curvatureOperator (isAlgebraicCurvature_modelCurvature4 (W := W) lam)
        (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y]) =
      lam * wedgeSq x y := by
  rw [modelCurvatureOperator_ιMulti]
  simp [modelCurvature4, wedgeSq, real_inner_comm]

/-- The full model curvature operator is the scalar multiple `lam` of the
metric wedge form on the whole exterior square, not only on decomposable
wedges. -/
theorem modelCurvatureOperator_eq_smul_wedgeInnerOperator
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (lam : ℝ) :
    curvatureOperator (isAlgebraicCurvature_modelCurvature4 (W := W) lam) =
      lam • wedgeInnerOperator (W := W) := by
  ext a b
  have ha : a = ![a 0, a 1] := by
    ext v
    fin_cases v <;> rfl
  have hb : b = ![b 0, b 1] := by
    ext v
    fin_cases v <;> rfl
  simp only [LinearMap.compAlternatingMap_apply]
  rw [ha, hb, curvatureOperator_ιMulti]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [wedgeInnerOperator_ιMulti]
  simp [modelCurvature4, wedgeInner, real_inner_comm]

/-- In one dimension the model operator vanishes on every decomposable
generator, recording the vacuity of two-plane curvature. -/
theorem modelCurvatureOperator_fin_one_ιMulti
    (lam : ℝ) (x y z w : EuclideanSpace ℝ (Fin 1)) :
    curvatureOperator
        (isAlgebraicCurvature_modelCurvature4 (W := EuclideanSpace ℝ (Fin 1)) lam)
        (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, w]) = 0 := by
  rw [modelCurvatureOperator_ιMulti]
  exact modelCurvature4_fin_one lam x y z w

/-- In one dimension the entire model curvature operator is zero, not merely
its decomposable evaluations. -/
theorem modelCurvatureOperator_fin_one
    (lam : ℝ) (phi psi : ⋀[ℝ]^2 (EuclideanSpace ℝ (Fin 1))) :
    curvatureOperator
        (isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 1)) lam) phi psi = 0 := by
  have hzero : curvatureOperator
        (isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 1)) lam) = 0 := by
    refine exteriorPower.linearMap_ext ?_
    apply DFunLike.ext _ _
    intro a
    refine exteriorPower.linearMap_ext ?_
    apply DFunLike.ext _ _
    intro b
    have ha : a = ![a 0, a 1] := by
      ext i
      fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by
      ext i
      fin_cases i <;> rfl
    rw [ha, hb]
    simp only [LinearMap.compAlternatingMap_apply]
    rw [curvatureOperator_ιMulti]
    exact modelCurvature4_fin_one lam (a 0) (a 1) (b 0) (b 1)
  rw [hzero]
  rfl

/-- In dimension zero the model curvature operator is zero on the entire
exterior square. -/
theorem modelCurvatureOperator_fin_zero
    (lam : ℝ) (phi psi : ⋀[ℝ]^2 (EuclideanSpace ℝ (Fin 0))) :
    curvatureOperator
        (isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 0)) lam) phi psi = 0 := by
  have hzero : curvatureOperator
        (isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 0)) lam) = 0 := by
    refine exteriorPower.linearMap_ext ?_
    apply DFunLike.ext _ _
    intro a
    refine exteriorPower.linearMap_ext ?_
    apply DFunLike.ext _ _
    intro b
    have ha : a = ![a 0, a 1] := by
      ext i
      fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by
      ext i
      fin_cases i <;> rfl
    rw [ha, hb]
    simp only [LinearMap.compAlternatingMap_apply]
    rw [curvatureOperator_ιMulti]
    exact modelCurvature4_fin_zero lam (a 0) (a 1) (b 0) (b 1)
  rw [hzero]
  rfl

/-- The zero-curvature model has the zero curvature operator. -/
@[simp] theorem modelCurvatureOperator_zero
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (phi psi : ⋀[ℝ]^2 W) :
    curvatureOperator (isAlgebraicCurvature_modelCurvature4 (W := W) 0) phi psi = 0 := by
  rw [modelCurvatureOperator_eq_smul_wedgeInnerOperator]
  simp

end Curvature
end Ch01
end MorganTianLib
