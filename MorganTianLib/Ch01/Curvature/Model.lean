import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FinCases

/-!
# Chapter 1 curvature convention model

This module fixes Morgan--Tian's curvature sign and argument order on a real
inner-product space, independently of any connection or manifold construction.

The connection-produced manifold facade is kept in
`MorganTianLib.Ch01.Curvature.Manifold`; this file is the stable model-only
import.
The model operator is

`R_K(X,Y)W = K (inner Y W * X - inner X W * Y)`,

and the associated four-tensor uses the third slot for metric pairing and the
fourth slot as the operator input:

`R4_K(X,Y,Z,W) = inner (R_K(X,Y)W) Z`.

The component, Jacobi, index-form, sectional, and algebraic slot-sign probes
below are sign regressions for the future manifold curvature API.  They do not
assert that a manifold has constant curvature or define geometric sectional or
Ricci curvature.  The finite-basis second/fourth-slot contraction theorem is
an inherited S06 model-kernel declaration; this S08 module adds no new Ricci or
scalar-curvature API.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
`morganTian2007`, Definition 1.4 and the constant-sectional-curvature formula on pp. 37--39,
the Jacobi and second-variation formulas on pp. 43--44, and Definition 1.8 on
p. 39.
-/

open Module
open Matrix
open scoped RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constant-curvature model operator in Morgan--Tian's sign convention:
`modelCurvature K X Y W = R_K(X,Y)W`.  The last argument is the vector on
which the curvature operator acts. -/
def modelCurvature (K : ℝ) (X Y W : E) : E :=
  K • (inner ℝ Y W • X - inner ℝ X W • Y)

/-- The constant-curvature model four-tensor in Morgan--Tian's positional
order.  Its third argument is the metric-pairing slot and its fourth argument
is the input of `modelCurvature`. -/
def modelCurvature4 (K : ℝ) (X Y Z W : E) : ℝ :=
  K * (inner ℝ X Z * inner ℝ Y W - inner ℝ X W * inner ℝ Y Z)

/-- Pairing the output of `modelCurvature K X Y W` with the third argument
`Z` gives the model four-tensor.  This fixes the last-two-slot order of
Morgan--Tian, Definition 1.4, pp. 37--38. -/
theorem modelCurvature4_eq_inner_modelCurvature (K : ℝ) (X Y Z W : E) :
    modelCurvature4 K X Y Z W = inner ℝ (modelCurvature K X Y W) Z := by
  simp only [modelCurvature, modelCurvature4, real_inner_smul_left,
    inner_sub_left]
  ring

/-- The exact component formula
`R_ijkl = K (g_ik g_jl - g_il g_jk)`.  The family `e` need not be
orthonormal: this is the model tensor evaluated on four indexed vectors. -/
theorem modelCurvature4_component {ι : Type*} (e : ι → E)
    (K : ℝ) (i j k l : ι) :
    modelCurvature4 K (e i) (e j) (e k) (e l) =
      K * (inner ℝ (e i) (e k) * inner ℝ (e j) (e l) -
        inner ℝ (e i) (e l) * inner ℝ (e j) (e k)) :=
  rfl

/-- Jacobi-sign regression: if `V` is unit and `J` is perpendicular to
`V`, then `R_K(J,V)V = K J`.  Thus the future equation
`D^2 J + R(J,V)V = 0` has the spherical sign for positive `K`. -/
theorem modelCurvature_apply_unit_orthogonal (K : ℝ) (J V : E)
    (hV : ‖V‖ = 1) (hJV : inner ℝ J V = 0) :
    modelCurvature K J V V = K • J := by
  rw [modelCurvature, real_inner_self_eq_norm_sq, hV]
  simp only [one_pow, one_smul, hJV, zero_smul, sub_zero]

/-- Index-form sign regression for a unit `V` perpendicular to `J`:
the curvature contribution is `-K * ‖J‖ ^ 2`. -/
theorem neg_inner_modelCurvature_apply_unit_orthogonal (K : ℝ) (J V : E)
    (hV : ‖V‖ = 1) (hJV : inner ℝ J V = 0) :
    -inner ℝ (modelCurvature K J V V) J = -K * ‖J‖ ^ 2 := by
  rw [modelCurvature_apply_unit_orthogonal K J V hV hJV,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

/-- Sectional-sign regression: on an orthonormal pair `X, Y`, the model
four-tensor satisfies `R4_K(X,Y,X,Y) = K`. -/
theorem modelCurvature4_apply_orthonormal (K : ℝ) (X Y : E)
    (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1) (hXY : inner ℝ X Y = 0) :
    modelCurvature4 K X Y X Y = K := by
  have hXX : inner ℝ X X = 1 := by
    rw [real_inner_self_eq_norm_sq, hX]
    norm_num
  have hYY : inner ℝ Y Y = 1 := by
    rw [real_inner_self_eq_norm_sq, hY]
    norm_num
  have hYX : inner ℝ Y X = 0 := by
    rw [real_inner_comm, hXY]
  rw [modelCurvature4, hXX, hYY, hXY, hYX]
  ring

/-- The flat model has identically zero vector-valued curvature. -/
@[simp] theorem modelCurvature_zero (X Y W : E) :
    modelCurvature 0 X Y W = 0 := by
  simp [modelCurvature]

/-- The flat model has identically zero four-tensor. -/
@[simp] theorem modelCurvature4_zero (X Y Z W : E) :
    modelCurvature4 0 X Y Z W = 0 := by
  simp [modelCurvature4]

/-! ### Explicit low-dimensional and component probes -/

/-- Every model component vanishes in dimension zero. -/
theorem modelCurvature4_fin_zero (K : ℝ)
    (X Y Z W : EuclideanSpace ℝ (Fin 0)) :
    modelCurvature4 K X Y Z W = 0 := by
  simp [modelCurvature4, Subsingleton.elim X (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim Y (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim Z (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim W (0 : EuclideanSpace ℝ (Fin 0))]

/-- Every diagonal two-plane component vanishes in dimension one. -/
theorem modelCurvature4_fin_one_diag (K : ℝ)
    (X Y : EuclideanSpace ℝ (Fin 1)) :
    modelCurvature4 K X Y X Y = 0 := by
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hX : X = X 0 • e := by
    apply PiLp.ext
    intro i
    fin_cases i
    simp [e]
  have hY : Y = Y 0 • e := by
    apply PiLp.ext
    intro i
    fin_cases i
    simp [e]
  rw [hX, hY, modelCurvature4, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
  have he : inner ℝ e e = 1 := by
    have hn : ‖e‖ = 1 := by simp [e]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  simp only [real_inner_smul_left, real_inner_smul_right, he]
  ring

/-- In one dimension every four-slot model component vanishes, so there is no
nonzero two-plane. -/
theorem modelCurvature4_fin_one (K : ℝ)
    (X Y Z W : EuclideanSpace ℝ (Fin 1)) :
    modelCurvature4 K X Y Z W = 0 := by
  let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have hvec : ∀ U : EuclideanSpace ℝ (Fin 1), U = U 0 • e := by
    intro U
    apply PiLp.ext
    intro i
    fin_cases i
    simp [e]
  have he : inner ℝ e e = 1 := by
    have hn : ‖e‖ = 1 := by simp [e]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  rw [hvec X, hvec Y, hvec Z, hvec W]
  rw [modelCurvature4]
  simp only [real_inner_smul_left, real_inner_smul_right, he]
  ring

/-- A two-dimensional basis probe fixes the scaling, last-slot sign, and
Morgan--Tian component order of the constant-curvature kernel. -/
theorem modelCurvature4_fin_two_component_probe (K : ℝ) :
    let e₀ := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
    let e₁ := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
    modelCurvature4 K ((2 : ℝ) • e₀) e₁ e₀ e₁ = 2 * K ∧
      modelCurvature4 K ((2 : ℝ) • e₀) e₁ e₁ e₀ = -(2 * K) := by
  dsimp
  have h00 : inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 0)
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 0) = 1 := by
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_one 0
  have h11 : inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 1)
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 1) = 1 := by
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_one 1
  have h01 : inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 0)
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 1) = 0 := by
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_zero (by decide)
  have h10 : inner ℝ ((EuclideanSpace.basisFun (Fin 2) ℝ) 1)
      ((EuclideanSpace.basisFun (Fin 2) ℝ) 0) = 0 := by
    rw [real_inner_comm, h01]
  constructor
  · rw [modelCurvature4, real_inner_smul_left, real_inner_smul_left,
      h00, h11, h01, h10]
    ring
  · rw [modelCurvature4, real_inner_smul_left, real_inner_smul_left,
      h00, h11, h01, h10]
    ring

/-! A nonuniform component probe.  This is intentionally a finite-dimensional
algebraic metric family, not a claim about a manifold: varying `t` changes one
coordinate weight, while the two displayed components detect both the frozen
third/fourth slot order and the sign of the antisymmetry. -/

/-- A two-coordinate algebraic metric whose first coordinate has weight `t`. -/
def componentProbeMetric (t : ℝ) (x y : Fin 2 → ℝ) : ℝ :=
  t * x 0 * y 0 + x 1 * y 1

/-- The determinant curvature form induced by `componentProbeMetric`. -/
def componentProbeCurvature4 (t : ℝ) (x y z w : Fin 2 → ℝ) : ℝ :=
  componentProbeMetric t x z * componentProbeMetric t y w -
    componentProbeMetric t x w * componentProbeMetric t y z

/-- The weighted component probe detects reversal of the final curvature
slots through an explicit sign change. -/
theorem componentProbeCurvature4_slots (t : ℝ) :
    let e₀ : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
    let e₁ : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0
    componentProbeCurvature4 t e₀ e₁ e₀ e₁ = t ∧
      componentProbeCurvature4 t e₀ e₁ e₁ e₀ = -t := by
  dsimp [componentProbeCurvature4, componentProbeMetric]
  norm_num

/-- Ricci-slot regression: contraction of the second and fourth slots against
a finite orthonormal basis is
`(finrank Real E - 1) * K * inner X Y`.

No nontriviality or lower dimension bound is needed.  In dimension zero the
inner product on the right is zero; in dimension one the displayed coefficient
is zero.  A finitely indexed `OrthonormalBasis` is the only finiteness input. -/
theorem sum_modelCurvature4_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (K : ℝ) (X Y : E) :
    ∑ i, modelCurvature4 K X (b i) Y (b i) =
      ((finrank ℝ E : ℝ) - 1) * K * inner ℝ X Y := by
  classical
  simp_rw [modelCurvature4, b.inner_eq_one, mul_one]
  calc
    ∑ i, K * (inner ℝ X Y - inner ℝ X (b i) * inner ℝ (b i) Y) =
        K * ((Fintype.card ι : ℝ) * inner ℝ X Y - inner ℝ X Y) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib,
        b.sum_inner_mul_inner, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ]
    _ = ((finrank ℝ E : ℝ) - 1) * K * inner ℝ X Y := by
      rw [← finrank_eq_card_basis b.toBasis]
      ring

end Curvature
end Ch01
end MorganTianLib
