import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter 1 curvature convention kernel

This module fixes Morgan--Tian's curvature sign and argument order on a real
inner-product space, independently of any connection or manifold construction.
The model operator is

`R_K(X,Y)W = K (inner Y W * X - inner X W * Y)`,

and the associated four-tensor uses the third slot for metric pairing and the
fourth slot as the operator input:

`R4_K(X,Y,Z,W) = inner (R_K(X,Y)W) Z`.

The component, Jacobi, index-form, sectional, and second/fourth-slot contraction
theorems below are sign regressions for the future manifold curvature API.  They
do not assert that a manifold has constant curvature or define geometric
sectional or Ricci curvature.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
Definition 1.4 and the constant-sectional-curvature formula on pp. 37--39,
the Jacobi and second-variation formulas on pp. 43--44, and Definition 1.8 on
p. 39.
-/

open Module
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
