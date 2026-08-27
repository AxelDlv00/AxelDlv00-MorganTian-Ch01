import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import MorganTianLib.Ch01.Curvature.Model

/-!
# Sectional curvature and the curvature operator

This module is the connection-free intrinsic algebraic boundary for
Morgan--Tian Chapter 1, Definitions 1.6--1.7 (`morganTian2007`).  It works
fibrewise on a real inner-product space (and, for a plain symmetric bilinear
form).  The selected-extension tangent adapters live in the direct-only
`Curvature.SectionalProvisional` module; they are intentionally absent from
this intrinsic import.

The sign and slot order are the repository convention
`curvature4 X Y Z W = g (curvature X Y W) Z`, so the constant model is
`lambda (g X Z * g Y W - g X W * g Y Z)`.  The standard sphere and hyperbolic
manifold constructions are intentionally deferred to the later model-manifold
milestone.

Cross-checks: do Carmo, *Riemannian Geometry*, Chapter 4, Section 3 (the
Gram-determinant and algebraic-curvature-form statements), bibliography key
`doCarmo1992`, and Petersen, *Riemannian Geometry*, Chapter 3 curvature
symmetries, key `petersen2016`; the checked repository prior-art files record
the corresponding `curvatureTensorFour_antisymm_right` and `pairSwap` routes.
The exterior-power declarations use the pinned Mathlib
`LinearAlgebra.ExteriorPower.Basic` universal-property API.
-/

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Algebraic curvature forms -/

/-- An algebraic `(0,4)` curvature form.  The first-slot linearity, the two
pair antisymmetries, and first Bianchi are the minimal algebraic hypotheses
used below; all remaining slot linearity and pair interchange are derived.
The Bianchi field uses the conventional `(1,2,3)` cycle (slot four fixed),
matching the algebraic form in do Carmo Chapter 4, Section 3
(`doCarmo1992`). -/
structure IsAlgebraicCurvature (B : V → V → V → V → ℝ) : Prop where
  add_left : ∀ x₁ x₂ y z w, B (x₁ + x₂) y z w = B x₁ y z w + B x₂ y z w
  smul_left : ∀ c x y z w, B (c • x) y z w = c * B x y z w
  antisymm_first : ∀ x y z w, B x y z w = -B y x z w
  antisymm_last : ∀ x y z w, B x y z w = -B x y w z
  bianchi : ∀ x y z w, B x y z w + B y z x w + B z x y w = 0

namespace IsAlgebraicCurvature

variable {B B' : V → V → V → V → ℝ}

/-- Pair interchange, derived from the two antisymmetries and four Bianchi
instances (Petersen Chapter 3, `petersen2016`). -/
theorem pair_swap (hB : IsAlgebraicCurvature B) (x y z w : V) :
    B x y z w = B z w x y := by
  have h1 := hB.bianchi y z x w
  have h2 := hB.bianchi z x w y
  have h3 := hB.bianchi x w y z
  have h4 := hB.bianchi w y z x
  have a1 := hB.antisymm_last y z x w
  have a2 := hB.antisymm_last z x y w
  have a3 := hB.antisymm_last x w z y
  have a4 := hB.antisymm_last w y z x
  have a5 := hB.antisymm_last x y z w
  have a6 := hB.antisymm_last w z x y
  have b1 := hB.antisymm_first y x w z
  have b2 := hB.antisymm_first z w y x
  have b3 := hB.antisymm_first w z x y
  linarith

/-- Additivity in the second slot, derived from first-pair antisymmetry. -/
theorem add_second (hB : IsAlgebraicCurvature B) (x y₁ y₂ z w : V) :
    B x (y₁ + y₂) z w = B x y₁ z w + B x y₂ z w := by
  rw [hB.antisymm_first x (y₁ + y₂) z w, hB.add_left,
    hB.antisymm_first y₁ x z w, hB.antisymm_first y₂ x z w]
  ring

/-- Additivity in the third slot, transported across pair interchange. -/
theorem add_third (hB : IsAlgebraicCurvature B) (x y z₁ z₂ w : V) :
    B x y (z₁ + z₂) w = B x y z₁ w + B x y z₂ w := by
  rw [hB.pair_swap x y (z₁ + z₂) w, hB.add_left,
    hB.pair_swap z₁ w x y, hB.pair_swap z₂ w x y]

/-- Additivity in the fourth slot, derived from last-pair antisymmetry. -/
theorem add_fourth (hB : IsAlgebraicCurvature B) (x y z w₁ w₂ : V) :
    B x y z (w₁ + w₂) = B x y z w₁ + B x y z w₂ := by
  rw [hB.antisymm_last x y z (w₁ + w₂), hB.add_third,
    hB.antisymm_last x y w₁ z, hB.antisymm_last x y w₂ z]
  ring

/-- Homogeneity in the second slot. -/
theorem smul_second (hB : IsAlgebraicCurvature B) (c : ℝ) (x y z w : V) :
    B x (c • y) z w = c * B x y z w := by
  rw [hB.antisymm_first x (c • y) z w, hB.smul_left c y x z w,
    hB.antisymm_first y x z w]
  ring

/-- Homogeneity in the third slot, transported across pair interchange. -/
theorem smul_third (hB : IsAlgebraicCurvature B) (c : ℝ) (x y z w : V) :
    B x y (c • z) w = c * B x y z w := by
  rw [hB.pair_swap x y (c • z) w, hB.smul_left c z w x y,
    hB.pair_swap z w x y]

/-- Homogeneity in the fourth slot. -/
theorem smul_fourth (hB : IsAlgebraicCurvature B) (c : ℝ) (x y z w : V) :
    B x y z (c • w) = c * B x y z w := by
  rw [hB.antisymm_last x y z (c • w), hB.smul_third c x y w z,
    hB.antisymm_last x y w z]
  ring

/-- A repeated first pair evaluates to zero. -/
theorem self_first (hB : IsAlgebraicCurvature B) (x z w : V) : B x x z w = 0 := by
  have h := hB.antisymm_first x x z w
  linarith

/-- A repeated last pair evaluates to zero. -/
theorem self_last (hB : IsAlgebraicCurvature B) (x y z : V) : B x y z z = 0 := by
  have h := hB.antisymm_last x y z z
  linarith

/-- A zero first argument evaluates to zero. -/
theorem zero_first (hB : IsAlgebraicCurvature B) (y z w : V) : B 0 y z w = 0 := by
  have h := hB.smul_left 0 y y z w
  simpa using h

/-- A zero second argument evaluates to zero. -/
theorem zero_second (hB : IsAlgebraicCurvature B) (x z w : V) : B x 0 z w = 0 := by
  have h := hB.smul_second 0 x x z w
  simpa using h

/-- A zero third argument evaluates to zero. -/
theorem zero_third (hB : IsAlgebraicCurvature B) (x y w : V) : B x y 0 w = 0 := by
  have h := hB.smul_third 0 x y (0 : V) w
  simpa using h

/-- A zero fourth argument evaluates to zero. -/
theorem zero_fourth (hB : IsAlgebraicCurvature B) (x y z : V) : B x y z 0 = 0 := by
  have h := hB.smul_fourth 0 x y z z
  simpa using h

/-- The difference of two algebraic curvature forms is algebraic. -/
theorem sub (hB : IsAlgebraicCurvature B) (hB' : IsAlgebraicCurvature B') :
    IsAlgebraicCurvature (fun x y z w => B x y z w - B' x y z w) where
  add_left x₁ x₂ y z w := by rw [hB.add_left, hB'.add_left]; ring
  smul_left c x y z w := by rw [hB.smul_left, hB'.smul_left]; ring
  antisymm_first x y z w := by rw [hB.antisymm_first, hB'.antisymm_first]; ring
  antisymm_last x y z w := by rw [hB.antisymm_last, hB'.antisymm_last]; ring
  bianchi x y z w := by linarith [hB.bianchi x y z w, hB'.bianchi x y z w]

/-- Scalar multiplication preserves the algebraic curvature laws. -/
theorem smul (hB : IsAlgebraicCurvature B) (c : ℝ) :
    IsAlgebraicCurvature (fun x y z w => c * B x y z w) where
  add_left x₁ x₂ y z w := by rw [hB.add_left]; ring
  smul_left c' x y z w := by rw [hB.smul_left]; ring
  antisymm_first x y z w := by rw [hB.antisymm_first]; ring
  antisymm_last x y z w := by rw [hB.antisymm_last]; ring
  bianchi x y z w := by linear_combination c * hB.bianchi x y z w

/-- The diagonal values determine an algebraic curvature form. -/
theorem eq_zero_of_diag (hB : IsAlgebraicCurvature B)
    (h0 : ∀ x y, B x y x y = 0) : ∀ x y z w, B x y z w = 0 := by
  have step1 : ∀ x y z, B x y z y = 0 := by
    intro x y z
    have h := h0 (x + z) y
    rw [hB.add_left, hB.add_third, hB.add_third, h0 x y, h0 z y,
      hB.pair_swap z y x y] at h
    linarith
  have cyc : ∀ x y z w, B x y z w = B y z x w := by
    intro x y z w
    have h := step1 x (y + w) z
    rw [hB.add_second, hB.add_fourth, hB.add_fourth, step1 x y z,
      step1 x w z] at h
    have ht : B x w z y = -B y z x w := by
      rw [hB.pair_swap, hB.antisymm_first]
    linarith
  intro x y z w
  have hb := hB.bianchi x y z w
  have hc1 := cyc x y z w
  have hc2 := cyc y z x w
  linarith

/-- Equality on all diagonal curvature components implies equality everywhere. -/
theorem ext (hB : IsAlgebraicCurvature B) (hB' : IsAlgebraicCurvature B')
    (hdiag : ∀ x y, B x y x y = B' x y x y) :
    ∀ x y z w, B x y z w = B' x y z w := by
  have hd := hB.sub hB'
  intro x y z w
  have hz := hd.eq_zero_of_diag (fun a b => by simp [hdiag a b]) x y z w
  linarith

/-- Determinant change-of-generators in the first two slots. -/
theorem bilin_det_12 (hB : IsAlgebraicCurvature B) (a b c d : ℝ)
    (x y z w : V) :
    B (a • x + b • y) (c • x + d • y) z w =
      (a * d - b * c) * B x y z w := by
  rw [hB.add_left (a • x) (b • y) (c • x + d • y) z w,
    hB.add_second (a • x) (c • x) (d • y) z w,
    hB.add_second (b • y) (c • x) (d • y) z w,
    hB.smul_left a x (c • x) z w, hB.smul_left a x (d • y) z w,
    hB.smul_left b y (c • x) z w, hB.smul_left b y (d • y) z w,
    hB.smul_second c x x z w, hB.smul_second d x y z w,
    hB.smul_second c y x z w, hB.smul_second d y y z w,
    hB.self_first x z w, hB.self_first y z w, hB.antisymm_first y x z w]
  ring

/-- Determinant change-of-generators in the last two slots. -/
theorem bilin_det_34 (hB : IsAlgebraicCurvature B) (a b c d : ℝ)
    (x y z w : V) :
    B x y (a • z + b • w) (c • z + d • w) =
      (a * d - b * c) * B x y z w := by
  rw [hB.add_third x y (a • z) (b • w) (c • z + d • w),
    hB.add_fourth x y (a • z) (c • z) (d • w),
    hB.add_fourth x y (b • w) (c • z) (d • w),
    hB.smul_third a x y z (c • z), hB.smul_third a x y z (d • w),
    hB.smul_third b x y w (c • z), hB.smul_third b x y w (d • w),
    hB.smul_fourth c x y z z, hB.smul_fourth d x y z w,
    hB.smul_fourth c x y w z, hB.smul_fourth d x y w w,
    hB.self_last x y z, hB.self_last x y w, hB.antisymm_last x y w z]
  ring

/-- Simultaneous two-slot change of generators scales a diagonal value by the
square of the determinant. -/
theorem diag_changeBasis (hB : IsAlgebraicCurvature B) (a b c d : ℝ)
    (x y : V) :
    B (a • x + b • y) (c • x + d • y)
        (a • x + b • y) (c • x + d • y) =
      (a * d - b * c) ^ 2 * B x y x y := by
  rw [hB.bilin_det_12, hB.bilin_det_34]
  ring

end IsAlgebraicCurvature

/-! ### Metric model and sectional curvature -/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The squared Gram determinant `|x ∧ y|²` used to normalize sectional
curvature (Morgan--Tian Definition 1.6, `morganTian2007`; do Carmo, Ch. 4,
§3, as cross-checked by `wedgeSq_pos_iff_linearIndependent`). -/
def wedgeSq (x y : W) : ℝ :=
  inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ x y

/-- Unfolding equation for the Gram determinant. -/
@[simp] theorem wedgeSq_self (x y : W) :
    wedgeSq x y = inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ x y := rfl

/-- The metric bivector pairing `g(x∧y,z∧w)`, with the source's third/fourth
slot order.  It is kept as a plain scalar form because the pinned Mathlib
exterior-power API does not install an inner-product instance on `⋀²W`. -/
def wedgeInner (x y z w : W) : ℝ :=
  inner ℝ x z * inner ℝ y w - inner ℝ x w * inner ℝ y z

/-- The metric bivector pairing restricts to the Gram determinant on a
decomposable self-pair. -/
theorem wedgeInner_self (x y : W) : wedgeInner x y x y = wedgeSq x y := by
  simp only [wedgeInner, wedgeSq]
  rw [real_inner_comm x y]

/-- The metric bivector pairing satisfies the algebraic curvature identities. -/
theorem isAlgebraicCurvature_wedgeInner :
    IsAlgebraicCurvature (wedgeInner (W := W)) where
  add_left x₁ x₂ y z w := by
    simp only [wedgeInner, inner_add_left]
    ring
  smul_left c x y z w := by
    simp only [wedgeInner, real_inner_smul_left]
    ring
  antisymm_first x y z w := by
    simp only [wedgeInner]
    ring
  antisymm_last x y z w := by
    simp only [wedgeInner]
    ring
  bianchi x y z w := by
    simp only [wedgeInner]
    rw [real_inner_comm x y, real_inner_comm x z, real_inner_comm y z]
    ring

/-! The same determinant construction for a plain symmetric bilinear form.
This version is used by the bundled tangent-space metric, which deliberately
does not install an `InnerProductSpace` instance on each fibre. -/

variable {U : Type*} [AddCommGroup U] [Module ℝ U]

/-- `G(x∧y,z∧w)` for a symmetric bilinear form `G`, the tangent-space
version of the bivector normalization in Morgan--Tian Definition 1.7
(`morganTian2007`). -/
def wedgePairing (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (x y z w : U) : ℝ :=
  G x z * G y w - G x w * G y z

/-- The diagonal Gram determinant associated with a bilinear form. -/
def wedgePairingDiag (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (x y : U) : ℝ :=
  wedgePairing G x y x y

/-- A symmetric bilinear form induces an algebraic curvature form by the
determinant construction. -/
theorem isAlgebraicCurvature_wedgePairing
    (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (hG : ∀ x y, G x y = G y x) :
    IsAlgebraicCurvature (wedgePairing G) where
  add_left x₁ x₂ y z w := by
    simp only [wedgePairing, map_add, LinearMap.add_apply]
    ring
  smul_left c x y z w := by
    simp only [wedgePairing, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  antisymm_first x y z w := by
    simp only [wedgePairing]
    ring
  antisymm_last x y z w := by
    simp only [wedgePairing]
    ring
  bianchi x y z w := by
    simp only [wedgePairing]
    rw [hG y x, hG z x, hG z y]
    ring

/-- Diagonal constant curvature is equivalent to the full determinant identity
for any symmetric bilinear form. -/
theorem hasConstantCurvature_iff_tensor_bilin
    {B : U → U → U → U → ℝ} (hB : IsAlgebraicCurvature B)
    (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (hG : ∀ x y, G x y = G y x) (lam : ℝ) :
    (∀ x y, B x y x y = lam * wedgePairingDiag G x y) ↔
      ∀ x y z w, B x y z w = lam * wedgePairing G x y z w := by
  let C : U → U → U → U → ℝ := fun x y z w => lam * wedgePairing G x y z w
  have hC : IsAlgebraicCurvature C :=
    (isAlgebraicCurvature_wedgePairing G hG).smul lam
  constructor
  · intro h x y z w
    have hz := (hB.sub hC).eq_zero_of_diag (fun a b => by
      simp [C, wedgePairingDiag, h a b]) x y z w
    dsimp [C] at hz
    linarith
  · intro h x y
    exact h x y x y

/-- The bilinear-form Gram determinant has the expected determinant-square
change-of-generators law. -/
theorem wedgePairingDiag_changeBasis
    (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) (a b c d : ℝ) (x y : U) :
    wedgePairingDiag G (a • x + b • y) (c • x + d • y) =
      (a * d - b * c) ^ 2 * wedgePairingDiag G x y := by
  simp only [wedgePairingDiag, wedgePairing, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The normalized diagonal quotient is invariant under an invertible `GL₂`
change of generators for a bilinear-form metric. -/
theorem sectionalCurvatureBilin_changeBasis
    {B : U → U → U → U → ℝ}
    (hB : IsAlgebraicCurvature B)
    (G : U →ₗ[ℝ] U →ₗ[ℝ] ℝ)
    (a b c d : ℝ) (x y : U)
    (hdet : a * d - b * c ≠ 0) :
    B (a • x + b • y) (c • x + d • y)
        (a • x + b • y) (c • x + d • y) /
        wedgePairingDiag G (a • x + b • y) (c • x + d • y) =
      B x y x y / wedgePairingDiag G x y := by
  have hn : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  rw [hB.diag_changeBasis, wedgePairingDiag_changeBasis]
  field_simp

/-- The Gram determinant is nonnegative by Cauchy--Schwarz. -/
theorem wedgeSq_nonneg (x y : W) : 0 ≤ wedgeSq x y := by
  have h := real_inner_mul_inner_self_le x y
  unfold wedgeSq
  linarith

/-- **Strict Gram inequality.**  A pair spans a genuine two-plane exactly
when its Gram determinant is positive.  This is the nondegeneracy bridge used
by the positive sectional-curvature statements below; it is the strict
Cauchy--Schwarz criterion formalized by
`LinearMap.BilinForm.apply_sq_lt_iff_linearIndependent_of_symm`. -/
theorem wedgeSq_pos_iff_linearIndependent (x y : W) :
    0 < wedgeSq x y ↔ LinearIndependent ℝ ![x, y] := by
  have hposdef : ∀ v : W, v ≠ 0 → 0 < (innerₗ W) v v := by
    intro v hv
    rw [innerₗ_apply_apply]
    exact real_inner_self_pos.mpr hv
  have h := LinearMap.BilinForm.apply_sq_lt_iff_linearIndependent_of_symm
    (innerₗ W) hposdef isSymm_inner x y
  rw [innerₗ_apply_apply, innerₗ_apply_apply, innerₗ_apply_apply] at h
  unfold wedgeSq
  constructor
  · intro hh
    apply h.mp
    nlinarith [hh]
  · intro hh
    have hs := h.mpr hh
    nlinarith [hs]

/-- Diagonal constant-sectional-curvature predicate on a four-tensor.  This
definition intentionally carries no algebraic-curvature witness: pair and
plane independence enter through `hB : IsAlgebraicCurvature B` in
`hasConstantCurvature_iff_tensor` and the other witness-indexed results. -/
def HasConstantCurvature (B : W → W → W → W → ℝ) (lam : ℝ) : Prop :=
  ∀ x y, B x y x y = lam * wedgeSq x y

/-- The total Gram-normalized quotient attached to a four-tensor, extending
Morgan--Tian Definition 1.6 (`morganTian2007`) from an orthonormal basis to a
spanning pair as in do Carmo, Chapter 4, Section 3 (`doCarmo1992`).  This
definition itself does not assert plane or generator independence; those
properties require `hB : IsAlgebraicCurvature B`, for example in
`sectionalCurvature_changeBasis`.  When the Gram determinant is zero, Lean's
field convention gives the value `0`; the witness-indexed degenerate theorem
proves that the numerator vanishes in that case. -/
def sectionalCurvature (B : W → W → W → W → ℝ) (x y : W) : ℝ :=
  B x y x y / wedgeSq x y

variable {B : W → W → W → W → ℝ}

/-- A dependent pair has zero diagonal curvature numerator. -/
theorem curvature_diag_eq_zero_of_not_linearIndependent
    (hB : IsAlgebraicCurvature B) {x y : W}
    (hdep : ¬ LinearIndependent ℝ ![x, y]) : B x y x y = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact hB.zero_first y 0 y
  · have hnot : ¬ (∀ a : ℝ, a • x ≠ y) := by
      intro hall
      exact hdep ((LinearIndependent.pair_iff' hx).mpr hall)
    push Not at hnot
    rcases hnot with ⟨a, ha⟩
    rw [← ha, hB.smul_second, hB.smul_fourth, hB.self_first]
    simp

/-- The sectional quotient is zero on a dependent pair, including the
zero-denominator case. -/
theorem sectionalCurvature_eq_zero_of_not_linearIndependent
    (hB : IsAlgebraicCurvature B) {x y : W}
    (hdep : ¬ LinearIndependent ℝ ![x, y]) :
    sectionalCurvature B x y = 0 := by
  have hnum := curvature_diag_eq_zero_of_not_linearIndependent hB hdep
  have hnpos : ¬ 0 < wedgeSq x y := by
    intro hpos
    exact hdep ((wedgeSq_pos_iff_linearIndependent x y).mp hpos)
  have hden : wedgeSq x y = 0 :=
    le_antisymm (not_lt.mp hnpos) (wedgeSq_nonneg x y)
  simp [sectionalCurvature, hnum]

/-- For an algebraic curvature form, diagonal constant curvature is equivalent
to the full tensor identity in Morgan--Tian's frozen slot order
(`morganTian2007`, Definition 1.6). -/
theorem hasConstantCurvature_iff_tensor (hB : IsAlgebraicCurvature B) (lam : ℝ) :
    HasConstantCurvature B lam ↔
      ∀ x y z w, B x y z w = lam * wedgeInner x y z w := by
  constructor
  · intro h x y z w
    let C : W → W → W → W → ℝ := fun a b c d => lam * wedgeInner a b c d
    have hC : IsAlgebraicCurvature C :=
      (isAlgebraicCurvature_wedgeInner (W := W)).smul lam
    have hz : (fun a b c d => B a b c d - C a b c d) x y z w = 0 := by
      apply (hB.sub hC).eq_zero_of_diag
      intro a b
      simp only [C, wedgeInner_self, h a b, sub_self]
    dsimp [C] at hz
    linarith
  · intro h x y
    rw [h, wedgeInner_self]

/-- The metric Gram determinant transforms by the square of a `GL₂`
determinant. -/
theorem wedgeSq_changeBasis (a b c d : ℝ) (x y : W) :
    wedgeSq (a • x + b • y) (c • x + d • y) =
      (a * d - b * c) ^ 2 * wedgeSq x y := by
  simp only [wedgeSq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

/-- `GL₂` change-of-generators invariance for the quotient.  This is the
intrinsic spanning-pair result; no quotient-of-planes choice is made. -/
theorem sectionalCurvature_changeBasis (hB : IsAlgebraicCurvature B)
    (a b c d : ℝ) (x y : W) (hdet : a * d - b * c ≠ 0) :
    (B (a • x + b • y) (c • x + d • y)
        (a • x + b • y) (c • x + d • y)) /
        wedgeSq (a • x + b • y) (c • x + d • y) =
      B x y x y / wedgeSq x y := by
  have hn : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  rw [hB.diag_changeBasis, wedgeSq_changeBasis]
  field_simp

/-- On an orthonormal pair the Gram normalization is one, so sectional
curvature is the source-ordered diagonal component. -/
theorem sectionalCurvature_orthonormal (B : W → W → W → W → ℝ)
    (x y : W) (hxx : inner ℝ x x = 1) (hyy : inner ℝ y y = 1)
    (hxy : inner ℝ x y = 0) :
    sectionalCurvature B x y = B x y x y := by
  unfold sectionalCurvature
  rw [wedgeSq, hxx, hyy, hxy]
  norm_num

/-- Constant curvature evaluates to its parameter on an orthonormal pair.
This is the pointwise specialization of Morgan--Tian Definition 1.6. -/
theorem hasConstantCurvature_orthonormal
    {B : W → W → W → W → ℝ} {lam : ℝ}
    (hB : HasConstantCurvature B lam) (x y : W)
    (hxx : inner ℝ x x = 1) (hyy : inner ℝ y y = 1)
    (hxy : inner ℝ x y = 0) : B x y x y = lam := by
  rw [hB x y, wedgeSq, hxx, hyy, hxy]
  norm_num

/-- The normalized sectional quotient equals the constant parameter on an
orthonormal pair. -/
theorem sectionalCurvature_eq_constant_of_orthonormal
    {B : W → W → W → W → ℝ} {lam : ℝ}
    (hB : HasConstantCurvature B lam) (x y : W)
    (hxx : inner ℝ x x = 1) (hyy : inner ℝ y y = 1)
    (hxy : inner ℝ x y = 0) : sectionalCurvature B x y = lam := by
  rw [sectionalCurvature_orthonormal B x y hxx hyy hxy]
  exact hasConstantCurvature_orthonormal hB x y hxx hyy hxy

/-- Sectional curvature vanishes when the first generator is zero. -/
theorem sectionalCurvature_zero_left (hB : IsAlgebraicCurvature B) (y : W) :
    sectionalCurvature B 0 y = 0 := by
  simp [sectionalCurvature, wedgeSq, hB.zero_first]

/-- Sectional curvature vanishes when the second generator is zero. -/
theorem sectionalCurvature_zero_right (hB : IsAlgebraicCurvature B) (x : W) :
    sectionalCurvature B x 0 = 0 := by
  simp [sectionalCurvature, wedgeSq, hB.zero_second]

/-- The constant-curvature model kernel is an algebraic curvature form. -/
theorem isAlgebraicCurvature_modelCurvature4 (lam : ℝ) :
    IsAlgebraicCurvature (modelCurvature4 lam (E := W)) := by
  change IsAlgebraicCurvature
    (fun x y z w => lam *
      (inner ℝ x z * inner ℝ y w - inner ℝ x w * inner ℝ y z))
  simpa [wedgeInner] using
    ((isAlgebraicCurvature_wedgeInner (W := W)).smul lam)

/-- The model kernel has constant sectional curvature `lam` in the frozen
Morgan--Tian slot order (Definition 1.6, `morganTian2007`). -/
theorem hasConstantCurvature_modelCurvature4 (lam : ℝ) :
    HasConstantCurvature (modelCurvature4 lam (E := W)) lam := by
  intro x y
  simp [modelCurvature4, wedgeSq, real_inner_comm]

end Curvature
end Ch01
end MorganTianLib
