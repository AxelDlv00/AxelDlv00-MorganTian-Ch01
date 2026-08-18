import MorganTianLib.Ch01.Comparison.TraceRiccati
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Determinant and positive-density comparison

This module turns logarithmic-derivative bounds into monotonicity of a positive
density, or of the absolute determinant of an invertible endomorphism family,
after normalization by a model power.  It also proves the basis-free Jacobi
formula needed to identify the logarithmic derivative of `|det J|`.

The pinned Mathlib provides the canonical basis-independent `LinearMap.det` and
the theorem `LinearMap.det_toMatrix`, but not a derivative theorem for that
map.  A private continuous-multilinear matrix adapter proves Jacobi's formula;
all public signatures remain coordinate-independent.  The determinant-only
calculus works on normed spaces, while the inner-product trace/Riccati facade
uses Mathlib's measure-facing `LinearMap.normDet` through
`LinearMap.normDet_eq_abs_det`.  In particular, none of the densities below is
asserted to be a polar Jacobian or a Riemannian volume.  Those producer and
coherence statements belong to N1/C2/C3, not this A1 analytic layer.

Mathematical anchors: Morgan--Tian, Chapter 1, Ricci comparison and the
determinant estimate on pp. 48--49; Petersen (2006), Chapter 9, Section 1; the
positive-curvature direction is cross-checked with Petersen (2016), Section
6.4, Corollary 6.4.2.
-/

open Real Filter Set Module
open scoped Topology RealInnerProductSpace Matrix

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Comparison

/-! ## A private matrix derivative adapter -/

namespace DeterminantAdapter

variable {n : Type*} [Fintype n] [DecidableEq n]

private def detCMM : ContinuousMultilinearMap ℝ (fun _ : n => (n → ℝ)) ℝ :=
  ContinuousMultilinearMap.mk Matrix.detRowAlternating.toMultilinearMap
    (by
      show Continuous fun M : n → n → ℝ => Matrix.det M
      simp only [Matrix.det_apply]
      refine continuous_finsetSum _ fun σ _ => Continuous.const_smul ?_ _
      exact continuous_finsetProd _ fun i _ =>
        (continuous_apply i).comp (continuous_apply (σ i)))

@[simp] private theorem detCMM_apply (M : n → n → ℝ) :
    detCMM M = Matrix.det M := rfl

private theorem hasFDerivAt_det (A : n → n → ℝ) :
    HasFDerivAt (fun M : n → n → ℝ => Matrix.det M) (detCMM.linearDeriv A) A :=
  detCMM.hasFDerivAt A

private theorem linearDeriv_apply (A B : Matrix n n ℝ) :
    detCMM.linearDeriv A B = ∑ i, Matrix.det (Matrix.updateRow A i (B i)) := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [detCMM_apply]
  rfl

private theorem linearDeriv_eq_trace (A B : Matrix n n ℝ) :
    detCMM.linearDeriv A B = (B * Matrix.adjugate A).trace := by
  rw [linearDeriv_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, ← Matrix.adjugate_transpose,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

private theorem linearDeriv_eq_det_mul_trace (A B : Matrix n n ℝ)
    (hA : IsUnit A.det) :
    detCMM.linearDeriv A B = A.det * ((A⁻¹ : Matrix n n ℝ) * B).trace := by
  rw [linearDeriv_eq_trace]
  have hadj : Matrix.adjugate A = A.det • (A⁻¹ : Matrix n n ℝ) := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hA, one_smul]
  rw [hadj, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm,
    smul_eq_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private def toMatrixCLM (b : Basis (Fin (finrank ℝ E)) ℝ E) :
    (E →L[ℝ] E) →L[ℝ] (Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ) :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.toMatrix b b).toLinearMap).comp (ContinuousLinearMap.coeLM ℝ))

/-- Basis-free Jacobi formula for the determinant of a differentiable,
invertible family of continuous endomorphisms:
`(det J)' = det J * trace (J' comp J⁻¹)`.

The proof computes in `Module.finBasis`; `LinearMap.det_toMatrix` and
`LinearMap.trace_eq_matrix_trace` identify both matrix expressions with their
canonical basis-independent values. -/
private theorem hasDerivAt_endomorphismDet {J J' : ℝ → E →L[ℝ] E} {r : ℝ}
    (hJ : HasDerivAt J (J' r) r) (hunit : IsUnit (J r)) :
    HasDerivAt (fun s => LinearMap.det ((J s : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) *
        LinearMap.trace ℝ E
          (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)) r := by
  classical
  set m := finrank ℝ E with hm
  set b := Module.finBasis ℝ E with hb
  set Mf : ℝ → Matrix (Fin m) (Fin m) ℝ :=
    fun s => LinearMap.toMatrix b b ((J s : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMf
  set Md : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix b b ((J' r : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMd
  set Jinv : E →L[ℝ] E := Ring.inverse (J r) with hJinv
  set Mi : Matrix (Fin m) (Fin m) ℝ :=
    LinearMap.toMatrix b b ((Jinv : E →L[ℝ] E) : E →ₗ[ℝ] E) with hMi
  have hmul : ∀ f g : E →L[ℝ] E,
      LinearMap.toMatrix b b ((f * g : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = LinearMap.toMatrix b b (f : E →ₗ[ℝ] E)
          * LinearMap.toMatrix b b (g : E →ₗ[ℝ] E) := by
    intro f g
    exact LinearMap.toMatrix_comp b b b _ _
  have hone : LinearMap.toMatrix b b ((1 : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 :=
    LinearMap.toMatrix_id _
  have hMfd : HasDerivAt
      (fun s => ((Mf s : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ))
      ((Md : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ) r :=
    (toMatrixCLM b).hasFDerivAt.comp_hasDerivAt r hJ
  have hcancel : J r * Jinv = 1 := Ring.mul_inverse_cancel _ hunit
  have hcancel' : Jinv * J r = 1 := Ring.inverse_mul_cancel _ hunit
  have hprod : Mf r * Mi = 1 := by
    rw [hMf, hMi, ← hmul, hcancel, hone]
  have hprod' : Mi * Mf r = 1 := by
    rw [hMf, hMi, ← hmul, hcancel', hone]
  have hdet : IsUnit (Mf r).det := by
    refine isUnit_iff_exists_inv.mpr ⟨Mi.det, ?_⟩
    rw [← Matrix.det_mul, hprod, Matrix.det_one]
  have hinvM : (Mf r)⁻¹ = Mi := Matrix.inv_eq_left_inv hprod'
  have hchain : HasDerivAt (fun s => Matrix.det (Mf s))
      (detCMM.linearDeriv (Mf r) Md) r :=
    (hasFDerivAt_det (Mf r)).comp_hasDerivAt r hMfd
  rw [linearDeriv_eq_det_mul_trace (Mf r) Md hdet, hinvM] at hchain
  have hdetEq : ∀ s : ℝ, Matrix.det (Mf s) =
      LinearMap.det ((J s : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    intro s
    rw [hMf, LinearMap.det_toMatrix]
  have htraceEq : (Mi * Md).trace = LinearMap.trace ℝ E
      (((J' r).comp Jinv : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    have hleft : ((Jinv * J' r : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = (Jinv : E →ₗ[ℝ] E) * ((J' r : E →L[ℝ] E) : E →ₗ[ℝ] E) := rfl
    have hright : (((J' r).comp Jinv : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = ((J' r : E →L[ℝ] E) : E →ₗ[ℝ] E) * (Jinv : E →ₗ[ℝ] E) := rfl
    rw [hMi, hMd, ← hmul, ← LinearMap.trace_eq_matrix_trace ℝ b,
      hleft, hright, LinearMap.trace_mul_comm]
  have hfun : (fun s => Matrix.det (Mf s)) =
      fun s => LinearMap.det ((J s : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    funext hdetEq
  rw [hfun, hdetEq r, htraceEq] at hchain
  exact hchain

end DeterminantAdapter

/-! ## Coordinate-independent determinant formulas -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The absolute determinant of an endomorphism family.  Absolute value removes
the arbitrary orientation sign while retaining a strictly positive density on
every interval where the family is invertible. -/
def endomorphismAbsDet (J : ℝ → E →L[ℝ] E) (r : ℝ) : ℝ :=
  |LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E)|

private theorem endomorphismDet_ne_zero {J : ℝ → E →L[ℝ] E} {r : ℝ}
    (hunit : IsUnit (J r)) :
    LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 := by
  have hunitLM : IsUnit ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
    hunit.map ContinuousLinearMap.toLinearMapRingHom
  exact isUnit_iff_ne_zero.mp
    ((LinearMap.isUnit_iff_isUnit_det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E)).mp hunitLM)

/-- Logarithmic Jacobi formula in coordinate-independent form.  If `J r` is
invertible and `J` has derivative `J' r`, then
`(log |det J|)' = trace (J' comp J⁻¹)` at `r`.

The absolute value makes the statement independent of orientation; Mathlib's
real logarithm already satisfies `log |x| = log x` away from zero. -/
theorem hasDerivAt_log_endomorphismAbsDet {J J' : ℝ → E →L[ℝ] E} {r : ℝ}
    (hJ : HasDerivAt J (J' r) r) (hunit : IsUnit (J r)) :
    HasDerivAt (fun s => Real.log (endomorphismAbsDet J s))
      (LinearMap.trace ℝ E
        (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)) r := by
  have hdet := DeterminantAdapter.hasDerivAt_endomorphismDet hJ hunit
  have hne := endomorphismDet_ne_zero hunit
  have hlog := (Real.hasDerivAt_log hne).comp r hdet
  have hfun : (fun s => Real.log (endomorphismAbsDet J s)) =
      fun s => Real.log (LinearMap.det ((J s : E →L[ℝ] E) : E →ₗ[ℝ] E)) := by
    funext s
    exact Real.log_abs _
  rw [hfun]
  have hvalue :
      (LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E))⁻¹ *
          (LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) *
            LinearMap.trace ℝ E
              (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E))
        = LinearMap.trace ℝ E
            (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hlog' := hlog.congr_deriv hvalue
  simpa only [Function.comp_def] using hlog'

/-- Differential form of Jacobi's formula for the orientation-free density:
`(|det J|)' = |det J| * trace (J' comp J⁻¹)` on the regular locus. -/
theorem hasDerivAt_endomorphismAbsDet {J J' : ℝ → E →L[ℝ] E} {r : ℝ}
    (hJ : HasDerivAt J (J' r) r) (hunit : IsUnit (J r)) :
    HasDerivAt (endomorphismAbsDet J)
      (endomorphismAbsDet J r * LinearMap.trace ℝ E
        (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)) r := by
  have hlog := hasDerivAt_log_endomorphismAbsDet hJ hunit
  have hdet := DeterminantAdapter.hasDerivAt_endomorphismDet hJ hunit
  have hne := endomorphismDet_ne_zero hunit
  have hexp := hlog.exp
  have hderiv : Real.exp (Real.log (endomorphismAbsDet J r)) *
      LinearMap.trace ℝ E
        (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)
      = endomorphismAbsDet J r * LinearMap.trace ℝ E
        (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    rw [show endomorphismAbsDet J r =
      |LinearMap.det ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E)| by rfl,
      Real.exp_log (abs_pos.mpr hne)]
  have hexp' := hexp.congr_deriv hderiv
  apply hexp'.congr_of_eventuallyEq
  filter_upwards [hdet.continuousAt.eventually_ne hne] with s hs
  exact (Real.exp_log (abs_pos.mpr hs)).symm

/-- The absolute determinant is positive at every point where the endomorphism
is invertible. -/
theorem endomorphismAbsDet_pos {J : ℝ → E →L[ℝ] E} {r : ℝ}
    (hunit : IsUnit (J r)) : 0 < endomorphismAbsDet J r :=
  abs_pos.mpr (endomorphismDet_ne_zero hunit)

end NormedSpace

/-! ## Abstract positive-density ratios -/

/-- Pointwise quotient-rule derivative for a density divided by a natural
power of a nonzero model function. -/
theorem hasDerivAt_div_pow {m : ℕ} {s s' ρ ρ' : ℝ → ℝ} {r : ℝ}
    (hs : HasDerivAt s (s' r) r) (hs0 : s r ≠ 0)
    (hρ : HasDerivAt ρ (ρ' r) r) :
    HasDerivAt (fun u => ρ u / s u ^ m)
      ((ρ' r * s r ^ m - ρ r * ((m : ℝ) * s r ^ (m - 1) * s' r)) /
        (s r ^ m) ^ 2) r := by
  exact hρ.div (hs.pow m) (pow_ne_zero _ hs0)

private theorem mul_div_mul_pow_eq {m : ℕ} {x y z : ℝ} (hx : x ≠ 0) :
    (m : ℝ) * (y / x) * z * x ^ m = z * ((m : ℝ) * x ^ (m - 1) * y) := by
  cases m with
  | zero => simp
  | succ n =>
      rw [Nat.succ_sub_one, pow_succ]
      field_simp

/-- Upper logarithmic-derivative comparison for an abstract positive density.
If `ρ' = ρ q` and `q <= m s'/s`, then `ρ/s^m` is antitone. -/
theorem antitoneOn_div_pow_of_logDeriv_le {r₀ : ℝ} {m : ℕ}
    {s s' ρ q : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, q r ≤ (m : ℝ) * (s' r / s r)) :
    AntitoneOn (fun r => ρ r / s r ^ m) (Ioo 0 r₀) := by
  have hD := fun r hr =>
    hasDerivAt_div_pow (m := m) (s := s) (s' := s') (ρ := ρ)
      (ρ' := fun u => ρ u * q u) (hs r hr) (hspos r hr).ne' (hρ r hr)
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have hmodel := mul_div_mul_pow_eq (m := m) (x := s r) (y := s' r) (z := ρ r)
      (hspos r hr).ne'
    have hmain : ρ r * q r * s r ^ m
        ≤ (m : ℝ) * (s' r / s r) * ρ r * s r ^ m := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hspos r hr).le _)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hle r hr) (hρpos r hr).le
    rw [hmodel] at hmain
    linarith

/-- Lower logarithmic-derivative comparison for an abstract positive density.
If `ρ' = ρ q` and `m s'/s <= q`, then `ρ/s^m` is monotone. -/
theorem monotoneOn_div_pow_of_le_logDeriv {r₀ : ℝ} {m : ℕ}
    {s s' ρ q : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, (m : ℝ) * (s' r / s r) ≤ q r) :
    MonotoneOn (fun r => ρ r / s r ^ m) (Ioo 0 r₀) := by
  have hD := fun r hr =>
    hasDerivAt_div_pow (m := m) (s := s) (s' := s') (ρ := ρ)
      (ρ' := fun u => ρ u * q u) (hs r hr) (hspos r hr).ne' (hρ r hr)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    apply div_nonneg _ (by positivity)
    have hmodel := mul_div_mul_pow_eq (m := m) (x := s r) (y := s' r) (z := ρ r)
      (hspos r hr).ne'
    have hmain : (m : ℝ) * (s' r / s r) * ρ r * s r ^ m
        ≤ ρ r * q r * s r ^ m := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (hspos r hr).le _)
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hle r hr) (hρpos r hr).le
    rw [hmodel] at hmain
    linarith

/-- An antitone normalized density with right-origin limit one is bounded above
by its model power.  This is the separate origin-normalization step; it makes
no claim that `ρ` is geometrically produced. -/
theorem density_le_model_pow_of_antitone {r₀ : ℝ} {m : ℕ} {s ρ : ℝ → ℝ}
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hanti : AntitoneOn (fun r => ρ r / s r ^ m) (Ioo 0 r₀))
    (h0 : Tendsto (fun r => ρ r / s r ^ m)
      (nhdsWithin 0 (Ioi 0)) (nhds 1)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ρ r ≤ s r ^ m := by
  intro r hr
  have hev : ∀ᶠ u in nhdsWithin 0 (Ioi (0 : ℝ)),
      ρ r / s r ^ m ≤ ρ u / s u ^ m := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with u hu
    exact hanti ⟨hu.1, hu.2.trans hr.2⟩ hr hu.2.le
  have hle : ρ r / s r ^ m ≤ 1 := ge_of_tendsto h0 hev
  exact (div_le_one (pow_pos (hspos r hr) m)).mp hle

/-- A monotone normalized density with right-origin limit one is bounded below
by its model power. -/
theorem model_pow_le_density_of_monotone {r₀ : ℝ} {m : ℕ} {s ρ : ℝ → ℝ}
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hmono : MonotoneOn (fun r => ρ r / s r ^ m) (Ioo 0 r₀))
    (h0 : Tendsto (fun r => ρ r / s r ^ m)
      (nhdsWithin 0 (Ioi 0)) (nhds 1)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, s r ^ m ≤ ρ r := by
  intro r hr
  have hev : ∀ᶠ u in nhdsWithin 0 (Ioi (0 : ℝ)),
      ρ u / s u ^ m ≤ ρ r / s r ^ m := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with u hu
    exact hmono ⟨hu.1, hu.2.trans hr.2⟩ hr hu.2.le
  have hle : 1 ≤ ρ r / s r ^ m := le_of_tendsto h0 hev
  exact (one_le_div (pow_pos (hspos r hr) m)).mp hle

/-! ## Model-specific abstract-density adapters -/

/-- Upper flat/hyperbolic logarithmic-derivative comparison for a positive
density: `q <= m * radialCoeff k` makes `ρ / sn k ^ m` antitone. -/
theorem antitoneOn_density_div_sn_pow {k r₀ : ℝ} (hk : 0 ≤ k) {m : ℕ}
    {ρ q : ℝ → ℝ}
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, q r ≤ (m : ℝ) * radialCoeff k r) :
    AntitoneOn (fun r => ρ r / sn k r ^ m) (Ioo 0 r₀) := by
  apply antitoneOn_div_pow_of_logDeriv_le
    (fun r _ => hasDerivAt_sn k r hk) (fun r hr => sn_pos k r hk hr.1) hρ hρpos
  intro r hr
  simpa [radialCoeff_eq_div k r hk] using hle r hr

/-- Lower flat/hyperbolic logarithmic-derivative comparison for a positive
density: `m * radialCoeff k <= q` makes `ρ / sn k ^ m` monotone. -/
theorem monotoneOn_density_div_sn_pow {k r₀ : ℝ} (hk : 0 ≤ k) {m : ℕ}
    {ρ q : ℝ → ℝ}
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, (m : ℝ) * radialCoeff k r ≤ q r) :
    MonotoneOn (fun r => ρ r / sn k r ^ m) (Ioo 0 r₀) := by
  apply monotoneOn_div_pow_of_le_logDeriv
    (fun r _ => hasDerivAt_sn k r hk) (fun r hr => sn_pos k r hk hr.1) hρ hρpos
  intro r hr
  simpa [radialCoeff_eq_div k r hk] using hle r hr

/-- Flat specialization of the upper density adapter.  The denominator is
definitionally reduced to `r ^ m` and the model logarithmic derivative to
`m / r`. -/
theorem antitoneOn_density_div_self_pow {r₀ : ℝ} {m : ℕ} {ρ q : ℝ → ℝ}
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, q r ≤ (m : ℝ) / r) :
    AntitoneOn (fun r => ρ r / r ^ m) (Ioo 0 r₀) := by
  simpa [radialCoeff, div_eq_mul_inv] using
    antitoneOn_density_div_sn_pow (k := 0) (r₀ := r₀) (m := m) (by positivity)
      hρ hρpos (fun r hr => by
        simpa [radialCoeff, div_eq_mul_inv] using hle r hr)

/-- Upper spherical logarithmic-derivative adapter on the regular first-pole
interval. -/
theorem antitoneOn_density_div_snPos_pow {K r₀ : ℝ} (hK : 0 ≤ K) {m : ℕ}
    {ρ q : ℝ → ℝ}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, q r ≤ (m : ℝ) * logDerivPos K r) :
    AntitoneOn (fun r => ρ r / snPos K r ^ m) (Ioo 0 r₀) := by
  apply antitoneOn_div_pow_of_logDeriv_le
    (fun r _ => hasDerivAt_snPos K r hK)
    (fun r hr => snPos_pos K r hK (hpole r hr)) hρ hρpos
  intro r hr
  simpa [logDerivPos_eq_div K r hK] using hle r hr

/-- Lower spherical logarithmic-derivative adapter on the regular first-pole
interval.  This is only an A1 analytic implication; geometric lower-Jacobian
producers remain pending. -/
theorem monotoneOn_density_div_snPos_pow {K r₀ : ℝ} (hK : 0 ≤ K) {m : ℕ}
    {ρ q : ℝ → ℝ}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hρ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ρ (ρ r * q r) r)
    (hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, (m : ℝ) * logDerivPos K r ≤ q r) :
    MonotoneOn (fun r => ρ r / snPos K r ^ m) (Ioo 0 r₀) := by
  apply monotoneOn_div_pow_of_le_logDeriv
    (fun r _ => hasDerivAt_snPos K r hK)
    (fun r hr => snPos_pos K r hK (hpole r hr)) hρ hρpos
  intro r hr
  simpa [logDerivPos_eq_div K r hK] using hle r hr

/-! ## Absolute-determinant specializations and the traced consequence -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A trace upper bound makes the absolute determinant ratio against the
flat/hyperbolic model antitone.  Invertibility supplies both positivity and the
orientation-independent derivative formula. -/
theorem antitoneOn_absDet_div_sn_pow {k r₀ : ℝ} (hk : 0 ≤ k)
    {J J' : ℝ → E →L[ℝ] E}
    (hJ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt J (J' r) r)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (J r))
    (htrace : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E
          (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)
        ≤ (finrank ℝ E : ℝ) * radialCoeff k r) :
    AntitoneOn (fun r => endomorphismAbsDet J r / sn k r ^ finrank ℝ E)
      (Ioo 0 r₀) :=
  antitoneOn_density_div_sn_pow hk
    (fun r hr => hasDerivAt_endomorphismAbsDet (hJ r hr) (hunit r hr))
    (fun r hr => endomorphismAbsDet_pos (hunit r hr)) htrace

/-- Lower-trace spherical specialization for the absolute determinant.  It is
direction-generic analysis and does not assert a geometric Jacobian theorem. -/
theorem monotoneOn_absDet_div_snPos_pow {K r₀ : ℝ} (hK : 0 ≤ K)
    {J J' : ℝ → E →L[ℝ] E}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hJ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt J (J' r) r)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (J r))
    (htrace : ∀ r ∈ Ioo (0 : ℝ) r₀,
      (finrank ℝ E : ℝ) * logDerivPos K r ≤ LinearMap.trace ℝ E
        (((J' r).comp (Ring.inverse (J r)) : E →L[ℝ] E) : E →ₗ[ℝ] E)) :
    MonotoneOn (fun r => endomorphismAbsDet J r / snPos K r ^ finrank ℝ E)
      (Ioo 0 r₀) :=
  monotoneOn_density_div_snPos_pow hK hpole
    (fun r hr => hasDerivAt_endomorphismAbsDet (hJ r hr) (hunit r hr))
    (fun r hr => endomorphismAbsDet_pos (hunit r hr)) htrace

end NormedSpace

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The canonical volume-factor consequence of `trace_riccati_comparison`.  If
`A` is the right logarithmic derivative `J' comp J⁻¹`, then the traced Riccati
hypotheses make `normDet J / sn k ^ finrank Real E` antitone. -/
theorem antitoneOn_normDet_div_sn_pow_of_trace_riccati [Nontrivial E]
    {k r₀ : ℝ} (hk : 0 ≤ k) {A A' J J' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, (A r : E →ₗ[ℝ] E).IsSymmetric)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑((A r).comp (A r))
        ≤ (finrank ℝ E : ℝ) * k)
    (hA0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hJ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt J (J' r) r)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (J r))
    (hlog : ∀ r ∈ Ioo (0 : ℝ) r₀,
      (J' r).comp (Ring.inverse (J r)) = A r) :
    AntitoneOn (fun r =>
      LinearMap.normDet ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) / sn k r ^ finrank ℝ E)
      (Ioo 0 r₀) := by
  have hcmp := trace_riccati_comparison (E := E) hk hA hsym hRic hA0
  have habs := antitoneOn_absDet_div_sn_pow hk hJ hunit (fun r hr => by
    rw [hlog r hr]
    exact hcmp r hr)
  simpa only [endomorphismAbsDet, LinearMap.normDet_eq_abs_det] using habs

/-- Origin-normalized determinant bound following from the traced Riccati
comparison.  The limit hypothesis is explicit because A1 does not construct a
geometric family with the required origin asymptotics. -/
theorem normDet_le_sn_pow_of_trace_riccati [Nontrivial E]
    {k r₀ : ℝ} (hk : 0 ≤ k) {A A' J J' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, (A r : E →ₗ[ℝ] E).IsSymmetric)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑((A r).comp (A r))
        ≤ (finrank ℝ E : ℝ) * k)
    (hA0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hJ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt J (J' r) r)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (J r))
    (hlog : ∀ r ∈ Ioo (0 : ℝ) r₀,
      (J' r).comp (Ring.inverse (J r)) = A r)
    (hJ0 : Tendsto
      (fun r => LinearMap.normDet ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) /
        sn k r ^ finrank ℝ E)
      (nhdsWithin 0 (Ioi 0)) (nhds 1)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.normDet ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) ≤
        sn k r ^ finrank ℝ E := by
  apply density_le_model_pow_of_antitone
    (fun r hr => sn_pos k r hk hr.1)
    (antitoneOn_normDet_div_sn_pow_of_trace_riccati hk hA hsym hRic hA0
      hJ hunit hlog) hJ0

/-- Flat canonical volume-factor consequence: the normalization is exactly
`normDet (J r) / r ^ finrank Real E`. -/
theorem antitoneOn_normDet_div_self_pow_of_trace_riccati [Nontrivial E]
    {r₀ : ℝ} {A A' J J' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, (A r : E →ₗ[ℝ] E).IsSymmetric)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑((A r).comp (A r)) ≤ 0)
    (hA0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hJ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt J (J' r) r)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (J r))
    (hlog : ∀ r ∈ Ioo (0 : ℝ) r₀,
      (J' r).comp (Ring.inverse (J r)) = A r) :
    AntitoneOn (fun r =>
      LinearMap.normDet ((J r : E →L[ℝ] E) : E →ₗ[ℝ] E) / r ^ finrank ℝ E)
      (Ioo 0 r₀) := by
  simpa using antitoneOn_normDet_div_sn_pow_of_trace_riccati
    (E := E) (k := 0) (by positivity) hA hsym
      (fun r hr => by simpa using hRic r hr) hA0 hJ hunit hlog

end InnerProductSpace

/-- Exact-model normalization regression.  Applying both
logarithmic-derivative adapters to `sn k ^ m` checks that equality gives both
antitonicity and monotonicity. -/
private theorem normalized_sn_pow_model {k r₀ : ℝ} (hk : 0 ≤ k) (m : ℕ) :
    AntitoneOn (fun r => sn k r ^ m / sn k r ^ m) (Ioo 0 r₀) ∧
      MonotoneOn (fun r => sn k r ^ m / sn k r ^ m) (Ioo 0 r₀) := by
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt (fun u => sn k u ^ m)
        (sn k r ^ m * ((m : ℝ) * radialCoeff k r)) r := by
    intro r hr
    have h := (hasDerivAt_sn k r hk).pow m
    apply h.congr_deriv
    rw [radialCoeff_eq_div k r hk]
    have hsn : sn k r ≠ 0 := (sn_pos k r hk hr.1).ne'
    cases m with
    | zero => simp
    | succ n =>
        rw [Nat.succ_sub_one, pow_succ]
        field_simp
  have hpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < sn k r ^ m :=
    fun r hr => pow_pos (sn_pos k r hk hr.1) m
  constructor
  · exact antitoneOn_density_div_sn_pow (m := m) hk hderiv hpos
      (fun _ _ => le_rfl)
  · exact monotoneOn_density_div_sn_pow (m := m) hk hderiv hpos
      (fun _ _ => le_rfl)

/-- Flat-branch normalization regression: the exact-model check specializes to
normalization by `r ^ m`, with no hidden nonzero-curvature denominator. -/
private theorem normalized_self_pow_model {r₀ : ℝ} (m : ℕ) :
    AntitoneOn (fun r => r ^ m / r ^ m) (Ioo 0 r₀) ∧
      MonotoneOn (fun r => r ^ m / r ^ m) (Ioo 0 r₀) := by
  simpa using normalized_sn_pow_model (k := 0) (r₀ := r₀) (by positivity) m

/-- Nonconstant upper-direction regression in the flat `m = 1` model.  The
constant positive density has normalized ratio `1 / r`, so the upper adapter
must return antitonicity. -/
private theorem normalized_const_div_self_antitone {r₀ : ℝ} :
    AntitoneOn (fun r : ℝ => 1 / r) (Ioo 0 r₀) := by
  simpa using antitoneOn_density_div_self_pow (r₀ := r₀) (m := 1)
    (ρ := fun _ => 1) (q := fun _ => 0)
    (fun r _ => by simpa using hasDerivAt_const (x := r) (c := (1 : ℝ)))
    (fun _ _ => by positivity)
    (fun r hr => by simpa using (one_div_pos.mpr hr.1).le)

/-- Nonconstant lower-direction regression in the flat `m = 1` model.  The
density `r ^ 2` has normalized ratio `r ^ 2 / r`, so the lower adapter must
return monotonicity. -/
private theorem normalized_sq_div_self_monotone {r₀ : ℝ} :
    MonotoneOn (fun r : ℝ => r ^ 2 / r) (Ioo 0 r₀) := by
  have hderiv : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt (fun u : ℝ => u ^ 2) (r ^ 2 * (2 / r)) r := by
    intro r hr
    apply ((hasDerivAt_id r).pow 2).congr_deriv
    norm_num
    field_simp [hr.1.ne']
  have hmono := monotoneOn_density_div_sn_pow (k := 0) (r₀ := r₀) (m := 1)
    (by positivity) hderiv (fun r hr => pow_pos hr.1 2) (fun r hr => by
      simp only [Nat.cast_one, one_mul, radialCoeff]
      exact div_le_div_of_nonneg_right (by norm_num) hr.1.le)
  simpa using hmono

end Comparison
end Ch01
end MorganTianLib
