import MorganTianLib.Ch01.Comparison.Model
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Traced Riccati comparison

This module supplies the finite-dimensional analytic trace layer used in Ricci
comparison.  It proves the trace Cauchy--Schwarz inequality for a symmetric
endomorphism and reduces the traced Riccati inequality to
`Comparison.scalar_riccati_comparison` after division by the dimension.

The statements are deliberately about real inner-product spaces and
endomorphism families.  No manifold, Jacobi-field, or polar-density producer is
chosen here.  This differs materially from the reference prior art, whose trace
file already describes a geometric shape operator.

Mathematical anchors: Morgan--Tian, Chapter 1, Ricci curvature comparison,
pp. 48--49; Petersen (2006), Chapter 9, Section 1.
-/

open Real Filter Set Module
open scoped Topology RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Trace Cauchy--Schwarz for a symmetric endomorphism of a finite-dimensional
real inner-product space:
`(trace A)^2 <= finrank Real E * trace (A.comp A)`.

The theorem includes the zero-dimensional case.  In an orthonormal basis the
proof combines scalar Cauchy--Schwarz for the diagonal entries with
`inner (A e_i) (A e_i) <= trace (A.comp A)`.  This is the algebraic step in
Morgan--Tian's traced Riccati argument on pp. 48--49. -/
theorem sq_trace_le_finrank_mul_trace_comp_self {A : E →L[ℝ] E}
    (hsym : (A : E →ₗ[ℝ] E).IsSymmetric) :
    LinearMap.trace ℝ E ↑A ^ 2
      ≤ (finrank ℝ E : ℝ) * LinearMap.trace ℝ E ↑(A.comp A) := by
  classical
  set b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  have hdiag : ∀ i, ⟪b i, A (b i)⟫ ^ 2 ≤ ⟪b i, A (A (b i))⟫ := by
    intro i
    have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
    have hself : ⟪b i, A (A (b i))⟫ = ‖A (b i)‖ ^ 2 := by
      calc
        ⟪b i, A (A (b i))⟫ = ⟪A (A (b i)), b i⟫ := real_inner_comm _ _
        _ = ⟪A (b i), A (b i)⟫ := by
          simpa only [ContinuousLinearMap.coe_coe] using hsym (A (b i)) (b i)
        _ = ‖A (b i)‖ ^ 2 := real_inner_self_eq_norm_sq _
    have hinner : |⟪b i, A (b i)⟫| ≤ ‖A (b i)‖ := by
      have h := abs_real_inner_le_norm (b i) (A (b i))
      rwa [hnorm, one_mul] at h
    rw [hself]
    nlinarith [mul_self_le_mul_self (abs_nonneg ⟪b i, A (b i)⟫) hinner,
      sq_abs ⟪b i, A (b i)⟫]
  have hsum : (∑ i, ⟪b i, A (b i)⟫) ^ 2
      ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (b i)⟫ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (finrank ℝ E))))
      (f := fun i => ⟪b i, A (b i)⟫)
    simpa using h
  calc
    (∑ i, ⟪b i, A (b i)⟫) ^ 2
        ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (b i)⟫ ^ 2 := hsum
    _ ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (A (b i))⟫ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdiag i)
        (Nat.cast_nonneg _)

/-- Flat/hyperbolic trace Riccati comparison.

Let `m = finrank Real E`, with `m > 0`.  If `A` is differentiable and symmetric,
`trace A' + trace (A.comp A) <= m * k`, and
`trace (A r) - m / r -> 0` from the right at the origin, then
`trace (A r) <= m * radialCoeff k r` on `(0, r0)`.

All derivative, domain, and normalization hypotheses are explicit.  The proof
applies `scalar_riccati_comparison` to `trace A / m`; the nontriviality
assumption occurs exactly where division by `m` is required.  See
Morgan--Tian, pp. 48--49, and Petersen (2006), Chapter 9, Section 1. -/
theorem trace_riccati_comparison [Nontrivial E] {k r₀ : ℝ} (hk : 0 ≤ k)
    {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, (A r : E →ₗ[ℝ] E).IsSymmetric)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑((A r).comp (A r))
        ≤ (finrank ℝ E : ℝ) * k)
    (h0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A r) ≤ (finrank ℝ E : ℝ) * radialCoeff k r := by
  have hm : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast finrank_pos
  let traceCLM : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))
  have htraceCLM : ∀ T : E →L[ℝ] E,
      traceCLM T = LinearMap.trace ℝ E ↑T := fun _ => rfl
  set m : ℝ := (finrank ℝ E : ℝ)
  set φ : ℝ → ℝ := fun r => LinearMap.trace ℝ E ↑(A r) / m
  set φ' : ℝ → ℝ := fun r => LinearMap.trace ℝ E ↑(A' r) / m
  have hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r := by
    intro r hr
    have h := (traceCLM.hasFDerivAt.comp_hasDerivAt r (hA r hr)).div_const m
    simpa only [Function.comp_def, htraceCLM] using h
  have hric : ∀ r ∈ Ioo (0 : ℝ) r₀, φ' r + φ r ^ 2 ≤ k := by
    intro r hr
    have hCS := sq_trace_le_finrank_mul_trace_comp_self (hsym r hr)
    have hR := hRic r hr
    have hmain : LinearMap.trace ℝ E ↑(A' r) * m
        + LinearMap.trace ℝ E ↑(A r) ^ 2 ≤ k * m ^ 2 := by
      nlinarith [hCS, mul_le_mul_of_nonneg_left hR hm.le]
    have heq : φ' r + φ r ^ 2
        = (LinearMap.trace ℝ E ↑(A' r) * m
            + LinearMap.trace ℝ E ↑(A r) ^ 2) / m ^ 2 := by
      simp only [φ', φ]
      field_simp
    rw [heq, div_le_iff₀ (pow_pos hm 2)]
    exact hmain
  have h0' : Tendsto (fun r => φ r - 1 / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := h0.div_const m
    rw [zero_div] at h
    refine h.congr fun r => ?_
    simp only [φ]
    rw [sub_div]
    congr 1
    rw [div_div, mul_comm r m, ← div_div, div_self hm.ne']
  have hcmp := scalar_riccati_comparison hk hφ hric h0'
  intro r hr
  have h := hcmp r hr
  simp only [φ] at h
  simpa [mul_comm] using (div_le_iff₀ hm).mp h

/-- Flat-branch trace comparison.  At `k = 0`, the total model coefficient is
exactly `1 / r`, so the conclusion is `trace (A r) <= finrank Real E / r`. -/
theorem trace_riccati_comparison_zero [Nontrivial E] {r₀ : ℝ}
    {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, (A r : E →ₗ[ℝ] E).IsSymmetric)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑((A r).comp (A r)) ≤ 0)
    (h0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A r) ≤ (finrank ℝ E : ℝ) / r := by
  simpa [radialCoeff, div_eq_mul_inv] using
    trace_riccati_comparison (E := E) (k := 0) (by positivity) hA hsym
      (fun r hr => by simpa using hRic r hr) h0

private theorem trace_smul_one (a : ℝ) :
    LinearMap.trace ℝ E ↑(a • (1 : E →L[ℝ] E)) = (finrank ℝ E : ℝ) * a := by
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul,
    ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one]
  ring

/-- Composition-order regression: the trace of `(a id).comp (a id)` is
`finrank Real E * a^2`, matching the quadratic term in the Riccati inequality. -/
private theorem trace_comp_smul_one (a : ℝ) :
    LinearMap.trace ℝ E
        ↑((a • (1 : E →L[ℝ] E)).comp (a • (1 : E →L[ℝ] E)))
      = (finrank ℝ E : ℝ) * a ^ 2 := by
  have hcomp : (a • (1 : E →L[ℝ] E)).comp (a • (1 : E →L[ℝ] E))
      = a ^ 2 • (1 : E →L[ℝ] E) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self,
      smul_smul, pow_two]
  rw [hcomp, trace_smul_one]

/-- Exact-model regression: a scalar multiple of the identity has precisely
the dimension factor used in `trace_riccati_comparison`. -/
private theorem trace_riccati_comparison_model (k r : ℝ) :
    LinearMap.trace ℝ E ↑(radialCoeff k r • (1 : E →L[ℝ] E))
      = (finrank ℝ E : ℝ) * radialCoeff k r :=
  trace_smul_one _

/-- Flat exact-model regression: composition/trace normalization gives
`trace ((1/r) id) = finrank Real E / r`. -/
private theorem trace_riccati_comparison_flat_model (r : ℝ) :
    LinearMap.trace ℝ E ↑((1 / r) • (1 : E →L[ℝ] E))
      = (finrank ℝ E : ℝ) / r := by
  rw [trace_smul_one]
  ring

end Comparison
end Ch01
end MorganTianLib
