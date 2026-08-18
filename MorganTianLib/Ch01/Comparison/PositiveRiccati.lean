import MorganTianLib.Ch01.Comparison.Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Positive-curvature scalar Riccati comparison

This module proves the scalar Riccati comparison for the positive-curvature
model from `MorganTianLib.Ch01.Comparison.Model`.  Its proof constructs an
interval-integral primitive, so the theorem lives here to keep the model
profiles, origin estimates, and ODE facts independent of measure integration.

Source: Petersen (2016), Section 6.4, Corollary 6.4.2(2), in the direction
used by the upper-sectional-curvature comparison.
-/

open Real Filter Set
open scoped Topology

namespace MorganTianLib
namespace Ch01
namespace Comparison

private theorem scalar_riccati_comparison_pos_of_primitive
    {K r₀ : ℝ} (hK : 0 ≤ K) {φ φ' D : ℝ → ℝ}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, -K ≤ φ' r + φ r ^ 2)
    (hdiff : Tendsto (fun r => φ r - logDerivPos K r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hD : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt D (φ r - logDerivPos K r) r)
    (hD0 : Tendsto D (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, logDerivPos K r ≤ φ r := by
  set a : ℝ → ℝ := logDerivPos K with ha
  set d : ℝ → ℝ := fun r => φ r - a r with hd
  set ψ : ℝ → ℝ := fun r => d r * snPos K r ^ 2 * Real.exp (D r) with hψ
  set ψ' : ℝ → ℝ := fun r =>
    snPos K r ^ 2 * Real.exp (D r) * (φ' r + K + φ r ^ 2) with hψ'
  have hdψ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ψ (ψ' r) r := by
    intro r hr
    have hsnpos : 0 < snPos K r := snPos_pos K r hK (hpole r hr)
    have haDeriv : HasDerivAt a (-(K + a r ^ 2)) r := by
      rw [ha]
      exact hasDerivAt_logDerivPos K r hK (hpole r hr)
    have hdDeriv : HasDerivAt d (φ' r - (-(K + a r ^ 2))) r := by
      rw [hd]
      exact (hφ r hr).sub haDeriv
    have hsq : HasDerivAt (fun x => snPos K x ^ 2)
        (2 * snPos K r * csPos K r) r := by
      have h := (hasDerivAt_snPos K r hK).pow 2
      apply h.congr_deriv
      push_cast
      ring
    have hexp : HasDerivAt (fun x => Real.exp (D x))
        (Real.exp (D r) * d r) r := by
      simpa [hd, ha] using (hD r hr).exp
    have h := (hdDeriv.mul hsq).mul hexp
    rw [hψ]
    apply h.congr_deriv
    have hcs : csPos K r = snPos K r * a r := by
      rw [ha, logDerivPos_eq_div K r hK]
      field_simp
    simp only [hψ', hcs, Pi.mul_apply]
    rw [hd]
    ring
  have hψ'nonneg : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ ψ' r := by
    intro r hr
    have hmain : 0 ≤ φ' r + K + φ r ^ 2 := by
      have := hric r hr
      linarith
    rw [hψ']
    positivity
  have hmono : MonotoneOn ψ (Ioo (0 : ℝ) r₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := ψ') (convex_Ioo _ _)
      (fun r hr => (hdψ r hr).continuousAt.continuousWithinAt)
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Ioo] at hr
      exact (hdψ r hr).hasDerivWithinAt
    · rw [interior_Ioo] at hr
      exact hψ'nonneg r hr
  have hsn_zero : Tendsto (fun r => snPos K r ^ 2)
      (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have h : Tendsto (snPos K) (nhds (0 : ℝ)) (nhds 0) := by
      simpa using (hasDerivAt_snPos K 0 hK).continuousAt.tendsto
    simpa using (h.mono_left nhdsWithin_le_nhds).pow 2
  have hψ_zero : Tendsto ψ (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hd_zero : Tendsto d (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      simpa [hd, ha] using hdiff
    have hDexp : Tendsto (fun r => Real.exp (D r))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
      change Tendsto (Real.exp ∘ D) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)
      have h := Real.continuous_exp.tendsto 0 |>.comp hD0
      simpa only [Real.exp_zero] using h
    have h := (hd_zero.mul hsn_zero).mul hDexp
    rw [zero_mul] at h
    simpa [hψ] using h
  intro r hr
  have hψnonneg : 0 ≤ ψ r := by
    have hev : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), ψ s ≤ ψ r := by
      have hpos : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s ∈ Ioi (0 : ℝ) :=
        eventually_mem_nhdsWithin
      have hlt : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s < r :=
        (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [hpos, hlt] with s hs hsr
      exact hmono ⟨hs, hsr.trans hr.2⟩ hr hsr.le
    exact le_of_tendsto hψ_zero hev
  have hfac : 0 < snPos K r ^ 2 * Real.exp (D r) := by
    exact mul_pos (pow_pos (snPos_pos K r hK (hpole r hr)) 2) (Real.exp_pos _)
  have hdnonneg : 0 ≤ d r := by
    apply (mul_nonneg_iff_of_pos_right hfac).1
    simpa [hψ, mul_assoc] using hψnonneg
  rw [hd, ha] at hdnonneg
  linarith

/-- Scalar Riccati comparison for the upper-sectional-curvature direction.
On `(0, r₀)` inside the regular first-pole interval, a differentiable scalar
with `-K <= φ' + φ^2` and Euclidean singular normalization
`φ r - 1/r -> 0` is bounded below by the spherical model coefficient.

The proof constructs the normalized integrating factor from the continuous
difference `φ - logDerivPos K`; no antiderivative or geometric producer is
part of the public hypotheses.  This is Petersen (2016), Corollary 6.4.2(2),
in the direction consumed by `Comparison.sectional_upper`. -/
theorem scalar_riccati_comparison_pos {K r₀ : ℝ} (hK : 0 ≤ K)
    {φ φ' : ℝ → ℝ}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, -K ≤ φ' r + φ r ^ 2)
    (h0 : Tendsto (fun r => φ r - 1 / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, logDerivPos K r ≤ φ r := by
  rcases le_or_gt r₀ 0 with hr₀ | hr₀
  · intro r hr
    exact (not_lt_of_ge hr₀ (hr.1.trans hr.2)).elim
  have hdiff : Tendsto (fun r => φ r - logDerivPos K r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h := h0.sub (tendsto_logDerivPos_sub_inv K hK)
    rw [sub_zero] at h
    refine h.congr fun r => ?_
    ring
  set d : ℝ → ℝ := fun r => φ r - logDerivPos K r with hd
  set d₀ : ℝ → ℝ := Function.update d 0 0 with hd₀
  set D : ℝ → ℝ := fun r => ∫ x in 0..r, d₀ x with hDdef
  have hcontdAt : ∀ r ∈ Ioo (0 : ℝ) r₀, ContinuousAt d r := by
    intro r hr
    rw [hd]
    exact ((hφ r hr).sub
      (hasDerivAt_logDerivPos K r hK (hpole r hr))).continuousAt
  have hcontAt : ∀ r ∈ Ioo (0 : ℝ) r₀, ContinuousAt d₀ r := by
    intro r hr
    rw [hd₀, continuousAt_update_of_ne hr.1.ne']
    exact hcontdAt r hr
  have hcont : ∀ r ∈ Ioo (0 : ℝ) r₀, ContinuousOn d₀ (Icc 0 r) := by
    intro r hr
    rw [hd₀, continuousOn_update_iff]
    constructor
    · intro x hx
      have hxne : x ≠ 0 := by simpa using hx.2
      have hxpos : 0 < x := lt_of_le_of_ne hx.1.1 (Ne.symm hxne)
      have hxmem : x ∈ Ioo (0 : ℝ) r₀ := ⟨hxpos, hx.1.2.trans_lt hr.2⟩
      exact (hcontdAt x hxmem).continuousWithinAt
    · intro _
      apply hdiff.mono_left
      apply nhdsWithin_mono
      intro x hx
      have hxne : x ≠ 0 := by simpa using hx.2
      exact lt_of_le_of_ne hx.1.1 (Ne.symm hxne)
  have hD : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt D (φ r - logDerivPos K r) r := by
    intro r hr
    have hmeas := ContinuousAt.stronglyMeasurableAtFilter
      (μ := MeasureTheory.volume) isOpen_Ioo hcontAt r hr
    have hint := intervalIntegral.integral_hasDerivAt_right
      ((hcont r hr).intervalIntegrable_of_Icc hr.1.le) hmeas (hcontAt r hr)
    simpa [hDdef, hd₀, hd, hr.1.ne'] using hint
  have hD0 : Tendsto D (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    set r₁ : ℝ := r₀ / 2 with hr₁
    have hr₁mem : r₁ ∈ Ioo (0 : ℝ) r₀ := by
      rw [hr₁]
      constructor <;> linarith
    have hc := hcont r₁ hr₁mem
    have hfilter : nhdsWithin 0 (Ioc 0 r₁) = nhdsWithin 0 (Ioi 0) := by
      rw [show Ioc (0 : ℝ) r₁ = Iic r₁ ∩ Ioi 0 by ext x; simp [and_comm]]
      exact nhdsWithin_inter_of_mem
        (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hr₁mem.1))
    have hint : IntervalIntegrable d₀ MeasureTheory.volume 0 0 := by
      rw [intervalIntegrable_iff]
      simp
    have hcIoc : ContinuousOn d₀ (Ioc 0 r₁) := hc.mono Ioc_subset_Icc_self
    have hmeas := hcIoc.stronglyMeasurableAtFilter_nhdsWithin
      (μ := MeasureTheory.volume) measurableSet_Ioc 0
    rw [hfilter] at hmeas
    have hc0 := (hc 0 ⟨le_rfl, hr₁mem.1.le⟩).mono Ioc_subset_Icc_self
    rw [ContinuousWithinAt, hfilter] at hc0
    have hderiv : HasDerivWithinAt D 0 (Ici 0) 0 := by
      have h := intervalIntegral.integral_hasDerivWithinAt_right
        (s := Ici (0 : ℝ)) (t := Ioi 0) hint hmeas hc0
      simpa [hDdef, hd₀] using h
    have h := hderiv.continuousWithinAt.tendsto.mono_left
      (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    simpa [hDdef] using h
  exact scalar_riccati_comparison_pos_of_primitive hK hpole hφ hric hdiff hD hD0

/-- Flat-branch form of `scalar_riccati_comparison_pos`.  The totalized model
coefficient is exactly `1/r`, with no finite first-pole restriction. -/
theorem scalar_riccati_comparison_pos_zero {r₀ : ℝ} {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ φ' r + φ r ^ 2)
    (h0 : Tendsto (fun r => φ r - 1 / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, 1 / r ≤ φ r := by
  simpa [logDerivPos] using scalar_riccati_comparison_pos (K := 0) (by positivity)
    (fun r hr => (beforeFirstPole_zero_iff r).2 hr.1) hφ
    (fun r hr => by simpa using hric r hr) h0

/-- Exact-model regression for `scalar_riccati_comparison_pos`.  Running the
comparison theorem on `logDerivPos K` checks the differential sign, singular
normalization, and first-pole domain simultaneously. -/
private theorem scalar_riccati_comparison_pos_model {K r₀ : ℝ} (hK : 0 ≤ K)
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, logDerivPos K r ≤ logDerivPos K r := by
  apply scalar_riccati_comparison_pos hK hpole
  · exact fun r hr => hasDerivAt_logDerivPos K r hK (hpole r hr)
  · intro _ _
    simp
  · exact tendsto_logDerivPos_sub_inv K hK

end Comparison
end Ch01
end MorganTianLib
