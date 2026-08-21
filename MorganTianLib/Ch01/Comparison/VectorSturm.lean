import MorganTianLib.Ch01.Comparison.Model
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Vector-valued Sturm comparison

This module contains the manifold-free vector step in the comparison argument
of Morgan--Tian, Chapter 1, pp. 48--49.  For a curve `V : ℝ → E` in a real
inner-product space, it proves the norm derivative identities away from zeros
and reduces the vector inequality to `Comparison.scalar_sturm_comparison_pos`.

The public comparison theorem assumes the explicit origin value `V 0 = 0`,
continuity on the closed interval, twice differentiability in its interior,
an eventual bound on `‖V'‖` at the right origin, and the slope limit
`‖V t‖ / t → c`.  Its curvature hypothesis is
`⟪V'' t, V t⟫ ≥ -(K * ‖V t‖^2)`.  The endpoint is obtained by continuity, and
the positive-slope corollary rules out zeros by taking the infimum of the
closed zero set rather than assuming an unproved first-zero convention.

No manifold, geodesic, Jacobi-field, frame, or polar-density data occur here.
The source anchor is Morgan--Tian, *Ricci Flow and the Poincare Conjecture*,
the comparison discussion on printed pp. 48--49, especially the positive
upper-curvature paragraph between Theorem 1.31 and Lemma 1.32 (retained arXiv
pagination).  This module supplies only an analytic input to that geometric
argument.  The scalar theorem used below is the already proved A1 interface in
`Comparison.Model`.
-/

open Real Filter Set
open scoped Topology RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from a zero of `V`, the norm has derivative
`⟪V', V⟫ / ‖V‖`. -/
theorem hasDerivAt_norm_of_ne_zero {V : ℝ → E} {v' : E} {t : ℝ}
    (hd : HasDerivAt V v' t) (hne : V t ≠ 0) :
    HasDerivAt (fun s => ‖V s‖) (⟪v', V t⟫ / ‖V t‖) t := by
  have hpos : (0 : ℝ) < ‖V t‖ := norm_pos_iff.mpr hne
  have hsqne : ‖V t‖ ^ 2 ≠ 0 := by positivity
  have h := (Real.hasDerivAt_sqrt hsqne).comp t hd.norm_sq
  have h' : HasDerivAt (fun s => Real.sqrt (‖V s‖ ^ 2))
      (1 / (2 * Real.sqrt (‖V t‖ ^ 2)) * (2 * ⟪V t, v'⟫)) t := h
  have heq : (fun s => Real.sqrt (‖V s‖ ^ 2)) = fun s => ‖V s‖ := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [heq] at h'
  convert h' using 1
  rw [Real.sqrt_sq (norm_nonneg _), real_inner_comm]
  field_simp

/-- Away from a zero of `V`, the derivative of
`⟪V', V⟫ / ‖V‖` is
`(⟪V'', V⟫ + ‖V'‖²) / ‖V‖ - ⟪V', V⟫² / ‖V‖³`. -/
theorem hasDerivAt_inner_div_norm {V V' : ℝ → E} {w : E} {s : ℝ}
    (hdV : HasDerivAt V (V' s) s) (hdV' : HasDerivAt V' w s) (hne : V s ≠ 0) :
    HasDerivAt (fun u => ⟪V' u, V u⟫ / ‖V u‖)
      ((⟪w, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ - ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3) s := by
  have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr hne
  have hnum : HasDerivAt (fun u => ⟪V' u, V u⟫)
      (⟪V' s, V' s⟫ + ⟪w, V s⟫) s := hdV'.inner ℝ hdV
  have hden : HasDerivAt (fun u => ‖V u‖) (⟪V' s, V s⟫ / ‖V s‖) s :=
    hasDerivAt_norm_of_ne_zero hdV hne
  have h := hnum.div hden hpos.ne'
  exact h.congr_deriv (by
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring)

/-- Vector Sturm comparison on a strict first-pole interval.

If `K ≥ 0`, `BeforeFirstPole K T`, and `V` satisfies the stated origin,
regularity, derivative-bound, slope, and curvature hypotheses, then
`c * snPos K t ≤ ‖V t‖` for every `0 < t ≤ T`.  The `c ≤ 0` branch is
totalized directly; the `c > 0` branch normalizes the norm by `c` and uses
the scalar Sturm theorem from `Comparison.Model` on each interval before a
hypothetical zero.

This is the manifold-free Sturm input to Morgan--Tian's positive
upper-curvature discussion between Theorem 1.31 and Lemma 1.32, printed
pp. 48--49; it does not assert the geometric comparison itself. -/
theorem vector_sturm_comparison {K T c C : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K T) {V V' V'' : ℝ → E}
    (hV0 : V 0 = 0)
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T, -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, c * snPos K t ≤ ‖V t‖ := by
  have hbefore : ∀ t ∈ Ioc (0 : ℝ) T, BeforeFirstPole K t := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rcases hpole.2 with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr <| (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)).trans_lt hlt
  have hsnpos : ∀ t ∈ Ioc (0 : ℝ) T, 0 < snPos K t := by
    intro t ht
    exact snPos_pos K t hK (hbefore t ht)
  by_cases hc : c ≤ 0
  · intro t ht
    have hsn := hsnpos t ht
    nlinarith [norm_nonneg (V t)]
  push Not at hc
  have hVne : ∀ᶠ s in 𝓝[>] (0 : ℝ), V s ≠ 0 := by
    filter_upwards [hslope.eventually (eventually_gt_nhds hc)] with s hs hzero
    rw [hzero, norm_zero, zero_div] at hs
    exact (lt_irrefl 0 hs)
  have hstep : ∀ t₁ ∈ Ioc (0 : ℝ) T,
      (∀ s ∈ Ioo (0 : ℝ) t₁, V s ≠ 0) →
        c * snPos K t₁ ≤ ‖V t₁‖ := by
    intro t₁ ht₁ hnz
    have hsub : Ioo (0 : ℝ) t₁ ⊆ Ioo (0 : ℝ) T :=
      Ioo_subset_Ioo le_rfl ht₁.2
    have hpole₁ : BeforeFirstPole K t₁ := hbefore t₁ ht₁
    let f : ℝ → ℝ := fun s => ‖V s‖ / c
    let f' : ℝ → ℝ := fun s => (⟪V' s, V s⟫ / ‖V s‖) / c
    let f'' : ℝ → ℝ := fun s =>
      ((⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ -
        ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3) / c
    have hf : ContinuousOn f (Icc 0 t₁) := by
      intro s hs
      exact ((hVc s ((Icc_subset_Icc le_rfl ht₁.2) hs)).norm.div_const c).mono
        (Icc_subset_Icc le_rfl ht₁.2)
    have hf0 : f 0 = 0 := by simp [f, hV0]
    have hslopef : Tendsto (fun s => (‖V s‖ / c) / s)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := hslope.div_const c
      rw [div_self hc.ne'] at h
      refine h.congr fun s => by ring
    have hunit : HasDerivWithinAt f 1 (Ici 0) 0 := by
      apply (hasDerivWithinAt_iff_tendsto_slope).2
      have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
        ext s
        simp [lt_iff_le_and_ne]
      rw [hset]
      refine hslopef.congr fun s => ?_
      simp [f, slope_def_field, hV0]
    have hD1 : ∀ s ∈ Ioo (0 : ℝ) t₁, HasDerivAt f (f' s) s := by
      intro s hs
      simpa [f, f'] using
        (hasDerivAt_norm_of_ne_zero (hd1 s (hsub hs)) (hnz s hs)).div_const c
    have hD2 : ∀ s ∈ Ioo (0 : ℝ) t₁, HasDerivAt f' (f'' s) s := by
      intro s hs
      simpa [f', f''] using
        (hasDerivAt_inner_div_norm (hd1 s (hsub hs)) (hd2 s (hsub hs))
          (hnz s hs)).div_const c
    have hineq : ∀ s ∈ Ioo (0 : ℝ) t₁, -(K * f s) ≤ f'' s := by
      intro s hs
      have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr (hnz s hs)
      have hCS : ⟪V' s, V s⟫ ^ 2 ≤ ‖V' s‖ ^ 2 * ‖V s‖ ^ 2 := by
        have h := abs_real_inner_le_norm (V' s) (V s)
        nlinarith [abs_nonneg ⟪V' s, V s⟫, sq_abs ⟪V' s, V s⟫,
          mul_nonneg (norm_nonneg (V' s)) (norm_nonneg (V s))]
      have hjs := hjac s (hsub hs)
      have h1 :
          (⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ -
              ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3 =
            ((⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) * ‖V s‖ ^ 2 -
              ⟪V' s, V s⟫ ^ 2) / ‖V s‖ ^ 3 := by
        field_simp
      have hE : -(K * ‖V s‖) ≤
          (⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ -
            ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3 := by
        rw [h1, le_div_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hjs (sq_nonneg ‖V s‖)]
      dsimp [f, f'']
      calc
        -(K * (‖V s‖ / c)) = (-(K * ‖V s‖)) / c := by ring
        _ ≤ ((⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ -
            ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3) / c :=
          div_le_div_of_nonneg_right hE hc.le
    have hbddf : ∀ᶠ s in 𝓝[>] (0 : ℝ), |f' s| ≤ C / c := by
      filter_upwards [hbdd, hVne] with s hC hne
      have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr hne
      have hq : |⟪V' s, V s⟫ / ‖V s‖| ≤ ‖V' s‖ := by
        rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
        exact abs_real_inner_le_norm _ _
      calc
        |f' s| = |⟪V' s, V s⟫ / ‖V s‖| / c := by
          simp only [f', abs_div, abs_of_pos hc]
        _ ≤ ‖V' s‖ / c := div_le_div_of_nonneg_right hq hc.le
        _ ≤ C / c := div_le_div_of_nonneg_right hC hc.le
    have hcmp := scalar_sturm_comparison_pos (K := K) (r₀ := t₁)
      (C := C / c) hK hpole₁ hf hf0 hunit hD1 hD2 hineq hbddf
    have hcmp₁ : snPos K t₁ ≤ ‖V t₁‖ / c :=
      hcmp t₁ ⟨ht₁.1, le_rfl⟩
    have hscaled := (le_div_iff₀ hc).mp hcmp₁
    nlinarith
  obtain ⟨ε, hε, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hVne
  have hnzall : ∀ s ∈ Ioc (0 : ℝ) T, V s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀, hz₀V⟩ := hcon
    have hzge : ∀ z ∈ Ioc (0 : ℝ) T, V z = 0 → ε ≤ z := by
      intro z hz hzV
      by_contra hlt
      push Not at hlt
      exact hIoo ⟨hz.1, hlt⟩ hzV
    set Z : Set ℝ := Icc ε T ∩ V ⁻¹' {0} with hZdef
    have hZclosed : IsClosed Z :=
      (hVc.mono (Icc_subset_Icc (le_of_lt hε) le_rfl)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hz₀Z : z₀ ∈ Z :=
      ⟨⟨hzge z₀ hz₀ hz₀V, hz₀.2⟩, by simpa using hz₀V⟩
    have hZbdd : BddBelow Z := bddBelow_Icc.mono inter_subset_left
    have htZ : sInf Z ∈ Z := hZclosed.csInf_mem ⟨z₀, hz₀Z⟩ hZbdd
    have htpos : 0 < sInf Z := lt_of_lt_of_le hε htZ.1.1
    have htT : sInf Z ≤ T := htZ.1.2
    have htV : V (sInf Z) = 0 := by simpa using htZ.2
    have hnz' : ∀ s ∈ Ioo (0 : ℝ) (sInf Z), V s ≠ 0 := by
      intro s hs hsV
      have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1, (hs.2.le.trans htT)⟩
      have hsZ : s ∈ Z :=
        ⟨⟨hzge s hsT hsV, hsT.2⟩, by simpa using hsV⟩
      exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hs.2)
    have hcontra := hstep (sInf Z) ⟨htpos, htT⟩ hnz'
    rw [htV, norm_zero] at hcontra
    have hsin := hsnpos (sInf Z) ⟨htpos, htT⟩
    nlinarith
  intro t ht
  exact hstep t ht fun s hs => hnzall s ⟨hs.1, hs.2.le.trans ht.2⟩

/-- Positive-slope form of `vector_sturm_comparison`: a curve satisfying its
hypotheses has no zero on the closed positive interval `(0, T]`.  Turning this
analytic statement into a no-conjugate-point theorem requires the later
Jacobi/sectional-curvature producer. -/
theorem vector_sturm_ne_zero {K T c C : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K T) {V V' V'' : ℝ → E}
    (hV0 : V 0 = 0)
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T, -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C)
    (hc : 0 < c)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, V t ≠ 0 := by
  intro t ht hzero
  have h := vector_sturm_comparison hK hpole hV0 hVc hd1 hd2 hjac hbdd hslope t ht
  rw [hzero, norm_zero] at h
  have hmodel : 0 < snPos K t := snPos_pos K t hK ⟨ht.1, ?_⟩
  · nlinarith
  · rcases hpole.2 with hKzero | hlt
    · exact Or.inl hKzero
    · exact Or.inr <| (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)).trans_lt hlt

/-- A one-sided derivative at an explicit zero gives the norm slope limit used
by `vector_sturm_comparison`. -/
theorem tendsto_norm_div_self_of_hasDerivWithinAt {V : ℝ → E} {v₀ : E}
    (h0 : V 0 = 0) (hd : HasDerivWithinAt V v₀ (Ici 0) 0) :
    Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 ‖v₀‖) := by
  have hs' : Tendsto (slope V 0) (𝓝[>] 0) (𝓝 v₀) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hd
    have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext x
      simp [lt_iff_le_and_ne]
    rw [hset] at h
    exact h
  have hnorm : Tendsto (fun t => ‖slope V 0 t‖) (𝓝[>] 0) (𝓝 ‖v₀‖) := hs'.norm
  refine hnorm.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
  rw [slope_def_module, h0, sub_zero, sub_zero, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos ht]
  ring

/-! ## Small model regressions

These private checks instantiate the public theorem on explicit models.  The
exact ODE equality in the inner-product hypothesis catches a reversed
curvature sign; the equality wrappers separately exercise the flat branch, a
strict positive-curvature branch, an arbitrary constant direction, and a
two-dimensional Euclidean space.  The nonconstant flat curve `t + t^2` guards
the comparison direction.  These are compile-time checks only and do not add a
geometric producer to the public API.
-/

private theorem spherical_model_vector_regression {K T : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K T) (v : E) :
    ∀ t ∈ Ioc (0 : ℝ) T, ‖v‖ * snPos K t ≤ ‖snPos K t • v‖ := by
  let V : ℝ → E := fun t => snPos K t • v
  let V' : ℝ → E := fun t => csPos K t • v
  let V'' : ℝ → E := fun t => -(K * snPos K t) • v
  have hV0 : V 0 = 0 := by simp [V]
  have hVc : ContinuousOn V (Icc 0 T) := by
    intro t ht
    exact ((hasDerivAt_snPos K t hK).smul_const v).continuousAt.continuousWithinAt
  have hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t := by
    intro t ht
    simpa [V, V'] using (hasDerivAt_snPos K t hK).smul_const v
  have hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t := by
    intro t ht
    have h := (hasDerivAt_csPos K t hK).smul_const v
    simpa [V', V'', mul_comm, mul_left_comm, mul_assoc] using h
  have hjac : ∀ t ∈ Ioo (0 : ℝ) T, -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫ := by
    intro t ht
    simp only [V, V'', real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (snPos_nonneg K t hK ⟨ht.1.le, ?_⟩)]
    · ring_nf
      nlinarith [sq_nonneg (snPos K t), sq_nonneg ‖v‖]
    · rcases hpole.2 with hzero | hlt
      · exact Or.inl hzero
      · exact Or.inr <|
          (mul_le_mul_of_nonneg_left ht.2.le (Real.sqrt_nonneg K)).trans hlt.le
  have hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ ‖v‖ := by
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    simp only [V', norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg v) (abs_csPos_le_one K t hK)
  have hd0 : HasDerivWithinAt V v (Ici 0) 0 := by
    simpa [V] using (hasDerivAt_snPos K 0 hK).smul_const v |>.hasDerivWithinAt
  have hslope := tendsto_norm_div_self_of_hasDerivWithinAt hV0 hd0
  have hcmp := vector_sturm_comparison hK hpole hV0 hVc hd1 hd2 hjac hbdd hslope
  intro t ht
  simpa [V] using hcmp t ht

private theorem flat_model_regression {T : ℝ} (hT : 0 < T) (v : ℝ) :
    ∀ t ∈ Ioc (0 : ℝ) T, ‖v‖ * t ≤ ‖t • v‖ := by
  simpa [snPos_zero_left] using
    (spherical_model_vector_regression (E := ℝ) (K := 0) (T := T)
      (by positivity) (beforeFirstPole_zero_iff T |>.2 hT) v)

private theorem flat_comparison_direction_regression (v : E) (hv : ‖v‖ = 1) :
    ∀ t ∈ Ioc (0 : ℝ) 1, t ≤ ‖(t + t ^ 2) • v‖ := by
  let V : ℝ → E := fun t => (t + t ^ 2) • v
  let V' : ℝ → E := fun t => (1 + 2 * t) • v
  let V'' : ℝ → E := fun _ => (2 : ℝ) • v
  have hV0 : V 0 = 0 := by simp [V]
  have hVc : ContinuousOn V (Icc 0 1) := by
    fun_prop
  have hd1 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V (V' t) t := by
    intro t ht
    simpa only [V, V', Pi.add_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      one_mul] using ((hasDerivAt_id t).add (hasDerivAt_pow 2 t)).smul_const v
  have hd2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt V' (V'' t) t := by
    intro t ht
    simpa only [V', V'', Pi.add_apply, id_eq, zero_add, mul_one] using
      ((hasDerivAt_const t (1 : ℝ)).add
        ((hasDerivAt_id t).const_mul 2)).smul_const v
  have hjac : ∀ t ∈ Ioo (0 : ℝ) 1, -((0 : ℝ) * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫ := by
    intro t ht
    simp only [V, V'', zero_mul, neg_zero, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [hv]
    nlinarith [ht.1]
  have hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ 3 := by
    filter_upwards [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with t ht hlt
    have htpos : 0 < t := ht
    rw [show V' t = (1 + 2 * t) • v by rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith), hv, mul_one]
    linarith
  have hd0 : HasDerivWithinAt V v (Ici 0) 0 := by
    apply HasDerivAt.hasDerivWithinAt
    simpa only [V, Pi.add_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      one_mul, mul_zero, add_zero, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).add (hasDerivAt_pow 2 (0 : ℝ))).smul_const v
  have hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 1) := by
    simpa [hv] using tendsto_norm_div_self_of_hasDerivWithinAt hV0 hd0
  have hcmp := vector_sturm_comparison (E := E) (K := 0) (T := 1)
    (c := 1) (C := 3) (by positivity) (by simp [BeforeFirstPole]) hV0 hVc hd1 hd2
      hjac hbdd hslope
  simpa [V] using hcmp

private theorem positive_curvature_model_regression {K T : ℝ} (hK : 0 < K)
    (hpole : BeforeFirstPole K T) (v : ℝ) :
    ∀ t ∈ Ioc (0 : ℝ) T, ‖v‖ * snPos K t ≤ ‖snPos K t • v‖ :=
  spherical_model_vector_regression (E := ℝ) hK.le hpole v

private theorem constant_direction_regression {K T : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K T) (v : E) :
    ∀ t ∈ Ioc (0 : ℝ) T, ‖v‖ * snPos K t ≤ ‖snPos K t • v‖ :=
  spherical_model_vector_regression hK hpole v

private theorem low_dimensional_model_regression {K T : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K T) (v : EuclideanSpace ℝ (Fin 2)) :
    ∀ t ∈ Ioc (0 : ℝ) T, ‖v‖ * snPos K t ≤ ‖snPos K t • v‖ :=
  spherical_model_vector_regression (E := EuclideanSpace ℝ (Fin 2)) hK hpole v

end Comparison
end Ch01
end MorganTianLib
