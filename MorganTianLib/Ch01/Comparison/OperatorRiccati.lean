import MorganTianLib.Ch01.Comparison.Model
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Operator Riccati comparison

This module lifts the scalar Riccati comparisons in
`MorganTianLib.Ch01.Comparison.Model` to continuous endomorphisms of real inner-product
spaces.  The upper flat/hyperbolic theorem works in arbitrary dimension.  The spherical lower
theorem uses an attained minimum of the Rayleigh quotient, and therefore assumes a nontrivial
finite-dimensional space.

Both the Riccati hypotheses and conclusions are stated as quadratic-form inequalities.  The
normalization at the singular endpoint is convergence in the operator norm.  No manifold,
geodesic, Jacobi-field, polar-coordinate, or cut-locus data enter this analytic layer.

The lower proof differs materially from applying scalar comparison to a fixed vector: that
argument gives the wrong inequality for the square term.  Instead, it follows a minimizing
eigenvector at each support point of the minimum Rayleigh value and closes the comparison with a
left-slope barrier.  Only the reusable Rayleigh facts are public; the support and barrier machinery
is private.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1, comparison discussion
on pp. 48--49.  The spherical direction and first-pole restriction are cross-checked against
Petersen (2016), Section 6.4, especially Corollary 6.4.2 and Theorems 6.4.3 and 6.4.6.
-/

open Real Filter Set Metric
open scoped Topology RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Comparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Quadratic forms and the upper comparison -/

/-- **Upper operator Riccati comparison.** Let `A` be a differentiable symmetric family of
continuous endomorphisms on a real inner-product space.  If, on `(0, r₀)`,

`⟪A' X, X⟫ + ⟪A (A X), X⟫ ≤ k * ‖X‖²`

and `A r - (1 / r) • id` tends to zero in operator norm at the origin, then the quadratic form of
`A r` is bounded above by `radialCoeff k r` times the norm square.  No finite-dimensionality
hypothesis is needed.

This is the manifold-free matrix comparison behind Morgan--Tian, Theorem 1.31, p. 49. -/
theorem operator_riccati_le {k r₀ : ℝ} (hk : 0 ≤ k) {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪A r X, Y⟫ = ⟪X, A r Y⟫)
    (h0 : Tendsto (fun r => A r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪A' r X, X⟫ + ⟪A r (A r X), X⟫ ≤ k * ‖X‖ ^ 2) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪A r X, X⟫ ≤ radialCoeff k r * ‖X‖ ^ 2 := by
  have hunit : ∀ X : E, ‖X‖ = 1 → ∀ r ∈ Ioo (0 : ℝ) r₀,
      ⟪A r X, X⟫ ≤ radialCoeff k r := by
    intro X hX
    have hφd : ∀ r ∈ Ioo (0 : ℝ) r₀,
        HasDerivAt (fun y => ⟪A y X, X⟫) ⟪A' r X, X⟫ r := by
      intro r hr
      have happly : HasDerivAt (fun y => A y X) (A' r X) r := by
        simpa using (hA r hr).clm_apply (hasDerivAt_const r X)
      simpa using happly.inner ℝ (hasDerivAt_const r X)
    have hφric : ∀ r ∈ Ioo (0 : ℝ) r₀,
        ⟪A' r X, X⟫ + ⟪A r X, X⟫ ^ 2 ≤ k := by
      intro r hr
      have hmain := hric r hr X
      have hsq_map : ⟪A r (A r X), X⟫ = ‖A r X‖ ^ 2 := by
        rw [hsymm r hr (A r X) X]
        exact real_inner_self_eq_norm_sq _
      have hsq_inner : ⟪A r X, X⟫ ^ 2 ≤ ‖A r X‖ ^ 2 := by
        have hbound := abs_real_inner_le_norm (A r X) X
        rw [hX, mul_one] at hbound
        nlinarith [abs_nonneg ⟪A r X, X⟫, sq_abs ⟪A r X, X⟫]
      rw [hsq_map, hX] at hmain
      nlinarith
    have hφ0 : Tendsto (fun r => ⟪A r X, X⟫ - 1 / r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      refine squeeze_zero_norm' ?_ (by simpa using h0.norm)
      filter_upwards [self_mem_nhdsWithin] with r (hr : (0 : ℝ) < r)
      have hid : ⟪(A r - r⁻¹ • ContinuousLinearMap.id ℝ E) X, X⟫ =
          ⟪A r X, X⟫ - 1 / r := by
        rw [sub_apply, inner_sub_left, smul_apply, ContinuousLinearMap.id_apply,
          real_inner_smul_left, real_inner_self_eq_norm_sq, hX]
        ring
      rw [← hid]
      simpa [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hX] using
          (A r - r⁻¹ • ContinuousLinearMap.id ℝ E).rayleighQuotient_le_norm X
    intro r hr
    exact scalar_riccati_comparison hk hφd hφric hφ0 r hr
  intro r hr X
  rcases eq_or_ne X 0 with rfl | hXne
  · simp
  have hXpos : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hXne
  have hunit' := hunit ((‖X‖⁻¹ : ℝ) • X) (norm_smul_inv_norm (𝕜 := ℝ) hXne) r hr
  rw [map_smul, real_inner_smul_left, real_inner_smul_right] at hunit'
  have hsq : (0 : ℝ) ≤ ‖X‖ ^ 2 := sq_nonneg _
  calc
    ⟪A r X, X⟫ = ‖X‖ ^ 2 * (‖X‖⁻¹ * (‖X‖⁻¹ * ⟪A r X, X⟫)) := by
      field_simp
    _ ≤ ‖X‖ ^ 2 * radialCoeff k r := mul_le_mul_of_nonneg_left hunit' hsq
    _ = radialCoeff k r * ‖X‖ ^ 2 := by ring

/-- Flat specialization of `operator_riccati_le`.  The model coefficient is exactly `1 / r`. -/
theorem operator_riccati_le_zero {r₀ : ℝ} {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪A r X, Y⟫ = ⟪X, A r Y⟫)
    (h0 : Tendsto (fun r => A r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪A' r X, X⟫ + ⟪A r (A r X), X⟫ ≤ 0) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E, ⟪A r X, X⟫ ≤ (1 / r) * ‖X‖ ^ 2 := by
  simpa [radialCoeff] using operator_riccati_le (E := E) (k := 0) (by positivity)
    hA hsymm h0 (fun r hr X => by simpa using hric r hr X)

/-! ## Minimum Rayleigh value -/

/-- The infimum of `X ↦ ⟪T X, X⟫` over the unit sphere.  For a symmetric endomorphism of a
nontrivial finite-dimensional real inner-product space, this is its smallest eigenvalue. -/
noncomputable def minRayleigh (T : E →L[ℝ] E) : ℝ :=
  sInf ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1)

private theorem bddBelow_image_sphere (T : E →L[ℝ] E) :
    BddBelow ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1) := by
  refine ⟨-‖T‖, ?_⟩
  rintro v ⟨Y, hY, rfl⟩
  have hY1 : ‖Y‖ = 1 := by simpa using hY
  have hnorm : |⟪T Y, Y⟫| ≤ ‖T‖ := by
    simpa [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, hY1] using
        T.rayleighQuotient_le_norm Y
  linarith [hnorm, neg_abs_le ⟪T Y, Y⟫]

/-- The minimum Rayleigh value bounds the quadratic form from below at every unit vector. -/
theorem minRayleigh_le {T : E →L[ℝ] E} {X : E} (hX : ‖X‖ = 1) :
    minRayleigh T ≤ ⟪T X, X⟫ :=
  csInf_le (bddBelow_image_sphere T) ⟨X, by simpa using hX, rfl⟩

section Nontrivial

variable [Nontrivial E]

private theorem sphere_one_nonempty : (sphere (0 : E) 1).Nonempty := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  exact ⟨(‖v‖⁻¹ : ℝ) • v, by simpa using norm_smul_inv_norm (𝕜 := ℝ) hv⟩

/-- The minimum Rayleigh functional is one-sided `1`-Lipschitz in the operator norm. -/
theorem minRayleigh_sub_le (T T' : E →L[ℝ] E) :
    minRayleigh T - minRayleigh T' ≤ ‖T - T'‖ := by
  by_contra hle
  have hlt : minRayleigh T' < minRayleigh T - ‖T - T'‖ := by
    push Not at hle
    linarith
  have himage : ((fun X => ⟪T' X, X⟫) '' sphere (0 : E) 1).Nonempty :=
    (sphere_one_nonempty (E := E)).image _
  obtain ⟨v, ⟨Y, hYmem, rfl⟩, hv⟩ :=
    (csInf_lt_iff (bddBelow_image_sphere T') himage).mp hlt
  have hY : ‖Y‖ = 1 := by simpa using hYmem
  have hmin : minRayleigh T ≤ ⟪T Y, Y⟫ := minRayleigh_le hY
  have hsub : ⟪T Y, Y⟫ - ⟪T' Y, Y⟫ = ⟪(T - T') Y, Y⟫ := by
    rw [sub_apply, inner_sub_left]
  have hnorm : |⟪(T - T') Y, Y⟫| ≤ ‖T - T'‖ := by
    simpa [ContinuousLinearMap.rayleighQuotient,
      ContinuousLinearMap.reApplyInnerSelf_apply, hY] using
        (T - T').rayleighQuotient_le_norm Y
  linarith [le_abs_self ⟪(T - T') Y, Y⟫]

/-- The minimum Rayleigh functional is `1`-Lipschitz in the operator norm. -/
theorem abs_minRayleigh_sub_le (T T' : E →L[ℝ] E) :
    |minRayleigh T - minRayleigh T'| ≤ ‖T - T'‖ := by
  rw [abs_sub_le_iff]
  refine ⟨minRayleigh_sub_le T T', ?_⟩
  rw [← norm_neg]
  simpa using minRayleigh_sub_le T' T

/-- The absolute minimum Rayleigh value is bounded by the operator norm. -/
theorem abs_minRayleigh_le (T : E →L[ℝ] E) : |minRayleigh T| ≤ ‖T‖ := by
  rw [abs_le]
  constructor
  · apply le_csInf ((sphere_one_nonempty (E := E)).image _)
    rintro v ⟨Y, hYmem, rfl⟩
    have hY : ‖Y‖ = 1 := by simpa using hYmem
    have hnorm : |⟪T Y, Y⟫| ≤ ‖T‖ := by
      simpa [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hY] using
          T.rayleighQuotient_le_norm Y
    linarith [neg_abs_le ⟪T Y, Y⟫]
  · obtain ⟨X, hXmem⟩ := sphere_one_nonempty (E := E)
    have hX : ‖X‖ = 1 := by simpa using hXmem
    have hmin : minRayleigh T ≤ ⟪T X, X⟫ := minRayleigh_le hX
    have hnorm : |⟪T X, X⟫| ≤ ‖T‖ := by
      simpa [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, hX] using
          T.rayleighQuotient_le_norm X
    linarith [le_abs_self ⟪T X, X⟫]

end Nontrivial

section Complete

variable [CompleteSpace E]

/-- A unit minimizer of the quadratic form of a self-adjoint endomorphism is an eigenvector whose
eigenvalue is the minimum value. -/
theorem apply_eq_minRayleigh_smul {T : E →L[ℝ] E} (hT : IsSelfAdjoint T)
    {X₀ : E} (hX₀ : ‖X₀‖ = 1)
    (hmin : IsMinOn (fun X => ⟪T X, X⟫) (sphere (0 : E) 1) X₀) :
    T X₀ = ⟪T X₀, X₀⟫ • X₀ := by
  have hX₀ne : X₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hX₀
    norm_num at hX₀
  have hextr : IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖X₀‖) X₀ := by
    rw [hX₀]
    intro Y hY
    simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hmin hY
  have hev := hT.hasEigenvector_of_isMinOn hX₀ne hextr
  have happ : T X₀ = (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) • X₀ := by
    simpa using hev.apply_eq_smul
  have hval : (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) =
      ⟪T X₀, X₀⟫ := by
    have h := congrArg (fun v => ⟪v, X₀⟫) happ
    simp only [real_inner_smul_left] at h
    rw [real_inner_self_eq_norm_sq, hX₀] at h
    simpa using h.symm
  rw [hval] at happ
  exact happ

end Complete

variable [FiniteDimensional ℝ E] [Nontrivial E]

/-- In a nontrivial finite-dimensional space, the minimum Rayleigh value is attained on the unit
sphere. -/
theorem exists_norm_eq_one_minRayleigh (T : E →L[ℝ] E) :
    ∃ X₀ : E, ‖X₀‖ = 1 ∧ ⟪T X₀, X₀⟫ = minRayleigh T ∧
      IsMinOn (fun X => ⟪T X, X⟫) (sphere (0 : E) 1) X₀ := by
  have hne : (sphere (0 : E) 1).Nonempty := sphere_one_nonempty (E := E)
  have hcont : ContinuousOn (fun X : E => ⟪T X, X⟫) (sphere 0 1) :=
    (T.continuous.inner continuous_id).continuousOn
  obtain ⟨X₀, hX₀mem, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne hcont
  have hX₀ : ‖X₀‖ = 1 := by simpa using hX₀mem
  refine ⟨X₀, hX₀, ?_, hmin⟩
  have hleast : IsLeast ((fun X => ⟪T X, X⟫) '' sphere (0 : E) 1) ⟪T X₀, X₀⟫ :=
    ⟨⟨X₀, hX₀mem, rfl⟩, by rintro v ⟨Y, hY, rfl⟩; exact hmin hY⟩
  exact hleast.csInf_eq.symm

/-! ## Private support-function argument -/

private theorem le_of_left_slope_eventually_lt {h : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hcont : ContinuousOn h (Icc c d))
    (hslope : ∀ x ∈ Ioc c d, ∀ δ : ℝ, 0 < δ → ∀ᶠ y in 𝓝[<] x, slope h y x < δ) :
    h d ≤ h c := by
  rcases eq_or_lt_of_le hcd with rfl | hlt
  · exact le_rfl
  set g : ℝ → ℝ := fun t => -h (-t) with hg
  have hgcont : ContinuousOn g (Icc (-d) (-c)) := by
    have hmaps : ∀ t ∈ Icc (-d) (-c), -t ∈ Icc c d := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact (hcont.comp continuous_neg.continuousOn hmaps).neg
  have hfence : ∀ ε : ℝ, 0 < ε → g (-c) ≤ g (-d) + ε * (-c - -d) := by
    intro ε hε
    have key := image_le_of_liminf_slope_right_lt_deriv_boundary (f := g)
      (f' := fun _ => 0) (a := -d) (b := -c) hgcont ?_
      (B := fun t => g (-d) + ε * (t - -d)) (B' := fun _ => ε) ?_ ?_ ?_
    · exact key ⟨by linarith, le_rfl⟩
    · intro x hx r hr
      have hx' : -x ∈ Ioc c d := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have hev := hslope (-x) hx' r hr
      have hmap : Tendsto (fun z : ℝ => -z) (𝓝[>] x) (𝓝[<] (-x)) := by
        refine continuous_neg.continuousWithinAt.tendsto_nhdsWithin ?_
        intro z hz
        exact mem_Iio.mpr (neg_lt_neg (mem_Ioi.mp hz))
      refine ((hmap.eventually hev).and self_mem_nhdsWithin).frequently.mono ?_
      rintro z ⟨hz, hz' : x < z⟩
      have hzx : z - x ≠ 0 := ne_of_gt (sub_pos.mpr hz')
      calc
        slope g x z = (g z - g x) / (z - x) := slope_def_field g x z
        _ = (h (-x) - h (-z)) / (-x - -z) := by
          rw [hg]
          have hne : -x - -z = z - x := by ring
          rw [hne]
          ring_nf
        _ = slope h (-z) (-x) := (slope_def_field h (-z) (-x)).symm
        _ < r := hz
    · simp
    · intro x
      simpa using (((hasDerivAt_id x).sub_const (-d)).const_mul ε).const_add (g (-d))
    · exact fun _ _ _ => hε
  by_contra hcon
  push Not at hcon
  have hdc : 0 < d - c := by linarith
  have hbound := hfence ((h d - h c) / (2 * (d - c)))
    (div_pos (by linarith) (by linarith))
  have harith : (h d - h c) / (2 * (d - c)) * (-c - -d) = (h d - h c) / 2 := by
    field_simp
    ring
  rw [harith] at hbound
  simp only [hg, neg_neg] at hbound
  linarith

private theorem eventually_lt_slope_of_upper_support {m φ : ℝ → ℝ} {x b δ : ℝ}
    (hle : ∀ y, m y ≤ φ y) (heq : m x = φ x)
    (hφ : HasDerivAt φ b x) (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝[<] x, b - δ < slope m y x := by
  have hsub : Iio x ⊆ {x}ᶜ := fun y (hy : y < x) => ne_of_lt hy
  have hslope : Tendsto (slope φ x) (𝓝[<] x) (𝓝 b) :=
    (hasDerivAt_iff_tendsto_slope.mp hφ).mono_left (nhdsWithin_mono x hsub)
  have hev : ∀ᶠ y in 𝓝[<] x, b - δ < slope φ x y :=
    hslope.eventually (eventually_gt_nhds (by linarith))
  filter_upwards [hev, self_mem_nhdsWithin] with y hy (hyx : y < x)
  have hxy : 0 < x - y := by linarith
  have h1 : slope φ x y ≤ slope m y x := by
    rw [slope_comm φ x y, slope_def_field, slope_def_field]
    have hnum : φ x - φ y ≤ m x - m y := by
      have := hle y
      linarith [heq]
    exact div_le_div_of_nonneg_right hnum hxy.le
  linarith

private theorem operator_riccati_nonneg {r₀ Cs : ℝ} {s s' : ℝ → ℝ}
    {U U' : ℝ → E →L[ℝ] E}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hsbdd : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), |s r| ≤ Cs)
    (hU : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt U (U' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪U r X, Y⟫ = ⟪X, U r Y⟫)
    (hU0 : Tendsto U (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      -(⟪U r (U r X), X⟫ + 2 * (s' r / s r) * ⟪U r X, X⟫) ≤ ⟪U' r X, X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E, 0 ≤ ⟪U r X, X⟫ := by
  set m : ℝ → ℝ := fun r => minRayleigh (U r) with hm_def
  have hmten : ∀ x ∈ Ioo (0 : ℝ) r₀, ContinuousAt m x := by
    intro x hx
    have h1 : Tendsto (fun y => U y - U x) (𝓝 x) (𝓝 (U x - U x)) :=
      (hU x hx).continuousAt.tendsto.sub tendsto_const_nhds
    rw [sub_self] at h1
    have h2 : Tendsto (fun y => ‖U y - U x‖) (𝓝 x) (𝓝 0) := by
      simpa using h1.norm
    have h3 : Tendsto (fun y => m y - m x) (𝓝 x) (𝓝 0) :=
      squeeze_zero_norm (fun y => by simpa using abs_minRayleigh_sub_le (U y) (U x)) h2
    have h4 := h3.add_const (m x)
    change Tendsto m (nhds x) (nhds (m x))
    simpa only [sub_add_cancel, zero_add] using h4
  have hm0 : Tendsto m (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm (fun r => by simpa using abs_minRayleigh_le (U r)) ?_
    simpa using hU0.norm
  suffices hmain : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ m r by
    intro r hr X
    rcases eq_or_ne X 0 with rfl | hXne
    · simp
    have hunit : ‖(‖X‖⁻¹ : ℝ) • X‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hXne
    have h1 : (0 : ℝ) ≤ ⟪U r ((‖X‖⁻¹ : ℝ) • X), (‖X‖⁻¹ : ℝ) • X⟫ :=
      (hmain r hr).trans (minRayleigh_le hunit)
    rw [map_smul, real_inner_smul_left, real_inner_smul_right] at h1
    have hX : (0 : ℝ) < ‖X‖ := norm_pos_iff.mpr hXne
    have hXi : (0 : ℝ) < ‖X‖⁻¹ := inv_pos.mpr hX
    by_contra hneg
    push Not at hneg
    have h3 : ‖X‖⁻¹ * (‖X‖⁻¹ * ⟪U r X, X⟫) < 0 :=
      mul_neg_of_pos_of_neg hXi (mul_neg_of_pos_of_neg hXi hneg)
    linarith
  by_contra hcon
  push Not at hcon
  obtain ⟨r₂, hr₂, hm₂⟩ := hcon
  obtain ⟨W, hW0, hWb⟩ : ∃ W, 0 ≤ W ∧ ∀ r ∈ Ioc (0 : ℝ) r₂, ‖U r‖ ≤ W := by
    have h1 : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), ‖U r‖ ≤ 1 := by
      have h2 : Tendsto (fun r => ‖U r‖) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        simpa using hU0.norm
      exact (h2.eventually (eventually_lt_nhds one_pos)).mono fun r hr => hr.le
    obtain ⟨ε, hε, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h1
    have hε₁pos : 0 < min ε r₂ := lt_min hε hr₂.1
    obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Icc (min ε r₂) r₂, ‖U x‖ ≤ C := by
      refine isCompact_Icc.exists_bound_of_continuousOn fun x hx => ?_
      exact ((hU x ⟨lt_of_lt_of_le hε₁pos hx.1,
        lt_of_le_of_lt hx.2 hr₂.2⟩).continuousAt).continuousWithinAt
    refine ⟨max 1 C, le_trans zero_le_one (le_max_left _ _), fun r hr => ?_⟩
    rcases lt_or_ge r (min ε r₂) with hlt | hge
    · exact le_trans (hIoo ⟨hr.1, lt_of_lt_of_le hlt (min_le_left _ _)⟩)
        (le_max_left _ _)
    · exact le_trans (hC r ⟨hge, hr.2⟩) (le_max_right _ _)
  have hmW : ∀ r ∈ Ioc (0 : ℝ) r₂, -(m r) ≤ W := by
    intro r hr
    have hbound := (abs_minRayleigh_le (U r)).trans (hWb r hr)
    have habs := neg_abs_le (m r)
    linarith
  set S : Set ℝ := insert 0 {r ∈ Ioc (0 : ℝ) r₂ | 0 ≤ m r} with hS
  have hS0 : (0 : ℝ) ∈ S := mem_insert _ _
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hSbdd : BddAbove S := by
    refine ⟨r₂, ?_⟩
    rintro x (rfl | ⟨hx, -⟩)
    · exact hr₂.1.le
    · exact hx.2
  set r₃ : ℝ := sSup S with hr₃def
  have hr₃0 : 0 ≤ r₃ := le_csSup hSbdd hS0
  have hr₃r₂ : r₃ < r₂ := by
    have hev : ∀ᶠ y in 𝓝 r₂, m y < 0 :=
      (hmten r₂ hr₂).eventually (eventually_lt_nhds hm₂)
    obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    have hbound : ∀ x ∈ S, x ≤ max l 0 := by
      rintro x (rfl | ⟨hx1, hx2⟩)
      · exact le_max_right _ _
      by_contra hgt
      push Not at hgt
      have hxIoo : x ∈ Ioo l u :=
        ⟨lt_of_le_of_lt (le_max_left _ _) hgt, lt_of_le_of_lt hx1.2 hmem.2⟩
      exact absurd hx2 (not_le.mpr (hsub hxIoo))
    exact lt_of_le_of_lt (csSup_le hSne hbound) (max_lt hmem.1 hr₂.1)
  have hmneg : ∀ x ∈ Ioc r₃ r₂, m x < 0 := by
    intro x hx
    by_contra hge
    push Not at hge
    have hxS : x ∈ S :=
      mem_insert_of_mem _ ⟨⟨lt_of_le_of_lt hr₃0 hx.1, hx.2⟩, hge⟩
    exact absurd (le_csSup hSbdd hxS) (not_le.mpr hx.1)
  have hr₃m : 0 < r₃ → 0 ≤ m r₃ := by
    intro hr₃pos
    by_contra hneg
    push Not at hneg
    have hr₃mem : r₃ ∈ Ioo (0 : ℝ) r₀ :=
      ⟨hr₃pos, lt_trans (lt_of_lt_of_le hr₃r₂ le_rfl) hr₂.2⟩
    have hev : ∀ᶠ y in 𝓝 r₃, m y < 0 :=
      (hmten r₃ hr₃mem).eventually (eventually_lt_nhds hneg)
    obtain ⟨l, u, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hev
    obtain ⟨x, hxS, hxgt⟩ :=
      exists_lt_of_lt_csSup hSne (show max l 0 < r₃ from max_lt hmem.1 hr₃pos)
    have hxle : x ≤ r₃ := le_csSup hSbdd hxS
    rcases hxS with rfl | ⟨hx1, hx2⟩
    · exact absurd hxgt (not_lt.mpr (le_max_right _ _))
    have hxIoo : x ∈ Ioo l u :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hxgt, lt_of_le_of_lt hxle hmem.2⟩
    exact absurd hx2 (not_le.mpr (hsub hxIoo))
  set ρ : ℝ → ℝ := fun r => s r ^ 2 * Real.exp (-(W * r)) with hρ_def
  set h : ℝ → ℝ := fun r => -(m r) * ρ r with hh_def
  have hρpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < ρ r := by
    intro r hr
    have := hspos r hr
    positivity
  have hρd : ∀ x ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt ρ ((2 * s x * s' x - W * s x ^ 2) * Real.exp (-(W * x))) x := by
    intro x hx
    have h1 : HasDerivAt (fun r => s r ^ 2) (2 * s x * s' x) x := by
      have hfun : (fun r => s r ^ 2) = s ^ 2 := by
        funext r
        rfl
      rw [hfun]
      simpa [mul_comm, mul_assoc, mul_left_comm] using (hs x hx).pow 2
    have h2 : HasDerivAt (fun r => Real.exp (-(W * r)))
        (Real.exp (-(W * x)) * -W) x := by
      have h3 : HasDerivAt (fun r : ℝ => -(W * r)) (-W) x := by
        have hfun : (fun r : ℝ => -(W * r)) = -(fun r : ℝ => W * r) := by
          funext r
          rfl
        rw [hfun]
        simpa using ((hasDerivAt_id x).const_mul W).neg
      exact h3.exp
    have hprod := h1.mul h2
    have hfun : ρ = (fun r => s r ^ 2) * fun r => Real.exp (-(W * r)) := by
      funext r
      rfl
    rw [hfun]
    exact hprod.congr_deriv (by ring)
  have hhcont : ∀ x ∈ Ioo (0 : ℝ) r₀, ContinuousAt h x := by
    intro x hx
    exact ((hmten x hx).neg).mul ((hρd x hx).continuousAt)
  have hslopeh : ∀ x ∈ Ioc r₃ r₂, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ y in 𝓝[<] x, slope h y x < δ := by
    intro x hx δ hδ
    have hxIoo : x ∈ Ioo (0 : ℝ) r₀ :=
      ⟨lt_of_le_of_lt hr₃0 hx.1, lt_of_le_of_lt hx.2 hr₂.2⟩
    have hx02 : x ∈ Ioc (0 : ℝ) r₂ := ⟨hxIoo.1, hx.2⟩
    have hρx : 0 < ρ x := hρpos x hxIoo
    have hsx : 0 < s x := hspos x hxIoo
    obtain ⟨X₀, hX₀unit, hX₀val, hX₀min⟩ := exists_norm_eq_one_minRayleigh (U x)
    have heig : U x X₀ = ⟪U x X₀, X₀⟫ • X₀ :=
      apply_eq_minRayleigh_smul
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (hsymm x hxIoo))
        hX₀unit hX₀min
    have hφd : HasDerivAt (fun y => ⟪U y X₀, X₀⟫) ⟪U' x X₀, X₀⟫ x := by
      have h1 : HasDerivAt (fun y => U y X₀) (U' x X₀) x := by
        simpa using (hU x hxIoo).clm_apply (hasDerivAt_const x X₀)
      simpa using h1.inner ℝ (hasDerivAt_const x X₀)
    have hφ'lb : -(m x ^ 2 + 2 * (s' x / s x) * m x) ≤ ⟪U' x X₀, X₀⟫ := by
      have h1 := hric x hxIoo X₀
      have h2 : ⟪U x X₀, X₀⟫ = m x := hX₀val
      have h3 : ⟪U x (U x X₀), X₀⟫ = m x ^ 2 := by
        rw [heig, map_smul, real_inner_smul_left, h2]
        ring
      rw [h3, h2] at h1
      linarith
    set δ₁ : ℝ := δ / (2 * ρ x) with hδ₁_def
    have hδ₁pos : 0 < δ₁ := by positivity
    have hm_slope : ∀ᶠ y in 𝓝[<] x, ⟪U' x X₀, X₀⟫ - δ₁ < slope m y x :=
      eventually_lt_slope_of_upper_support
        (fun y => minRayleigh_le hX₀unit) hX₀val.symm hφd hδ₁pos
    set ρ'x : ℝ := (2 * s x * s' x - W * s x ^ 2) * Real.exp (-(W * x))
      with hρ'x_def
    have hρslope : Tendsto (fun y => slope ρ y x) (𝓝[<] x) (𝓝 ρ'x) := by
      have h1 := hasDerivAt_iff_tendsto_slope.mp (hρd x hxIoo)
      have h2 := h1.mono_left
        (nhdsWithin_mono x (fun y (hy : y < x) => ne_of_lt hy))
      exact h2.congr fun y => slope_comm ρ x y
    have hwcont : Tendsto (fun y => -(m y)) (𝓝[<] x) (𝓝 (-(m x))) :=
      ((hmten x hxIoo).neg).tendsto.mono_left nhdsWithin_le_nhds
    have hprod : Tendsto (fun y => -(m y) * slope ρ y x) (𝓝[<] x)
        (𝓝 (-(m x) * ρ'x)) := hwcont.mul hρslope
    have hprod_ev : ∀ᶠ y in 𝓝[<] x,
        -(m y) * slope ρ y x < -(m x) * ρ'x + δ / 2 :=
      hprod.eventually (eventually_lt_nhds (by linarith))
    have hmx : m x < 0 := hmneg x hx
    have hmxW : -(m x) ≤ W := hmW x hx02
    have hmain_le :
        ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x ≤ 0 := by
      have hexp : (0 : ℝ) < Real.exp (-(W * x)) := Real.exp_pos _
      have hkey :
          ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x =
            Real.exp (-(W * x)) * s x ^ 2 * (m x * (m x + W)) := by
        rw [hρ_def, hρ'x_def]
        field_simp
        ring
      rw [hkey]
      have h1 : m x * (m x + W) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hmx.le (by linarith)
      have h2 : (0 : ℝ) ≤ Real.exp (-(W * x)) * s x ^ 2 := by positivity
      exact mul_nonpos_of_nonneg_of_nonpos h2 h1
    filter_upwards [hm_slope, hprod_ev, self_mem_nhdsWithin]
      with y h1 h2 (h3 : y < x)
    have hxy : x - y ≠ 0 := by
      intro hzero
      have : x = y := by linarith [sub_eq_zero.mp hzero]
      linarith
    have hkey : slope h y x = ρ x * (-(slope m y x)) + -(m y) * slope ρ y x := by
      rw [slope_def_field, slope_def_field, slope_def_field, hh_def]
      field_simp
      ring
    have hb1 : -(slope m y x) < -(⟪U' x X₀, X₀⟫) + δ₁ := by linarith
    have hb2 : -(⟪U' x X₀, X₀⟫) ≤ m x ^ 2 + 2 * (s' x / s x) * m x := by
      linarith
    have hb3 : ρ x * (-(slope m y x)) <
        ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + ρ x * δ₁ := by
      have h4 : -(slope m y x) < m x ^ 2 + 2 * (s' x / s x) * m x + δ₁ := by
        linarith
      have h5 := mul_lt_mul_of_pos_left h4 hρx
      rw [mul_add] at h5
      exact h5
    have hδ₁ρ : ρ x * δ₁ = δ / 2 := by
      rw [hδ₁_def]
      field_simp
    rw [hkey]
    calc
      ρ x * (-(slope m y x)) + -(m y) * slope ρ y x <
          (ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + ρ x * δ₁) +
            (-(m x) * ρ'x + δ / 2) := by linarith
      _ = (ρ x * (m x ^ 2 + 2 * (s' x / s x) * m x) + -(m x) * ρ'x) +
            (ρ x * δ₁ + δ / 2) := by ring
      _ ≤ 0 + (δ / 2 + δ / 2) := by rw [hδ₁ρ]; linarith
      _ = δ := by ring
  have hh2pos : 0 < h r₂ := by
    have hw2 : 0 < -(m r₂) := neg_pos.mpr hm₂
    have hρ2 : 0 < ρ r₂ := hρpos r₂ hr₂
    exact mul_pos hw2 hρ2
  obtain ⟨rb, hrbmem, hrblt⟩ : ∃ rb ∈ Ioo r₃ r₂, h rb < h r₂ := by
    have hIoomem : Ioo r₃ r₂ ∈ 𝓝[>] r₃ := Ioo_mem_nhdsGT hr₃r₂
    rcases eq_or_lt_of_le hr₃0 with hr₃eq | hr₃pos
    · have hten : Tendsto h (𝓝[>] r₃) (𝓝 0) := by
        rw [← hr₃eq]
        have hbound : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), ‖h r‖ ≤ |m r| * Cs ^ 2 := by
          filter_upwards [hsbdd, self_mem_nhdsWithin] with r hr (hrpos : 0 < r)
          have hρle : ρ r ≤ Cs ^ 2 := by
            have h1 : s r ^ 2 ≤ Cs ^ 2 := by
              have := sq_abs (s r)
              nlinarith [abs_nonneg (s r)]
            have h2 : Real.exp (-(W * r)) ≤ 1 := by
              rw [Real.exp_le_one_iff]
              nlinarith
            nlinarith [sq_nonneg (s r), Real.exp_pos (-(W * r))]
          have hρnn : 0 ≤ ρ r := by positivity
          rw [hh_def]
          simp only [norm_mul, Real.norm_eq_abs, abs_neg]
          calc
            |m r| * |ρ r| = |m r| * ρ r := by rw [abs_of_nonneg hρnn]
            _ ≤ |m r| * Cs ^ 2 := mul_le_mul_of_nonneg_left hρle (abs_nonneg _)
        have hg0 : Tendsto (fun r => |m r| * Cs ^ 2)
            (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
          have hlim := hm0.abs.mul_const (Cs ^ 2)
          simpa using hlim
        exact squeeze_zero_norm' hbound hg0
      have hev := (hten.eventually (eventually_lt_nhds hh2pos)).and hIoomem
      obtain ⟨rb, hrb1, hrb2⟩ := hev.exists
      exact ⟨rb, hrb2, hrb1⟩
    · have hr₃mem : r₃ ∈ Ioo (0 : ℝ) r₀ := ⟨hr₃pos, lt_trans hr₃r₂ hr₂.2⟩
      have hh3 : h r₃ ≤ 0 := by
        have hw3 : -(m r₃) ≤ 0 := by linarith [hr₃m hr₃pos]
        have hρ3 : 0 ≤ ρ r₃ := (hρpos r₃ hr₃mem).le
        exact mul_nonpos_of_nonpos_of_nonneg hw3 hρ3
      have hten : Tendsto h (𝓝[>] r₃) (𝓝 (h r₃)) :=
        (hhcont r₃ hr₃mem).tendsto.mono_left nhdsWithin_le_nhds
      have hev := (hten.eventually
        (eventually_lt_nhds (lt_of_le_of_lt hh3 hh2pos))).and hIoomem
      obtain ⟨rb, hrb1, hrb2⟩ := hev.exists
      exact ⟨rb, hrb2, hrb1⟩
  have hcontIcc : ContinuousOn h (Icc rb r₂) := by
    intro z hz
    have hzIoo : z ∈ Ioo (0 : ℝ) r₀ :=
      ⟨lt_of_le_of_lt hr₃0 (lt_of_lt_of_le hrbmem.1 hz.1),
        lt_of_le_of_lt hz.2 hr₂.2⟩
    exact (hhcont z hzIoo).continuousWithinAt
  have hslopeIcc : ∀ x ∈ Ioc rb r₂, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ y in 𝓝[<] x, slope h y x < δ := by
    intro x hx δ hδ
    exact hslopeh x ⟨lt_trans hrbmem.1 hx.1, hx.2⟩ δ hδ
  have hfinal := le_of_left_slope_eventually_lt hrbmem.2.le hcontIcc hslopeIcc
  linarith

/-! ## Spherical lower comparison -/

/-- **Spherical lower operator Riccati comparison.** Let `A` be a differentiable symmetric
family of continuous endomorphisms of a nontrivial finite-dimensional real inner-product space.
Assume every radius in `(0, r₀)` is before the first spherical pole, and

`-K * ‖X‖² ≤ ⟪A' X, X⟫ + ⟪A (A X), X⟫`.

If `A r - (1 / r) • id` tends to zero in operator norm at the origin, then
`logDerivPos K r • id ≤ A r` as quadratic forms.  The `K = 0` branch is total and has no finite
pole.

The minimum-Rayleigh argument is the analytic operator form of the upper-sectional-curvature
comparison discussed by Morgan--Tian on p. 49; see also Petersen (2016), Section 6.4. -/
theorem logDerivPos_le_operator_riccati {K r₀ : ℝ} (hK : 0 ≤ K)
    {A A' : ℝ → E →L[ℝ] E}
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r)
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪A r X, Y⟫ = ⟪X, A r Y⟫)
    (h0 : Tendsto (fun r => A r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      -K * ‖X‖ ^ 2 ≤ ⟪A' r X, X⟫ + ⟪A r (A r X), X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      logDerivPos K r * ‖X‖ ^ 2 ≤ ⟪A r X, X⟫ := by
  set a : ℝ → ℝ := logDerivPos K with ha
  set U : ℝ → E →L[ℝ] E := fun r => A r - a r • ContinuousLinearMap.id ℝ E with hUdef
  set U' : ℝ → E →L[ℝ] E := fun r =>
    A' r - (-(K + a r ^ 2)) • ContinuousLinearMap.id ℝ E with hU'def
  have hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt (snPos K) (csPos K r) r :=
    fun r _ => hasDerivAt_snPos K r hK
  have hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < snPos K r :=
    fun r hr => snPos_pos K r hK (hpole r hr)
  have hsbdd : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), |snPos K r| ≤ 1 := by
    have hsn0 : Tendsto (snPos K) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      simpa using
        (hasDerivAt_snPos K 0 hK).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hzero : ‖(0 : ℝ)‖ < 1 := by norm_num
    have hevent := hsn0.norm.eventually (eventually_lt_nhds hzero)
    exact hevent.mono fun r hr => by simpa [Real.norm_eq_abs] using hr.le
  have hU : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt U (U' r) r := by
    intro r hr
    have ha' : HasDerivAt a (-(K + a r ^ 2)) r := by
      rw [ha]
      exact hasDerivAt_logDerivPos K r hK (hpole r hr)
    rw [hUdef, hU'def]
    exact (hA r hr).sub (ha'.smul_const (ContinuousLinearMap.id ℝ E))
  have hUsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E,
      ⟪U r X, Y⟫ = ⟪X, U r Y⟫ := by
    intro r hr X Y
    rw [hUdef, sub_apply, sub_apply, inner_sub_left, inner_sub_right,
      smul_apply, smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_left, real_inner_smul_right, hsymm r hr]
  have hU0 : Tendsto U (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have ha0 : Tendsto (fun r => a r - 1 / r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      rw [ha]
      exact tendsto_logDerivPos_sub_inv K hK
    have ha0op := ha0.smul_const (ContinuousLinearMap.id ℝ E)
    have hdiff := h0.sub ha0op
    rw [hUdef]
    convert hdiff using 1
    · funext r
      ext X
      simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, sub_smul]
      module
    · simp
  have hUric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      -(⟪U r (U r X), X⟫ +
          2 * (csPos K r / snPos K r) * ⟪U r X, X⟫) ≤ ⟪U' r X, X⟫ := by
    intro r hr X
    have ha_div : csPos K r / snPos K r = a r := by
      rw [ha]
      exact (logDerivPos_eq_div K r hK).symm
    have hUX : U r X = A r X - a r • X := by
      simp [hUdef]
    have hinnerU : ⟪U r X, X⟫ = ⟪A r X, X⟫ - a r * ‖X‖ ^ 2 := by
      rw [hUX, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hinnerUU : ⟪U r (U r X), X⟫ =
        ⟪A r (A r X), X⟫ - 2 * a r * ⟪A r X, X⟫ + a r ^ 2 * ‖X‖ ^ 2 := by
      rw [hUX]
      simp only [hUdef, sub_apply, map_sub, map_smul, smul_apply,
        ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
      ring
    have hinnerU' : ⟪U' r X, X⟫ =
        ⟪A' r X, X⟫ + (K + a r ^ 2) * ‖X‖ ^ 2 := by
      simp only [hU'def, sub_apply, smul_apply, ContinuousLinearMap.id_apply,
        inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
      ring
    rw [ha_div, hinnerU, hinnerUU, hinnerU']
    nlinarith [hric r hr X]
  have hnonneg := operator_riccati_nonneg (E := E) (r₀ := r₀) (Cs := 1)
    hs hspos hsbdd hU hUsymm hU0 hUric
  intro r hr X
  have h := hnonneg r hr X
  rw [hUdef, sub_apply, inner_sub_left, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left, real_inner_self_eq_norm_sq, ha] at h
  linarith

/-- Flat specialization of `logDerivPos_le_operator_riccati`.  There is no first-pole bound in
this branch, and the model coefficient is exactly `1 / r`. -/
theorem inv_le_operator_riccati {r₀ : ℝ} {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsymm : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E, ⟪A r X, Y⟫ = ⟪X, A r Y⟫)
    (h0 : Tendsto (fun r => A r - r⁻¹ • ContinuousLinearMap.id ℝ E)
      (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      0 ≤ ⟪A' r X, X⟫ + ⟪A r (A r X), X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      (1 / r) * ‖X‖ ^ 2 ≤ ⟪A r X, X⟫ := by
  simpa [logDerivPos] using logDerivPos_le_operator_riccati (E := E) (K := 0)
    (by positivity) (fun r hr => (beforeFirstPole_zero_iff r).2 hr.1)
    hA hsymm h0 (fun r hr X => by simpa using hric r hr X)

/-! ## Compile-time model regressions -/

omit [FiniteDimensional ℝ E] [Nontrivial E] in
private theorem operator_riccati_le_model {k r₀ : ℝ} (hk : 0 ≤ k) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪(radialCoeff k r • ContinuousLinearMap.id ℝ E) X, X⟫ ≤
        radialCoeff k r * ‖X‖ ^ 2 := by
  apply operator_riccati_le hk
  · intro r hr
    have hcoeff : HasDerivAt (radialCoeff k)
        (k - radialCoeff k r ^ 2) r := by
      rw [show radialCoeff k = cs k / sn k by
        funext x
        exact radialCoeff_eq_div k x hk]
      exact hasDerivAt_cs_div_sn k r hk hr.1
    exact hcoeff.smul_const (ContinuousLinearMap.id ℝ E)
  · intro r hr X Y
    simp [real_inner_smul_left, real_inner_smul_right]
  · have hcoeff := (tendsto_radialCoeff_sub_inv k hk).smul_const
      (ContinuousLinearMap.id ℝ E)
    simpa [sub_smul] using hcoeff
  · intro r hr X
    simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring_nf
    exact le_rfl

private theorem logDerivPos_le_operator_riccati_model {K r₀ : ℝ} (hK : 0 ≤ K)
    (hpole : ∀ r ∈ Ioo (0 : ℝ) r₀, BeforeFirstPole K r) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      logDerivPos K r * ‖X‖ ^ 2 ≤
        ⟪(logDerivPos K r • ContinuousLinearMap.id ℝ E) X, X⟫ := by
  apply logDerivPos_le_operator_riccati hK hpole
  · intro r hr
    exact (hasDerivAt_logDerivPos K r hK (hpole r hr)).smul_const
      (ContinuousLinearMap.id ℝ E)
  · intro r hr X Y
    simp [real_inner_smul_left, real_inner_smul_right]
  · have hcoeff := (tendsto_logDerivPos_sub_inv K hK).smul_const
      (ContinuousLinearMap.id ℝ E)
    simpa [sub_smul] using hcoeff
  · intro r hr X
    simp only [smul_apply, ContinuousLinearMap.id_apply, map_smul,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith

end Comparison
end Ch01
end MorganTianLib
