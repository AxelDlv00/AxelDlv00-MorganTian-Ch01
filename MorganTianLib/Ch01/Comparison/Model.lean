import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Real.Sqrt

/-!
# Chapter 1 comparison model functions

This module contains the scalar profiles used by the comparison arguments in
Morgan--Tian, Chapter 1.  `sn k r` is the flat/hyperbolic profile

`sn k r = r` when `k = 0`, and `sinh (sqrt k * r) / sqrt k` when `k > 0`.

The positive-curvature profile `snPos K r` is the corresponding sine solution.
The definitions are total so they can be passed through ordinary Lean APIs;
theorems involving geometry carry the nonnegativity and first-pole hypotheses
that give these total functions their intended meaning.  In particular, the
flat radial logarithmic derivative is defined as `1 / r`, rather than by a
division by the zero parameter.

The model functions are the analytic A1 layer.  They do not quantify over a
manifold, a Jacobi field, or a polar density; those bridges belong to later
milestones.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
Definition 1.30 and the comparison discussion on pp. 48--49; the positive
curvature first-pole facts are cross-checked against Petersen (2016),
Section 6.4.
-/

open Real Filter Set
open scoped Topology

namespace MorganTianLib
namespace Ch01
namespace Comparison

/-! ## Flat and hyperbolic profiles -/

/-- The flat/hyperbolic radial profile `sn_k`.  The branch at `k = 0` is
explicit so that the definition remains total and has no zero denominator. -/
noncomputable def sn (k r : ℝ) : ℝ :=
  if k = 0 then r else Real.sinh (Real.sqrt k * r) / Real.sqrt k

/-- The derivative profile `cs_k = sn_k'`. -/
noncomputable def cs (k r : ℝ) : ℝ :=
  if k = 0 then 1 else Real.cosh (Real.sqrt k * r)

/-- The hyperbolic cotangent factor.  It is only used with `0 < k` and
`0 < r`; the zero branch is a harmless total value. -/
noncomputable def ct (k r : ℝ) : ℝ :=
  if k = 0 then 0 else cs k r / (Real.sqrt k * sn k r)

/-- The radial logarithmic derivative `sn_k' / sn_k`, with the flat branch
spelled out to avoid division by `sn 0 r` at the origin. -/
noncomputable def radialCoeff (k r : ℝ) : ℝ :=
  if k = 0 then 1 / r else cs k r / sn k r

@[simp] theorem sn_zero_left (r : ℝ) : sn 0 r = r := by
  simp [sn]

@[simp] theorem sn_zero_right (k : ℝ) : sn k 0 = 0 := by
  unfold sn
  split <;> simp

@[simp] theorem cs_zero_right (k : ℝ) : cs k 0 = 1 := by
  unfold cs
  split <;> simp

theorem sn_eq (k r : ℝ) (hk : 0 < k) :
    sn k r = Real.sinh (Real.sqrt k * r) / Real.sqrt k := by
  simp [sn, hk.ne']

theorem cs_eq (k r : ℝ) (hk : 0 < k) :
    cs k r = Real.cosh (Real.sqrt k * r) := by
  simp [cs, hk.ne']

theorem ct_eq (k r : ℝ) (hk : 0 < k) :
    ct k r = Real.cosh (Real.sqrt k * r) / Real.sinh (Real.sqrt k * r) := by
  have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk).ne'
  simp only [ct, if_neg hk.ne', cs_eq k r hk, sn_eq k r hk]
  field_simp

theorem hasDerivAt_sn (k r : ℝ) (hk : 0 ≤ k) :
    HasDerivAt (sn k) (cs k r) r := by
  rcases hk.eq_or_lt with rfl | hk
  · have hfun : sn 0 = fun x : ℝ => x := by funext x; simp [sn]
    have hcs : cs 0 = fun _ : ℝ => (1 : ℝ) := by funext x; simp [cs]
    rw [hfun, hcs]
    exact hasDerivAt_id r
  · have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk).ne'
    have harg : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt k)
    have hsinh := harg.sinh.div_const (Real.sqrt k)
    have hfun : sn k = fun x : ℝ => Real.sinh (Real.sqrt k * x) / Real.sqrt k := by
      funext x; exact sn_eq k x hk
    rw [hfun]
    have heq : Real.cosh (Real.sqrt k * r) * Real.sqrt k / Real.sqrt k = cs k r := by
      rw [cs_eq k r hk, mul_div_assoc, div_self hsqrt, mul_one]
    rwa [heq] at hsinh

theorem hasDerivAt_cs (k r : ℝ) (hk : 0 ≤ k) :
    HasDerivAt (cs k) (k * sn k r) r := by
  rcases hk.eq_or_lt with rfl | hk
  · have hfun : cs 0 = fun _ : ℝ => (1 : ℝ) := by funext x; simp [cs]
    rw [hfun]
    simp only [zero_mul]
    exact hasDerivAt_const r (1 : ℝ)
  · have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk).ne'
    have harg : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt k)
    have hcosh := harg.cosh
    rw [show cs k = fun x : ℝ => Real.cosh (Real.sqrt k * x) by
      funext x; exact cs_eq k x hk]
    convert hcosh using 1
    rw [sn_eq k r hk]
    field_simp
    rw [Real.sq_sqrt hk.le]

/-- The normalized model solves `sn'' = k sn`, with `sn 0 = 0` and
`sn' 0 = 1`. -/
theorem sn_ode (k : ℝ) (hk : 0 ≤ k) :
    (∀ r, deriv (deriv (sn k)) r = k * sn k r) ∧
      sn k 0 = 0 ∧ deriv (sn k) 0 = 1 := by
  have hderiv : deriv (sn k) = cs k := funext fun r => (hasDerivAt_sn k r hk).deriv
  refine ⟨fun r => ?_, sn_zero_right k, ?_⟩
  · rw [hderiv]
    exact (hasDerivAt_cs k r hk).deriv
  · rw [hderiv]
    exact cs_zero_right k

theorem cs_pos (k r : ℝ) (hk : 0 ≤ k) : 0 < cs k r := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [cs]
  · rw [cs_eq k r hk]
    exact lt_of_lt_of_le (by norm_num) (Real.one_le_cosh _)

theorem sn_pos (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) : 0 < sn k r := by
  rcases hk.eq_or_lt with rfl | hk
  · simpa [sn] using hr
  · rw [sn_eq k r hk]
    exact div_pos (Real.sinh_pos_iff.2 (mul_pos (Real.sqrt_pos.2 hk) hr))
      (Real.sqrt_pos.2 hk)

theorem sn_nonneg (k r : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) : 0 ≤ sn k r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  · exact (sn_pos k r hk hr).le

theorem sn_strictMono (k : ℝ) (hk : 0 ≤ k) : StrictMono (sn k) :=
  strictMono_of_hasDerivAt_pos (fun r => hasDerivAt_sn k r hk)
    (fun r => cs_pos k r hk)

theorem cs_sq_sub_mul_sn_sq (k r : ℝ) (hk : 0 ≤ k) :
    cs k r ^ 2 - k * sn k r ^ 2 = 1 := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [cs, sn]
  · rw [cs_eq k r hk, sn_eq k r hk, div_pow, Real.sq_sqrt hk.le]
    field_simp [hk.ne']
    exact Real.cosh_sq_sub_sinh_sq _

theorem self_le_sn (k r : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) : r ≤ sn k r := by
  rcases hk.eq_or_lt with rfl | hk
  · simp
  · rw [sn_eq k r hk]
    rw [le_div_iff₀ (Real.sqrt_pos.2 hk)]
    calc
      r * Real.sqrt k = Real.sqrt k * r := mul_comm _ _
      _ ≤ Real.sinh (Real.sqrt k * r) :=
        Real.self_le_sinh_iff.2 (by positivity)

/-- On the positive branch, `radialCoeff` is `sqrt k * ct k r`. -/
theorem radialCoeff_eq (k r : ℝ) (hk : 0 < k) :
    radialCoeff k r = Real.sqrt k * ct k r := by
  simp only [radialCoeff, if_neg hk.ne', ct_eq k r hk]
  rw [sn_eq k r hk, cs_eq k r hk]
  field_simp

/-! ## Positive-curvature spherical profiles -/

/-- The spherical profile `s_K`, totalized at `K = 0` by the flat profile. -/
noncomputable def snPos (K r : ℝ) : ℝ :=
  if K = 0 then r else Real.sin (Real.sqrt K * r) / Real.sqrt K

/-- The derivative profile `csPos = snPos'`. -/
noncomputable def csPos (K r : ℝ) : ℝ :=
  if K = 0 then 1 else Real.cos (Real.sqrt K * r)

/-- The positive-curvature logarithmic derivative on its regular domain. -/
noncomputable def logDerivPos (K r : ℝ) : ℝ :=
  if K = 0 then 1 / r else Real.sqrt K * (Real.cos (Real.sqrt K * r) /
    Real.sin (Real.sqrt K * r))

/-- The first positive zero of `snPos`.  The flat branch is unbounded. -/
noncomputable def firstPole (K : ℝ) : WithTop ℝ :=
  if K = 0 then ⊤ else (Real.pi / Real.sqrt K : ℝ)

/-- A radius lies before the first spherical pole.  This formulation keeps
the flat branch unbounded without forcing finite arithmetic on `⊤`. -/
def BeforeFirstPole (K r : ℝ) : Prop :=
  0 < r ∧ (K = 0 ∨ Real.sqrt K * r < Real.pi)

@[simp] theorem firstPole_zero : firstPole 0 = ⊤ := by
  simp [firstPole]

theorem firstPole_eq (K : ℝ) (hK : 0 < K) :
    firstPole K = (Real.pi / Real.sqrt K : ℝ) := by
  simp [firstPole, hK.ne']

@[simp] theorem beforeFirstPole_zero_iff (r : ℝ) :
    BeforeFirstPole 0 r ↔ 0 < r := by
  simp [BeforeFirstPole]

theorem beforeFirstPole_iff (K r : ℝ) (hK : 0 < K) :
    BeforeFirstPole K r ↔ 0 < r ∧ Real.sqrt K * r < Real.pi := by
  simp [BeforeFirstPole, hK.ne']

@[simp] theorem snPos_zero_left (r : ℝ) : snPos 0 r = r := by
  simp [snPos]

@[simp] theorem snPos_zero_right (K : ℝ) : snPos K 0 = 0 := by
  unfold snPos
  split <;> simp

@[simp] theorem csPos_zero_right (K : ℝ) : csPos K 0 = 1 := by
  unfold csPos
  split <;> simp

theorem snPos_eq (K r : ℝ) (hK : 0 < K) :
    snPos K r = Real.sin (Real.sqrt K * r) / Real.sqrt K := by
  simp [snPos, hK.ne']

/-- The first finite spherical pole is a zero of the positive-curvature
profile. -/
theorem snPos_firstPole (K : ℝ) (hK : 0 < K) :
    snPos K (Real.pi / Real.sqrt K) = 0 := by
  rw [snPos_eq K _ hK]
  have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
  have harg : Real.sqrt K * (Real.pi / Real.sqrt K) = Real.pi := by
    field_simp
  rw [harg, Real.sin_pi, zero_div]

theorem csPos_eq (K r : ℝ) (hK : 0 < K) :
    csPos K r = Real.cos (Real.sqrt K * r) := by
  simp [csPos, hK.ne']

theorem hasDerivAt_snPos (K r : ℝ) (hK : 0 ≤ K) :
    HasDerivAt (snPos K) (csPos K r) r := by
  rcases hK.eq_or_lt with rfl | hK
  · have hfun : snPos 0 = fun x : ℝ => x := by funext x; simp [snPos]
    have hcs : csPos 0 = fun _ : ℝ => (1 : ℝ) := by funext x; simp [csPos]
    rw [hfun, hcs]
    exact hasDerivAt_id r
  · have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
    have harg : HasDerivAt (fun x : ℝ => Real.sqrt K * x) (Real.sqrt K) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt K)
    have hsin := harg.sin.div_const (Real.sqrt K)
    have hfun : snPos K = fun x : ℝ => Real.sin (Real.sqrt K * x) / Real.sqrt K := by
      funext x; exact snPos_eq K x hK
    rw [hfun]
    have heq : Real.cos (Real.sqrt K * r) * Real.sqrt K / Real.sqrt K = csPos K r := by
      rw [csPos_eq K r hK, mul_div_assoc, div_self hsqrt, mul_one]
    rwa [heq] at hsin

theorem hasDerivAt_csPos (K r : ℝ) (hK : 0 ≤ K) :
    HasDerivAt (csPos K) (-(K * snPos K r)) r := by
  rcases hK.eq_or_lt with rfl | hK
  · have hfun : csPos 0 = fun _ : ℝ => (1 : ℝ) := by funext x; simp [csPos]
    rw [hfun]
    simp only [zero_mul, neg_zero]
    exact hasDerivAt_const r (1 : ℝ)
  · have hsqrt : Real.sqrt K ≠ 0 := (Real.sqrt_pos.2 hK).ne'
    have harg : HasDerivAt (fun x : ℝ => Real.sqrt K * x) (Real.sqrt K) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt K)
    have hcos := harg.cos
    rw [show csPos K = fun x : ℝ => Real.cos (Real.sqrt K * x) by
      funext x; exact csPos_eq K x hK]
    convert hcos using 1
    rw [snPos_eq K r hK]
    field_simp
    rw [Real.sq_sqrt hK.le]

/-- The spherical profile satisfies `s'' + K s = 0`. -/
theorem snPos_ode (K : ℝ) (hK : 0 ≤ K) :
    (∀ r, deriv (deriv (snPos K)) r = -(K * snPos K r)) ∧
      snPos K 0 = 0 ∧ deriv (snPos K) 0 = 1 := by
  have hderiv : deriv (snPos K) = csPos K :=
    funext fun r => (hasDerivAt_snPos K r hK).deriv
  refine ⟨fun r => ?_, snPos_zero_right K, ?_⟩
  · rw [hderiv]
    exact (hasDerivAt_csPos K r hK).deriv
  · rw [hderiv]
    exact csPos_zero_right K

theorem snPos_pos (K r : ℝ) (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r) : 0 < snPos K r := by
  rcases hK.eq_or_lt with rfl | hK
  · simpa using hpole.1
  · rw [snPos_eq K r hK]
    rcases hpole.2 with hzero | hlt
    · exact (hK.ne' hzero).elim
    · exact div_pos (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos (Real.sqrt_pos.2 hK) hpole.1) hlt) (Real.sqrt_pos.2 hK)

theorem snPos_nonneg (K r : ℝ) (hK : 0 ≤ K)
    (hpole : 0 ≤ r ∧ (K = 0 ∨ Real.sqrt K * r ≤ Real.pi)) :
    0 ≤ snPos K r := by
  rcases hK.eq_or_lt with rfl | hK
  · simpa using hpole.1
  · rw [snPos_eq K r hK]
    rcases hpole.2 with hzero | hle
    · exact (hK.ne' hzero).elim
    · exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (mul_nonneg (Real.sqrt_nonneg K) hpole.1) hle) (Real.sqrt_pos.2 hK).le

theorem abs_csPos_le_one (K r : ℝ) (hK : 0 ≤ K) : |csPos K r| ≤ 1 := by
  rcases hK.eq_or_lt with rfl | hK
  · simp [csPos]
  · rw [csPos_eq K r hK]
    exact Real.abs_cos_le_one _

theorem csPos_sq_add_mul_snPos_sq (K r : ℝ) (hK : 0 ≤ K) :
    csPos K r ^ 2 + K * snPos K r ^ 2 = 1 := by
  rcases hK.eq_or_lt with rfl | hK
  · simp [csPos, snPos]
  · rw [csPos_eq K r hK, snPos_eq K r hK, div_pow, Real.sq_sqrt hK.le]
    field_simp [hK.ne']
    exact Real.cos_sq_add_sin_sq _

theorem snPos_le_self (K r : ℝ) (hK : 0 ≤ K) (hr : 0 ≤ r) : snPos K r ≤ r := by
  rcases hK.eq_or_lt with rfl | hK
  · simp
  · rw [snPos_eq K r hK]
    rw [div_le_iff₀ (Real.sqrt_pos.2 hK)]
    calc
      Real.sin (Real.sqrt K * r) ≤ Real.sqrt K * r :=
        Real.sin_le (by positivity)
      _ = r * Real.sqrt K := mul_comm _ _

/-- The normalized spherical profile has unit right-hand slope at the origin.
This includes the flat branch `K = 0` without a separate convention. -/
theorem tendsto_snPos_div_self (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun r => snPos K r / r) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_snPos K 0 hK)
  rw [csPos_zero_right] at hslope
  have hmono : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
    nhdsWithin_mono 0 fun _ hx => ne_of_gt hx
  refine (hslope.mono_left hmono).congr fun r => ?_
  simp [slope_def_field, div_eq_inv_mul]

theorem logDerivPos_eq (K r : ℝ) (hK : 0 < K) :
    logDerivPos K r = csPos K r / snPos K r := by
  simp only [logDerivPos, if_neg hK.ne', csPos_eq K r hK, snPos_eq K r hK]
  field_simp

/-- For nonnegative curvature parameter, the total spherical coefficient is
the quotient `csPos K r / snPos K r`, including the flat branch. -/
theorem logDerivPos_eq_div (K r : ℝ) (hK : 0 ≤ K) :
    logDerivPos K r = csPos K r / snPos K r := by
  rcases hK.eq_or_lt with rfl | hK
  · simp [logDerivPos, csPos, snPos]
  · exact logDerivPos_eq K r hK

/-- The spherical coefficient agrees with Mathlib's logarithmic derivative. -/
theorem logDerivPos_eq_logDeriv (K r : ℝ) (hK : 0 ≤ K) :
    logDerivPos K r = logDeriv (snPos K) r := by
  rw [logDeriv_apply, (hasDerivAt_snPos K r hK).deriv]
  rcases hK.eq_or_lt with rfl | hK
  · simp [logDerivPos, csPos, snPos]
  · exact logDerivPos_eq K r hK

/-- The spherical logarithmic derivative has the Euclidean singular
normalization `r * logDerivPos K r -> 1` from the right. -/
theorem tendsto_self_mul_logDerivPos (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun r => r * logDerivPos K r) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hinv := (tendsto_snPos_div_self K hK).inv₀ one_ne_zero
  rw [inv_one] at hinv
  have hcs : Tendsto (csPos K) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have h := (hasDerivAt_csPos K 0 hK).continuousAt.tendsto
    rw [csPos_zero_right] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := hcs.mul hinv
  rw [one_mul] at h
  refine h.congr fun r => ?_
  rw [logDerivPos_eq_div K r hK, inv_div]
  ring

/-- On the regular first-pole interval, the spherical logarithmic derivative
solves `a' = -(K + a^2)`.  The pole hypothesis is exactly what makes the
quotient denominator nonzero.

This is the scalar model equality used in Petersen (2016), Corollary 6.4.2. -/
theorem hasDerivAt_logDerivPos (K r : ℝ) (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r) :
    HasDerivAt (logDerivPos K) (-(K + (logDerivPos K r) ^ 2)) r := by
  have hsn : snPos K r ≠ 0 := (snPos_pos K r hK hpole).ne'
  have hdiv := (hasDerivAt_csPos K r hK).div (hasDerivAt_snPos K r hK) hsn
  have hfun : logDerivPos K = csPos K / snPos K := by
    funext x
    exact logDerivPos_eq_div K x hK
  rw [hfun]
  apply hdiv.congr_deriv
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Derivative form of `hasDerivAt_logDerivPos`. -/
theorem deriv_logDerivPos (K r : ℝ) (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r) :
    deriv (logDerivPos K) r = -(K + (logDerivPos K r) ^ 2) :=
  (hasDerivAt_logDerivPos K r hK hpole).deriv

/-! ## Positive-curvature scalar Riccati comparison -/

/-- Quantitative origin control for the spherical coefficient.  On the first
half of the regular spherical interval,
`-K * r / 2 <= logDerivPos K r - 1 / r <= 0`. -/
theorem logDerivPos_sub_inv_mem_Icc (K r : ℝ) (hK : 0 ≤ K) (hr : 0 < r)
    (hhalf : Real.sqrt K * r ≤ Real.pi / 2) :
    logDerivPos K r - 1 / r ∈ Icc (-(K * r / 2)) 0 := by
  have hpole : BeforeFirstPole K r := by
    refine ⟨hr, ?_⟩
    rcases hK.eq_or_lt with rfl | hK
    · exact Or.inl rfl
    · exact Or.inr <| hhalf.trans_lt (div_lt_self Real.pi_pos one_lt_two)
  have hsnpos : 0 < snPos K r := snPos_pos K r hK hpole
  set h₁ : ℝ → ℝ := fun x => x * csPos K x - snPos K x with hh₁
  have hd₁ : ∀ x : ℝ, HasDerivAt h₁ (-(K * x * snPos K x)) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (hasDerivAt_csPos K x hK)).sub
      (hasDerivAt_snPos K x hK)
    have heq : 1 * csPos K x + id x * (-(K * snPos K x)) - csPos K x =
        -(K * x * snPos K x) := by
      simp only [id_eq]
      ring
    rwa [heq] at h
  have hsn_nonneg : ∀ x ∈ Icc (0 : ℝ) r, 0 ≤ snPos K x := by
    intro x hx
    apply snPos_nonneg K x hK
    refine ⟨hx.1, ?_⟩
    rcases hK.eq_or_lt with rfl | hK
    · exact Or.inl rfl
    · exact Or.inr <| (mul_le_mul_of_nonneg_left hx.2
        (Real.sqrt_nonneg K)).trans (hhalf.trans (div_le_self Real.pi_pos.le one_le_two))
  have hanti₁ : AntitoneOn h₁ (Icc (0 : ℝ) r) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 r)
      (fun x _ => (hd₁ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₁ x).hasDerivWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    have hsn := hsn_nonneg x ⟨hx.1.le, hx.2.le⟩
    exact neg_nonpos.mpr (mul_nonneg (mul_nonneg hK hx.1.le) hsn)
  have h₁0 : h₁ 0 = 0 := by simp [hh₁]
  have h₁nonpos : h₁ r ≤ 0 := by
    have h := hanti₁ (left_mem_Icc.2 hr.le) (right_mem_Icc.2 hr.le) hr.le
    rwa [h₁0] at h
  set h₂ : ℝ → ℝ := fun x => h₁ x + K * x ^ 2 / 2 * snPos K x with hh₂
  have hd₂ : ∀ x : ℝ, HasDerivAt h₂ (K * x ^ 2 / 2 * csPos K x) x := by
    intro x
    have hpoly : HasDerivAt (fun y : ℝ => K * y ^ 2 / 2) (K * x) x := by
      have h := ((hasDerivAt_pow 2 x).const_mul K).div_const 2
      have heq : K * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2 = K * x := by
        push_cast
        ring
      rwa [heq] at h
    have h := (hd₁ x).add (hpoly.mul (hasDerivAt_snPos K x hK))
    have heq : -(K * x * snPos K x) +
        (K * x * snPos K x + K * x ^ 2 / 2 * csPos K x) =
        K * x ^ 2 / 2 * csPos K x := by
      ring
    rwa [heq] at h
  have hcs_nonneg : ∀ x ∈ Icc (0 : ℝ) r, 0 ≤ csPos K x := by
    intro x hx
    rcases hK.eq_or_lt with rfl | hK
    · simp [csPos]
    · rw [csPos_eq K x hK]
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · exact (neg_nonpos_of_nonneg (div_nonneg Real.pi_pos.le (by norm_num))).trans
          (mul_nonneg (Real.sqrt_nonneg K) hx.1)
      · exact (mul_le_mul_of_nonneg_left hx.2 (Real.sqrt_nonneg K)).trans hhalf
  have hmono₂ : MonotoneOn h₂ (Icc (0 : ℝ) r) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 r)
      (fun x _ => (hd₂ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₂ x).hasDerivWithinAt) fun x hx => ?_
    rw [interior_Icc] at hx
    have hcs := hcs_nonneg x ⟨hx.1.le, hx.2.le⟩
    positivity
  have h₂0 : h₂ 0 = 0 := by simp [hh₂, h₁0]
  have h₂nonneg : 0 ≤ h₂ r := by
    have h := hmono₂ (left_mem_Icc.2 hr.le) (right_mem_Icc.2 hr.le) hr.le
    rwa [h₂0] at h
  have hkey : logDerivPos K r - 1 / r = h₁ r / (r * snPos K r) := by
    rw [logDerivPos_eq_div K r hK, hh₁]
    field_simp
  constructor
  · rw [hkey]
    have hbound : -(K * r ^ 2 / 2 * snPos K r) ≤ h₁ r := by
      rw [hh₂] at h₂nonneg
      linarith
    have hdiv := div_le_div_of_nonneg_right hbound (by positivity : 0 ≤ r * snPos K r)
    calc
      -(K * r / 2) = -(K * r ^ 2 / 2 * snPos K r) / (r * snPos K r) := by
        field_simp
      _ ≤ h₁ r / (r * snPos K r) := hdiv
  · rw [hkey]
    exact div_nonpos_of_nonpos_of_nonneg h₁nonpos (by positivity)

/-- The spherical model has the strong Euclidean singular normalization
`logDerivPos K r - 1/r -> 0` from the right. -/
theorem tendsto_logDerivPos_sub_inv (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun r => logDerivPos K r - 1 / r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlower : Tendsto (fun r : ℝ => -(K * r / 2))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun r : ℝ => -(K * r / 2)) (nhds (0 : ℝ))
        (nhds (-(K * 0 / 2))) :=
      ((continuous_const.mul continuous_id).div_const 2).neg.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have harg : Tendsto (fun r : ℝ => Real.sqrt K * r)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun r : ℝ => Real.sqrt K * r) (nhds (0 : ℝ))
        (nhds (Real.sqrt K * 0)) := (continuous_const.mul continuous_id).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hhalf : ∀ᶠ r in nhdsWithin 0 (Ioi (0 : ℝ)),
      Real.sqrt K * r ≤ Real.pi / 2 :=
    harg.eventually (Iic_mem_nhds Real.pi_div_two_pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin, hhalf] with r hr hbound
    exact (logDerivPos_sub_inv_mem_Icc K r hK hr hbound).1
  · filter_upwards [eventually_mem_nhdsWithin, hhalf] with r hr hbound
    exact (logDerivPos_sub_inv_mem_Icc K r hK hr hbound).2

/-! ## Flat and hyperbolic scalar Riccati comparison

The following results are still independent of manifold data.  They prove the
scalar comparison statement that later radial shape and trace estimates will
consume.
-/

/-- For nonnegative curvature parameter, the total radial coefficient agrees
with `cs k r / sn k r`, including the flat branch. -/
theorem radialCoeff_eq_div (k r : ℝ) (hk : 0 ≤ k) :
    radialCoeff k r = cs k r / sn k r := by
  rcases hk.eq_or_lt with rfl | hk
  · simp [radialCoeff, cs, sn]
  · simp [radialCoeff, hk.ne']

/-- The radial coefficient agrees with Mathlib's logarithmic derivative. -/
theorem radialCoeff_eq_logDeriv (k r : ℝ) (hk : 0 ≤ k) :
    radialCoeff k r = logDeriv (sn k) r := by
  rw [logDeriv_apply, (hasDerivAt_sn k r hk).deriv]
  exact radialCoeff_eq_div k r hk

/-- The quotient model solves `a' = k - a^2` away from the origin. -/
theorem hasDerivAt_cs_div_sn (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    HasDerivAt (cs k / sn k) (k - (cs k r / sn k r) ^ 2) r := by
  have hsn : sn k r ≠ 0 := (sn_pos k r hk hr).ne'
  have hdiv := (hasDerivAt_cs k r hk).div (hasDerivAt_sn k r hk) hsn
  have heq : (k * sn k r * sn k r - cs k r * cs k r) / sn k r ^ 2 =
      k - (cs k r / sn k r) ^ 2 := by
    field_simp
  rwa [heq] at hdiv

/-- Quantitative small-radius control of the hyperbolic model:
`0 <= radialCoeff k r - 1/r <= k*r/2`. -/
theorem radialCoeff_sub_inv_mem_Icc (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    radialCoeff k r - 1 / r ∈ Icc 0 (k * r / 2) := by
  have hsnpos : 0 < sn k r := sn_pos k r hk hr
  set h₁ : ℝ → ℝ := fun x => x * cs k x - sn k x with hh₁
  have hd₁ : ∀ x : ℝ, HasDerivAt h₁ (k * x * sn k x) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (hasDerivAt_cs k x hk)).sub
      (hasDerivAt_sn k x hk)
    have heq : 1 * cs k x + id x * (k * sn k x) - cs k x = k * x * sn k x := by
      simp only [id_eq]
      ring
    rwa [heq] at h
  have hmono₁ : MonotoneOn h₁ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₁ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₁ x).hasDerivWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    have hsn := sn_nonneg k x hk hx.le
    exact mul_nonneg (mul_nonneg hk hx.le) hsn
  have h₁0 : h₁ 0 = 0 := by simp [hh₁]
  have h₁nonneg : 0 ≤ h₁ r := by
    have h := hmono₁ (self_mem_Ici) (mem_Ici.2 hr.le) hr.le
    rwa [h₁0] at h
  set h₂ : ℝ → ℝ := fun x => k * x ^ 2 / 2 * sn k x - h₁ x with hh₂
  have hd₂ : ∀ x : ℝ, HasDerivAt h₂ (k * x ^ 2 / 2 * cs k x) x := by
    intro x
    have hpoly : HasDerivAt (fun y : ℝ => k * y ^ 2 / 2) (k * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul k
      have h' := h.div_const 2
      have heq : k * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2 = k * x := by
        push_cast
        ring
      rwa [heq] at h'
    have h := (hpoly.mul (hasDerivAt_sn k x hk)).sub (hd₁ x)
    have heq : k * x * sn k x + k * x ^ 2 / 2 * cs k x - k * x * sn k x =
        k * x ^ 2 / 2 * cs k x := by ring
    rwa [heq] at h
  have hmono₂ : MonotoneOn h₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₂ x).continuousAt.continuousWithinAt)
      (fun x _ => (hd₂ x).hasDerivWithinAt) fun x _ => ?_
    have hcs := (cs_pos k x hk).le
    positivity
  have h₂0 : h₂ 0 = 0 := by simp [hh₂, h₁0]
  have h₂nonneg : 0 ≤ h₂ r := by
    have h := hmono₂ (self_mem_Ici) (mem_Ici.2 hr.le) hr.le
    rwa [h₂0] at h
  have hkey : radialCoeff k r - 1 / r = h₁ r / (r * sn k r) := by
    rw [radialCoeff_eq_div k r hk, hh₁]
    field_simp
  constructor
  · rw [hkey]
    positivity
  · rw [hkey]
    have hbound : h₁ r ≤ k * r ^ 2 / 2 * sn k r := by
      rw [hh₂] at h₂nonneg
      linarith
    calc
      h₁ r / (r * sn k r) ≤ k * r ^ 2 / 2 * sn k r / (r * sn k r) :=
        div_le_div_of_nonneg_right hbound (by positivity)
      _ = k * r / 2 := by field_simp

/-- The singular parts cancel: `radialCoeff k r - 1/r` tends to zero from
the right at the origin. -/
theorem tendsto_radialCoeff_sub_inv (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun r => radialCoeff k r - 1 / r) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hupper : Tendsto (fun r : ℝ => k * r / 2) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have h : Tendsto (fun r : ℝ => k * r / 2) (nhds (0 : ℝ)) (nhds (k * 0 / 2)) :=
      ((continuous_const.mul continuous_id).div_const 2).tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact (radialCoeff_sub_inv_mem_Icc k r hk hr).1
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact (radialCoeff_sub_inv_mem_Icc k r hk hr).2

/-- Scalar Riccati comparison on `(0, r0)`.  A function with
`phi' + phi^2 <= k` and the Euclidean singular normalization is bounded above
by the flat/hyperbolic model coefficient. -/
theorem scalar_riccati_comparison {k r₀ : ℝ} (hk : 0 ≤ k) {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, φ' r + φ r ^ 2 ≤ k)
    (h0 : Tendsto (fun r => φ r - 1 / r) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, φ r ≤ radialCoeff k r := by
  set a : ℝ → ℝ := cs k / sn k with ha
  set ψ : ℝ → ℝ := (fun x => sn k x ^ 2) * (φ - a) with hψ
  set ψ' : ℝ → ℝ := fun x =>
    2 * sn k x * cs k x * (φ x - a x) +
      sn k x ^ 2 * (φ' x - (k - a x ^ 2)) with hψ'
  have hdψ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ψ (ψ' r) r := by
    intro r hr
    have hsq : HasDerivAt (fun x => sn k x ^ 2) (2 * sn k r * cs k r) r := by
      have h := (hasDerivAt_sn k r hk).pow 2
      have heq : ((2 : ℕ) : ℝ) * sn k r ^ (2 - 1) * cs k r =
          2 * sn k r * cs k r := by
        push_cast
        ring
      rwa [heq] at h
    have haDeriv : HasDerivAt a (k - a r ^ 2) r := by
      rw [ha]
      simpa only [Pi.div_apply] using hasDerivAt_cs_div_sn k r hk hr.1
    have hsub : HasDerivAt (φ - a) (φ' r - (k - a r ^ 2)) r :=
      (hφ r hr).sub haDeriv
    exact hsq.mul hsub
  have hψ'le : ∀ r ∈ Ioo (0 : ℝ) r₀, ψ' r ≤ 0 := by
    intro r hr
    have hsnpos : 0 < sn k r := sn_pos k r hk hr.1
    have hcs : cs k r = sn k r * a r := by
      rw [ha]
      simp only [Pi.div_apply]
      field_simp
    have hφle : φ' r - k ≤ -φ r ^ 2 := by
      have h := hric r hr
      linarith
    have hmul : sn k r ^ 2 * (φ' r - k) ≤ sn k r ^ 2 * (-φ r ^ 2) :=
      mul_le_mul_of_nonneg_left hφle (sq_nonneg _)
    simp only [hψ', hcs]
    nlinarith [sq_nonneg (sn k r * (φ r - a r))]
  have hanti : AntitoneOn ψ (Ioo (0 : ℝ) r₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := ψ') (convex_Ioo _ _)
      (fun x hx => (hdψ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdψ x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      exact hψ'le x hx
  have hψ0 : Tendsto ψ (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsn0 : Tendsto (fun r => sn k r ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hc : Tendsto (sn k) (nhds (0 : ℝ)) (nhds (sn k 0)) :=
        (hasDerivAt_sn k 0 hk).continuousAt.tendsto
      rw [sn_zero_right] at hc
      have hc' : Tendsto (sn k) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
        hc.mono_left nhdsWithin_le_nhds
      simpa using hc'.pow 2
    have hdiff : Tendsto (fun r => (φ r - 1 / r) - (a r - 1 / r))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      have hmodel : Tendsto (fun r => a r - 1 / r) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
        have heq : (fun r => a r - 1 / r) =
            (fun r => radialCoeff k r - 1 / r) := by
          funext r
          rw [ha]
          simp only [Pi.div_apply]
          rw [radialCoeff_eq_div k r hk]
        rw [heq]
        exact tendsto_radialCoeff_sub_inv k hk
      simpa using h0.sub hmodel
    have h := hsn0.mul hdiff
    rw [zero_mul] at h
    refine h.congr fun r => ?_
    rw [hψ]
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  intro r hr
  have hψr : ψ r ≤ 0 := by
    have hev : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), ψ r ≤ ψ s := by
      have h1 : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s ∈ Ioi (0 : ℝ) :=
        eventually_mem_nhdsWithin
      have h2 : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s < r :=
        (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2] with s hs1 hs2
      exact hanti ⟨hs1, hs2.trans hr.2⟩ hr hs2.le
    exact ge_of_tendsto hψ0 hev
  have hsn2 : 0 < sn k r ^ 2 := pow_pos (sn_pos k r hk hr.1) 2
  have h : sn k r ^ 2 * (φ r - a r) ≤ 0 := by
    simpa only [hψ, Pi.mul_apply, Pi.sub_apply] using hψr
  have hle : φ r ≤ a r := by nlinarith
  rw [ha] at hle
  simp only [Pi.div_apply] at hle
  rwa [radialCoeff_eq_div k r hk]

/-- Scalar Riccati comparison on the whole positive ray. -/
theorem scalar_riccati_comparison_Ioi {k : ℝ} (hk : 0 ≤ k) {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioi (0 : ℝ), φ' r + φ r ^ 2 ≤ k)
    (h0 : Tendsto (fun r => φ r - 1 / r) (nhdsWithin 0 (Ioi 0)) (nhds 0)) :
    ∀ r ∈ Ioi (0 : ℝ), φ r ≤ radialCoeff k r := fun r hr =>
  scalar_riccati_comparison hk (fun s hs => hφ s hs.1) (fun s hs => hric s hs.1)
    h0 r ⟨hr, lt_add_one r⟩

/-! ## Positive-curvature scalar Sturm comparison -/

/-- Scalar Sturm comparison for the upper-curvature branch.  Let `f` vanish at
the origin with unit right derivative and satisfy `f'' + K f >= 0`.  If `r₀`
is before the first spherical pole, then `snPos K r <= f r` through the
endpoint; in particular, `f` is positive there.

The boundedness hypothesis on `f'` is the exact origin control used to make the
Wronskian tend to zero.  In the later Jacobi reduction, `f` is the norm of a
Jacobi field normalized by the norm of its initial covariant derivative.  This
norm supplies `hd1` and `hd2` only where the Jacobi field is nonzero, so the
bridge must apply this theorem up to a hypothetical first zero and use `hf` to
extend the inequality to that endpoint by continuity.  On the nonvanishing
interval, the Jacobi equation and Cauchy--Schwarz give the displayed scalar
inequality.

Source: Morgan--Tian, comparison discussion on pp. 48--49.  Petersen (2016),
Theorems 6.4.3 and 6.4.6, are geometric targets and cross-checks for this scalar
Wronskian theorem, rather than statements of the theorem itself. -/
theorem scalar_sturm_comparison_pos {K r₀ C : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r₀) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 r₀)) (hf0 : f 0 = 0)
    (hunit : HasDerivWithinAt f 1 (Ici 0) 0)
    (hd1 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f (f' r) r)
    (hd2 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f' (f'' r) r)
    (hineq : ∀ r ∈ Ioo (0 : ℝ) r₀, -(K * f r) ≤ f'' r)
    (hbdd : ∀ᶠ r in nhdsWithin 0 (Ioi (0 : ℝ)), |f' r| ≤ C) :
    ∀ r ∈ Ioc (0 : ℝ) r₀, snPos K r ≤ f r := by
  have hsnpos : ∀ r ∈ Ioc (0 : ℝ) r₀, 0 < snPos K r := by
    intro r hr
    apply snPos_pos K r hK
    refine ⟨hr.1, ?_⟩
    rcases hpole.2 with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr <| (mul_le_mul_of_nonneg_left hr.2 (Real.sqrt_nonneg K)).trans_lt hlt
  have hslope : Tendsto (fun r => f r / r) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hslope := hasDerivWithinAt_iff_tendsto_slope.1 hunit
    have hset : Ici (0 : ℝ) \ {0} = Ioi 0 := by
      ext r
      simp [lt_iff_le_and_ne]
    rw [hset] at hslope
    refine hslope.congr fun r => ?_
    simp [slope_def_field, hf0]
  set W : ℝ → ℝ := fun r => f' r * snPos K r - f r * csPos K r with hW
  have hdW : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt W (snPos K r * (f'' r + K * f r)) r := by
    intro r hr
    have h := ((hd2 r hr).mul (hasDerivAt_snPos K r hK)).sub
      ((hd1 r hr).mul (hasDerivAt_csPos K r hK))
    have heq : f'' r * snPos K r + f' r * csPos K r -
        (f' r * csPos K r + f r * -(K * snPos K r)) =
        snPos K r * (f'' r + K * f r) := by
      ring
    rwa [heq] at h
  have hWmono : MonotoneOn W (Ioo (0 : ℝ) r₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun r => snPos K r * (f'' r + K * f r)) (convex_Ioo _ _)
      (fun r hr => (hdW r hr).continuousAt.continuousWithinAt)
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Ioo] at hr
      exact (hdW r hr).hasDerivWithinAt
    · rw [interior_Ioo] at hr
      have hsn : 0 ≤ snPos K r := (hsnpos r ⟨hr.1, hr.2.le⟩).le
      have hnonneg : 0 ≤ f'' r + K * f r := by
        have := hineq r hr
        linarith
      positivity
  have hf_zero : Tendsto f (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hid : Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := hslope.mul hid
    rw [one_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with r hr
    have hrne : r ≠ 0 := ne_of_gt hr
    field_simp [hrne]
  have hW_zero : Tendsto W (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
    have hsn_zero : Tendsto (snPos K) (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      have h := (hasDerivAt_snPos K 0 hK).continuousAt.tendsto
      rw [snPos_zero_right] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hterm1 : Tendsto (fun r => f' r * snPos K r)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      refine squeeze_zero_norm' (a := fun r => C * |snPos K r|) ?_ ?_
      · filter_upwards [hbdd] with r hr
        calc
          ‖f' r * snPos K r‖ = |f' r| * |snPos K r| := abs_mul _ _
          _ ≤ C * |snPos K r| := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
      · have h : Tendsto (fun r => C * |snPos K r|)
            (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (C * |0|)) :=
          hsn_zero.abs.const_mul C
        simpa using h
    have hcs : Tendsto (csPos K) (nhdsWithin 0 (Ioi (0 : ℝ)))
        (nhds (csPos K 0)) :=
      ((hasDerivAt_csPos K 0 hK).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have hterm2 : Tendsto (fun r => f r * csPos K r)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 0) := by
      have h := hf_zero.mul hcs
      rw [zero_mul] at h
      exact h
    have h := hterm1.sub hterm2
    rw [zero_sub] at h
    simpa only [hW, neg_zero] using h
  have hWnonneg : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ W r := by
    intro r hr
    have hev : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), W s ≤ W r := by
      have hpos : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s ∈ Ioi (0 : ℝ) :=
        eventually_mem_nhdsWithin
      have hlt : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s < r :=
        (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [hpos, hlt] with s hs hsr
      exact hWmono ⟨hs, hsr.trans hr.2⟩ hr hsr.le
    exact le_of_tendsto hW_zero hev
  set Q : ℝ → ℝ := fun r => f r / snPos K r with hQ
  have hdQ : ∀ r ∈ Ioo (0 : ℝ) r₀,
      HasDerivAt Q (W r / snPos K r ^ 2) r := by
    intro r hr
    have hsn : snPos K r ≠ 0 := (hsnpos r ⟨hr.1, hr.2.le⟩).ne'
    exact (hd1 r hr).div (hasDerivAt_snPos K r hK) hsn
  have hQmono : MonotoneOn Q (Ioo (0 : ℝ) r₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun r => W r / snPos K r ^ 2) (convex_Ioo _ _)
      (fun r hr => (hdQ r hr).continuousAt.continuousWithinAt)
      (fun r hr => ?_) (fun r hr => ?_)
    · rw [interior_Ioo] at hr
      exact (hdQ r hr).hasDerivWithinAt
    · rw [interior_Ioo] at hr
      have hWpos := hWnonneg r hr
      have hsn : 0 < snPos K r ^ 2 := pow_pos (hsnpos r ⟨hr.1, hr.2.le⟩) 2
      positivity
  have hQ_zero : Tendsto Q (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
    have hratio : Tendsto (fun r => r / snPos K r)
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1) := by
      have h := (tendsto_snPos_div_self K hK).inv₀ one_ne_zero
      rw [inv_one] at h
      refine h.congr fun r => ?_
      rw [inv_div]
    have h := hslope.mul hratio
    rw [one_mul] at h
    refine h.congr' ?_
    have hlt : ∀ᶠ r in nhdsWithin 0 (Ioi (0 : ℝ)), r < r₀ :=
      (eventually_lt_nhds hpole.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [eventually_mem_nhdsWithin, hlt] with r hr hrlt
    have hrne : r ≠ 0 := ne_of_gt hr
    have hsnne : snPos K r ≠ 0 := (hsnpos r ⟨hr, hrlt.le⟩).ne'
    rw [hQ]
    field_simp [hrne, hsnne]
  have hQge : ∀ r ∈ Ioo (0 : ℝ) r₀, 1 ≤ Q r := by
    intro r hr
    have hev : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), Q s ≤ Q r := by
      have hpos : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s ∈ Ioi (0 : ℝ) :=
        eventually_mem_nhdsWithin
      have hlt : ∀ᶠ s in nhdsWithin 0 (Ioi (0 : ℝ)), s < r :=
        (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [hpos, hlt] with s hs hsr
      exact hQmono ⟨hs, hsr.trans hr.2⟩ hr hsr.le
    exact le_of_tendsto hQ_zero hev
  have hmain : ∀ r ∈ Ioo (0 : ℝ) r₀, snPos K r ≤ f r := by
    intro r hr
    have hsn : 0 < snPos K r := hsnpos r ⟨hr.1, hr.2.le⟩
    have h := hQge r hr
    rw [hQ] at h
    simpa only [one_mul] using (le_div_iff₀ hsn).1 h
  intro r hr
  rcases lt_or_eq_of_le hr.2 with hlt | heq
  · exact hmain r ⟨hr.1, hlt⟩
  · subst r
    have hne : (nhdsWithin r₀ (Ioo (0 : ℝ) r₀)).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hpole.1.ne]
      exact ⟨hpole.1.le, le_rfl⟩
    have hft : Tendsto f (nhdsWithin r₀ (Ioo (0 : ℝ) r₀)) (nhds (f r₀)) := by
      have hcw : ContinuousWithinAt f (Icc 0 r₀) r₀ :=
        hf r₀ ⟨hpole.1.le, le_rfl⟩
      exact hcw.tendsto.mono_left (nhdsWithin_mono r₀ Ioo_subset_Icc_self)
    have hst : Tendsto (snPos K) (nhdsWithin r₀ (Ioo (0 : ℝ) r₀))
        (nhds (snPos K r₀)) :=
      ((hasDerivAt_snPos K r₀ hK).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hst hft ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    exact hmain s hs

/-- Positivity consequence of `scalar_sturm_comparison_pos`: the normalized
solution cannot vanish at or before any radius preceding the first pole. -/
theorem scalar_sturm_pos {K r₀ C : ℝ} (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r₀) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 r₀)) (hf0 : f 0 = 0)
    (hunit : HasDerivWithinAt f 1 (Ici 0) 0)
    (hd1 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f (f' r) r)
    (hd2 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f' (f'' r) r)
    (hineq : ∀ r ∈ Ioo (0 : ℝ) r₀, -(K * f r) ≤ f'' r)
    (hbdd : ∀ᶠ r in nhdsWithin 0 (Ioi (0 : ℝ)), |f' r| ≤ C) :
    ∀ r ∈ Ioc (0 : ℝ) r₀, 0 < f r := by
  have hcmp := scalar_sturm_comparison_pos hK hpole hf hf0 hunit hd1 hd2 hineq hbdd
  intro r hr
  have hmodel : 0 < snPos K r := by
    apply snPos_pos K r hK
    refine ⟨hr.1, ?_⟩
    rcases hpole.2 with hzero | hlt
    · exact Or.inl hzero
    · exact Or.inr <| (mul_le_mul_of_nonneg_left hr.2
        (Real.sqrt_nonneg K)).trans_lt hlt
  exact hmodel.trans_le (hcmp r hr)

/-- Flat-branch form of `scalar_sturm_comparison_pos`: a normalized function
with `f'' >= 0` lies above the Euclidean profile `r`. -/
theorem scalar_sturm_comparison_zero {r₀ C : ℝ} (hr₀ : 0 < r₀)
    {f f' f'' : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 r₀)) (hf0 : f 0 = 0)
    (hunit : HasDerivWithinAt f 1 (Ici 0) 0)
    (hd1 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f (f' r) r)
    (hd2 : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt f' (f'' r) r)
    (hineq : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 ≤ f'' r)
    (hbdd : ∀ᶠ r in nhdsWithin 0 (Ioi (0 : ℝ)), |f' r| ≤ C) :
    ∀ r ∈ Ioc (0 : ℝ) r₀, r ≤ f r := by
  simpa using scalar_sturm_comparison_pos (K := 0) (C := C) (by positivity)
    (beforeFirstPole_zero_iff r₀ |>.2 hr₀) hf hf0 hunit hd1 hd2
    (fun r hr => by simpa using hineq r hr) hbdd

/-- Exact-model regression for `scalar_sturm_comparison_pos`.  This invokes the
comparison theorem with `f = snPos K`, so a reversed ODE sign or first-pole
condition makes the check fail. -/
private theorem scalar_sturm_comparison_pos_model (K r₀ : ℝ) (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r₀) :
    ∀ r ∈ Ioc (0 : ℝ) r₀, snPos K r ≤ snPos K r := by
  apply scalar_sturm_comparison_pos (K := K) (C := 1) hK hpole
  · exact fun r _ => (hasDerivAt_snPos K r hK).continuousAt.continuousWithinAt
  · exact snPos_zero_right K
  · simpa using (hasDerivAt_snPos K 0 hK).hasDerivWithinAt
  · exact fun r _ => hasDerivAt_snPos K r hK
  · exact fun r _ => hasDerivAt_csPos K r hK
  · intro r _
    exact le_rfl
  · exact Filter.Eventually.of_forall fun r => abs_csPos_le_one K r hK

end Comparison
end Ch01
end MorganTianLib
