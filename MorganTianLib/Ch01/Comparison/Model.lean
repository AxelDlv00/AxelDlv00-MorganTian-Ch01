import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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

theorem logDerivPos_eq (K r : ℝ) (hK : 0 < K) :
    logDerivPos K r = csPos K r / snPos K r := by
  simp only [logDerivPos, if_neg hK.ne', csPos_eq K r hK, snPos_eq K r hK]
  field_simp

/-- The spherical coefficient agrees with Mathlib's logarithmic derivative. -/
theorem logDerivPos_eq_logDeriv (K r : ℝ) (hK : 0 ≤ K) :
    logDerivPos K r = logDeriv (snPos K) r := by
  rw [logDeriv_apply, (hasDerivAt_snPos K r hK).deriv]
  rcases hK.eq_or_lt with rfl | hK
  · simp [logDerivPos, csPos, snPos]
  · exact logDerivPos_eq K r hK


/-! ## Scalar Riccati comparison

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

end Comparison
end Ch01
end MorganTianLib
