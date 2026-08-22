import MorganTianLib.Ch01.Curvature

/-!
# Pointwise tensoriality of the Levi--Civita curvature

This module supplies the first pointwise consumer of the canonical commutator
from `MorganTianLib.Ch01.Curvature`.  Morgan--Tian Definition 1.4 and Claim
1.5 treat the curvature as a tensor at a point.  Mathlib's bundled
`CovariantDerivative` exposes the commutator first on differentiable sections,
so the proofs below make the local smooth extension used at the evaluation
point explicit.  The resulting additivity and scalar laws are then packaged
as `TensorialAt` witnesses.

The layer proves the three `(1,3)` slots, the corresponding extension-local
congruence, and the first Bianchi identity in both the operator and
source-ordered `(0,4)` forms.  Metric last-pair skew and pair interchange
remain downstream of the metric-compatible tensor-covariant-derivative API;
the differential/second Bianchi identity is outside this module.
-/

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

section Tensoriality

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

private abbrev SmoothAt (X : (x : M) → TangentSpace I x) (p : M) : Prop :=
  ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% X) p

private lemma smoothAt_eventually_mdifferentiableAt
    {X : (x : M) → TangentSpace I x} {p : M} (hX : SmoothAt X p) :
    ∀ᶠ q in 𝓝 p, MDiffAt (T% X) q := by
  have hX1 := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hX1
  exact hn.mono fun q hq => hq.mdifferentiableAt one_ne_zero

private lemma covariantField_mdifferentiableAt_lc
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) :
    MDiffAt (T% (covariantField (Connection.leviCivitaConnection g) X Y)) p := by
  exact (Connection.contMDiffAt_leviCivitaConnection_apply g hX hY).mdifferentiableAt
    (by simp)

private lemma extend_add_eventuallyEq {p : M} (X Y : TangentSpace I p) :
    FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM (X + Y) =ᶠ[𝓝 p]
      FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM X +
        FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM Y := by
  let t := trivializationAt EM (TangentSpace I) p
  have hp : p ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  filter_upwards [t.open_baseSet.mem_nhds hp] with q hq
  change
    (letI t' := trivializationAt EM (TangentSpace I) p
     letI w : EM := (t' ⟨p, X + Y⟩).2
     t'.symm q w) =
      (letI t' := trivializationAt EM (TangentSpace I) p
       letI w : EM := (t' ⟨p, X⟩).2
       t'.symm q w) +
       (letI t' := trivializationAt EM (TangentSpace I) p
        letI w : EM := (t' ⟨p, Y⟩).2
        t'.symm q w)
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ) t hq,
    ← Bundle.Trivialization.symmL_apply (R := ℝ) t hq,
    ← Bundle.Trivialization.symmL_apply (R := ℝ) t hq]
  rw [← map_add]
  congr 1
  rw [← t.continuousLinearMapAt_apply_of_mem ℝ hp,
    ← t.continuousLinearMapAt_apply_of_mem ℝ hp,
    ← t.continuousLinearMapAt_apply_of_mem ℝ hp, map_add]

private lemma extend_smul_eventuallyEq {p : M} (c : ℝ) (X : TangentSpace I p) :
    FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM (c • X) =ᶠ[𝓝 p]
      (fun _ : M => c) • FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM X := by
  let t := trivializationAt EM (TangentSpace I) p
  have hp : p ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  filter_upwards [t.open_baseSet.mem_nhds hp] with q hq
  change
    (letI t' := trivializationAt EM (TangentSpace I) p
     letI w : EM := (t' ⟨p, c • X⟩).2
     t'.symm q w) =
      c • (letI t' := trivializationAt EM (TangentSpace I) p
       letI w : EM := (t' ⟨p, X⟩).2
       t'.symm q w)
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ) t hq,
    ← Bundle.Trivialization.symmL_apply (R := ℝ) t hq]
  rw [← t.continuousLinearMapAt_apply_of_mem ℝ hp,
    ← t.continuousLinearMapAt_apply_of_mem ℝ hp]
  rw [map_smul (t.continuousLinearMapAt ℝ p) c X]
  exact map_smul (t.symmL ℝ q) c ((t.continuousLinearMapAt ℝ p) X)

private lemma covariantField_add_eventually_at
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Z W : (x : M) → TangentSpace I x} {p : M}
    (hZ : SmoothAt Z p) (hW : SmoothAt W p) :
    covariantField cov X (Z + W) =ᶠ[𝓝 p]
      covariantField cov X Z + covariantField cov X W := by
  filter_upwards [smoothAt_eventually_mdifferentiableAt hZ,
    smoothAt_eventually_mdifferentiableAt hW] with q hZq hWq
  exact covariantField_add_argument cov hZq hWq

private lemma covariantField_congr_eventually_at
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Y' : (x : M) → TangentSpace I x} {p : M}
    (hY : ∀ᶠ q in 𝓝 p, MDiffAt (T% Y) q)
    (hY' : ∀ᶠ q in 𝓝 p, MDiffAt (T% Y') q)
    (h : ∀ᶠ q in 𝓝 p, Y q = Y' q) :
    ∀ᶠ q in 𝓝 p, covariantField cov X Y q = covariantField cov X Y' q := by
  rw [eventually_iff_exists_mem] at h
  obtain ⟨s, hs, hEq⟩ := h
  rcases mem_nhds_iff.mp hs with ⟨u, hus, huo, hpu⟩
  filter_upwards [huo.mem_nhds hpu, hY, hY'] with q hqu hYq hY'q
  unfold covariantField
  have hcov := cov.isCovariantDerivativeOn.congr_of_eqOn hYq hY'q
    (huo.mem_nhds hqu) (fun r hru => hEq r (hus hru))
  rw [hcov]

private lemma curvatureField_add_left_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) (X + Y) Z W p =
      curvatureField (Connection.leviCivitaConnection g) X Z W p +
        curvatureField (Connection.leviCivitaConnection g) Y Z W p := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := Connection.contMDiff_leviCivitaConnection g
  have hX' : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) p := hY.mdifferentiableAt (by simp)
  have hXW : MDiffAt (T% (covariantField cov X W)) p :=
    covariantField_mdifferentiableAt_lc g hX hW
  have hYW : MDiffAt (T% (covariantField cov Y W)) p :=
    covariantField_mdifferentiableAt_lc g hY hW
  have hbr : VectorField.mlieBracket I (X + Y) Z p =
      VectorField.mlieBracket I X Z p + VectorField.mlieBracket I Y Z p :=
    VectorField.mlieBracket_add_left hX' hY'
  have hinner : covariantField cov (X + Y) W =
      covariantField cov X W + covariantField cov Y W := by
    funext q
    exact covariantField_add_direction cov
  unfold curvatureField
  rw [hinner, covariantField_add_direction cov,
    covariantField_add_argument cov hXW hYW,
    covariantField_congr_direction (X := VectorField.mlieBracket I (X + Y) Z)
      (X' := VectorField.mlieBracket I X Z + VectorField.mlieBracket I Y Z)
      cov hbr,
    covariantField_add_direction cov]
  abel

private lemma curvatureField_smul_left_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {c : ℝ} {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) (c • X) Y W p =
      c • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := Connection.contMDiff_leviCivitaConnection g
  have hX' : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) p := hY.mdifferentiableAt (by simp)
  have hW' : MDiffAt (T% W) p := hW.mdifferentiableAt (by simp)
  have hYW' : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
      (fun q => (⟨q, covariantField cov Y W q⟩ : TangentBundle I M)) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hY hW
  have hXW' : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
      (fun q => (⟨q, covariantField cov X W q⟩ : TangentBundle I M)) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hX hW
  have hYW : MDiffAt (T% (covariantField cov Y W)) p := hYW'.mdifferentiableAt (by simp)
  have hXW : MDiffAt (T% (covariantField cov X W)) p := hXW'.mdifferentiableAt (by simp)
  unfold curvatureField
  have hfirst : covariantField cov (c • X) (covariantField cov Y W) p =
      c • covariantField cov X (covariantField cov Y W) p := by
    unfold covariantField
    change cov (covariantField cov Y W) p (c • X p) =
      c • cov (covariantField cov Y W) p (X p)
    rw [map_smul]
  have hinner : covariantField cov (c • X) W = c • covariantField cov X W := by
    funext q
    unfold covariantField
    change cov W q (c • X q) = c • cov W q (X q)
    rw [map_smul]
  have hsecond : covariantField cov Y (covariantField cov (c • X) W) p =
      c • covariantField cov Y (covariantField cov X W) p +
        (d% (fun _ : M => c) p).smulRight (covariantField cov X W p) (Y p) := by
    rw [hinner]
    exact covariantField_smul_argument cov mdifferentiableAt_const hXW
  have hbracket : VectorField.mlieBracket I (c • X) Y p =
      c • VectorField.mlieBracket I X Y p := by
    simpa using VectorField.mlieBracket_const_smul_left hX'
  have hthird : covariantField cov (VectorField.mlieBracket I (c • X) Y) W p =
      c • covariantField cov (VectorField.mlieBracket I X Y) W p := by
    unfold covariantField
    rw [hbracket]
    change cov W p (c • VectorField.mlieBracket I X Y p) = _
    rw [map_smul]
  rw [hfirst, hsecond, hthird]
  simp only [smul_sub, ContinuousLinearMap.smulRight_apply]
  simp [mvfderiv]
  module

private lemma curvatureField_add_right_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p)
    (hZ : SmoothAt Z p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) X Y (Z + W) p =
      curvatureField (Connection.leviCivitaConnection g) X Y Z p +
        curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := Connection.contMDiff_leviCivitaConnection g
  have hX' : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) p := hY.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) p := hZ.mdifferentiableAt (by simp)
  have hW' : MDiffAt (T% W) p := hW.mdifferentiableAt (by simp)
  have hYZ := covariantField_mdifferentiableAt_lc g hY hZ
  have hYW := covariantField_mdifferentiableAt_lc g hY hW
  have hXZ := covariantField_mdifferentiableAt_lc g hX hZ
  have hXW := covariantField_mdifferentiableAt_lc g hX hW
  have hsum : SmoothAt (Z + W) p := hZ.add_section hW
  have hYZsum := covariantField_mdifferentiableAt_lc g hY hsum
  have hXZsum := covariantField_mdifferentiableAt_lc g hX hsum
  have hYeq : covariantField cov Y (Z + W) =ᶠ[𝓝 p]
      covariantField cov Y Z + covariantField cov Y W :=
    covariantField_add_eventually_at cov (X := Y) hZ hW
  have hXeq : covariantField cov X (Z + W) =ᶠ[𝓝 p]
      covariantField cov X Z + covariantField cov X W :=
    covariantField_add_eventually_at cov (X := X) hZ hW
  unfold curvatureField
  have houterY := covariantField_congr_argument (X := X) cov hYZsum
    (mdifferentiableAt_add_section hYZ hYW) hYeq
  have houterX := covariantField_congr_argument (X := Y) cov hXZsum
    (mdifferentiableAt_add_section hXZ hXW) hXeq
  have hbr : covariantField cov (VectorField.mlieBracket I X Y) (Z + W) p =
      covariantField cov (VectorField.mlieBracket I X Y) Z p +
        covariantField cov (VectorField.mlieBracket I X Y) W p :=
    covariantField_add_argument cov hZ' hW'
  rw [houterY, houterX, hbr,
    covariantField_add_argument cov hYZ hYW,
    covariantField_add_argument cov hXZ hXW]
  abel

private lemma curvatureField_smul_right_const_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {c : ℝ} {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) X Y (c • W) p =
      c • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := Connection.contMDiff_leviCivitaConnection g
  have hX' : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hY' : MDiffAt (T% Y) p := hY.mdifferentiableAt (by simp)
  have hW' : MDiffAt (T% W) p := hW.mdifferentiableAt (by simp)
  have hWc : SmoothAt (c • W) p := hW.const_smul_section
  have hYW : MDiffAt (T% (covariantField cov Y W)) p :=
    covariantField_mdifferentiableAt_lc g hY hW
  have hXW : MDiffAt (T% (covariantField cov X W)) p :=
    covariantField_mdifferentiableAt_lc g hX hW
  have hYWc : MDiffAt (T% (covariantField cov Y (c • W))) p :=
    covariantField_mdifferentiableAt_lc g hY hWc
  have hXWc : MDiffAt (T% (covariantField cov X (c • W))) p :=
    covariantField_mdifferentiableAt_lc g hX hWc
  have hYWscale : MDiffAt (T% (c • covariantField cov Y W)) p :=
    mdifferentiableAt_const.smul_section hYW
  have hXWscale : MDiffAt (T% (c • covariantField cov X W)) p :=
    mdifferentiableAt_const.smul_section hXW
  have hWev := smoothAt_eventually_mdifferentiableAt hW
  have hYinner : covariantField cov Y (c • W) =ᶠ[𝓝 p]
      c • covariantField cov Y W := by
    filter_upwards [hWev] with q hWq
    have hc := cov.isCovariantDerivativeOn.smul_const c hWq
    exact congrArg (fun A => A (Y q)) hc
  have hXinner : covariantField cov X (c • W) =ᶠ[𝓝 p]
      c • covariantField cov X W := by
    filter_upwards [hWev] with q hWq
    have hc := cov.isCovariantDerivativeOn.smul_const c hWq
    exact congrArg (fun A => A (X q)) hc
  have hfirst : covariantField cov X (covariantField cov Y (c • W)) p =
      c • covariantField cov X (covariantField cov Y W) p := by
    rw [covariantField_congr_argument cov hYWc hYWscale hYinner]
    unfold covariantField
    change cov (c • covariantField cov Y W) p (X p) = _
    have hc := cov.isCovariantDerivativeOn.smul_const c hYW
    exact congrArg (fun A => A (X p)) hc
  have hsecond : covariantField cov Y (covariantField cov X (c • W)) p =
      c • covariantField cov Y (covariantField cov X W) p := by
    rw [covariantField_congr_argument cov hXWc hXWscale hXinner]
    unfold covariantField
    change cov (c • covariantField cov X W) p (Y p) = _
    have hc := cov.isCovariantDerivativeOn.smul_const c hXW
    exact congrArg (fun A => A (Y p)) hc
  have hthird : covariantField cov (VectorField.mlieBracket I X Y) (c • W) p =
      c • covariantField cov (VectorField.mlieBracket I X Y) W p := by
    unfold covariantField
    have hc := cov.isCovariantDerivativeOn.smul_const c hW'
    exact congrArg (fun A => A (VectorField.mlieBracket I X Y p)) hc
  unfold curvatureField
  rw [hfirst, hsecond, hthird]
  module

/-! ### Canonical pointwise slot laws -/

/-- Additivity of the canonical curvature operator in its first vector slot. -/
theorem curvature_add_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature g p (X + Y) Z W = curvature g p X Z W + curvature g p Y Z W := by
  let cov := Connection.leviCivitaConnection g
  let X' := FiberBundle.extend EM X
  let Y' := FiberBundle.extend EM Y
  let Z' := FiberBundle.extend EM Z
  let W' := FiberBundle.extend EM W
  let S' := FiberBundle.extend EM (X + Y)
  let T' := X' + Y'
  have hXc : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM X
  have hYc : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM Y
  have hZc : SmoothAt Z' p := FiberBundle.contMDiffAt_extend I EM Z
  have hWc : SmoothAt W' p := FiberBundle.contMDiffAt_extend I EM W
  have hSc : SmoothAt S' p := FiberBundle.contMDiffAt_extend I EM (X + Y)
  have hTc : SmoothAt T' p := hXc.add_section hYc
  have hSXW := covariantField_mdifferentiableAt_lc g hSc hWc
  have hTXW := covariantField_mdifferentiableAt_lc g hTc hWc
  have heq : S' =ᶠ[𝓝 p] T' := extend_add_eventuallyEq X Y
  have hcovEq : covariantField cov S' W' =ᶠ[𝓝 p]
      covariantField cov T' W' := by
    filter_upwards [heq] with q hq
    exact covariantField_congr_direction cov hq
  have hfirst := curvatureField_congr_first (Y := Z') cov hSXW hTXW hcovEq heq
  have hadd := curvatureField_add_left_at (X := X') (Y := Y') (Z := Z') (W := W')
    g hXc hYc hWc
  change curvatureField cov S' Z' W' p =
    curvatureField cov X' Z' W' p + curvatureField cov Y' Z' W' p
  rw [hfirst]
  simpa [curvature_def, cov, X', Y', Z', W', S', T'] using hadd

/-- Homogeneity of the canonical curvature operator in its first vector slot. -/
theorem curvature_smul_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y W : TangentSpace I p) :
    curvature g p (c • X) Y W = c • curvature g p X Y W := by
  let cov := Connection.leviCivitaConnection g
  let X' := FiberBundle.extend EM X
  let Y' := FiberBundle.extend EM Y
  let W' := FiberBundle.extend EM W
  let S' := FiberBundle.extend EM (c • X)
  let T' := (fun _ : M => c) • X'
  have hXc : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM X
  have hYc : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM Y
  have hWc : SmoothAt W' p := FiberBundle.contMDiffAt_extend I EM W
  have hSc : SmoothAt S' p := FiberBundle.contMDiffAt_extend I EM (c • X)
  have hTc : SmoothAt T' p := contMDiffAt_const.smul_section hXc
  have hSXW := covariantField_mdifferentiableAt_lc g hSc hWc
  have hTXW := covariantField_mdifferentiableAt_lc g hTc hWc
  have heq : S' =ᶠ[𝓝 p] T' := extend_smul_eventuallyEq c X
  have hcovEq : covariantField cov S' W' =ᶠ[𝓝 p]
      covariantField cov T' W' := by
    filter_upwards [heq] with q hq
    exact covariantField_congr_direction cov hq
  have hfirst := curvatureField_congr_first (Y := Y') cov hSXW hTXW hcovEq heq
  have hsmul := curvatureField_smul_left_at (c := c) (X := X') (Y := Y') (W := W')
    g hXc hYc hWc
  change curvatureField cov S' Y' W' p = c • curvatureField cov X' Y' W' p
  rw [hfirst]
  have hT : T' = c • X' := by
    funext q
    simp [T']
  rw [hT]
  exact hsmul

/-- Additivity of the canonical curvature operator in its second vector slot. -/
theorem curvature_add_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature g p X (Y + Z) W = curvature g p X Y W + curvature g p X Z W := by
  calc
    curvature g p X (Y + Z) W = -curvature g p (Y + Z) X W := by
      rw [curvature_swap]
    _ = -(curvature g p Y X W + curvature g p Z X W) := by
      rw [curvature_add_first]
    _ = curvature g p X Y W + curvature g p X Z W := by
      rw [curvature_swap g p Y X W, curvature_swap g p Z X W]
      abel

/-- Homogeneity of the canonical curvature operator in its second vector slot. -/
theorem curvature_smul_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y W : TangentSpace I p) :
    curvature g p X (c • Y) W = c • curvature g p X Y W := by
  calc
    curvature g p X (c • Y) W = -curvature g p (c • Y) X W := by
      rw [curvature_swap]
    _ = -(c • curvature g p Y X W) := by
      rw [curvature_smul_first (g := g) (p := p) (c := c)
        (X := Y) (Y := X) (W := W)]
    _ = c • curvature g p X Y W := by
      rw [curvature_swap g p Y X W]
      module

/-- Additivity of the canonical curvature operator in its third vector slot. -/
theorem curvature_add_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature g p X Y (Z + W) = curvature g p X Y Z + curvature g p X Y W := by
  let cov := Connection.leviCivitaConnection g
  let X' := FiberBundle.extend EM X
  let Y' := FiberBundle.extend EM Y
  let Z' := FiberBundle.extend EM Z
  let W' := FiberBundle.extend EM W
  let S' := FiberBundle.extend EM (Z + W)
  let T' := Z' + W'
  have hXc : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM X
  have hYc : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM Y
  have hZc : SmoothAt Z' p := FiberBundle.contMDiffAt_extend I EM Z
  have hWc : SmoothAt W' p := FiberBundle.contMDiffAt_extend I EM W
  have hSc : SmoothAt S' p := FiberBundle.contMDiffAt_extend I EM (Z + W)
  have hTc : SmoothAt T' p := hZc.add_section hWc
  have hYS := covariantField_mdifferentiableAt_lc g hYc hSc
  have hYT := covariantField_mdifferentiableAt_lc g hYc hTc
  have hXS := covariantField_mdifferentiableAt_lc g hXc hSc
  have hXT := covariantField_mdifferentiableAt_lc g hXc hTc
  have heq : S' =ᶠ[𝓝 p] T' := extend_add_eventuallyEq Z W
  have hYeq : covariantField cov Y' S' =ᶠ[𝓝 p]
      covariantField cov Y' T' := by
    apply covariantField_congr_eventually_at cov
    · exact smoothAt_eventually_mdifferentiableAt hSc
    · exact smoothAt_eventually_mdifferentiableAt hTc
    · exact heq
  have hXeq : covariantField cov X' S' =ᶠ[𝓝 p]
      covariantField cov X' T' := by
    apply covariantField_congr_eventually_at cov
    · exact smoothAt_eventually_mdifferentiableAt hSc
    · exact smoothAt_eventually_mdifferentiableAt hTc
    · exact heq
  have hthird := curvatureField_congr_third cov
    (hSc.mdifferentiableAt (by simp)) (hTc.mdifferentiableAt (by simp))
    hYS hYT hXS hXT hYeq hXeq heq
  have hadd := curvatureField_add_right_at (X := X') (Y := Y') (Z := Z') (W := W')
    g hXc hYc hZc hWc
  change curvatureField cov X' Y' S' p =
    curvatureField cov X' Y' Z' p + curvatureField cov X' Y' W' p
  rw [hthird]
  simpa [curvature_def, cov, X', Y', Z', W', S', T'] using hadd

/-- Homogeneity of the canonical curvature operator in its third vector slot. -/
theorem curvature_smul_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y Z : TangentSpace I p) :
    curvature g p X Y (c • Z) = c • curvature g p X Y Z := by
  let cov := Connection.leviCivitaConnection g
  let X' := FiberBundle.extend EM X
  let Y' := FiberBundle.extend EM Y
  let Z' := FiberBundle.extend EM Z
  let S' := FiberBundle.extend EM (c • Z)
  let T' := (fun _ : M => c) • Z'
  have hXc : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM X
  have hYc : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM Y
  have hZc : SmoothAt Z' p := FiberBundle.contMDiffAt_extend I EM Z
  have hSc : SmoothAt S' p := FiberBundle.contMDiffAt_extend I EM (c • Z)
  have hTc : SmoothAt T' p := contMDiffAt_const.smul_section hZc
  have hYS := covariantField_mdifferentiableAt_lc g hYc hSc
  have hYT := covariantField_mdifferentiableAt_lc g hYc hTc
  have hXS := covariantField_mdifferentiableAt_lc g hXc hSc
  have hXT := covariantField_mdifferentiableAt_lc g hXc hTc
  have heq : S' =ᶠ[𝓝 p] T' := extend_smul_eventuallyEq c Z
  have hYeq : covariantField cov Y' S' =ᶠ[𝓝 p]
      covariantField cov Y' T' := by
    apply covariantField_congr_eventually_at cov
    · exact smoothAt_eventually_mdifferentiableAt hSc
    · exact smoothAt_eventually_mdifferentiableAt hTc
    · exact heq
  have hXeq : covariantField cov X' S' =ᶠ[𝓝 p]
      covariantField cov X' T' := by
    apply covariantField_congr_eventually_at cov
    · exact smoothAt_eventually_mdifferentiableAt hSc
    · exact smoothAt_eventually_mdifferentiableAt hTc
    · exact heq
  have hthird := curvatureField_congr_third cov
    (hSc.mdifferentiableAt (by simp)) (hTc.mdifferentiableAt (by simp))
    hYS hYT hXS hXT hYeq hXeq heq
  have hsmul := curvatureField_smul_right_const_at (c := c)
    (X := X') (Y := Y') (W := Z') g hXc hYc hZc
  change curvatureField cov X' Y' S' p = c • curvatureField cov X' Y' Z' p
  rw [hthird]
  have hT : T' = c • Z' := by
    funext q
    simp [T']
  rw [hT]
  exact hsmul

/-! ### TensorialAt witnesses -/

/-- The first-slot pointwise operation is a `TensorialAt`. -/
theorem curvature_tensorial_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (Y W : TangentSpace I p) :
    TensorialAt I EM
      (fun X : (x : M) → TangentSpace I x => curvature g p (X p) Y W) p := by
  constructor
  · intro f X hf hX
    change curvature g p ((f p) • X p) Y W = f p • curvature g p (X p) Y W
    exact curvature_smul_first g p (f p) (X p) Y W
  · intro X X' hX hX'
    change curvature g p ((X + X') p) Y W =
      curvature g p (X p) Y W + curvature g p (X' p) Y W
    rw [Pi.add_apply, curvature_add_first]

/-- The second-slot pointwise operation is a `TensorialAt`. -/
theorem curvature_tensorial_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X W : TangentSpace I p) :
    TensorialAt I EM
      (fun Y : (x : M) → TangentSpace I x => curvature g p X (Y p) W) p := by
  constructor
  · intro f Y hf hY
    change curvature g p X ((f p) • Y p) W = f p • curvature g p X (Y p) W
    exact curvature_smul_second g p (f p) X (Y p) W
  · intro Y Y' hY hY'
    change curvature g p X ((Y + Y') p) W =
      curvature g p X (Y p) W + curvature g p X (Y' p) W
    rw [Pi.add_apply, curvature_add_second]

/-- The third-slot pointwise operation is a `TensorialAt`. -/
theorem curvature_tensorial_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y : TangentSpace I p) :
    TensorialAt I EM
      (fun W : (x : M) → TangentSpace I x => curvature g p X Y (W p)) p := by
  constructor
  · intro f W hf hW
    change curvature g p X Y ((f p) • W p) = f p • curvature g p X Y (W p)
    exact curvature_smul_third g p (f p) X Y (W p)
  · intro W W' hW hW'
    change curvature g p X Y ((W + W') p) =
      curvature g p X Y (W p) + curvature g p X Y (W' p)
    rw [Pi.add_apply, curvature_add_third]

/-! ### Metric-paired curvature linearity -/

/-- Additivity of the metric-paired curvature in its first vector slot. -/
theorem curvature4_add_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W V : TangentSpace I p) :
    curvature4 g p (X + Y) Z W V =
      curvature4 g p X Z W V + curvature4 g p Y Z W V := by
  rw [curvature4_def, curvature4_def, curvature4_def, curvature_add_first]
  rw [map_add]
  simp only [_root_.add_apply]

/-- Homogeneity of the metric-paired curvature in its first vector slot. -/
theorem curvature4_smul_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y Z W : TangentSpace I p) :
    curvature4 g p (c • X) Y Z W = c • curvature4 g p X Y Z W := by
  rw [curvature4_def, curvature4_def, curvature_smul_first]
  rw [map_smul]
  simp only [_root_.smul_apply]

/-- Additivity of the metric-paired curvature in its second vector slot. -/
theorem curvature4_add_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W V : TangentSpace I p) :
    curvature4 g p X (Y + Z) W V =
      curvature4 g p X Y W V + curvature4 g p X Z W V := by
  rw [curvature4_def, curvature4_def, curvature4_def, curvature_add_second]
  rw [map_add]
  simp only [_root_.add_apply]

/-- Homogeneity of the metric-paired curvature in its second vector slot. -/
theorem curvature4_smul_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y Z W : TangentSpace I p) :
    curvature4 g p X (c • Y) Z W = c • curvature4 g p X Y Z W := by
  rw [curvature4_def, curvature4_def, curvature_smul_second]
  rw [map_smul]
  simp only [_root_.smul_apply]

/-- Additivity of the metric-paired curvature in its metric-pairing slot. -/
theorem curvature4_add_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W V : TangentSpace I p) :
    curvature4 g p X Y (Z + W) V =
      curvature4 g p X Y Z V + curvature4 g p X Y W V := by
  simp only [curvature4_def]
  rw [map_add]

/-- Homogeneity of the metric-paired curvature in its metric-pairing slot. -/
theorem curvature4_smul_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y Z V : TangentSpace I p) :
    curvature4 g p X Y (c • Z) V = c • curvature4 g p X Y Z V := by
  simp only [curvature4_def]
  rw [map_smul]

/-- Additivity of the metric-paired curvature in its fourth vector slot. -/
theorem curvature4_add_fourth
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W V : TangentSpace I p) :
    curvature4 g p X Y Z (W + V) =
      curvature4 g p X Y Z W + curvature4 g p X Y Z V := by
  rw [curvature4_def, curvature4_def, curvature4_def, curvature_add_third]
  rw [map_add]
  simp only [_root_.add_apply]

/-- Homogeneity of the metric-paired curvature in its fourth vector slot. -/
theorem curvature4_smul_fourth
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (c : ℝ) (X Y Z W : TangentSpace I p) :
    curvature4 g p X Y Z (c • W) = c • curvature4 g p X Y Z W := by
  rw [curvature4_def, curvature4_def, curvature_smul_third]
  rw [map_smul]
  simp only [_root_.smul_apply]

/-! The four-tensor is tensorial in each tangent slot.  The hypotheses on
sections are consumed only by `TensorialAt`; the pointwise laws above reduce
the resulting goals to the canonical tangent-fiber operations. -/

/-- The metric-paired curvature is a `TensorialAt` in its first slot. -/
theorem curvature4_tensorial_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (Y Z W : TangentSpace I p) :
    TensorialAt I EM
      (fun X : (x : M) → TangentSpace I x => curvature4 g p (X p) Y Z W) p := by
  constructor
  · intro f X _hf _hX
    change curvature4 g p ((f p) • X p) Y Z W = _
    exact curvature4_smul_first g p (f p) (X p) Y Z W
  · intro X X' _hX _hX'
    change curvature4 g p ((X + X') p) Y Z W = _
    rw [Pi.add_apply, curvature4_add_first]

/-- The metric-paired curvature is a `TensorialAt` in its second slot. -/
theorem curvature4_tensorial_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Z W : TangentSpace I p) :
    TensorialAt I EM
      (fun Y : (x : M) → TangentSpace I x => curvature4 g p X (Y p) Z W) p := by
  constructor
  · intro f Y _hf _hY
    change curvature4 g p X ((f p) • Y p) Z W = _
    exact curvature4_smul_second g p (f p) X (Y p) Z W
  · intro Y Y' _hY _hY'
    change curvature4 g p X ((Y + Y') p) Z W = _
    rw [Pi.add_apply, curvature4_add_second]

/-- The metric-paired curvature is a `TensorialAt` in its third slot. -/
theorem curvature4_tensorial_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y W : TangentSpace I p) :
    TensorialAt I EM
      (fun Z : (x : M) → TangentSpace I x => curvature4 g p X Y (Z p) W) p := by
  constructor
  · intro f Z _hf _hZ
    change curvature4 g p X Y ((f p) • Z p) W = _
    exact curvature4_smul_third g p (f p) X Y (Z p) W
  · intro Z Z' _hZ _hZ'
    change curvature4 g p X Y ((Z + Z') p) W = _
    rw [Pi.add_apply, curvature4_add_third]

/-- The metric-paired curvature is a `TensorialAt` in its fourth slot. -/
theorem curvature4_tensorial_fourth
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z : TangentSpace I p) :
    TensorialAt I EM
      (fun W : (x : M) → TangentSpace I x => curvature4 g p X Y Z (W p)) p := by
  constructor
  · intro f W _hf _hW
    change curvature4 g p X Y Z ((f p) • W p) = _
    exact curvature4_smul_fourth g p (f p) X Y Z (W p)
  · intro W W' _hW _hW'
    change curvature4 g p X Y Z ((W + W') p) = _
    rw [Pi.add_apply, curvature4_add_fourth]

/-! ### First Bianchi identity -/

private lemma curvatureField_bianchi_local
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hZ : SmoothAt Z p) :
    curvatureField (Connection.leviCivitaConnection g) X Y Z p +
      curvatureField (Connection.leviCivitaConnection g) Y Z X p +
      curvatureField (Connection.leviCivitaConnection g) Z X Y p = 0 := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := Connection.contMDiff_leviCivitaConnection g
  letI : IsManifold I (minSmoothness ℝ 3) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  have htor : cov.torsion = 0 := by
    dsimp [cov]
    exact Connection.torsion_leviCivitaConnection_eq_zero g
  have torsion_free_at {A B : (x : M) → TangentSpace I x} {q : M}
      (hA : MDiffAt (T% A) q) (hB : MDiffAt (T% B) q) :
      covariantField cov A B q - covariantField cov B A q =
        VectorField.mlieBracket I A B q := by
    exact (CovariantDerivative.torsion_eq_zero_iff cov).mp htor
      (x := q) hA hB
  have cov_sub_argument {A B C : (x : M) → TangentSpace I x}
      (hB : SmoothAt B p) (hC : SmoothAt C p) :
      covariantField cov A (B - C) p =
        covariantField cov A B p - covariantField cov A C p := by
    have hCneg : SmoothAt ((fun _ : M => (-1 : ℝ)) • C) p :=
      contMDiffAt_const.smul_section hC
    have hadd := covariantField_add_argument cov
      (X := A) (Y := B) (Z := (fun _ : M => (-1 : ℝ)) • C)
      (hB.mdifferentiableAt (by simp)) (hCneg.mdifferentiableAt (by simp))
    have hneg := covariantField_smul_argument cov
      (X := A) (Y := C) (f := fun _ : M => (-1 : ℝ))
      mdifferentiableAt_const (hC.mdifferentiableAt (by simp))
    have hBC : B - C = B + (fun _ : M => (-1 : ℝ)) • C := by
      funext q
      change B q - C q = B q + (-1 : ℝ) • C q
      rw [neg_one_smul]
      simp only [sub_eq_add_neg]
    rw [hBC, hadd]
    have hneg' : covariantField cov A ((fun _ : M => (-1 : ℝ)) • C) p =
        -covariantField cov A C p := by
      simpa [mvfderiv] using hneg
    rw [hneg']
    module
  have hXY := torsion_free_at (hX.mdifferentiableAt (by simp))
    (hY.mdifferentiableAt (by simp))
  have hYZ := torsion_free_at (hY.mdifferentiableAt (by simp))
    (hZ.mdifferentiableAt (by simp))
  have hZX := torsion_free_at (hZ.mdifferentiableAt (by simp))
    (hX.mdifferentiableAt (by simp))
  have hDYZ : SmoothAt (covariantField cov Y Z) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hY hZ
  have hDZY : SmoothAt (covariantField cov Z Y) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hZ hY
  have hDZX : SmoothAt (covariantField cov Z X) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hZ hX
  have hDXZ : SmoothAt (covariantField cov X Z) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hX hZ
  have hDXY : SmoothAt (covariantField cov X Y) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hX hY
  have hDYX : SmoothAt (covariantField cov Y X) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hY hX
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (ENat.LEInfty.out : (2 : ℕ∞ω) ≤ ∞))
  letI : IsManifold I ((↑(2 : ℕ∞) : ℕ∞ω) + 1) M := by
    apply IsManifold.of_le (n := ∞)
    norm_num
    exact ENat.LEInfty.out
  have hX2 : ContMDiffAt I I.tangent (↑(2 : ℕ∞))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := by
    change ContMDiffAt I (I.prod 𝓘(ℝ, EM)) (↑(2 : ℕ∞)) (T% X) p
    exact hX.of_le (ENat.LEInfty.out : (2 : ℕ∞ω) ≤ ∞)
  have hY2 : ContMDiffAt I I.tangent (↑(2 : ℕ∞))
      (fun q => (⟨q, Y q⟩ : TangentBundle I M)) p := by
    change ContMDiffAt I (I.prod 𝓘(ℝ, EM)) (↑(2 : ℕ∞)) (T% Y) p
    exact hY.of_le (ENat.LEInfty.out : (2 : ℕ∞ω) ≤ ∞)
  have hZ2 : ContMDiffAt I I.tangent (↑(2 : ℕ∞))
      (fun q => (⟨q, Z q⟩ : TangentBundle I M)) p := by
    change ContMDiffAt I (I.prod 𝓘(ℝ, EM)) (↑(2 : ℕ∞)) (T% Z) p
    exact hZ.of_le (ENat.LEInfty.out : (2 : ℕ∞ω) ≤ ∞)
  have hbrXY : MDiffAt (T% (VectorField.mlieBracket I X Y)) p := by
    exact (ContMDiffAt.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
      hX2 hY2 (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)).mdifferentiableAt (by norm_num)
  have hbrYZ : MDiffAt (T% (VectorField.mlieBracket I Y Z)) p := by
    exact (ContMDiffAt.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
      hY2 hZ2 (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)).mdifferentiableAt (by norm_num)
  have hbrZX : MDiffAt (T% (VectorField.mlieBracket I Z X)) p := by
    exact (ContMDiffAt.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
      hZ2 hX2 (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)).mdifferentiableAt (by norm_num)
  have hbrXZ : MDiffAt (T% (VectorField.mlieBracket I X Z)) p := by
    exact (ContMDiffAt.mlieBracket_vectorField (m := (1 : ℕ∞)) (n := (2 : ℕ∞))
      hX2 hZ2 (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)).mdifferentiableAt (by norm_num)
  have hYZ_ev : ∀ᶠ q in 𝓝 p,
      covariantField cov Y Z q - covariantField cov Z Y q =
        VectorField.mlieBracket I Y Z q := by
    filter_upwards [smoothAt_eventually_mdifferentiableAt hY,
      smoothAt_eventually_mdifferentiableAt hZ] with q hYq hZq
    exact torsion_free_at hYq hZq
  have hZX_ev : ∀ᶠ q in 𝓝 p,
      covariantField cov Z X q - covariantField cov X Z q =
        VectorField.mlieBracket I Z X q := by
    filter_upwards [smoothAt_eventually_mdifferentiableAt hZ,
      smoothAt_eventually_mdifferentiableAt hX] with q hZq hXq
    exact torsion_free_at hZq hXq
  have hXY_ev : ∀ᶠ q in 𝓝 p,
      covariantField cov X Y q - covariantField cov Y X q =
        VectorField.mlieBracket I X Y q := by
    filter_upwards [smoothAt_eventually_mdifferentiableAt hX,
      smoothAt_eventually_mdifferentiableAt hY] with q hXq hYq
    exact torsion_free_at hXq hYq
  have hA :
      covariantField cov X (covariantField cov Y Z) p -
          covariantField cov X (covariantField cov Z Y) p =
        covariantField cov X (VectorField.mlieBracket I Y Z) p := by
    have hdiff : MDiffAt (T% (covariantField cov Y Z - covariantField cov Z Y)) p :=
      (hDYZ.sub_section hDZY).mdifferentiableAt (by simp)
    calc
      _ = covariantField cov X (covariantField cov Y Z - covariantField cov Z Y) p :=
        (cov_sub_argument (A := X) hDYZ hDZY).symm
      _ = covariantField cov X (VectorField.mlieBracket I Y Z) p :=
        covariantField_congr_argument cov hdiff hbrYZ hYZ_ev
  have hB :
      covariantField cov Y (covariantField cov Z X) p -
          covariantField cov Y (covariantField cov X Z) p =
        covariantField cov Y (VectorField.mlieBracket I Z X) p := by
    have hdiff : MDiffAt (T% (covariantField cov Z X - covariantField cov X Z)) p :=
      (hDZX.sub_section hDXZ).mdifferentiableAt (by simp)
    calc
      _ = covariantField cov Y (covariantField cov Z X - covariantField cov X Z) p :=
        (cov_sub_argument (A := Y) hDZX hDXZ).symm
      _ = covariantField cov Y (VectorField.mlieBracket I Z X) p :=
        covariantField_congr_argument cov hdiff hbrZX hZX_ev
  have hC :
      covariantField cov Z (covariantField cov X Y) p -
          covariantField cov Z (covariantField cov Y X) p =
        covariantField cov Z (VectorField.mlieBracket I X Y) p := by
    have hdiff : MDiffAt (T% (covariantField cov X Y - covariantField cov Y X)) p :=
      (hDXY.sub_section hDYX).mdifferentiableAt (by simp)
    calc
      _ = covariantField cov Z (covariantField cov X Y - covariantField cov Y X) p :=
        (cov_sub_argument (A := Z) hDXY hDYX).symm
      _ = covariantField cov Z (VectorField.mlieBracket I X Y) p :=
        covariantField_congr_argument cov hdiff hbrXY hXY_ev
  have hT1 := torsion_free_at (hX.mdifferentiableAt (by simp)) hbrYZ
  have hT2 := torsion_free_at (hY.mdifferentiableAt (by simp)) hbrZX
  have hT3 := torsion_free_at (hZ.mdifferentiableAt (by simp)) hbrXY
  change
    (covariantField cov X (covariantField cov Y Z) p -
        covariantField cov Y (covariantField cov X Z) p -
        covariantField cov (VectorField.mlieBracket I X Y) Z p) +
      (covariantField cov Y (covariantField cov Z X) p -
        covariantField cov Z (covariantField cov Y X) p -
        covariantField cov (VectorField.mlieBracket I Y Z) X p) +
      (covariantField cov Z (covariantField cov X Y) p -
        covariantField cov X (covariantField cov Z Y) p -
        covariantField cov (VectorField.mlieBracket I Z X) Y p) = 0
  rw [show
      (covariantField cov X (covariantField cov Y Z) p -
          covariantField cov Y (covariantField cov X Z) p -
          covariantField cov (VectorField.mlieBracket I X Y) Z p) +
        (covariantField cov Y (covariantField cov Z X) p -
          covariantField cov Z (covariantField cov Y X) p -
          covariantField cov (VectorField.mlieBracket I Y Z) X p) +
        (covariantField cov Z (covariantField cov X Y) p -
          covariantField cov X (covariantField cov Z Y) p -
          covariantField cov (VectorField.mlieBracket I Z X) Y p) =
      (covariantField cov X (covariantField cov Y Z) p -
          covariantField cov X (covariantField cov Z Y) p) +
        (covariantField cov Y (covariantField cov Z X) p -
          covariantField cov Y (covariantField cov X Z) p) +
        (covariantField cov Z (covariantField cov X Y) p -
          covariantField cov Z (covariantField cov Y X) p) -
        (covariantField cov (VectorField.mlieBracket I X Y) Z p +
          covariantField cov (VectorField.mlieBracket I Y Z) X p +
          covariantField cov (VectorField.mlieBracket I Z X) Y p) by module]
  rw [hA, hB, hC]
  rw [show
      (covariantField cov X (VectorField.mlieBracket I Y Z) p +
          covariantField cov Y (VectorField.mlieBracket I Z X) p +
          covariantField cov Z (VectorField.mlieBracket I X Y) p) -
        (covariantField cov (VectorField.mlieBracket I X Y) Z p +
          covariantField cov (VectorField.mlieBracket I Y Z) X p +
          covariantField cov (VectorField.mlieBracket I Z X) Y p) =
      (covariantField cov X (VectorField.mlieBracket I Y Z) p -
          covariantField cov (VectorField.mlieBracket I Y Z) X p) +
        (covariantField cov Y (VectorField.mlieBracket I Z X) p -
          covariantField cov (VectorField.mlieBracket I Z X) Y p) +
        (covariantField cov Z (VectorField.mlieBracket I X Y) p -
          covariantField cov (VectorField.mlieBracket I X Y) Z p) by module]
  rw [hT1, hT2, hT3]
  have hX2j : ContMDiffAt I I.tangent (minSmoothness ℝ 2)
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hX2
  have hY2j : ContMDiffAt I I.tangent (minSmoothness ℝ 2)
      (fun q => (⟨q, Y q⟩ : TangentBundle I M)) p := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hY2
  have hZ2j : ContMDiffAt I I.tangent (minSmoothness ℝ 2)
      (fun q => (⟨q, Z q⟩ : TangentBundle I M)) p := by
    simpa [minSmoothness_of_isRCLikeNormedField] using hZ2
  have hj := VectorField.leibniz_identity_mlieBracket_apply hX2j hY2j hZ2j
  have hBswap : VectorField.mlieBracket I Y (VectorField.mlieBracket I Z X) p =
      -VectorField.mlieBracket I Y (VectorField.mlieBracket I X Z) p := by
    rw [show VectorField.mlieBracket I Z X =
      -(VectorField.mlieBracket I X Z) by rw [mlieBracket_swap]]
    simpa [Pi.smul_apply, mvfderiv] using
      (VectorField.mlieBracket_const_smul_right (I := I) (V := Y)
        (W := VectorField.mlieBracket I X Z) (c := (-1 : ℝ)) hbrXZ)
  have hCswap : VectorField.mlieBracket I Z (VectorField.mlieBracket I X Y) p =
      -VectorField.mlieBracket I (VectorField.mlieBracket I X Y) Z p := by
    rw [mlieBracket_swap_apply]
  rw [hBswap, hCswap, hj]
  module

/-- The extension-based first Bianchi identity in the source curvature order:
`R X Y Z + R Y Z X + R Z X Y = 0`. -/
theorem curvature_bianchi
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z : TangentSpace I p) :
    curvature g p X Y Z + curvature g p Y Z X + curvature g p Z X Y = 0 := by
  let X' := FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM X
  let Y' := FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM Y
  let Z' := FiberBundle.extend (E := (TangentSpace I : M → Type _)) EM Z
  have hX' : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM X
  have hY' : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM Y
  have hZ' : SmoothAt Z' p := FiberBundle.contMDiffAt_extend I EM Z
  have h := curvatureField_bianchi_local g hX' hY' hZ'
  simpa [curvature, curvature_def, X', Y', Z'] using h

/-! The same identity after the source-ordered metric pairing. -/

/-- First Bianchi in Morgan--Tian's `(0,4)` order.  The cyclic slots are the
first, second, and fourth arguments; the third argument is the pairing slot. -/
theorem curvature4_bianchi
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature4 g p X Y Z W + curvature4 g p Y W Z X +
      curvature4 g p W X Z Y = 0 := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := curvature_bianchi g p X Y W
  have hp := congrArg (fun V => g.inner p V Z) h
  rw [map_add, map_add, map_zero] at hp
  simpa [curvature4_def] using hp

end Tensoriality

end Curvature
end Ch01
end MorganTianLib
