import MorganTianLib.Ch01.Curvature.Tensoriality
import MorganTianLib.Ch01.Curvature.Sectional
import MorganTianLib.Ch01.Curvature.ScalarCommutator
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Intrinsic curvature symmetries

This module owns the metric-symmetry boundary for the connection-produced
curvature of Chapter 1.  The public four-tensor follows Morgan--Tian Claim 1.5
(`morganTian2007`, printed pp. 37--38):

`R X Y Z W = g (R X Y W) Z`.

In particular, the pairing slot is the third argument and the curvature input
is the fourth argument.  The declarations below are pointwise and field-level;
they do not introduce a covariant derivative on tensor bundles or a
differential-Bianchi facade.

The field-level definitions deliberately use the canonical bundled
`Connection.leviCivitaConnection`; no coordinate or selected-extension
connection is introduced here.  The algebraic pair-interchange lemma is kept
separate from the analytic metric-skew proof, so downstream users can consume
it with an explicitly checked last-pair theorem.

The metric calculation uses
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq`; the scalar
second-derivative commutator is isolated in `ScalarCommutator` and the first
Bianchi identity is consumed from `Tensoriality`.  No coordinate frame or
second connection is introduced.

The polarization and pair-interchange arguments are the standard ones checked
against do Carmo, *Riemannian Geometry*, Chapter 4, Section 3
(`doCarmo1992`), and Petersen, *Riemannian Geometry*, Chapter 3
(`petersen2016`).

The exported `SmoothTensorialAt` contract is the smooth-local analogue of
Mathlib's `TensorialAt`; its local-frame pointwise lemma and the
`curvatureField_eq_of_value_eq` corollary provides the extension/germ
bridge while retaining the exact bundled `RiemannianBundle` metric.  The
weaker first-order `TensorialAt` producer and a public chart-component bridge
remain separate follow-up boundaries.
-/

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

section Symmetries

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-- Smoothness at a point for a tangent-bundle vector field.  The bundled
`T%` presentation is the one consumed by Mathlib's covariant-derivative and
Lie-bracket APIs. -/
abbrev SmoothAt (X : (x : M) → TangentSpace I x) (p : M) : Prop :=
  ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% X) p

/-! ### Field-level source-ordered tensors -/

/-- The source-ordered `(0,4)` curvature field.  The third argument is paired
with the output of the curvature operator applied to the fourth argument. -/
noncomputable def curvature4Field
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (X Y Z W : (x : M) → TangentSpace I x) : M → ℝ :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  fun p => g.inner p (curvatureField (Connection.leviCivitaConnection g) X Y W p) (Z p)

/-- Pointwise evaluation of `curvature4Field`, exposing the source-ordered
pairing without unfolding its local metric instance. -/
@[simp] theorem curvature4Field_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (X Y Z W : (x : M) → TangentSpace I x) (p : M) :
    curvature4Field g X Y Z W p =
      g.inner p (curvatureField (Connection.leviCivitaConnection g) X Y W p) (Z p) := rfl

/-- Smoothness of the source-ordered four-tensor on smooth tangent sections.
The proof uses the bundled Levi--Civita regularity theorem and the metric
pairing operation; it does not choose a coordinate frame or a selected
extension. -/
theorem curvature4Field_smooth
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hW : CMDiff ∞ (T% W)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (curvature4Field g X Y Z W) := by
  intro p
  let cov := Connection.leviCivitaConnection g
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : cov.ContMDiffCovariantDerivative ∞ := by
    dsimp [cov]
    exact Connection.contMDiff_leviCivitaConnection g
  have hR : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
      (T% (curvatureField cov X Y W)) p :=
    curvatureField_smooth cov hX hY hW p
  change ContMDiffAt I 𝓘(ℝ, ℝ) ∞
    (fun q => inner ℝ (curvatureField cov X Y W q) (Z q)) p
  exact ContMDiffAt.inner_bundle (IB := I) (F := EM)
    (E := (TangentSpace I : M → Type _)) (b := fun q => q)
    (v := curvatureField cov X Y W) (w := Z) hR (hZ p)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ EM] in
/-- Equality of scalar manifold derivatives follows from equality of germs. -/
theorem mvfderiv_eq_of_eventuallyEq_scalar {f₁ f₂ : M → ℝ} {q : M}
    (h : f₁ =ᶠ[𝓝 q] f₂) :
    (d% f₁ q) = (d% f₂ q) := by
  have hm : mfderiv I 𝓘(ℝ, ℝ) f₁ q = mfderiv I 𝓘(ℝ, ℝ) f₂ q :=
    Filter.EventuallyEq.mfderiv_eq h
  have hq : f₁ q = f₂ q := h.eq_of_nhds
  change (NormedSpace.fromTangentSpace (f₁ q)).toContinuousLinearMap ∘L
      (mfderiv I 𝓘(ℝ, ℝ) f₁ q) =
    (NormedSpace.fromTangentSpace (f₂ q)).toContinuousLinearMap ∘L
      (mfderiv I 𝓘(ℝ, ℝ) f₂ q)
  rw [hm, hq]

/-! ### Metric self-contraction

The diagonal vanishing proof is the local metric argument behind the last-pair
skew.  The scalar commutator is proved in `ScalarCommutator` from the manifold
Jacobi identity, so this layer does not assume a coordinate curvature formula.
-/

/-- The source-ordered curvature four-tensor vanishes when its final two
arguments agree.  This is the metric-compatibility diagonal used for
polarization. -/
theorem curvature4Field_self_zero_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hZ : SmoothAt Z p) :
    curvature4Field g X Y Z Z p = 0 := by
  let cov := Connection.leviCivitaConnection g
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : cov.ContMDiffCovariantDerivative ∞ := by
    dsimp [cov]
    exact Connection.contMDiff_leviCivitaConnection g
  have hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I) := by
    dsimp [cov]
    exact Connection.isMetricCompatible_leviCivitaConnection g
  let f : M → ℝ := fun q => inner ℝ (Z q) (Z q)
  have hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p := by
    change ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => inner ℝ (Z q) (Z q)) p
    exact ContMDiffAt.inner_bundle (IB := I) (F := EM)
      (E := (TangentSpace I : M → Type _)) (b := fun q => q)
      (v := Z) (w := Z) hZ hZ
  have hhalf_at : ∀ {A : (x : M) → TangentSpace I x} {q : M},
      MDiffAt (T% A) q → MDiffAt (T% Z) q →
      inner ℝ (covariantField cov A Z q) (Z q) =
        (1 / 2 : ℝ) * (d% f q) (A q) := by
    intro A q hA hZq
    have hc := hmetric.mvfderiv_inner_eq (x := q) A hZq hZq
    change (d% f q) (A q) =
      inner ℝ (covariantField cov A Z q) (Z q) +
        inner ℝ (Z q) (covariantField cov A Z q) at hc
    nth_rewrite 2 [real_inner_comm] at hc
    linarith
  have hYZ : SmoothAt (covariantField cov Y Z) p := by
    dsimp [SmoothAt, cov, covariantField]
    exact Connection.contMDiffAt_leviCivitaConnection_apply g hY hZ
  have hXZ : SmoothAt (covariantField cov X Z) p := by
    dsimp [SmoothAt, cov, covariantField]
    exact Connection.contMDiffAt_leviCivitaConnection_apply g hX hZ
  have hI1 :
      (d% (fun q => inner ℝ (covariantField cov Y Z q) (Z q)) p) (X p) =
        inner ℝ (covariantField cov X (covariantField cov Y Z) p) (Z p) +
          inner ℝ (covariantField cov Y Z p) (covariantField cov X Z p) := by
    have hc := hmetric.mvfderiv_inner_eq X
      (hYZ.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
    simpa [covariantField] using hc
  have hI2 :
      (d% (fun q => inner ℝ (covariantField cov X Z q) (Z q)) p) (Y p) =
        inner ℝ (covariantField cov Y (covariantField cov X Z) p) (Z p) +
          inner ℝ (covariantField cov X Z p) (covariantField cov Y Z p) := by
    have hc := hmetric.mvfderiv_inner_eq Y
      (hXZ.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
    simpa [covariantField] using hc
  have hhalf_derivative : ∀ {A B : (x : M) → TangentSpace I x},
      SmoothAt A p → SmoothAt B p →
      (d% (fun q => inner ℝ (covariantField cov A Z q) (Z q)) p) (B p) =
        (1 / 2 : ℝ) * (d% (fun q => d% f q (A q)) p) (B p) := by
    intro A B hA hB
    have hAev : ∀ᶠ q in 𝓝 p, MDiffAt (T% A) q := by
      exact ScalarCommutator.smoothAt_eventually_mdifferentiableAt hA
    have hZev : ∀ᶠ q in 𝓝 p, MDiffAt (T% Z) q := by
      exact ScalarCommutator.smoothAt_eventually_mdifferentiableAt hZ
    have hev : (fun q => inner ℝ (covariantField cov A Z q) (Z q)) =ᶠ[𝓝 p]
        (fun q => (1 / 2 : ℝ) * (d% f q (A q))) := by
      filter_upwards [hAev, hZev] with q hAq hZq
      exact hhalf_at hAq hZq
    have hda : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun q => d% f q (A q)) p := by
      exact ScalarCommutator.contMDiffAt_mvfderiv_apply_along hf hA
    have hda' : MDiffAt (fun q => d% f q (A q)) p :=
      hda.mdifferentiableAt (by simp)
    have hderiv :
        (d% (fun q => inner ℝ (covariantField cov A Z q) (Z q)) p) =
          (d% (fun q => (1 / 2 : ℝ) * (d% f q (A q))) p) := by
      exact mvfderiv_eq_of_eventuallyEq_scalar hev
    have hsm := mvfderiv_mul (f := fun _ : M => (1 / 2 : ℝ))
      (g := fun q => d% f q (A q)) mdifferentiableAt_const hda'
    have heval := congrArg (fun L => L (B p)) hderiv
    have heval' := congrArg (fun L => L (B p)) hsm
    simpa [mvfderiv, smul_eq_mul] using heval.trans heval'
  have hD1 := hhalf_derivative (A := Y) (B := X) hY hX
  have hD2 := hhalf_derivative (A := X) (B := Y) hX hY
  have hbr : SmoothAt (VectorField.mlieBracket I X Y) p :=
    ScalarCommutator.mlieBracket_smoothAt hX hY
  have hD3 := hhalf_at
    (A := VectorField.mlieBracket I X Y) (q := p)
    (hbr.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))
  have hcomm := ScalarCommutator.scalar_bracket_commutator_at
    (p := p) hf hX hY
  have hscalar :
      (d% (fun q => inner ℝ (covariantField cov Y Z q) (Z q)) p) (X p) -
          (d% (fun q => inner ℝ (covariantField cov X Z q) (Z q)) p) (Y p) -
          inner ℝ (covariantField cov (VectorField.mlieBracket I X Y) Z p) (Z p) = 0 := by
    have hcomm' :
        (d% (fun q => d% f q (Y q)) p) (X p) -
            (d% (fun q => d% f q (X q)) p) (Y p) -
            (d% f p) (VectorField.mlieBracket I X Y p) = 0 := by
      exact sub_eq_zero.mpr hcomm
    linarith
  have hcross :
      inner ℝ (covariantField cov Y Z p) (covariantField cov X Z p) =
        inner ℝ (covariantField cov X Z p) (covariantField cov Y Z p) := by
    exact real_inner_comm _ _
  rw [curvature4Field_apply]
  change inner ℝ
    (covariantField cov X (covariantField cov Y Z) p -
        covariantField cov Y (covariantField cov X Z) p -
        covariantField cov (VectorField.mlieBracket I X Y) Z p) (Z p) = 0
  rw [inner_sub_left, inner_sub_left]
  linarith [hI1, hI2, hD1, hD2, hD3, hscalar, hcross]

/-- The metric last-pair skew follows by polarizing the diagonal identity. -/
theorem curvature4Field_antisymm_last_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p)
    (hZ : SmoothAt Z p) (hW : SmoothAt W p) :
    curvature4Field g X Y Z W p = -curvature4Field g X Y W Z p := by
  have hZW : SmoothAt (Z + W) p := by
    exact hZ.add_section hW
  have h0 := curvature4Field_self_zero_smoothAt g hX hY hZW
  have hZ0 := curvature4Field_self_zero_smoothAt g hX hY hZ
  have hW0 := curvature4Field_self_zero_smoothAt g hX hY hW
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hadd := curvatureField_add_right_smoothAt g hX hY hZ hW
  rw [curvature4Field_apply] at h0 hZ0 hW0
  change inner ℝ
      (curvatureField (Connection.leviCivitaConnection g) X Y (Z + W) p)
        ((Z + W) p) = _ at h0
  change inner ℝ
      (curvatureField (Connection.leviCivitaConnection g) X Y Z p) (Z p) = 0 at hZ0
  change inner ℝ
      (curvatureField (Connection.leviCivitaConnection g) X Y W p) (W p) = 0 at hW0
  rw [hadd] at h0
  simp only [Pi.add_apply, inner_add_left, inner_add_right] at h0
  change inner ℝ
      (curvatureField (Connection.leviCivitaConnection g) X Y W p) (Z p) =
    -inner ℝ
      (curvatureField (Connection.leviCivitaConnection g) X Y Z p) (W p)
  linarith [h0, hZ0, hW0]

/-- The corresponding `(1,3)` output-pairing identity.  It is stated with
the operator input in the third displayed slot, matching the source order. -/
theorem curvatureField_inner_last_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p)
    (hZ : SmoothAt Z p) (hW : SmoothAt W p) :
    g.inner p (curvatureField (Connection.leviCivitaConnection g) X Y Z p) (W p) =
      -g.inner p (curvatureField (Connection.leviCivitaConnection g) X Y W p) (Z p) := by
  simpa [curvature4Field_apply] using
    (curvature4Field_antisymm_last_smoothAt g hX hY hW hZ)

/-- Pair interchange for arbitrary smooth local vector fields.  This combines
the field-level first Bianchi identity with the two metric skew laws. -/
theorem curvature4Field_pair_swap_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p)
    (hZ : SmoothAt Z p) (hW : SmoothAt W p) :
    curvature4Field g X Y Z W p = curvature4Field g Z W X Y p := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfirst : ∀ {A B C D : (x : M) → TangentSpace I x},
      SmoothAt A p → SmoothAt B p → SmoothAt C p → SmoothAt D p →
      curvature4Field g B A C D p = -curvature4Field g A B C D p := by
    intro A B C D hA hB hC hD
    rw [curvature4Field_apply, curvature4Field_apply, curvatureField_swap]
    change inner ℝ (-(curvatureField (Connection.leviCivitaConnection g) A B D p))
        (C p) = _
    exact inner_neg_left _ _
  have hBianchi : ∀ {A B C D : (x : M) → TangentSpace I x},
      SmoothAt A p → SmoothAt B p → SmoothAt C p → SmoothAt D p →
      curvature4Field g A B C D p + curvature4Field g B D C A p +
          curvature4Field g D A C B p = 0 := by
    intro A B C D hA hB hC hD
    rw [curvature4Field_apply, curvature4Field_apply, curvature4Field_apply]
    have h := curvatureField_bianchi_smoothAt g hA hB hD
    have hp := congrArg (fun V => inner ℝ V (C p)) h
    change inner ℝ
        (curvatureField (Connection.leviCivitaConnection g) A B D p) (C p) +
      inner ℝ
        (curvatureField (Connection.leviCivitaConnection g) B D A p) (C p) +
      inner ℝ
        (curvatureField (Connection.leviCivitaConnection g) D A B p) (C p) = 0
    simpa only [inner_add_left, inner_zero_left] using hp
  have eq1 := hBianchi hY hZ hW hX
  have eq2 := hBianchi hZ hX hY hW
  have eq3 := hBianchi hX hW hZ hY
  have eq4 := hBianchi hW hY hX hZ
  have ar1 := curvature4Field_antisymm_last_smoothAt g hY hZ hX hW
  have ar2 := curvature4Field_antisymm_last_smoothAt g hZ hX hY hW
  have ar3 := curvature4Field_antisymm_last_smoothAt g hX hW hZ hY
  have ar4 := curvature4Field_antisymm_last_smoothAt g hW hY hZ hX
  have ar5 := curvature4Field_antisymm_last_smoothAt g hX hY hZ hW
  have ar6 := curvature4Field_antisymm_last_smoothAt g hW hZ hX hY
  have al1 := hfirst hY hX hZ hW
  have al2 := hfirst hW hZ hX hY
  have al3 := hfirst hZ hW hY hX
  linarith [eq1, eq2, eq3, eq4, ar1, ar2, ar3, ar4, ar5, ar6,
    al1, al2, al3]

/-! ### Smooth function-scalar laws

The following local statements record the jet cancellation needed to turn the
field commutator into a pointwise curvature operation.  They are deliberately
stated for smooth local sections: the weaker `TensorialAt` hypotheses in
Mathlib do not provide enough regularity for the nested covariant derivatives
in the present bundled API. -/

/-- A smooth scalar in the first curvature slot factors through its value at
the base point. -/
theorem curvatureField_smul_first_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {f : M → ℝ} {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hf : MDiffAt f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) (f • X) Y W p =
      f p • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  let cov := Connection.leviCivitaConnection g
  letI : cov.ContMDiffCovariantDerivative ∞ := by
    dsimp [cov]
    exact Connection.contMDiff_leviCivitaConnection g
  letI : CompleteSpace EM := FiniteDimensional.complete ℝ EM
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  have hX' : MDiffAt (T% X) p := hX.mdifferentiableAt (by simp)
  have hYW' : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
      (T% (covariantField cov Y W)) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hY hW
  have hXW' : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
      (T% (covariantField cov X W)) p :=
    Connection.contMDiffAt_leviCivitaConnection_apply g hX hW
  have hYW : MDiffAt (T% (covariantField cov Y W)) p :=
    hYW'.mdifferentiableAt (by simp)
  have hXW : MDiffAt (T% (covariantField cov X W)) p :=
    hXW'.mdifferentiableAt (by simp)
  unfold curvatureField
  have hfirst : covariantField cov (f • X) (covariantField cov Y W) p =
      f p • covariantField cov X (covariantField cov Y W) p := by
    unfold covariantField
    change cov (covariantField cov Y W) p (f p • X p) = _
    rw [map_smul]
    rfl
  have hinner : covariantField cov (f • X) W =
      f • covariantField cov X W := by
    funext q
    unfold covariantField
    change cov W q (f q • X q) = f q • cov W q (X q)
    rw [map_smul]
  have hsecond : covariantField cov Y (covariantField cov (f • X) W) p =
      f p • covariantField cov Y (covariantField cov X W) p +
        (d% f p).smulRight (covariantField cov X W p) (Y p) := by
    rw [hinner]
    exact covariantField_smul_argument cov hf hXW
  have hbracket : VectorField.mlieBracket I (f • X) Y p =
      -(d% f p) (Y p) • X p + f p • VectorField.mlieBracket I X Y p := by
    exact VectorField.mlieBracket_smul_left hf hX'
  have hthird : covariantField cov (VectorField.mlieBracket I (f • X) Y) W p =
      -(d% f p) (Y p) • covariantField cov X W p +
        f p • covariantField cov (VectorField.mlieBracket I X Y) W p := by
    unfold covariantField
    rw [hbracket]
    change cov W p (-(d% f p) (Y p) • X p +
      f p • VectorField.mlieBracket I X Y p) = _
    rw [map_add, map_smul, map_smul]
  rw [hfirst, hsecond, hthird]
  simp only [smul_sub, ContinuousLinearMap.smulRight_apply]
  module

/-- A smooth scalar in the second curvature slot factors through its value at
the base point. -/
theorem curvatureField_smul_second_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {f : M → ℝ} {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hf : MDiffAt f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) X (f • Y) W p =
      f p • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  let cov := Connection.leviCivitaConnection g
  have h := curvatureField_smul_first_smoothAt (g := g) (f := f)
    (X := Y) (Y := X) (W := W) hf hY hX hW
  have hs₂ := curvatureField_swap cov X Y W p
  have hs₁' : curvatureField (Connection.leviCivitaConnection g) X (f • Y) W p =
      -curvatureField cov (f • Y) X W p := by
    simpa [cov] using curvatureField_swap cov (f • Y) X W p
  calc
    curvatureField (Connection.leviCivitaConnection g) X (f • Y) W p =
        -curvatureField cov (f • Y) X W p := hs₁'
    _ = -(f p • curvatureField cov Y X W p) := by rw [h]
    _ = -(f p • (-curvatureField cov X Y W p)) := by rw [hs₂]
    _ = f p • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
      module

/-- A smooth scalar in the third curvature slot factors through its value at
the base point.  The proof uses first Bianchi to avoid introducing a second
coordinate curvature facade. -/
theorem curvatureField_smul_third_smoothAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {f : M → ℝ} {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f p)
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) X Y (f • W) p =
      f p • curvatureField (Connection.leviCivitaConnection g) X Y W p := by
  have hfw : SmoothAt (f • W) p := hf.smul_section hW
  have hBf := curvatureField_bianchi_smoothAt g hX hY hfw
  have hB := curvatureField_bianchi_smoothAt g hX hY hW
  have hfirst := curvatureField_smul_first_smoothAt (g := g) (f := f)
    (X := W) (Y := X) (W := Y)
    (hf.mdifferentiableAt (by simp)) hW hX hY
  have hsecond := curvatureField_smul_second_smoothAt (g := g) (f := f)
    (X := Y) (Y := W) (W := X)
    (hf.mdifferentiableAt (by simp)) hY hW hX
  have hsecond' := curvatureField_smul_second_smoothAt (g := g) (f := f)
    (X := X) (Y := W) (W := Y)
    (hf.mdifferentiableAt (by simp)) hX hW hY
  have hswap0 : curvatureField (Connection.leviCivitaConnection g) (f • W)
      X Y p =
      -curvatureField (Connection.leviCivitaConnection g) X (f • W) Y p := by
    simpa using curvatureField_swap (Connection.leviCivitaConnection g)
      X (f • W) Y p
  rw [hsecond, hswap0, hsecond'] at hBf
  have hswapXY := curvatureField_swap (Connection.leviCivitaConnection g) X W Y p
  rw [hswapXY] at hB
  linear_combination (norm := module) hBf - (f p) • hB

/-! ### Smooth pointwise tensoriality

`TensorialAt` in the pinned Mathlib release is intentionally formulated with
only first-order differentiability hypotheses.  The nested curvature
commutator above is currently available at the smooth local regularity needed
by its construction, so this small contract records the corresponding
extension-independent statement without introducing a second tensor-bundle
connection. -/

/-- A smooth-at pointwise tensorial operation on tangent-bundle sections.
Unlike Mathlib's `TensorialAt`, the scalar and section hypotheses are
explicitly `ContMDiffAt` at order `∞`; this is the regularity available for the
bundled curvature commutator in this module. -/
structure SmoothTensorialAt
    {A : Type*} [AddCommGroup A] [Module ℝ A]
    (Φ : ((x : M) → TangentSpace I x) → A) (x : M) : Prop where
  /-- Smooth scalar multiplication factors through the scalar's value at `x`. -/
  smul : ∀ (f : M → ℝ) (σ : (x : M) → TangentSpace I x),
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x →
    SmoothAt σ x →
    Φ (f • σ) = f x • Φ σ
  /-- Smooth section addition is preserved by the operation. -/
  add : ∀ (σ σ' : (x : M) → TangentSpace I x),
    SmoothAt σ x → SmoothAt σ' x →
    Φ (σ + σ') = Φ σ + Φ σ'

namespace SmoothTensorialAt

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

omit [FiniteDimensional ℝ EM] in
/-- A smooth pointwise tensorial operation is local on smooth section germs. -/
protected theorem «local»
    {Φ : ((x : M) → TangentSpace I x) → A} {x : M}
    (hΦ : SmoothTensorialAt Φ x)
    {σ σ' : (x : M) → TangentSpace I x}
    (hσ : SmoothAt σ x) (hσ' : SmoothAt σ' x)
    (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  let ψ (x' : M) : ℝ := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have heq (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ψ x := by
    have hconst : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun (_ : M) => (1 : ℝ)) x :=
      contMDiffAt_const
    exact hconst.congr_of_eventuallyEq
      (hσσ'.mono (fun x' hx' => by simp [ψ, hx']))
  calc
    Φ σ = Φ (ψ • σ) := by rw [hΦ.smul ψ σ hψ hσ, hψx]; simp
    _ = Φ (ψ • σ') := by rw [funext heq]
    _ = Φ σ' := by rw [hΦ.smul ψ σ' hψ hσ', hψx]; simp

omit [FiniteDimensional ℝ EM] in
/-- Finite sums can be expanded using smooth pointwise tensoriality. -/
theorem sum
    {Φ : ((x : M) → TangentSpace I x) → A} {x : M}
    (hΦ : SmoothTensorialAt Φ x) {ι : Type*} {s : Finset ι}
    (τ : ι → (x : M) → TangentSpace I x)
    (hτ : ∀ i ∈ s, SmoothAt (τ i) x) :
    Φ (fun x' ↦ ∑ i ∈ s, τ i x') = ∑ i ∈ s, Φ (τ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have hz : Φ (0 : (x : M) → TangentSpace I x) = 0 := by
        have hzsec : SmoothAt (0 : (x : M) → TangentSpace I x) x := by
          change ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞
            (zeroSection EM (TangentSpace I)) x
          exact contMDiffAt_zeroSection (𝕜 := ℝ)
            (E := (TangentSpace I : M → Type _)) (F := EM)
            (IB := I) (x := x) (n := ∞)
        have h := hΦ.smul (fun _ : M => (0 : ℝ))
          (0 : (x : M) → TangentSpace I x) contMDiffAt_const hzsec
        simpa using h
      exact hz
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hsum : SmoothAt (fun x' ↦ ∑ i ∈ s, τ i x') x := by
        exact ContMDiffAt.sum_section
          (fun i hi => hτ i (Finset.mem_insert_of_mem hi))
      rw [show (fun x' ↦ τ a x' + ∑ i ∈ s, τ i x') =
          τ a + (fun x' ↦ ∑ i ∈ s, τ i x') by rfl]
      rw [hΦ.add _ _ (hτ a (Finset.mem_insert_self _ _)) hsum]
      rw [ih (fun i hi => hτ i (Finset.mem_insert_of_mem hi))]

/-- A smooth pointwise tensorial operation depends only on a section value. -/
theorem pointwise
    {Φ : ((x : M) → TangentSpace I x) → A} {x : M}
    (hΦ : SmoothTensorialAt Φ x)
    {σ σ' : (x : M) → TangentSpace I x}
    (hσ : SmoothAt σ x) (hσ' : SmoothAt σ' x)
    (hσσ' : σ x = σ' x) : Φ σ = Φ σ' := by
  classical
  let t := trivializationAt EM (TangentSpace I) x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt EM
    (TangentSpace I) x
  let b := Basis.ofVectorSpace ℝ EM
  let c := t.localFrame_coeff I b
  let s := t.localFrame b
  have hs (i) : SmoothAt (s i) x := by
    exact contMDiffAt_localFrame_of_mem (I := I) (F := EM)
      (V := (TangentSpace I : M → Type _)) (n := ∞)
      (e := t) (b := b) i x_mem
  have hc {τ : (x : M) → TangentSpace I x} (hτ : SmoothAt τ x) (i) :
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (LinearMap.piApply (c i) τ) x := by
    exact contMDiffAt_localFrame_coeff b x_mem hτ i
  have hΦ_eq {τ : (x : M) → TangentSpace I x} (hτ : SmoothAt τ x) :
      Φ τ = Φ (fun x' ↦ ∑ i, c i x' (τ x') • s i x') := by
    apply hΦ.local hτ
      (.sum_section fun i _ ↦ (hc hτ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  rw [hΦ_eq hσ, hΦ_eq hσ']
  have hsumσ :
      Φ (fun x' ↦ ∑ i, c i x' (σ x') • s i x') =
        ∑ i, Φ ((LinearMap.piApply (c i) σ) • (s i)) := by
    have heq : (fun x' ↦ ∑ i, c i x' (σ x') • s i x') =
        (fun x' ↦ ∑ i, (((LinearMap.piApply (c i) σ) • (s i)) x')) := by
      rfl
    rw [heq]
    exact hΦ.sum (s := Finset.univ)
      (fun i ↦ (LinearMap.piApply (c i) σ) • (s i))
      (fun i hi ↦ (hc hσ i).smul_section (hs i))
  have hsumσ' :
      Φ (fun x' ↦ ∑ i, c i x' (σ' x') • s i x') =
        ∑ i, Φ ((LinearMap.piApply (c i) σ') • (s i)) := by
    have heq : (fun x' ↦ ∑ i, c i x' (σ' x') • s i x') =
        (fun x' ↦ ∑ i, (((LinearMap.piApply (c i) σ') • (s i)) x')) := by
      rfl
    rw [heq]
    exact hΦ.sum (s := Finset.univ)
      (fun i ↦ (LinearMap.piApply (c i) σ') • (s i))
      (fun i hi ↦ (hc hσ' i).smul_section (hs i))
  rw [hsumσ, hsumσ']
  apply Finset.sum_congr rfl
  intro i hi
  calc
    Φ ((LinearMap.piApply (c i) σ) • (s i)) =
        c i x (σ x) • Φ (s i) := hΦ.smul _ _ (hc hσ i) (hs i)
    _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
    _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
      (hΦ.smul _ _ (hc hσ' i) (hs i)).symm

/-! A value-level linear adapter.  This is useful for fixed-slot curvature
operations and keeps the selected extension hidden behind a proved
extension-independence theorem. -/

/-- Evaluate a smooth pointwise tensorial operation on the canonical local
extension, producing a fibrewise linear map. -/
noncomputable def mkLinearMap
    {Φ : ((x : M) → TangentSpace I x) → A} (p : M)
    (hΦ : SmoothTensorialAt Φ p) : TangentSpace I p →ₗ[ℝ] A :=
  { toFun := fun v => Φ (FiberBundle.extend EM v)
    map_add' := by
      intro v w
      have hext : SmoothAt (FiberBundle.extend EM (v + w)) p :=
        FiberBundle.contMDiffAt_extend I EM (v + w)
      have hsum : SmoothAt (FiberBundle.extend EM v + FiberBundle.extend EM w) p :=
        (FiberBundle.contMDiffAt_extend I EM v).add_section
          (FiberBundle.contMDiffAt_extend I EM w)
      have hp := SmoothTensorialAt.pointwise hΦ hext hsum (by simp)
      rw [hp, hΦ.add _ _
        (FiberBundle.contMDiffAt_extend I EM v)
        (FiberBundle.contMDiffAt_extend I EM w)]
    map_smul' := by
      intro c v
      have hext : SmoothAt (FiberBundle.extend EM (c • v)) p :=
        FiberBundle.contMDiffAt_extend I EM (c • v)
      have hsmul : SmoothAt ((fun _ : M => c) • FiberBundle.extend EM v) p :=
        (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) p).smul_section
          (FiberBundle.contMDiffAt_extend I EM v)
      have hp := SmoothTensorialAt.pointwise hΦ hext hsmul (by simp)
      rw [hp, hΦ.smul _ _ contMDiffAt_const
        (FiberBundle.contMDiffAt_extend I EM v)]
      rfl }

/-- The linear adapter agrees with the original operation on every smooth
section at the base point. -/
theorem mkLinearMap_apply
    {Φ : ((x : M) → TangentSpace I x) → A} {p : M}
    (hΦ : SmoothTensorialAt Φ p)
    {σ : (x : M) → TangentSpace I x} (hσ : SmoothAt σ p) :
    mkLinearMap (I := I) (EM := EM) (Φ := Φ) p hΦ (σ p) = Φ σ := by
  apply SmoothTensorialAt.pointwise hΦ
    (FiberBundle.contMDiffAt_extend I EM (σ p)) hσ
  simp

end SmoothTensorialAt

/-! The curvature slots satisfy this smooth tensorial contract. -/

/-- Smooth pointwise tensoriality in the first curvature slot. -/
theorem curvatureField_smoothTensorial_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {Y W : (x : M) → TangentSpace I x} {p : M}
    (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    SmoothTensorialAt
      (fun X => curvatureField (Connection.leviCivitaConnection g) X Y W p) p := by
  constructor
  · intro f X hf hX
    exact curvatureField_smul_first_smoothAt g
      (hf.mdifferentiableAt (by simp)) hX hY hW
  · intro X X' hX hX'
    exact curvatureField_add_left_smoothAt g hX hX' hW

/-- Smooth pointwise tensoriality in the second curvature slot. -/
theorem curvatureField_smoothTensorial_second
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hW : SmoothAt W p) :
    SmoothTensorialAt
      (fun Y => curvatureField (Connection.leviCivitaConnection g) X Y W p) p := by
  constructor
  · intro f Y hf hY
    exact curvatureField_smul_second_smoothAt g
      (hf.mdifferentiableAt (by simp)) hX hY hW
  · intro Y Y' hY hY'
    have hswap0 := curvatureField_swap (Connection.leviCivitaConnection g)
      (Y + Y') X W p
    have hadd := curvatureField_add_left_smoothAt (Z := X) g hY hY' hW
    have hswapY := curvatureField_swap (Connection.leviCivitaConnection g) Y X W p
    have hswapY' := curvatureField_swap (Connection.leviCivitaConnection g) Y' X W p
    rw [hadd] at hswap0
    linear_combination (norm := module) hswap0 - hswapY - hswapY'

/-- Smooth pointwise tensoriality in the third curvature slot. -/
theorem curvatureField_smoothTensorial_third
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X Y : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) :
    SmoothTensorialAt
      (fun W => curvatureField (Connection.leviCivitaConnection g) X Y W p) p := by
  constructor
  · intro f W hf hW
    exact curvatureField_smul_third_smoothAt g hf hX hY hW
  · intro W W' hW hW'
    exact curvatureField_add_right_smoothAt g hX hY hW hW'

/-! ### Smooth extension independence -/

/-- The curvature commutator is independent of the chosen smooth local
extension with fixed values at the base point. -/
theorem curvatureField_eq_provisional
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X Y W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvatureField (Connection.leviCivitaConnection g) X Y W p =
      Provisional.curvature g p (X p) (Y p) (W p) := by
  let X' : (q : M) → TangentSpace I q := FiberBundle.extend EM (X p)
  let Y' : (q : M) → TangentSpace I q := FiberBundle.extend EM (Y p)
  let W' : (q : M) → TangentSpace I q := FiberBundle.extend EM (W p)
  have hX' : SmoothAt X' p := FiberBundle.contMDiffAt_extend I EM (X p)
  have hY' : SmoothAt Y' p := FiberBundle.contMDiffAt_extend I EM (Y p)
  have hW' : SmoothAt W' p := FiberBundle.contMDiffAt_extend I EM (W p)
  have e1 := SmoothTensorialAt.pointwise
    (curvatureField_smoothTensorial_first g hY hW) hX hX' (by simp [X'])
  have e2 := SmoothTensorialAt.pointwise
    (curvatureField_smoothTensorial_second g hX' hW) hY hY' (by simp [Y'])
  have e3 := SmoothTensorialAt.pointwise
    (curvatureField_smoothTensorial_third g hX' hY') hW hW' (by simp [W'])
  rw [e1, e2, e3]
  rfl

/-- The source-ordered four-tensor agrees with the selected extension only as
an evaluation theorem; the field-level definition remains the canonical public
object used by the smooth identities above. -/
theorem curvature4Field_eq_provisional
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X Y Z W : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hY : SmoothAt Y p) (hW : SmoothAt W p) :
    curvature4Field g X Y Z W p =
      Provisional.curvature4 g p (X p) (Y p) (Z p) (W p) := by
  rw [curvature4Field_apply, Provisional.curvature4_def,
    curvatureField_eq_provisional g hX hY hW]

/-- Smooth local extensions with the same three operator values give the same
curvature value at the base point.  This is the intrinsic extension-
independence statement used by the selected-extension compatibility theorem. -/
theorem curvatureField_eq_of_value_eq
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X X' Y Y' W W' : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hX' : SmoothAt X' p)
    (hY : SmoothAt Y p) (hY' : SmoothAt Y' p)
    (hW : SmoothAt W p) (hW' : SmoothAt W' p)
    (hXX' : X p = X' p) (hYY' : Y p = Y' p) (hWW' : W p = W' p) :
    curvatureField (Connection.leviCivitaConnection g) X Y W p =
      curvatureField (Connection.leviCivitaConnection g) X' Y' W' p := by
  calc
    curvatureField (Connection.leviCivitaConnection g) X Y W p =
        Provisional.curvature g p (X p) (Y p) (W p) :=
      curvatureField_eq_provisional g hX hY hW
    _ = Provisional.curvature g p (X' p) (Y' p) (W' p) := by
      rw [hXX', hYY', hWW']
    _ = curvatureField (Connection.leviCivitaConnection g) X' Y' W' p :=
      (curvatureField_eq_provisional g hX' hY' hW').symm

/-- The corresponding extension-independence statement for the source-ordered
metric pairing. -/
theorem curvature4Field_eq_of_value_eq
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM
      (TangentSpace I : M → Type _))
    {X X' Y Y' Z Z' W W' : (x : M) → TangentSpace I x} {p : M}
    (hX : SmoothAt X p) (hX' : SmoothAt X' p)
    (hY : SmoothAt Y p) (hY' : SmoothAt Y' p)
    (hW : SmoothAt W p) (hW' : SmoothAt W' p)
    (hXX' : X p = X' p) (hYY' : Y p = Y' p)
    (hZZ' : Z p = Z' p) (hWW' : W p = W' p) :
    curvature4Field g X Y Z W p = curvature4Field g X' Y' Z' W' p := by
  calc
    curvature4Field g X Y Z W p =
        Provisional.curvature4 g p (X p) (Y p) (Z p) (W p) :=
      curvature4Field_eq_provisional g hX hY hW
    _ = Provisional.curvature4 g p (X' p) (Y' p) (Z' p) (W' p) := by
      rw [hXX', hYY', hZZ', hWW']
    _ = curvature4Field g X' Y' Z' W' p :=
      (curvature4Field_eq_provisional g hX' hY' hW').symm

/-! ### Algebraic consequences -/

/-- Once the metric last-pair skew has been checked, the existing first-pair
skew and first Bianchi laws make the selected pointwise four-tensor an
algebraic curvature form.  This is the bridge consumed by the exterior-square
and plane adapters. -/
theorem provisional_isAlgebraicCurvature
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M)
    (hLast : ∀ x y z w : TangentSpace I p,
      Provisional.curvature4 g p x y z w =
        -Provisional.curvature4 g p x y w z) :
    IsAlgebraicCurvature (fun x y z w => Provisional.curvature4 g p x y z w) := by
  constructor
  · intro x₁ x₂ y z w
    simpa using Provisional.curvature4_add_first g p x₁ x₂ y z w
  · intro c x y z w
    simpa [smul_eq_mul] using Provisional.curvature4_smul_first g p c x y z w
  · intro x y z w
    simpa [neg_neg] using Provisional.curvature4_swap_first g p y x z w
  · intro x y z w
    exact hLast x y z w
  · intro x y z w
    have h := Provisional.curvature4_bianchi g p x y w z
    have h₁ := hLast x y z w
    have h₂ := hLast y z w x
    have h₃ := hLast z x w y
    linarith

namespace Provisional

/-- Metric skew in the final two slots of the selected-extension
source-ordered four-tensor. -/
theorem curvature4_antisymm_last
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y z w : TangentSpace I p) :
    curvature4 g p x y z w = -curvature4 g p x y w z := by
  let X : (q : M) → TangentSpace I q := FiberBundle.extend EM x
  let Y : (q : M) → TangentSpace I q := FiberBundle.extend EM y
  let Z : (q : M) → TangentSpace I q := FiberBundle.extend EM z
  let W : (q : M) → TangentSpace I q := FiberBundle.extend EM w
  have hX : SmoothAt X p := FiberBundle.contMDiffAt_extend I EM x
  have hY : SmoothAt Y p := FiberBundle.contMDiffAt_extend I EM y
  have hZ : SmoothAt Z p := FiberBundle.contMDiffAt_extend I EM z
  have hW : SmoothAt W p := FiberBundle.contMDiffAt_extend I EM w
  have h := curvature4Field_antisymm_last_smoothAt g hX hY hZ hW
  simpa [curvature4, curvature4_def, curvature, curvature4Field,
    X, Y, Z, W] using h

/-- The selected-extension four-tensor satisfies the complete algebraic
curvature contract. -/
theorem curvature4_isAlgebraicCurvature
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) :
    IsAlgebraicCurvature (fun x y z w => curvature4 g p x y z w) := by
  exact provisional_isAlgebraicCurvature g p (curvature4_antisymm_last g p)

/-- Pair interchange in Morgan--Tian's source order. -/
theorem curvature4_pair_swap
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y z w : TangentSpace I p) :
    curvature4 g p x y z w = curvature4 g p z w x y := by
  exact (curvature4_isAlgebraicCurvature g p).pair_swap x y z w

end Provisional

end Symmetries

end Curvature
end Ch01
end MorganTianLib
