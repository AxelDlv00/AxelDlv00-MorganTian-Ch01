/-
Copyright (c) 2026 Axel Dlv. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
-/

import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Finite tensor covariant derivatives and the connection Laplacian

This file supplies the rank-generic evaluation layer used by the Chapter 1
connection consumers. A finite tensor is represented by an evaluation on
vector and covector section arguments. The evaluation type is deliberately
unbundled; `IsPointwiseMultilinear` and `IsPointwiseTensorial` are the
admissibility predicates used when it is turned into a frame-independent fibre
map.

The two derivative directions are kept separate from the tensor slots. The
public order is the one used by Morgan--Tian immediately before `lapformula`
(Chapter 1, pp. 39--40):

`∇² A (X, Y) = ∇_X (∇_Y A) - ∇_{∇_X Y} A`.

The source notes that the two direction slots are generally not symmetric. The
implementation uses Mathlib's bundled `CovariantDerivative` and the exact
`leviCivitaConnection g` exported by `MorganTianLib.Ch01.Connection`; no second
connection or metric is introduced here.

The pinned Mathlib release provides a section-level connection but no induced
connection on arbitrary tensor-product bundles (the Hom/tensor-product
construction is not yet provided by `CovariantDerivative.Metric`). Smoothness,
multilinearity, and tensoriality predicates are therefore explicit in this
module. The raw evaluator definitions accept arbitrary evaluations; the
producer-level regularity and extension-independence theorems below carry the
corresponding hypotheses rather than asserting them by definition. The
`TensorialAt`/`mkHom`/`mkHom₂` lemmas from Mathlib are the fibre-level
interface.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
discussion preceding `lapformula`, pp. 39--40, bibliography key
`morganTian2007`. Mathlib references:
`Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`,
`Geometry.Manifold.VectorBundle.CovariantDerivative.Metric`,
`Geometry.Manifold.VectorBundle.Tensoriality`, and
`Analysis.InnerProductSpace.Trace` (`LinearMap.trace_eq_sum_inner`). The chart
component bridge reuses
`MorganTianLib.Ch01.Connection.christoffel_formula`.
-/

noncomputable section

open Bundle FiberBundle Filter Function Module NormedSpace
open scoped Bundle ContDiff Manifold RealInnerProductSpace Topology

namespace MorganTianLib
namespace Ch01
namespace Connection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section BasicTypes

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- A (not necessarily smooth) section of the tangent bundle. -/
abbrev TangentSection := ∀ x : M, TangentSpace I x

/-- A (not necessarily smooth) cotangent section.  The continuous-linear map
representation makes fibrewise linearity part of the type, while still
leaving the section-level smoothness predicate explicit. -/
abbrev CovectorSection := ∀ x : M, TangentSpace I x →L[ℝ] ℝ

/-- Fibrewise linearity of a cotangent section (a useful named regression
predicate even though it is now built into `CovectorSection`). -/
def IsFiberwiseCovector (θ : CovectorSection (I := I) (M := M)) : Prop :=
  ∀ x, ∀ u v, θ x (u + v) = θ x u + θ x v ∧
    ∀ c, θ x (c • u) = c * θ x u

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
@[simp] theorem isFiberwiseCovector (θ : CovectorSection (I := I) (M := M)) :
    IsFiberwiseCovector θ := by
  intro x u v
  exact ⟨map_add (θ x) u v, fun c => by simp⟩

/-- Smoothness of a tangent section in Mathlib's bundle-section notation. -/
def IsSmoothTangentSection (X : TangentSection (I := I) (M := M)) : Prop :=
  CMDiff ∞ (T% X)

/-- Evaluation-level smoothness test for a covector section. It quantifies
smooth tangent test sections and is not asserted to be equivalent to a
bundled Hom-bundle `ContMDiff` predicate. -/
def IsSmoothCovectorSection (θ : CovectorSection (I := I) (M := M)) : Prop :=
  ∀ Z : TangentSection (I := I) (M := M),
    IsSmoothTangentSection Z → CMDiff ∞ (fun x => θ x (Z x))

/-- A finite mixed tensor evaluation. The first `p` slots are contravariant
slots (fed covectors), and the next `q` slots are covariant slots (fed
vectors). -/
abbrev MixedTensorSection (p q : ℕ) :=
  (Fin p → CovectorSection (I := I) (M := M)) →
    (Fin q → TangentSection (I := I) (M := M)) → M → ℝ

/-- Covariant tensors are the `p = 0` specialization. -/
abbrev CovariantTensorSection (q : ℕ) :=
  MixedTensorSection (I := I) (M := M) 0 q

/-- A one-form in the evaluation representation. -/
abbrev OneFormSection := CovariantTensorSection (I := I) (M := M) 1

/-- A scalar section. -/
abbrev ScalarSection := M → ℝ

/-- Evaluation-level smoothness test on all smooth tensor arguments. The
representation is deliberately weaker than a bundled tensor-product section
until Mathlib supplies that induced bundle connection. -/
def IsSmoothMixedTensorSection {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q) : Prop :=
  ∀ (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)),
    (∀ i, IsSmoothCovectorSection (θ i)) →
    (∀ i, IsSmoothTangentSection (Y i)) →
    CMDiff ∞ (A θ Y)

/-- Pointwise multilinearity in every tensor slot. -/
def IsPointwiseMultilinear {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q) : Prop :=
  ∀ x,
    (∀ (θ θ' : Fin p → CovectorSection (I := I) (M := M))
      (Y : Fin q → TangentSection (I := I) (M := M)) (i : Fin p),
      A (Function.update θ i (θ i + θ' i)) Y x =
        A θ Y x + A (Function.update θ i (θ' i)) Y x) ∧
    (∀ (θ : Fin p → CovectorSection (I := I) (M := M))
      (Y Y' : Fin q → TangentSection (I := I) (M := M)) (i : Fin q),
      A θ (Function.update Y i (Y i + Y' i)) x =
        A θ Y x + A θ (Function.update Y i (Y' i)) x) ∧
    (∀ (c : ℝ) (θ : Fin p → CovectorSection (I := I) (M := M))
      (Y : Fin q → TangentSection (I := I) (M := M)) (i : Fin p),
      A (Function.update θ i (c • θ i)) Y x = c * A θ Y x) ∧
    (∀ (c : ℝ) (θ : Fin p → CovectorSection (I := I) (M := M))
      (Y : Fin q → TangentSection (I := I) (M := M)) (i : Fin q),
      A θ (Function.update Y i (c • Y i)) x = c * A θ Y x)

/-- Pointwise tensoriality in every tensor slot. -/
def IsPointwiseTensorial {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q) : Prop :=
  ∀ x,
    (∀ (f : M → ℝ) (θ : Fin p → CovectorSection (I := I) (M := M))
      (Y : Fin q → TangentSection (I := I) (M := M)) (i : Fin p),
      A (Function.update θ i (f • θ i)) Y x = f x * A θ Y x) ∧
    (∀ (f : M → ℝ) (θ : Fin p → CovectorSection (I := I) (M := M))
      (Y : Fin q → TangentSection (I := I) (M := M)) (i : Fin q),
      A θ (Function.update Y i (f • Y i)) x = f x * A θ Y x)

/-- The hypotheses carried by a smooth finite tensor evaluation.  The raw
`MixedTensorSection` type remains useful for defining operators, while this
predicate is the explicit evaluation-level contract for tensorial/regularity
results.  It is not a bundled tensor-bundle smoothness class: the pinned
Mathlib release does not yet provide induced tensor-product connections. -/
def IsSmoothFiniteTensorSection {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q) : Prop :=
  IsSmoothMixedTensorSection A ∧ IsPointwiseMultilinear A ∧ IsPointwiseTensorial A

/-- A direction-slot evaluation is independent of arbitrary section extensions
when the fibre values agree. This is an intentionally strong, unconditional
contract; the `TensorialAt` adapters below use their weaker differentiability
guarded form. -/
def IsDirectionExtensionIndependent {p q : ℕ}
    (B : (Fin p → CovectorSection (I := I) (M := M)) →
      (Fin q → TangentSection (I := I) (M := M)) →
      TangentSection (I := I) (M := M) →
      TangentSection (I := I) (M := M) → M → ℝ) : Prop :=
  ∀ θ Y x X Z,
    (∀ X', X x = X' x → B θ Y X Z x = B θ Y X' Z x) ∧
    (∀ Z', Z x = Z' x → B θ Y X Z x = B θ Y X Z' x)

/-- Pointwise tensoriality for the two direction slots.  Extension
independence is listed explicitly alongside additivity and scalar laws so a
consumer cannot accidentally use a merely linear-in-sections statement as a
fibre tensor.  The final two clauses are unconditional section-level
function-scalar laws, stronger than the differentiability-guarded premises
used by Mathlib's `TensorialAt`, rather than only constant-scalar linearity. -/
def IsDirectionTensorial {p q : ℕ}
    (B : (Fin p → CovectorSection (I := I) (M := M)) →
      (Fin q → TangentSection (I := I) (M := M)) →
      TangentSection (I := I) (M := M) →
      TangentSection (I := I) (M := M) → M → ℝ) : Prop :=
  IsDirectionExtensionIndependent B ∧
    (∀ θ Y x X X' Z,
      B θ Y (X + X') Z x = B θ Y X Z x + B θ Y X' Z x) ∧
    (∀ θ Y x c X Z,
      B θ Y (c • X) Z x = c * B θ Y X Z x) ∧
    (∀ θ Y x X Z Z',
      B θ Y X (Z + Z') x = B θ Y X Z x + B θ Y X Z' x) ∧
    (∀ θ Y x c X Z,
      B θ Y X (c • Z) x = c * B θ Y X Z x) ∧
    (∀ (θ : Fin p → CovectorSection (I := I) (M := M))
        (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
        (f : ScalarSection (M := M))
        (X Z : TangentSection (I := I) (M := M)),
      B θ Y (f • X) Z x = f x * B θ Y X Z x) ∧
    (∀ (θ : Fin p → CovectorSection (I := I) (M := M))
        (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
        (f : ScalarSection (M := M))
        (X Z : TangentSection (I := I) (M := M)),
      B θ Y X (f • Z) x = f x * B θ Y X Z x)

end BasicTypes

section ConnectionOperations

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The canonical pointwise operation `∇_X Y`, with Mathlib's argument order
`cov Y x (X x)`. The only local instance installed here is the scoped
`Bundle.RiemannianBundle` selected by the explicit metric `g`. -/
noncomputable def covariantVector
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Y : TangentSection (I := I) (M := M)) : TangentSection (I := I) (M := M) :=
  fun x =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    leviCivitaConnection g Y x (X x)

@[simp] theorem covariantVector_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Y : TangentSection (I := I) (M := M)) (x : M) :
    covariantVector g X Y x =
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      leviCivitaConnection g Y x (X x) := rfl

/-- Leibniz rule in the tensor argument of the covariant direction action.
This is the cancellation term needed when the second direction is multiplied
by a function. -/
theorem covariantVector_smul_argument_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M))
    (X Z : TangentSection (I := I) (M := M)) (x : M)
    (hZ : IsSmoothTangentSection Z) (hf : MDiffAt f x) :
    covariantVector g X (f • Z) x =
      f x • covariantVector g X Z x +
        d% f x (X x) • Z x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := (leviCivitaConnection g).isCovariantDerivativeOn.leibniz
    (hZ.mdifferentiableAt (by simp)) hf (x := x)
  have h' := congrArg (fun L => L (X x)) h
  simpa [covariantVector, ContinuousLinearMap.smulRight_apply] using h'

/-- The metric-dual tangent section associated to a cotangent section. -/
noncomputable def metricDualSection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (θ : CovectorSection (I := I) (M := M)) :
    TangentSection (I := I) (M := M) :=
  fun x =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
    (InnerProductSpace.toDual ℝ (TangentSpace I x)).symm (θ x)

/-- The dual connection used in contravariant slots.  It is defined through
the Riesz/metric-dual equivalence and the exact bundled Levi--Civita
connection, so the result is a genuine fibrewise continuous linear map rather
than an extension-dependent raw function. -/
noncomputable def dualCovariantVector
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
  (θ : CovectorSection (I := I) (M := M)) :
    CovectorSection (I := I) (M := M) :=
  fun (x : M) =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    letI : CompleteSpace (TangentSpace I x) := FiniteDimensional.complete ℝ _
    (InnerProductSpace.toDual ℝ (TangentSpace I x))
      (leviCivitaConnection g (metricDualSection g θ) x (X x))

/-- Directional differentiation of a scalar section along a tangent section. -/
def directionalDerivative (X : TangentSection (I := I) (M := M))
    (f : ScalarSection (M := M)) (x : M) : ℝ := d% f x (X x)

/-- Metric-compatibility expansion of the contravariant correction.  Under the
explicit smoothness hypothesis on the metric-dual section, this is the usual
dual-connection formula; it is the bridge from the `+Γ` slot comment in the
evaluation definition to the bundled Levi--Civita API. -/
theorem dualCovariantVector_apply_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M))
    (Z : TangentSection (I := I) (M := M)) (x : M)
    (hdual : IsSmoothTangentSection (metricDualSection g θ))
    (hZ : IsSmoothTangentSection Z) :
    dualCovariantVector g X θ x (Z x) =
      directionalDerivative X (fun y => θ y (Z y)) x -
        θ x (covariantVector g X Z x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) :=
    FiniteDimensional.complete ℝ (TangentSpace I x)
  have hmetric :
      (leviCivitaConnection g).IsMetricCompatible (M := M)
        (V := TangentSpace I) := by
    exact isMetricCompatible_leviCivitaConnection g
  have hdual' : MDiffAt (T% (metricDualSection g θ)) x :=
    hdual.mdifferentiableAt (by simp)
  have hZ' : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  have hcompat := hmetric.mvfderiv_inner_eq (x := x) X hdual' hZ'
  have heval :
      (fun y => inner ℝ (metricDualSection g θ y) (Z y)) =
        (fun y => θ y (Z y)) := by
    funext y
    simp [metricDualSection]
  rw [heval] at hcompat
  have hcompat' :
      d% (fun y => θ y (Z y)) x (X x) =
        inner ℝ (leviCivitaConnection g (metricDualSection g θ) x (X x)) (Z x) +
          inner ℝ (metricDualSection g θ x)
            (leviCivitaConnection g Z x (X x)) := by
    simpa [heval] using hcompat
  change
    ((InnerProductSpace.toDual ℝ (TangentSpace I x))
      (leviCivitaConnection g (metricDualSection g θ) x (X x))) (Z x) = _
  rw [InnerProductSpace.toDual_apply_apply]
  have htheta :
      θ x (covariantVector g X Z x) =
        inner ℝ (metricDualSection g θ x)
          (leviCivitaConnection g Z x (X x)) := by
    simp [metricDualSection, covariantVector]
  rw [directionalDerivative, htheta]
  linear_combination -hcompat'

/-- Function-scalar Leibniz rule for the dual connection, stated on a smooth
tangent test section.  This is the contravariant counterpart of
`covariantVector_smul_argument_at`; together they expose the cancellation
needed for tensoriality in the second derivative directions. -/
theorem dualCovariantVector_smul_argument_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M))
    (X : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M))
    (Z : TangentSection (I := I) (M := M)) (x : M)
    (hf : MDiffAt f x)
    (hθZ : MDiffAt (fun y => θ y (Z y)) x)
    (hdual : IsSmoothTangentSection (metricDualSection g θ))
    (hdual_f : IsSmoothTangentSection (metricDualSection g (f • θ)))
    (hZ : IsSmoothTangentSection Z) :
    dualCovariantVector g X (f • θ) x (Z x) =
      d% f x (X x) * θ x (Z x) +
        f x * dualCovariantVector g X θ x (Z x) := by
  have hθ' := dualCovariantVector_apply_formula g X θ Z x hdual hZ
  have hθf' := dualCovariantVector_apply_formula g X (f • θ) Z x hdual_f hZ
  have hprod := congrArg (fun L => L (X x)) (mvfderiv_fun_mul hf hθZ)
  rw [hθf']
  have hfun : (fun y => (f • θ) y (Z y)) =
      (fun y => f y * θ y (Z y)) := by
    funext y
    simp
  rw [hfun]
  simp only [directionalDerivative]
  rw [hprod]
  rw [hθ']
  have htheta_f :
      (f • θ) x (covariantVector g X Z x) =
        f x * θ x (covariantVector g X Z x) := by
    simp
  rw [htheta_f]
  simp only [add_apply, smul_apply, smul_eq_mul, directionalDerivative]
  ring

/-- Raw evaluation of the covariant derivative of a mixed tensor along one
direction. Every tensor argument is corrected with a minus sign in the
evaluation formula; after passing to genuine tensor components, the dual
(contravariant) slots therefore carry `+Γ` and the vector (covariant) slots
carry `-Γ`. The evaluation-level tensoriality hypotheses are intentionally
kept separate from this definition. -/
noncomputable def mixedCovariantDerivativeAlong {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q) :
    MixedTensorSection (I := I) (M := M) p q :=
  fun θ Y x =>
    directionalDerivative X (A θ Y) x
      - ∑ i, A (Function.update θ i (dualCovariantVector g X (θ i))) Y x
      - ∑ i, A θ (Function.update Y i (covariantVector g X (Y i))) x

/-- Full first covariant derivative, with its direction slot last. -/
noncomputable def mixedCovariantDerivative {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q) :
    MixedTensorSection (I := I) (M := M) p (q + 1) :=
  fun θ Y x =>
    mixedCovariantDerivativeAlong g (Y (Fin.last q)) A θ
      (fun i => Y (Fin.castSucc i)) x

/-- The source-order second covariant derivative. Tensor slots come first,
followed by the two derivative directions, so swapping the directions is
visible and is not hidden by a `Fin.cons` convention. -/
noncomputable def secondCovariantDerivativeEval {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M)) : M → ℝ :=
  mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z A)
      θ Y -
    mixedCovariantDerivativeAlong g (covariantVector g X Z) A θ Y

@[simp] theorem secondCovariantDerivativeEval_apply {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M)) (x : M) :
    secondCovariantDerivativeEval g A θ Y X Z x =
      mixedCovariantDerivativeAlong g X
          (mixedCovariantDerivativeAlong g Z A) θ Y x -
        mixedCovariantDerivativeAlong g (covariantVector g X Z) A θ Y x :=
  rfl

/-! The rank-preserving evaluator is obtained by reserving the last two slots
for the derivative directions. It is a raw section; the regularity and
tensoriality obligations are explicit hypotheses in the theorems below. -/

/-- The full second covariant derivative, with the two direction slots kept
distinct from the original tensor slots. The appended slots are ordered
`(X, Z)`: `Fin.castSucc (Fin.last q)` is the outer direction `X`, and
`Fin.last (q + 1)` is the inner direction `Z`, matching
`secondCovariantDerivativeEval g A ... X Z`. -/
noncomputable def secondCovariantDerivative {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q) :
    MixedTensorSection (I := I) (M := M) p (q + 2) :=
  fun θ Y x =>
    secondCovariantDerivativeEval g A θ
      (fun i => Y (Fin.castSucc (Fin.castSucc i)))
      (Y (Fin.castSucc (Fin.last q)))
      (Y (Fin.last (q + 1))) x

@[simp] theorem secondCovariantDerivative_apply {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin (q + 2) → TangentSection (I := I) (M := M)) (x : M) :
    secondCovariantDerivative g A θ Y x =
      secondCovariantDerivativeEval g A θ
        (fun i => Y (Fin.castSucc (Fin.castSucc i)))
        (Y (Fin.castSucc (Fin.last q)))
        (Y (Fin.last (q + 1))) x :=
  rfl

end ConnectionOperations

section CovariantSpecialization

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The unique empty family of contravariant arguments. -/
def emptyCovectorArgs : Fin 0 → CovectorSection (I := I) (M := M) :=
  Fin.elim0

/-- The unique empty family of tangent arguments. -/
def emptyTangentArgs : Fin 0 → TangentSection (I := I) (M := M) :=
  Fin.elim0

/-- Covariant-tensor specialization of `mixedCovariantDerivativeAlong`. -/
noncomputable def covariantDerivativeAlong {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (Y : Fin q → TangentSection (I := I) (M := M)) : M → ℝ :=
  mixedCovariantDerivativeAlong g X A emptyCovectorArgs Y

/-- The covariant-tensor formula with tensor argument slots displayed. -/
theorem covariantDerivativeAlong_apply {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    covariantDerivativeAlong g X A Y x =
      directionalDerivative X (A emptyCovectorArgs Y) x
        - ∑ i, A emptyCovectorArgs
          (Function.update Y i (covariantVector g X (Y i))) x := by
  simp [covariantDerivativeAlong, mixedCovariantDerivativeAlong,
    directionalDerivative]

/-- Full first derivative of a covariant tensor. The new direction is the
last slot, matching the source order used by `secondCovariantDerivative`. -/
noncomputable def covariantDerivative {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : CovariantTensorSection (I := I) (M := M) q) :
    CovariantTensorSection (I := I) (M := M) (q + 1) :=
  fun _ Y x => covariantDerivativeAlong g (Y (Fin.last q)) A
    (fun i => Y (Fin.castSucc i)) x

@[simp] theorem covariantDerivative_apply {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (Y : Fin (q + 1) → TangentSection (I := I) (M := M)) (x : M) :
    covariantDerivative g A emptyCovectorArgs Y x =
      covariantDerivativeAlong g (Y (Fin.last q)) A
        (fun i => Y (Fin.castSucc i)) x :=
  rfl

/-- The corrected second derivative in the covariant-only representation. -/
noncomputable def secondCovariantDerivativeCovariant {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M)) : M → ℝ :=
  secondCovariantDerivativeEval g A emptyCovectorArgs Y X Z

/-- Embed a scalar section as a rank-zero covariant tensor. -/
def scalarTensor (f : ScalarSection (M := M)) :
    CovariantTensorSection (I := I) (M := M) 0 :=
  fun _ _ => f

@[simp] theorem secondCovariantDerivativeCovariant_rank_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X Z : TangentSection (I := I) (M := M)) :
    secondCovariantDerivativeCovariant g (scalarTensor f) emptyTangentArgs X Z =
      fun x =>
        directionalDerivative X (fun y => directionalDerivative Z f y) x
          - directionalDerivative (covariantVector g X Z) f x := by
  funext x
  have hfirst :
      mixedCovariantDerivativeAlong g Z (scalarTensor f)
          = scalarTensor (fun y => directionalDerivative Z f y) := by
    funext theta Y y
    simp [mixedCovariantDerivativeAlong, scalarTensor, directionalDerivative]
  unfold secondCovariantDerivativeCovariant secondCovariantDerivativeEval
  have hsecond := congrArg
    (fun F : CovariantTensorSection (I := I) (M := M) 0 =>
      mixedCovariantDerivativeAlong g X F emptyCovectorArgs emptyTangentArgs x) hfirst
  change mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z (scalarTensor f))
      emptyCovectorArgs emptyTangentArgs x -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) (scalarTensor f)
        emptyCovectorArgs emptyTangentArgs x = _
  rw [hsecond]
  simp [mixedCovariantDerivativeAlong, scalarTensor, directionalDerivative]

@[simp] theorem secondCovariantDerivativeCovariant_constant
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (X Z : TangentSection (I := I) (M := M)) :
    secondCovariantDerivativeCovariant g (scalarTensor (fun _ => c))
      emptyTangentArgs X Z = 0 := by
  funext x
  rw [secondCovariantDerivativeCovariant_rank_zero]
  simp [directionalDerivative, mvfderiv_const]

/-- Rank one is the canonical one-form adapter. -/
noncomputable def secondCovariantDerivativeOneForm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (omega : OneFormSection (I := I) (M := M))
    (Y : Fin 1 → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M)) : M → ℝ :=
  secondCovariantDerivativeCovariant g omega Y X Z

/-- Rank-one adapter for the full `(q+2)`-slot section. -/
noncomputable def secondCovariantDerivativeOneFormSection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (omega : OneFormSection (I := I) (M := M)) :
    CovariantTensorSection (I := I) (M := M) 3 :=
  secondCovariantDerivative g omega

/-- Rank-zero adapter for the full second-derivative section. -/
noncomputable def secondCovariantDerivativeScalarSection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) :
    CovariantTensorSection (I := I) (M := M) 2 :=
  secondCovariantDerivative g (scalarTensor f)

end CovariantSpecialization

section Laplacian

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-! The trace is first defined on fixed tensor arguments, then lifted to a
rank-preserving raw evaluator.  Its basis independence is exposed separately
through the finite-dimensional trace API and tensoriality hypotheses. -/

/-- Raw metric trace of the source-ordered second derivative over the two
direction slots at fixed tensor arguments. For an arbitrary evaluation `A`,
the chosen extension/frame sum is only a provisional evaluator; the
conditional trace theorem below records the hypotheses that make it intrinsic. -/
noncomputable def connectionLaplacianEval {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) : M → ℝ :=
  fun x =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    ∑ i : Fin (finrank ℝ (TangentSpace I x)),
      secondCovariantDerivativeEval g A θ Y
        (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
          (stdOrthonormalBasis ℝ (TangentSpace I x) i) y)
      (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
          (stdOrthonormalBasis ℝ (TangentSpace I x) i) y) x

/-- Raw rank-preserving connection-Laplacian evaluator. It becomes a
frame-independent tensor contraction only under the explicit regularity and
direction-slot tensoriality hypotheses below. -/
noncomputable def connectionLaplacian {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q) :
    MixedTensorSection (I := I) (M := M) p q :=
  fun θ Y => connectionLaplacianEval g A θ Y

/-- The endomorphism obtained from a continuous bilinear form by the metric
Riesz identification.  This is the fibre map whose trace is the contraction
of the two direction slots. -/
noncomputable def bilinearTraceOperator {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (H : V →L[ℝ] V →L[ℝ] ℝ) : V →ₗ[ℝ] V := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  exact
    { toFun := fun u =>
        (InnerProductSpace.toDual ℝ V).symm (H u)
      map_add' := by
        intro u v
        simp
      map_smul' := by
        intro c u
        simp }

@[simp] theorem inner_bilinearTraceOperator {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (H : V →L[ℝ] V →L[ℝ] ℝ) (u v : V) :
    inner ℝ (bilinearTraceOperator H u) v = H u v := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  exact InnerProductSpace.toDual_symm_apply

/-- The diagonal contraction of a continuous bilinear form is its trace in
any finite orthonormal basis.  This is the frame-independent core used by
`connectionLaplacian_eq_trace_of_tensorial`; the proof is exactly the pinned
Mathlib `LinearMap.trace_eq_sum_inner` theorem. -/
theorem diagonal_bilinear_sum_eq_trace {V ι : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι]
    (H : V →L[ℝ] V →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ V) :
    ∑ i, H (b i) (b i) =
      LinearMap.trace ℝ V (bilinearTraceOperator H) := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  rw [LinearMap.trace_eq_sum_inner (bilinearTraceOperator H) b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← real_inner_comm, inner_bilinearTraceOperator]

/-- Two orthonormal frames give the same diagonal contraction. -/
theorem diagonal_bilinear_sum_eq_diagonal_bilinear_sum {V ι κ : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] [Fintype κ]
    (H : V →L[ℝ] V →L[ℝ] ℝ)
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis κ ℝ V) :
    (∑ i, H (b i) (b i)) = ∑ j, H (c j) (c j) := by
  rw [diagonal_bilinear_sum_eq_trace H b,
    diagonal_bilinear_sum_eq_trace H c]

/-- The defining orthonormal-frame expansion of `connectionLaplacian`. -/
theorem connectionLaplacian_apply {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    connectionLaplacian g A θ Y x =
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
      ∑ i : Fin (finrank ℝ (TangentSpace I x)),
        secondCovariantDerivativeEval g A θ Y
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
            (stdOrthonormalBasis ℝ (TangentSpace I x) i) y)
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
            (stdOrthonormalBasis ℝ (TangentSpace I x) i) y) x := by
  rfl

/-- Additivity of the metric trace, conditional on additivity of the
source-ordered second-derivative evaluator.  The condition is deliberately
quantified over all tensor and direction arguments so it is strong enough to
rewrite every frame summand, including the correction-slot evaluations. -/
theorem connectionLaplacianEval_add_of_second_add {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A A' : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hsecond : ∀ θ' Y' X Z y,
      secondCovariantDerivativeEval g (A + A') θ' Y' X Z y =
        secondCovariantDerivativeEval g A θ' Y' X Z y +
          secondCovariantDerivativeEval g A' θ' Y' X Z y) :
    connectionLaplacianEval g (A + A') θ Y x =
      connectionLaplacianEval g A θ Y x +
        connectionLaplacianEval g A' θ Y x := by
  classical
  unfold connectionLaplacianEval
  simp_rw [hsecond]
  rw [Finset.sum_add_distrib]

/-- Constant-scalar linearity of the metric trace, conditional on the
corresponding second-derivative evaluator law. -/
theorem connectionLaplacianEval_smul_of_second_smul {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hsecond : ∀ θ' Y' X Z y,
      secondCovariantDerivativeEval g (c • A) θ' Y' X Z y =
        c * secondCovariantDerivativeEval g A θ' Y' X Z y) :
    connectionLaplacianEval g (c • A) θ Y x =
      c * connectionLaplacianEval g A θ Y x := by
  classical
  unfold connectionLaplacianEval
  simp_rw [hsecond]
  rw [← Finset.mul_sum]

@[simp] theorem connectionLaplacianEval_eq_zero_of_finrank_eq_zero {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (h : finrank ℝ (TangentSpace I x) = 0) :
    connectionLaplacianEval g A θ Y x = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : IsEmpty (Fin (finrank ℝ (TangentSpace I x))) := by
    rw [h]
    infer_instance
  simp [connectionLaplacianEval]

@[simp] theorem connectionLaplacianEval_eq_single_of_finrank_eq_one {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (h : finrank ℝ (TangentSpace I x) = 1) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    connectionLaplacianEval g A θ Y x =
      secondCovariantDerivativeEval g A θ Y
        (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
          (stdOrthonormalBasis ℝ (TangentSpace I x)
            (Fin.cast h.symm (0 : Fin 1))) y)
        (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
          (stdOrthonormalBasis ℝ (TangentSpace I x)
            (Fin.cast h.symm (0 : Fin 1))) y) x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  let i0 : Fin (finrank ℝ (TangentSpace I x)) :=
    Fin.cast h.symm (0 : Fin 1)
  letI : Unique (Fin (finrank ℝ (TangentSpace I x))) :=
    { default := i0
      uniq := by
        intro i
        apply Fin.ext
        have hi : i.val < 1 := by simpa [h] using i.isLt
        have hi0 : i.val = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by simpa using hi))
        simp [i0, hi0] }
  unfold connectionLaplacianEval
  rw [Fintype.sum_unique]
  rfl

/-! A scalar constant is a useful sign and trace-normalization regression: the
source Laplacian annihilates it in every fibre dimension, including the empty
orthonormal frame. -/
@[simp] theorem connectionLaplacianEval_scalar_constant {c : ℝ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) :
    connectionLaplacianEval g (scalarTensor (fun _ : M => c))
      emptyCovectorArgs emptyTangentArgs x = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  unfold connectionLaplacianEval
  apply Finset.sum_eq_zero
  intro i hi
  have h := secondCovariantDerivativeCovariant_constant g c
    (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
      (stdOrthonormalBasis ℝ (TangentSpace I x) i) y)
    (fun y => FiberBundle.extend (F := E) (E := TangentSpace I)
      (stdOrthonormalBasis ℝ (TangentSpace I x) i) y)
  exact congrFun h x

/-- Scalar specialization of the rank-preserving connection Laplacian. -/
noncomputable def connectionLaplacianScalar
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) : ScalarSection (M := M) :=
  connectionLaplacian g (scalarTensor f) emptyCovectorArgs emptyTangentArgs

/-- One-form specialization of the rank-preserving connection Laplacian. -/
noncomputable def connectionLaplacianOneForm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (omega : OneFormSection (I := I) (M := M)) :
    OneFormSection (I := I) (M := M) :=
  connectionLaplacian g omega

@[simp] theorem connectionLaplacianScalar_constant {c : ℝ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) :
    connectionLaplacianScalar g (fun _ : M => c) x = 0 := by
  exact connectionLaplacianEval_scalar_constant g x

/-- Basis-independent trace form of the connection Laplacian. The supplied
endomorphism `B` is the fibre map represented by the two direction slots; the
equality is exactly Mathlib's finite-dimensional trace theorem. -/
theorem connectionLaplacian_eq_trace {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hB : ∀ u v,
      g.inner x (B u) v =
        secondCovariantDerivativeEval g A θ Y
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) u y)
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) v y) x) :
    connectionLaplacian g A θ Y x = LinearMap.trace ℝ (TangentSpace I x) B := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  rw [LinearMap.trace_eq_sum_inner B (stdOrthonormalBasis ℝ (TangentSpace I x))]
  simp only [connectionLaplacian, connectionLaplacianEval]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← real_inner_comm]
  exact (hB _ _).symm

/-- The same contraction may be read in any finite orthonormal frame.  The
`letI` in the frame binder makes the tangent-fibre metric selected by `g`
explicit, so this theorem cannot silently use a competing bundle metric. -/
theorem connectionLaplacian_eq_sum_of_orthonormal_basis {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    {ι : Type*} [Fintype ι]
    (b : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
      letI : FiniteDimensional ℝ (TangentSpace I x) :=
        VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
      OrthonormalBasis ι ℝ (TangentSpace I x))
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x)
    (hB : ∀ u v,
      g.inner x (B u) v =
        secondCovariantDerivativeEval g A θ Y
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) u y)
          (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) v y) x) :
    connectionLaplacian g A θ Y x =
      ∑ i, secondCovariantDerivativeEval g A θ Y
        (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) (b i) y)
        (fun y => FiberBundle.extend (F := E) (E := TangentSpace I) (b i) y) x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  rw [connectionLaplacian_eq_trace g A θ Y x B hB,
    LinearMap.trace_eq_sum_inner B b]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← real_inner_comm]
  change g.inner x (B (b i)) (b i) = _
  exact hB _ _

end Laplacian

section RegularityAndTensoriality

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- A compact hypothesis spelling out the regularity needed for an iterated
evaluation. It is intentionally a predicate on scalar evaluations, rather
than a false claim that Mathlib already carries an induced tensor connection. -/
def IsSmoothSecondCovariantDerivative {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q) : Prop :=
  ∀ (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M)),
    (∀ i, IsSmoothCovectorSection (θ i)) →
    (∀ i, IsSmoothTangentSection (Y i)) →
    IsSmoothTangentSection X → IsSmoothTangentSection Z →
    CMDiff ∞ (secondCovariantDerivativeEval g A θ Y X Z)

/-- The regularity projection for the second derivative. -/
theorem secondCovariantDerivative_contMDiff {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (hA : IsSmoothSecondCovariantDerivative g A)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X Z : TangentSection (I := I) (M := M))
    (hθ : ∀ i, IsSmoothCovectorSection (θ i))
    (hY : ∀ i, IsSmoothTangentSection (Y i))
    (hX : IsSmoothTangentSection X) (hZ : IsSmoothTangentSection Z) :
    CMDiff ∞ (secondCovariantDerivativeEval g A θ Y X Z) :=
  hA θ Y X Z hθ hY hX hZ

/-- The two-direction evaluation used by `TensorialAt.mkHom₂`. -/
def secondDirectionEvaluation {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (X Z : TangentSection (I := I) (M := M)) : ℝ :=
  secondCovariantDerivativeEval g A θ Y X Z x

omit [FiniteDimensional ℝ E] in
/-- Convert the explicit direction-slot contract into Mathlib's left-slot
`TensorialAt` witness. The extension-independence clause is retained in the
contract for section-level consumers; `TensorialAt` itself records the fibre
additivity and function-scalar law. -/
theorem isDirectionTensorial_tensorialAt_left {p q : ℕ}
    (B : (Fin p → CovectorSection (I := I) (M := M)) →
      (Fin q → TangentSection (I := I) (M := M)) →
      TangentSection (I := I) (M := M) →
      TangentSection (I := I) (M := M) → M → ℝ)
    (hB : IsDirectionTensorial B)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (Z : TangentSection (I := I) (M := M)) {x : M} :
    TensorialAt I E (fun X => B θ Y X Z x) x := by
  rcases hB with ⟨hExt, hAddX, hSmulX, hAddZ, hSmulZ, hFunX, hFunZ⟩
  refine { smul := ?_, add := ?_ }
  · intro f X hf hX
    exact hFunX θ Y x f X Z
  · intro X X' hX hX'
    exact hAddX θ Y x X X' Z

omit [FiniteDimensional ℝ E] in
/-- Right-slot counterpart of `isDirectionTensorial_tensorialAt_left`. -/
theorem isDirectionTensorial_tensorialAt_right {p q : ℕ}
    (B : (Fin p → CovectorSection (I := I) (M := M)) →
      (Fin q → TangentSection (I := I) (M := M)) →
      TangentSection (I := I) (M := M) →
      TangentSection (I := I) (M := M) → M → ℝ)
    (hB : IsDirectionTensorial B)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X : TangentSection (I := I) (M := M)) {x : M} :
    TensorialAt I E (fun Z => B θ Y X Z x) x := by
  rcases hB with ⟨hExt, hAddX, hSmulX, hAddZ, hSmulZ, hFunX, hFunZ⟩
  refine { smul := ?_, add := ?_ }
  · intro f Z hf hZ
    exact hFunZ θ Y x f X Z
  · intro Z Z' hZ hZ'
    exact hAddZ θ Y x X Z Z'

/-- Extension independence in both direction slots. The hypotheses are exactly
Mathlib's `TensorialAt` hypotheses, and the conclusion is obtained from its
pointwise₂ theorem. -/
theorem secondCovariantDerivative_pointwise {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hleft : ∀ Z, MDiffAt (T% Z) x →
      TensorialAt I E (fun X => secondDirectionEvaluation g A θ Y x X Z) x)
    (hright : ∀ X, MDiffAt (T% X) x →
      TensorialAt I E (fun Z => secondDirectionEvaluation g A θ Y x X Z) x)
    {X X' Z Z' : TangentSection (I := I) (M := M)}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hXX' : X x = X' x) (hZZ' : Z x = Z' x) :
    secondCovariantDerivativeEval g A θ Y X Z x =
      secondCovariantDerivativeEval g A θ Y X' Z' x := by
  exact TensorialAt.pointwise₂ hleft hright hX hX' hZ hZ' hXX' hZZ'

/-- The fibre bilinear map associated with tensorial direction slots. -/
noncomputable def secondDirectionHom₂ {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hleft : ∀ Z, MDiffAt (T% Z) x →
      TensorialAt I E (fun X => secondDirectionEvaluation g A θ Y x X Z) x)
    (hright : ∀ X, MDiffAt (T% X) x →
      TensorialAt I E (fun Z => secondDirectionEvaluation g A θ Y x X Z) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom₂ (fun X Z => secondDirectionEvaluation g A θ Y x X Z) x
    (fun Z hZ => hleft Z hZ) (fun X hX => hright X hX)

/-- Once the two direction-slot tensoriality obligations are discharged, the
metric trace is produced by the Riesz endomorphism of the resulting bilinear
form.  Under these explicit obligations the basis sum in
`connectionLaplacian` is a genuine trace, not a choice-dependent definition. -/
theorem connectionLaplacian_eq_trace_of_tensorial {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hleft : ∀ Z, MDiffAt (T% Z) x →
      TensorialAt I E (fun X => secondDirectionEvaluation g A θ Y x X Z) x)
    (hright : ∀ X, MDiffAt (T% X) x →
      TensorialAt I E (fun Z => secondDirectionEvaluation g A θ Y x X Z) x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    letI : CompleteSpace (TangentSpace I x) :=
      FiniteDimensional.complete ℝ (TangentSpace I x)
    connectionLaplacian g A θ Y x =
      LinearMap.trace ℝ (TangentSpace I x)
        (bilinearTraceOperator (V := TangentSpace I x)
          (secondDirectionHom₂ (x := x) g A θ Y hleft hright)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) :=
    FiniteDimensional.complete ℝ (TangentSpace I x)
  apply connectionLaplacian_eq_trace g A θ Y x
    (bilinearTraceOperator (V := TangentSpace I x)
      (secondDirectionHom₂ (x := x) g A θ Y hleft hright))
  intro u v
  change inner ℝ
      (bilinearTraceOperator
        (V := TangentSpace I x)
        (secondDirectionHom₂ (x := x) g A θ Y hleft hright) u) v = _
  rw [inner_bilinearTraceOperator]
  unfold secondDirectionHom₂
  rw [TensorialAt.mkHom₂_apply_eq_extend]
  rfl

end RegularityAndTensoriality

section AlgebraicLaws

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
@[simp] theorem directionalDerivative_zero
    (X : TangentSection (I := I) (M := M))
    (x : M) : directionalDerivative X 0 x = 0 := by
  simp [directionalDerivative]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
@[simp] theorem directionalDerivative_neg
    (X : TangentSection (I := I) (M := M)) (f : ScalarSection (M := M))
    (x : M) : directionalDerivative X (-f) x = -directionalDerivative X f x := by
  simp [directionalDerivative]

/-- Additivity of `∇_X Y` in the direction field at a point. -/
theorem covariantVector_add_direction_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X X' Y : TangentSection (I := I) (M := M)) (x : M) :
    covariantVector g (X + X') Y x =
      covariantVector g X Y x + covariantVector g X' Y x := by
  simp [covariantVector]

/-- Function-scalar linearity of `∇_X Y` in the direction field. -/
theorem covariantVector_smul_direction_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X Y : TangentSection (I := I) (M := M))
    (x : M) :
    covariantVector g (f • X) Y x = f x • covariantVector g X Y x := by
  simp [covariantVector]

/-- Additivity of the metric-dual connection in its direction field. -/
theorem dualCovariantVector_add_direction_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X X' : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M)) (x : M) :
    dualCovariantVector g (X + X') θ x =
      dualCovariantVector g X θ x + dualCovariantVector g X' θ x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) :=
    FiniteDimensional.complete ℝ (TangentSpace I x)
  ext v
  change
    ((InnerProductSpace.toDual ℝ (TangentSpace I x))
      ((leviCivitaConnection g (metricDualSection g θ) x) (X x + X' x))) v = _
  simp only [map_add]
  rfl

/-- Function-scalar linearity of the metric-dual connection in its direction
field. -/
theorem dualCovariantVector_smul_direction_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M)) (x : M) :
    dualCovariantVector g (f • X) θ x =
      f x • dualCovariantVector g X θ x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  letI : CompleteSpace (TangentSpace I x) :=
    FiniteDimensional.complete ℝ (TangentSpace I x)
  ext v
  change
    ((InnerProductSpace.toDual ℝ (TangentSpace I x))
      ((leviCivitaConnection g (metricDualSection g θ) x) (f x • X x))) v = _
  simp only [map_smul]
  rfl

/-- Evaluation-sign expansion of the mixed derivative. The two sums are kept
separate so the contravariant and covariant correction signs remain visible. -/
theorem mixedCovariantDerivativeAlong_component_formula {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    mixedCovariantDerivativeAlong g X A θ Y x =
      directionalDerivative X (A θ Y) x
        + (-∑ i, A (Function.update θ i (dualCovariantVector g X (θ i))) Y x)
        + (-∑ i, A θ (Function.update Y i (covariantVector g X (Y i))) x) := by
  simp [mixedCovariantDerivativeAlong]
  ring

/-! The identity evaluation is a small rank-one sign regression.  Its
covariant derivative vanishes because the metric-dual correction and the
vector-slot correction are the two terms in
`dualCovariantVector_apply_formula`. -/

/-- The raw evaluation of the identity endomorphism as a `(1,1)` tensor. -/
def identityTensorSection : MixedTensorSection (I := I) (M := M) 1 1 :=
  fun θ Y x => θ 0 x (Y 0 x)

/-- The identity evaluation is parallel for the raw mixed derivative, under
the smoothness hypotheses needed by the metric-dual compatibility formula.
This is an executable rank-one sign and slot-order regression. -/
theorem identityTensorSection_mixedCovariantDerivativeAlong
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (θ : Fin 1 → CovectorSection (I := I) (M := M))
    (Y : Fin 1 → TangentSection (I := I) (M := M)) (x : M)
    (hdual : IsSmoothTangentSection (metricDualSection g (θ 0)))
    (hY : IsSmoothTangentSection (Y 0)) :
    mixedCovariantDerivativeAlong g X identityTensorSection θ Y x = 0 := by
  have hform := dualCovariantVector_apply_formula g X (θ 0) (Y 0) x hdual hY
  unfold mixedCovariantDerivativeAlong identityTensorSection
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  have hdual_eval :
      (Function.update θ 0 (dualCovariantVector g X (θ 0)) 0 x) (Y 0 x) =
        dualCovariantVector g X (θ 0) x (Y 0 x) := by
    simp [Function.update]
  have hvector_eval :
      (θ 0 x) (Function.update Y 0 (covariantVector g X (Y 0)) 0 x) =
        (θ 0 x) (covariantVector g X (Y 0) x) := by
    simp [Function.update]
  rw [hdual_eval, hvector_eval, hform]
  ring

/-- Chart-frame coefficient bridge for the covariant direction action used by
the mixed evaluator. This is the existing canonical Christoffel theorem
specialized through `covariantVector`; it exposes the inverse-Gram formula
without introducing a second connection or a coordinate-dependent tensor
representation. Together with the preceding sign-separated evaluator
formula it records the vector-slot `-Γ` action. The full dual-frame
`+Γ` expansion remains a separate obligation for a future tensor-bundle
producer. -/
theorem covariantVector_christoffel_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j k : Fin (Module.finrank ℝ E)) :
    let t := trivializationAt E (TangentSpace I) alpha
    let b := Module.finBasis ℝ E
    let e := t.localFrame b
    let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun a b => g.inner p (e a p) (e b p)
    let gij (a b : Fin (Module.finrank ℝ E)) (y : E) :=
      let q := (extChartAt I alpha).symm y
      g.inner q (e a q) (e b q)
    (t.basisAt b (by
      change p ∈ (chartAt H alpha).source
      exact hp)).repr
        (covariantVector g (e i) (e j) p) k =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        G⁻¹ k l *
          (fderiv ℝ (gij l j) (extChartAt I alpha p) (b i) +
            fderiv ℝ (gij i l) (extChartAt I alpha p) (b j) -
            fderiv ℝ (gij i j) (extChartAt I alpha p) (b l)) := by
  simpa only [covariantVector_apply] using
    (christoffel_formula (I := I) (H := H) g hp hinterior i j k)

/-- The raw covariant derivative annihilates the zero evaluation. -/
theorem mixedCovariantDerivativeAlong_zero {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) :
    mixedCovariantDerivativeAlong g X (fun _ _ => 0) θ Y = 0 := by
  funext x
  simp [mixedCovariantDerivativeAlong, directionalDerivative]

/-- Negation is preserved by the raw covariant derivative. -/
theorem mixedCovariantDerivativeAlong_neg {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) :
    mixedCovariantDerivativeAlong g X (fun θ Y => -A θ Y) θ Y =
      -mixedCovariantDerivativeAlong g X A θ Y := by
  funext x
  simp [mixedCovariantDerivativeAlong, directionalDerivative]
  ring

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Directional derivatives are additive under the usual differentiability
hypotheses. This small lemma is the calculus bridge used by downstream
additivity proofs. -/
theorem directionalDerivative_add
    (X : TangentSection (I := I) (M := M))
    {f f' : ScalarSection (M := M)} {x : M}
    (hf : MDiffAt f x) (hf' : MDiffAt f' x) :
    directionalDerivative X (f + f') x =
      directionalDerivative X f x + directionalDerivative X f' x := by
  simp [directionalDerivative, mvfderiv_add hf hf']

/-! The next two lemmas make the direction-slot linearity explicit for an
admissible finite tensor.  The multilinearity hypothesis is precisely what
allows the connection-action corrections to distribute through `Function.update`.
-/

/-- Additivity of the raw mixed derivative in its direction field, under
pointwise tensor-slot multilinearity. -/
theorem mixedCovariantDerivativeAlong_add_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X X' : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA : IsPointwiseMultilinear A) :
    mixedCovariantDerivativeAlong g (X + X') A θ Y x =
      mixedCovariantDerivativeAlong g X A θ Y x +
        mixedCovariantDerivativeAlong g X' A θ Y x := by
  have hθ (i : Fin p) :
      A (Function.update θ i (dualCovariantVector g (X + X') (θ i))) Y x =
        A (Function.update θ i (dualCovariantVector g X (θ i))) Y x +
          A (Function.update θ i (dualCovariantVector g X' (θ i))) Y x := by
    have hdual : dualCovariantVector g (X + X') (θ i) =
        dualCovariantVector g X (θ i) + dualCovariantVector g X' (θ i) := by
      funext y
      exact dualCovariantVector_add_direction_at g X X' (θ i) y
    rw [hdual]
    have h := (hA x).1
      (Function.update θ i (dualCovariantVector g X (θ i)))
      (Function.update θ i (dualCovariantVector g X' (θ i))) Y i
    simpa [Function.update] using h
  have hY (i : Fin q) :
      A θ (Function.update Y i (covariantVector g (X + X') (Y i))) x =
        A θ (Function.update Y i (covariantVector g X (Y i))) x +
          A θ (Function.update Y i (covariantVector g X' (Y i))) x := by
    have hvector : covariantVector g (X + X') (Y i) =
        covariantVector g X (Y i) + covariantVector g X' (Y i) := by
      funext y
      exact covariantVector_add_direction_at g X X' (Y i) y
    rw [hvector]
    have h := (hA x).2.1 θ
      (Function.update Y i (covariantVector g X (Y i)))
      (Function.update Y i (covariantVector g X' (Y i))) i
    simpa [Function.update] using h
  simp only [mixedCovariantDerivativeAlong, directionalDerivative, Pi.add_apply,
    map_add]
  simp_rw [hθ, hY, Finset.sum_add_distrib]
  ring

/-- Function-scalar linearity of the raw mixed derivative in its direction
field, under pointwise tensor-slot tensoriality. -/
theorem mixedCovariantDerivativeAlong_smul_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hT : IsPointwiseTensorial A) :
    mixedCovariantDerivativeAlong g (f • X) A θ Y x =
      f x * mixedCovariantDerivativeAlong g X A θ Y x := by
  have hθ (i : Fin p) :
      A (Function.update θ i (dualCovariantVector g (f • X) (θ i))) Y x =
        f x * A (Function.update θ i (dualCovariantVector g X (θ i))) Y x := by
    have hdual : dualCovariantVector g (f • X) (θ i) =
        f • dualCovariantVector g X (θ i) := by
      funext y
      exact dualCovariantVector_smul_direction_at g f X (θ i) y
    rw [hdual]
    have h := (hT x).1 f
      (Function.update θ i (dualCovariantVector g X (θ i))) Y i
    simpa [Function.update] using h
  have hY (i : Fin q) :
      A θ (Function.update Y i (covariantVector g (f • X) (Y i))) x =
        f x * A θ (Function.update Y i (covariantVector g X (Y i))) x := by
    have hvector : covariantVector g (f • X) (Y i) =
        f • covariantVector g X (Y i) := by
      funext y
      exact covariantVector_smul_direction_at g f X (Y i) y
    rw [hvector]
    have h := (hT x).2 f θ
      (Function.update Y i (covariantVector g X (Y i))) i
    simpa [Function.update] using h
  have hdir : directionalDerivative (f • X) (A θ Y) x =
      f x * directionalDerivative X (A θ Y) x := by
    simp [directionalDerivative]
  simp only [mixedCovariantDerivativeAlong]
  rw [hdir]
  simp only [hθ, hY]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- The first-direction derivative is a fibrewise linear map once the raw
evaluation is multilinear in tensor slots and tensorial in those slots. This
is the proved `TensorialAt` bridge used by the conditional second-derivative
API below. -/
theorem mixedCovariantDerivativeAlong_tensorialAt {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hM : IsPointwiseMultilinear A) (hT : IsPointwiseTensorial A) :
    TensorialAt I E (fun X => mixedCovariantDerivativeAlong g X A θ Y x) x := by
  refine { smul := ?_, add := ?_ }
  · intro f X hf hX
    simpa [smul_eq_mul] using
      (mixedCovariantDerivativeAlong_smul_direction_at g f X A θ Y x hT)
  · intro X X' hX hX'
    simpa using
      (mixedCovariantDerivativeAlong_add_direction_at g X X' A θ Y x hM)

/-! The following locality adapter is the direct `TensorialAt.pointwise`
interface for the first direction.  The second-derivative locality theorem
below remains conditional on the corresponding two-slot witnesses. -/

/-- Equal differentiable first-direction extensions give the same mixed
derivative evaluation at the point. -/
theorem mixedCovariantDerivativeAlong_pointwise {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hM : IsPointwiseMultilinear A) (hT : IsPointwiseTensorial A)
    {X X' : TangentSection (I := I) (M := M)}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hXX' : X x = X' x) :
    mixedCovariantDerivativeAlong g X A θ Y x =
      mixedCovariantDerivativeAlong g X' A θ Y x := by
  exact (mixedCovariantDerivativeAlong_tensorialAt (x := x) g A θ Y hM hT).pointwise
    hX hX' hXX'

/-- Pointwise additivity in the tensor argument, assuming the displayed
evaluations are differentiable at the chosen point. -/
theorem mixedCovariantDerivativeAlong_add_tensor_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (A A' : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA : MDiffAt (A θ Y) x) (hA' : MDiffAt (A' θ Y) x) :
    mixedCovariantDerivativeAlong g X (A + A') θ Y x =
      mixedCovariantDerivativeAlong g X A θ Y x +
        mixedCovariantDerivativeAlong g X A' θ Y x := by
  have hdir : directionalDerivative X ((A + A') θ Y) x =
      directionalDerivative X (A θ Y) x + directionalDerivative X (A' θ Y) x := by
    apply directionalDerivative_add X hA hA'
  simp only [mixedCovariantDerivativeAlong]
  rw [hdir]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- Constant-scalar linearity in the tensor argument, with the required
pointwise differentiability hypothesis. -/
theorem mixedCovariantDerivativeAlong_smul_tensor_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA : MDiffAt (A θ Y) x) :
    mixedCovariantDerivativeAlong g X (c • A) θ Y x =
      c * mixedCovariantDerivativeAlong g X A θ Y x := by
  simp only [mixedCovariantDerivativeAlong]
  have hdir : directionalDerivative X ((c • A) θ Y) x =
    c * directionalDerivative X (A θ Y) x := by
    change d% ((fun _ : M => c) • (A θ Y)) x (X x) = _
    rw [mvfderiv_smul (mdifferentiableAt_const) hA]
    simp [mvfderiv_const, directionalDerivative]
  rw [hdir]
  change c * directionalDerivative X (A θ Y) x -
      ∑ i, c * A (Function.update θ i (dualCovariantVector g X (θ i))) Y x -
      ∑ i, c * A θ (Function.update Y i (covariantVector g X (Y i))) x = _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Additivity of the source-ordered second derivative in its tensor
argument.  The two `MDiffAt` hypotheses for the inner derivative are
necessary: the first covariant derivative is only additive on differentiable
sections, as required by Mathlib's `IsCovariantDerivativeOn` contract. -/
theorem secondCovariantDerivativeEval_add_tensor_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Z : TangentSection (I := I) (M := M))
    (A A' : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hAall : ∀ θ' Y' y, MDiffAt (A θ' Y') y)
    (hA'all : ∀ θ' Y' y, MDiffAt (A' θ' Y') y)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hZA' : MDiffAt (mixedCovariantDerivativeAlong g Z A' θ Y) x)
    (hA : MDiffAt (A θ Y) x) (hA' : MDiffAt (A' θ Y) x) :
    secondCovariantDerivativeEval g (A + A') θ Y X Z x =
    secondCovariantDerivativeEval g A θ Y X Z x +
        secondCovariantDerivativeEval g A' θ Y X Z x := by
  have hinner : mixedCovariantDerivativeAlong g Z (A + A') =
      mixedCovariantDerivativeAlong g Z A +
        mixedCovariantDerivativeAlong g Z A' := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_add_tensor_at g Z A A' θ' Y' y
      (hAall θ' Y' y) (hA'all θ' Y' y)
  have houter := mixedCovariantDerivativeAlong_add_tensor_at g X
    (mixedCovariantDerivativeAlong g Z A)
    (mixedCovariantDerivativeAlong g Z A') θ Y x hZA hZA'
  have hcorr := mixedCovariantDerivativeAlong_add_tensor_at g
    (covariantVector g X Z) A A' θ Y x hA hA'
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z (A + A')) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) (A + A') θ Y x) = _
  rw [hinner, houter, hcorr]
  simp only [Pi.sub_apply]
  ring

/-- Constant-scalar linearity of the source-ordered second derivative in its
tensor argument. -/
theorem secondCovariantDerivativeEval_smul_tensor_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hAall : ∀ θ' Y' y, MDiffAt (A θ' Y') y)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hA : MDiffAt (A θ Y) x) :
    secondCovariantDerivativeEval g (c • A) θ Y X Z x =
      c * secondCovariantDerivativeEval g A θ Y X Z x := by
  have hinner : mixedCovariantDerivativeAlong g Z (c • A) =
      c • mixedCovariantDerivativeAlong g Z A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_smul_tensor_at g c Z A θ' Y' y
      (hAall θ' Y' y)
  have houter := mixedCovariantDerivativeAlong_smul_tensor_at g c X
    (mixedCovariantDerivativeAlong g Z A) θ Y x hZA
  have hcorr := mixedCovariantDerivativeAlong_smul_tensor_at g c
    (covariantVector g X Z) A θ Y x hA
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z (c • A)) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) (c • A) θ Y x) = _
  rw [hinner, houter, hcorr]
  simp only [Pi.sub_apply]
  ring

/-- Leibniz rule for multiplying the tensor evaluation by a scalar function.
This is the cancellation lemma needed to prove tensoriality in the inner
second-derivative direction. -/
theorem mixedCovariantDerivativeAlong_smul_function_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hf : MDiffAt f x) (hA : MDiffAt (A θ Y) x) :
    mixedCovariantDerivativeAlong g X (f • A) θ Y x =
      d% f x (X x) * A θ Y x +
        f x * mixedCovariantDerivativeAlong g X A θ Y x := by
  have hdir : directionalDerivative X ((f • A) θ Y) x =
      d% f x (X x) * A θ Y x + f x * directionalDerivative X (A θ Y) x := by
    change d% (fun y => f y * A θ Y y) x (X x) = _
    rw [mvfderiv_fun_mul hf hA]
    simp [directionalDerivative]
    ring
  have hθ (i : Fin p) :
      (f • A) (Function.update θ i (dualCovariantVector g X (θ i))) Y x =
        f x * A (Function.update θ i (dualCovariantVector g X (θ i))) Y x := by
    simp
  have hY (i : Fin q) :
      (f • A) θ (Function.update Y i (covariantVector g X (Y i))) x =
        f x * A θ (Function.update Y i (covariantVector g X (Y i))) x := by
    simp
  simp only [mixedCovariantDerivativeAlong]
  rw [hdir]
  simp only [hθ, hY]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Additivity of the source-ordered second derivative in its outer (first)
direction. The hypotheses state exactly the multilinearity needed by the two
first-derivative correction terms. -/
theorem secondCovariantDerivativeEval_add_first_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X X' Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA : IsPointwiseMultilinear A)
    (hZA : IsPointwiseMultilinear (mixedCovariantDerivativeAlong g Z A)) :
    secondCovariantDerivativeEval g A θ Y (X + X') Z x =
      secondCovariantDerivativeEval g A θ Y X Z x +
        secondCovariantDerivativeEval g A θ Y X' Z x := by
  have hvec : covariantVector g (X + X') Z =
      covariantVector g X Z + covariantVector g X' Z := by
    funext y
    exact covariantVector_add_direction_at g X X' Z y
  unfold secondCovariantDerivativeEval
  simp only [Pi.sub_apply]
  rw [mixedCovariantDerivativeAlong_add_direction_at g X X'
      (mixedCovariantDerivativeAlong g Z A) θ Y x hZA]
  rw [hvec]
  rw [mixedCovariantDerivativeAlong_add_direction_at g
      (covariantVector g X Z) (covariantVector g X' Z) A θ Y x hA]
  ring

/-- Constant/function-scalar linearity of the source-ordered second derivative
in its outer (first) direction. -/
theorem secondCovariantDerivativeEval_smul_first_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA : IsPointwiseTensorial A)
    (hZA : IsPointwiseTensorial (mixedCovariantDerivativeAlong g Z A)) :
    secondCovariantDerivativeEval g A θ Y (f • X) Z x =
      f x * secondCovariantDerivativeEval g A θ Y X Z x := by
  have hvec : covariantVector g (f • X) Z =
      f • covariantVector g X Z := by
    funext y
    exact covariantVector_smul_direction_at g f X Z y
  unfold secondCovariantDerivativeEval
  simp only [Pi.sub_apply]
  rw [mixedCovariantDerivativeAlong_smul_direction_at g f X
      (mixedCovariantDerivativeAlong g Z A) θ Y x hZA]
  rw [hvec]
  rw [mixedCovariantDerivativeAlong_smul_direction_at g f
      (covariantVector g X Z) A θ Y x hA]
  ring

/-- Conditional function-scalar law in the inner (second) direction. The
explicit hypotheses expose the smoothness and tensoriality needed for the
Leibniz cancellation, instead of hiding them in a bundled tensor connection. -/
theorem secondCovariantDerivativeEval_smul_second_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hZ : IsSmoothTangentSection Z)
    (hf : ∀ y, MDiffAt f y) :
    secondCovariantDerivativeEval g A θ Y X (f • Z) x =
      f x * secondCovariantDerivativeEval g A θ Y X Z x := by
  have hinner : mixedCovariantDerivativeAlong g (f • Z) A =
      f • mixedCovariantDerivativeAlong g Z A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_smul_direction_at g f Z A θ' Y' y hA_T
  have hvec : covariantVector g X (f • Z) =
      f • covariantVector g X Z + directionalDerivative X f • Z := by
    funext y
    exact covariantVector_smul_argument_at g f X Z y hZ (hf y)
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g (f • Z) A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X (f • Z)) A θ Y x) = _
  rw [hinner]
  rw [mixedCovariantDerivativeAlong_smul_function_at g f X
      (mixedCovariantDerivativeAlong g Z A) θ Y x (hf x) hZA]
  rw [hvec]
  rw [mixedCovariantDerivativeAlong_add_direction_at g
      (f • covariantVector g X Z) (directionalDerivative X f • Z)
      A θ Y x hA_M]
  rw [mixedCovariantDerivativeAlong_smul_direction_at g f
      (covariantVector g X Z) A θ Y x hA_T]
  rw [mixedCovariantDerivativeAlong_smul_direction_at g
      (directionalDerivative X f) Z A θ Y x hA_T]
  simp only [Pi.sub_apply]
  simp only [directionalDerivative]
  ring

/-- Additivity of the source-ordered second derivative in the inner (second)
direction. The smoothness assumptions are used only to expand the connection
action on the summed direction section. -/
theorem secondCovariantDerivativeEval_add_second_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Z Z' : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA_M : IsPointwiseMultilinear A)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hZA' : MDiffAt (mixedCovariantDerivativeAlong g Z' A θ Y) x)
    (hZ : IsSmoothTangentSection Z)
    (hZ' : IsSmoothTangentSection Z') :
    secondCovariantDerivativeEval g A θ Y X (Z + Z') x =
      secondCovariantDerivativeEval g A θ Y X Z x +
        secondCovariantDerivativeEval g A θ Y X Z' x := by
  have hinner : mixedCovariantDerivativeAlong g (Z + Z') A =
      mixedCovariantDerivativeAlong g Z A +
        mixedCovariantDerivativeAlong g Z' A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_add_direction_at g Z Z' A θ' Y' y hA_M
  have hconn : covariantVector g X (Z + Z') =
      covariantVector g X Z + covariantVector g X Z' := by
    funext y
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := (leviCivitaConnection g).isCovariantDerivativeOn.add
      (hZ.mdifferentiableAt (by simp)) (hZ'.mdifferentiableAt (by simp)) (x := y)
    have h' := congrArg (fun L => L (X y)) h
    simpa [covariantVector] using h'
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g (Z + Z') A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X (Z + Z')) A θ Y x) = _
  rw [hinner]
  rw [mixedCovariantDerivativeAlong_add_tensor_at g X
      (mixedCovariantDerivativeAlong g Z A)
      (mixedCovariantDerivativeAlong g Z' A) θ Y x hZA hZA']
  rw [hconn]
  rw [mixedCovariantDerivativeAlong_add_direction_at g
      (covariantVector g X Z) (covariantVector g X Z') A θ Y x hA_M]
  simp only [Pi.sub_apply]
  ring

/-- Package any proved inner-direction additivity and function-scalar law as
Mathlib's `TensorialAt` witness. This keeps the regularity premises visible at
the API boundary while avoiding a second, unbundled tensor connection. -/
theorem secondCovariantDerivativeEval_second_direction_tensorialAt_of_laws
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X : TangentSection (I := I) (M := M)) {x : M}
    (hsmul : ∀ {f : ScalarSection (M := M)}
      {Z : TangentSection (I := I) (M := M)},
      MDiffAt f x → MDiffAt (T% Z) x →
      secondCovariantDerivativeEval g A θ Y X (f • Z) x =
        f x * secondCovariantDerivativeEval g A θ Y X Z x)
    (hadd : ∀ {Z Z' : TangentSection (I := I) (M := M)},
      MDiffAt (T% Z) x → MDiffAt (T% Z') x →
      secondCovariantDerivativeEval g A θ Y X (Z + Z') x =
        secondCovariantDerivativeEval g A θ Y X Z x +
          secondCovariantDerivativeEval g A θ Y X Z' x) :
    TensorialAt I E (fun Z => secondCovariantDerivativeEval g A θ Y X Z x) x := by
  refine { smul := ?_, add := ?_ }
  · intro f Z hf hZ
    exact hsmul hf hZ
  · intro Z Z' hZ hZ'
    exact hadd hZ hZ'

/-- `TensorialAt` packaging of the proved outer-direction laws. The inner
direction has a separate conditional packaging theorem above; wiring either
one to a bundled smooth tensor producer remains an explicit obligation. -/
theorem secondCovariantDerivativeEval_first_direction_tensorialAt {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (Z : TangentSection (I := I) (M := M)) {x : M}
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hZA_M : IsPointwiseMultilinear (mixedCovariantDerivativeAlong g Z A))
    (hZA_T : IsPointwiseTensorial (mixedCovariantDerivativeAlong g Z A)) :
    TensorialAt I E (fun X => secondCovariantDerivativeEval g A θ Y X Z x) x := by
  refine { smul := ?_, add := ?_ }
  · intro f X hf hX
    simpa [smul_eq_mul] using
      (secondCovariantDerivativeEval_smul_first_direction_at g f X Z A θ Y x
        hA_T hZA_T)
  · intro X X' hX hX'
    simpa using
      (secondCovariantDerivativeEval_add_first_direction_at g X X' Z A θ Y x
        hA_M hZA_M)

end AlgebraicLaws
