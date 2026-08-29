/-
Copyright (c) 2026 Axel Dlv. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
-/

import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

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

The pinned Mathlib release provides a section-level connection and smooth Hom
bundles, but no induced covariant derivative on arbitrary Hom/tensor-product
bundles (the tensor-product bundle construction is not yet provided by
`Topology.VectorBundle.Hom`, and `CovariantDerivative.Metric` leaves the
induced connection as future work). Smoothness, multilinearity, and
tensoriality predicates are therefore explicit in this module. The raw
evaluator definitions accept arbitrary evaluations; the producer-level
regularity and extension-independence theorems below carry the corresponding
hypotheses rather than asserting them by definition. The
`TensorialAt`/`mkHom`/`mkHom₂` lemmas from Mathlib are the fibre-level
interface. Until a bundled, extension-independent producer lands, this module
is a provisional direct-import leaf and is deliberately absent from the stable
`MorganTianLib.Ch01` umbrella. Before S13's Bochner consumer is accepted, that
producer must be proved and the consumer migrated; otherwise this raw leaf
remains direct-only. The indexed producer below handles arbitrary finite
`(p,q)` evaluations under an explicit metric-dual regularity witness; its
`p = 0` specialization supplies the witness-free evaluation-level covariant,
scalar, and one-form adapters. The witness is kept visible because the
evaluation-level
`IsSmoothCovectorSection` predicate does not itself provide smoothness of the
metric-dual section. The local-frame covector bridge records the dual-action
`-Γ` sign; inverse-Gram coefficient regularity discharges that premise for the
canonical local-frame wrapper. The unconditional constant-scalar laws below
use the totalized `mvfderiv`/`mfderiv` API and concern only the displayed
algebraic operations; they do not discharge the remaining producer-level
smoothness obligations.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
discussion preceding `lapformula`, pp. 39--40, bibliography key
`morganTian2007`. Mathlib references:
`Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`,
`Geometry.Manifold.VectorBundle.CovariantDerivative.Metric`,
`Geometry.Manifold.VectorBundle.Hom`,
`Geometry.Manifold.VectorBundle.Tensoriality`,
`Geometry.Manifold.ContMDiffMFDeriv`,
`Geometry.Manifold.MFDeriv.NormedSpace`/`Basic` (`mvfderiv_smul`,
`mfderiv_zero_of_not_mdifferentiableAt`), and
`Analysis.InnerProductSpace.GramMatrix`,
`LinearAlgebra.Matrix.Adjugate`/`NonsingularInverse`, and
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

/-! The local form below is the one needed by `TensorialAt`: a covariant
derivative only consumes a first-order germ of its differentiated section at
the evaluation point.  The smooth-section theorem above is retained as the
convenient compatibility wrapper used by the earlier API. -/

/-- Leibniz rule for `∇_X (f • Z)` with only pointwise differentiability
hypotheses.  This is the local-regularity form of
`covariantVector_smul_argument_at`, and uses the same bundled
`leviCivitaConnection` selected by `g`. -/
theorem covariantVector_smul_argument_at_of_mdifferentiableAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M))
    (X Z : TangentSection (I := I) (M := M)) (x : M)
    (hZ : MDiffAt (T% Z) x) (hf : MDiffAt f x) :
    covariantVector g X (f • Z) x =
      f x • covariantVector g X Z x +
        d% f x (X x) • Z x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := (leviCivitaConnection g).isCovariantDerivativeOn.leibniz
    hZ hf (x := x)
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

omit [FiniteDimensional ℝ E] in
/-- The directional derivative of a smooth `F`-valued function on the
manifold along a smooth tangent section is smooth at the evaluation point.
The proof uses the Hom-bundle regularity theorem for `mfderiv` and then
evaluates its continuous linear-map fibre on the tangent section.  This is the
local calculus bridge used by the scalar second-derivative producer below. -/
theorem contMDiffAt_mvfderiv_apply_along
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {X : ∀ y : M, TangentSpace I y} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ∞ f x)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) x) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => d% f y (X y)) x := by
  have hsection :
      ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] F)
          (E := fun y : M => TangentSpace I y →L[ℝ] F) y (d% f y)) x := by
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    convert hf.mfderiv_const (m := ∞) (by simp) using 1
    ext y v
    simp [mvfderiv, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl
  have h := hsection.clm_bundle_apply hX
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

/-! The local bridge above is independent of finite-dimensionality of the model
space. -/
omit [FiniteDimensional ℝ E] in
/-- Global smoothness form of
`contMDiffAt_mvfderiv_apply_along` for the scalar directional derivative. -/
theorem directionalDerivative_contMDiff
    {f : ScalarSection (M := M)} {X : TangentSection (I := I) (M := M)}
    (hf : CMDiff ∞ f) (hX : IsSmoothTangentSection X) :
    CMDiff ∞ (fun y => directionalDerivative X f y) := by
  intro x
  exact contMDiffAt_mvfderiv_apply_along (hf := hf.contMDiffAt)
    (hX := hX.contMDiffAt)

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

/-- Pointwise version of `dualCovariantVector_apply_formula`.  Unlike the
global wrapper, this form asks only for first-order differentiability of the
metric-dual and test sections at `x`; it is the form used by local-frame
component calculations. -/
theorem dualCovariantVector_apply_formula_at
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M))
    (Z : TangentSection (I := I) (M := M)) (x : M)
    (hdual : MDiffAt (T% (metricDualSection g θ)) x)
    (hZ : MDiffAt (T% Z) x) :
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
  have hcompat := hmetric.mvfderiv_inner_eq (x := x) X hdual hZ
  have heval :
      (fun y => inner ℝ (metricDualSection g θ y) (Z y)) =
        (fun y => θ y (Z y)) := by
    funext y
    simp [metricDualSection]
  rw [heval] at hcompat
  have hcompat' :
      d% (fun y => θ y (Z y)) x (X x) =
        inner ℝ (leviCivitaConnection g (metricDualSection g θ) x (X x))
            (Z x) +
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

/-- If a covector section and its metric dual are smooth, the dual connection
along a smooth tangent section is smooth as an evaluation-level covector.
This is the contravariant regularity bridge used by the conditional mixed
producer below. -/
theorem dualCovariantVector_isSmoothCovectorSection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (X : TangentSection (I := I) (M := M))
    (θ : CovectorSection (I := I) (M := M))
    (hθ : IsSmoothCovectorSection θ)
    (hdual : IsSmoothTangentSection (metricDualSection g θ))
    (hX : IsSmoothTangentSection X) :
    IsSmoothCovectorSection (dualCovariantVector g X θ) := by
  intro Z hZ
  have hθZ : CMDiff ∞ (fun x => θ x (Z x)) := hθ Z hZ
  have hconn : IsSmoothTangentSection (covariantVector g X Z) := by
    intro x
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Connection.contMDiffAt_leviCivitaConnection_apply g
      hX.contMDiffAt hZ.contMDiffAt
  have hθconn : CMDiff ∞
      (fun x => θ x (covariantVector g X Z x)) :=
    hθ (covariantVector g X Z) hconn
  have hdir := directionalDerivative_contMDiff hθZ hX
  have hEq : (fun x => dualCovariantVector g X θ x (Z x)) =
      directionalDerivative X (fun y => θ y (Z y)) -
        (fun x => θ x (covariantVector g X Z x)) := by
    funext x
    exact dualCovariantVector_apply_formula g X θ Z x hdual hZ
  rw [hEq]
  exact hdir.sub hθconn

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
evaluation formula; genuine tensor components would therefore carry `+Γ` in
dual (contravariant) slots and `-Γ` in vector (covariant) slots. The
evaluation-level tensoriality hypotheses are intentionally kept separate from
this definition. -/
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
direction-slot tensoriality hypotheses below. Because arbitrary inputs need
not be intrinsic, this declaration is intentionally available only through the
direct provisional leaf, not the stable Chapter 1 umbrella. -/
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

/-- A smooth mixed evaluation has a smooth first covariant derivative whenever
each contravariant slot's metric-dual section is supplied as smooth data.
The indexed premise is vacuous for `p = 0`, while retaining the exact
regularity obligation for contravariant slots.  This returns the
evaluation-level predicate `IsSmoothMixedTensorSection`; it does not add
multilinearity, tensoriality, or a bundled tensor section, nor does it assert
that the pinned Mathlib release carries an induced tensor-product connection.
Source: Morgan--Tian, Chapter 1, discussion preceding `lapformula`, pp. 39--40,
`morganTian2007`. -/
theorem mixedCovariantDerivativeAlong_isSmooth
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (hA : IsSmoothMixedTensorSection (p := p) (q := q) A)
    (X : TangentSection (I := I) (M := M))
    (hX : IsSmoothTangentSection X)
    (hdual : ∀ (θ : Fin p → CovectorSection (I := I) (M := M)),
      (∀ i, IsSmoothCovectorSection (θ i)) →
      ∀ i, IsSmoothTangentSection (metricDualSection g (θ i))) :
    IsSmoothMixedTensorSection
      (mixedCovariantDerivativeAlong g X A) := by
  intro θ Y hθ hY
  have hbase := hA θ Y hθ hY
  have hdir : CMDiff ∞ (directionalDerivative X (A θ Y)) := by
    exact directionalDerivative_contMDiff hbase hX
  have hdualCov : ∀ i : Fin p,
      IsSmoothCovectorSection (dualCovariantVector g X (θ i)) := by
    intro i
    exact dualCovariantVector_isSmoothCovectorSection g X (θ i)
      (hθ i) (hdual θ hθ i) hX
  have htermDual : ∀ i : Fin p,
      CMDiff ∞ (fun x => A
        (Function.update θ i (dualCovariantVector g X (θ i))) Y x) := by
    intro i
    apply hA
    · intro j
      by_cases hij : j = i
      · subst j
        simpa [Function.update_apply] using hdualCov i
      · simpa [Function.update_apply, hij] using hθ j
    · exact hY
  have hsumDual : CMDiff ∞ (fun x =>
      ∑ i, A (Function.update θ i (dualCovariantVector g X (θ i))) Y x) := by
    exact contMDiff_finsetSum (t := Finset.univ) (f := fun i x =>
      A (Function.update θ i (dualCovariantVector g X (θ i))) Y x)
      (by intro i hi; exact htermDual i)
  have hconn : ∀ i : Fin q,
      IsSmoothTangentSection (covariantVector g X (Y i)) := by
    intro i x
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Connection.contMDiffAt_leviCivitaConnection_apply g
      hX.contMDiffAt (hY i).contMDiffAt
  have htermVector : ∀ i : Fin q,
      CMDiff ∞ (fun x => A θ
        (Function.update Y i (covariantVector g X (Y i))) x) := by
    intro i
    apply hA
    · exact hθ
    · intro j
      by_cases hij : j = i
      · subst j
        simpa [Function.update_apply] using hconn i
      · simpa [Function.update_apply, hij] using hY j
  have hsumVector : CMDiff ∞ (fun x =>
      ∑ i, A θ (Function.update Y i (covariantVector g X (Y i))) x) := by
    exact contMDiff_finsetSum (t := Finset.univ) (f := fun i x =>
      A θ (Function.update Y i (covariantVector g X (Y i))) x)
      (by intro i hi; exact htermVector i)
  have hEq : mixedCovariantDerivativeAlong g X A θ Y =
      (fun x => directionalDerivative X (A θ Y) x -
        ∑ i, A (Function.update θ i (dualCovariantVector g X (θ i))) Y x -
        ∑ i, A θ (Function.update Y i (covariantVector g X (Y i))) x) := by
    funext x
    simp [mixedCovariantDerivativeAlong, directionalDerivative,
      Finset.sum_fin_eq_sum_range]
  rw [hEq]
  exact (hdir.sub hsumDual).sub hsumVector

/-- Under the indexed metric-dual regularity premise, the source-ordered
second covariant derivative of any smooth mixed evaluation is smooth.  The
result is evaluation-level (`IsSmoothSecondCovariantDerivative`), not a
bundled tensor-section producer.  The two applications of the first-producer
theorem preserve the order `∇_X (∇_Z A) - ∇_{∇_X Z} A` exactly.  Source:
Morgan--Tian, Chapter 1, discussion preceding `lapformula`, pp. 39--40,
`morganTian2007`. -/
theorem secondCovariantDerivative_isSmooth
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (hA : IsSmoothMixedTensorSection (p := p) (q := q) A)
    (hdual : ∀ (θ : Fin p → CovectorSection (I := I) (M := M)),
      (∀ i, IsSmoothCovectorSection (θ i)) →
      ∀ i, IsSmoothTangentSection (metricDualSection g (θ i))) :
    IsSmoothSecondCovariantDerivative g A := by
  intro θ Y X Z hθ hY hX hZ
  have hinner : IsSmoothMixedTensorSection
      (mixedCovariantDerivativeAlong g Z A) :=
    mixedCovariantDerivativeAlong_isSmooth g A hA Z hZ hdual
  have houterMixed : IsSmoothMixedTensorSection
      (mixedCovariantDerivativeAlong g X
        (mixedCovariantDerivativeAlong g Z A)) :=
    mixedCovariantDerivativeAlong_isSmooth g
      (mixedCovariantDerivativeAlong g Z A) hinner X hX hdual
  have houter := houterMixed θ Y hθ hY
  have hconn : IsSmoothTangentSection (covariantVector g X Z) := by
    intro x
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Connection.contMDiffAt_leviCivitaConnection_apply g
      hX.contMDiffAt hZ.contMDiffAt
  have hcorrMixed : IsSmoothMixedTensorSection
      (mixedCovariantDerivativeAlong g (covariantVector g X Z) A) :=
    mixedCovariantDerivativeAlong_isSmooth g A hA
      (covariantVector g X Z) hconn hdual
  have hcorr := hcorrMixed θ Y hθ hY
  change CMDiff ∞
    (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z A) θ Y -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) A θ Y)
  exact houter.sub hcorr

/-- The covariant-only specialization of the indexed first-derivative
producer for an evaluation-level smooth input. Its metric-dual premise is
vacuous because there are no contravariant slots. -/
theorem covariantTensor_mixedCovariantDerivativeAlong_isSmooth
    {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (hA : IsSmoothMixedTensorSection (p := 0) (q := q) A)
    (X : TangentSection (I := I) (M := M))
    (hX : IsSmoothTangentSection X) :
    IsSmoothMixedTensorSection
      (mixedCovariantDerivativeAlong g X A) :=
  mixedCovariantDerivativeAlong_isSmooth g A hA X hX
    (fun _θ _hθ i => Fin.elim0 i)

/-- The covariant-only specialization of the indexed second-derivative
producer for an evaluation-level smooth input. -/
theorem covariantTensor_secondCovariantDerivative_isSmooth
    {q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (A : CovariantTensorSection (I := I) (M := M) q)
    (hA : IsSmoothMixedTensorSection (p := 0) (q := q) A) :
    IsSmoothSecondCovariantDerivative g A :=
  secondCovariantDerivative_isSmooth g A hA
    (fun _θ _hθ i => Fin.elim0 i)

omit [FiniteDimensional ℝ E] in
/-- A smooth scalar is a smooth rank-zero covariant tensor evaluation. -/
theorem scalarTensor_isSmoothMixedTensorSection
    {f : ScalarSection (M := M)}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothMixedTensorSection (I := I) (M := M) (p := 0) (q := 0)
      (scalarTensor f) := by
  intro θ Y hθ hY
  have hθeq : θ = emptyCovectorArgs := Subsingleton.elim _ _
  have hYeq : Y = emptyTangentArgs := Subsingleton.elim _ _
  subst θ
  subst Y
  exact hf

/-- The scalar rank-zero adapter is an evaluation-level regularity wrapper for
the source-ordered second covariant derivative.  For a smooth scalar `f`, it
supplies `IsSmoothSecondCovariantDerivative`; the explicit rank-zero evaluator
equation is `secondCovariantDerivativeCovariant_rank_zero`. -/
theorem scalarTensor_isSmoothSecondCovariantDerivative
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {f : ScalarSection (M := M)}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    IsSmoothSecondCovariantDerivative g (scalarTensor f) :=
  covariantTensor_secondCovariantDerivative_isSmooth g (scalarTensor f)
    (scalarTensor_isSmoothMixedTensorSection hf)

/-- Direct scalar-Hessian regularity wrapper.  This is the rank-zero
compatibility surface for consumers that use the covariant specialization
rather than the generic smoothness predicate. -/
theorem secondCovariantDerivativeCovariant_rank_zero_contMDiff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {f : ScalarSection (M := M)} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Z : TangentSection (I := I) (M := M))
    (hX : IsSmoothTangentSection X) (hZ : IsSmoothTangentSection Z) :
    CMDiff ∞ (secondCovariantDerivativeCovariant g (scalarTensor f)
      emptyTangentArgs X Z) := by
  exact scalarTensor_isSmoothSecondCovariantDerivative (I := I) (M := M)
    g hf emptyCovectorArgs emptyTangentArgs X Z
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hX hZ

/-- Constant scalars instantiate the rank-zero evaluation-level regularity
producer.  The separate normalization fact is supplied by
`secondCovariantDerivativeCovariant_constant`; this theorem establishes only
`IsSmoothSecondCovariantDerivative`, without imposing a positive-dimensional
model. -/
theorem scalarTensor_constant_isSmoothSecondCovariantDerivative
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) :
    IsSmoothSecondCovariantDerivative g (scalarTensor (fun _ : M => c)) := by
  exact scalarTensor_isSmoothSecondCovariantDerivative g contMDiff_const

/-- The first covariant derivative of an evaluation-level smooth one-form is
smooth when tested on a smooth vector field. This rank-one adapter specializes
the covariant producer and uses the canonical Levi--Civita connection for the
correction vector. -/
theorem oneForm_mixedCovariantDerivativeAlong_contMDiff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (omega : OneFormSection (I := I) (M := M))
    (hω : IsSmoothMixedTensorSection (p := 0) (q := 1) omega)
    (U W : TangentSection (I := I) (M := M))
    (hU : IsSmoothTangentSection U)
    (hW : IsSmoothTangentSection W) :
    CMDiff ∞ (mixedCovariantDerivativeAlong g U omega emptyCovectorArgs
      (fun _ => W)) := by
  have h := covariantTensor_mixedCovariantDerivativeAlong_isSmooth
    (q := 1) g omega hω U hU
  exact h emptyCovectorArgs (fun _ => W)
    (fun i => Fin.elim0 i) (fun _ => hW)

/-- A smooth one-form evaluation has a smooth source-ordered second
covariant derivative.  The proof is the rank-one counterpart of the scalar
producer above, obtained from the covariant (`p = 0`) specialization of the
indexed evaluation-level producer.  No induced tensor-product connection is
introduced by this adapter. -/
theorem oneForm_isSmoothSecondCovariantDerivative
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (omega : OneFormSection (I := I) (M := M))
    (hω : IsSmoothMixedTensorSection (p := 0) (q := 1) omega) :
    IsSmoothSecondCovariantDerivative g omega :=
  covariantTensor_secondCovariantDerivative_isSmooth (q := 1) g omega hω

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

/-- The raw metric-trace sum can use any differentiable extensions of the
orthonormal-frame vectors.  The displayed value condition identifies those
extensions with the canonical `stdOrthonormalBasis` at `x`; the two
`TensorialAt` witnesses then remove all dependence on their behaviour away
from `x`.  This is the extension certificate for the provisional trace
evaluator, and does not assert a smooth tensor producer. -/
theorem connectionLaplacianEval_eq_sum_of_extensions {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hleft : ∀ Z, MDiffAt (T% Z) x →
      TensorialAt I E (fun X => secondDirectionEvaluation g A θ Y x X Z) x)
    (hright : ∀ X, MDiffAt (T% X) x →
      TensorialAt I E (fun Z => secondDirectionEvaluation g A θ Y x X Z) x)
    (U : Fin (finrank ℝ (TangentSpace I x)) → TangentSection (I := I) (M := M))
    (hU : ∀ i, MDiffAt (T% (U i)) x)
    (hUval : ∀ i,
      U i x =
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        letI : FiniteDimensional ℝ (TangentSpace I x) :=
          VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
        (stdOrthonormalBasis ℝ (TangentSpace I x)) i) :
    connectionLaplacianEval g A θ Y x =
      ∑ i, secondCovariantDerivativeEval g A θ Y (U i) (U i) x := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  unfold connectionLaplacianEval
  apply Finset.sum_congr rfl
  intro i hi
  apply secondCovariantDerivative_pointwise g A θ Y hleft hright
    (mdifferentiableAt_extend I E _)
    (hU i)
    (mdifferentiableAt_extend I E _)
    (hU i)
    (by simpa using (hUval i).symm)
    (by simpa using (hUval i).symm)

/-- Two differentiable extension families with the same frame values give the
same raw trace sum.  Keeping this as a separate theorem makes the locality
claim usable without mentioning the implementation's `FiberBundle.extend`
choice. -/
theorem connectionLaplacianEval_sum_extensions_eq {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hleft : ∀ Z, MDiffAt (T% Z) x →
      TensorialAt I E (fun X => secondDirectionEvaluation g A θ Y x X Z) x)
    (hright : ∀ X, MDiffAt (T% X) x →
      TensorialAt I E (fun Z => secondDirectionEvaluation g A θ Y x X Z) x)
    (U V : Fin (finrank ℝ (TangentSpace I x)) → TangentSection (I := I) (M := M))
    (hU : ∀ i, MDiffAt (T% (U i)) x)
    (hV : ∀ i, MDiffAt (T% (V i)) x)
    (hUV : ∀ i, U i x = V i x) :
    (∑ i, secondCovariantDerivativeEval g A θ Y (U i) (U i) x) =
      ∑ i, secondCovariantDerivativeEval g A θ Y (V i) (V i) x := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  exact secondCovariantDerivative_pointwise g A θ Y hleft hright
    (hU i) (hV i) (hU i) (hV i) (hUV i) (hUV i)

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
pointwise metric trace is produced by the Riesz endomorphism of the resulting
bilinear form. Under these explicit obligations the basis sum in
`connectionLaplacian` at the displayed tensor arguments is a genuine trace,
not a choice-dependent pointwise definition. -/
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

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Constant-scalar linearity of a directional derivative, without a
differentiability premise on the scalar section.  The non-differentiable case
uses the totalized `mfderiv` convention: a nonzero constant multiple is
non-differentiable exactly when the original section is, while the zero
multiple is handled separately. -/
theorem directionalDerivative_const_smul
    (X : TangentSection (I := I) (M := M)) (c : ℝ)
    (f : ScalarSection (M := M)) (x : M) :
    directionalDerivative X (c • f) x =
      c * directionalDerivative X f x := by
  unfold directionalDerivative
  by_cases hf : MDiffAt f x
  · have h := mvfderiv_smul (a := fun _ : M => c) (g := f)
      (mdifferentiableAt_const) hf
    have h' := congrArg (fun L => L (X x)) h
    have hfun : (fun _ : M => c) • f = c • f := by
      funext y
      simp [smul_eq_mul]
    rw [hfun] at h'
    simpa [smul_eq_mul, mvfderiv_const] using h'
  · by_cases hc : c = 0
    · subst c
      simp
    · have hcf : ¬ MDiffAt (c • f) x := by
        intro h
        apply hf
        have hi := h.const_smul c⁻¹
        simpa [smul_smul, hc] using hi
      simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hcf,
        mfderiv_zero_of_not_mdifferentiableAt hf]

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

/-- Turn a local trivialization coefficient into a cotangent section.  The
coefficient is converted to a continuous linear map only after installing the
canonical finite-dimensional fibre instance; no second cotangent or tensor
representation is introduced. -/
noncomputable def frameCovector
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (i : Fin (Module.finrank ℝ E)) : CovectorSection (I := I) (M := M) :=
  fun x =>
    letI : T2Space (TangentSpace I x) :=
      FiberBundle.t2Space E (TangentSpace I) x
    letI : FiniteDimensional ℝ (TangentSpace I x) :=
      VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
    LinearMap.toContinuousLinearMap (t.localFrame_coeff I b i x)

/-- At a point `x` in the trivialization base set, the `i`th frame covector
evaluates on the `j`th local-frame vector as the Kronecker delta. -/
@[simp] theorem frameCovector_apply_frame_of_mem
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {x : M} (hx : x ∈ t.baseSet)
    (i j : Fin (Module.finrank ℝ E)) :
    frameCovector (I := I) t b i x (t.localFrame b j x) =
      if i = j then 1 else 0 := by
  change (t.localFrame_coeff I b i x) (t.localFrame b j x) = _
  rw [t.localFrame_coeff_apply_of_mem_baseSet b hx]
  rw [t.localFrame_apply_of_mem_baseSet b hx]
  by_cases hij : i = j <;> simp [hij]

-- Keep the user-facing frame statement in its local-frame form; its simp-normal
-- form uses `basisAt`, which is less useful to component calculations.
attribute [nolint simpNF] frameCovector_apply_frame_of_mem

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private lemma contMDiffAt_matrix_det_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : M → Matrix ι ι ℝ} {x : M}
    (hentry : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => A y i j) x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (A y).det) x := by
  simp only [Matrix.det_apply']
  refine ContMDiffAt.sum (fun σ _ => ?_)
  refine (contMDiffAt_const.mul ?_)
  exact ContMDiffAt.prod (fun i _ => hentry (σ i) i)

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
private lemma contMDiffAt_matrix_inv_entry_entries
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : M → Matrix ι ι ℝ} {x : M}
    (hentry : ∀ i j, ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => A y i j) x)
    (hdet : (A x).det ≠ 0) (i j : ι) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (A y)⁻¹ i j) x := by
  have hdet' := contMDiffAt_matrix_det_entries hentry
  have hinvdet : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => ((A y).det)⁻¹) x := hdet'.inv₀ hdet
  have hentry_upd : ∀ r s, ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (A y).updateRow j (Pi.single i 1) r s) x := by
    intro r s
    by_cases hr : r = j
    · subst r
      simp only [Matrix.updateRow_self]
      by_cases hs : s = i
      · subst s
        exact contMDiffAt_const
      · simpa [Pi.single_apply, hs] using
          (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
            (fun _ : M => (0 : ℝ)) x)
    · simp only [Matrix.updateRow_apply, hr]
      exact hentry r s
  have hadjdet := contMDiffAt_matrix_det_entries hentry_upd
  have hadj : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => (A y).adjugate i j) x := by
    simpa only [Matrix.adjugate_apply] using hadjdet
  have hprod : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y => ((A y).det)⁻¹ * (A y).adjugate i j) x := by
    convert hinvdet.mul hadj using 1
    funext y
    rfl
  convert hprod using 1
  funext y
  rw [Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.smul_apply, smul_eq_mul]

/-- In a local frame, the metric-dual of the `a`th frame covector has the
corresponding inverse-Gram coefficient.  The proof is pointwise, so it uses
the canonical Riemannian fibre instance only for the Gram non-singularity and
Riesz identities. -/
theorem metricDualSection_frameCovector_coeff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {p : M} (hp : p ∈ t.baseSet)
    (a k : Fin (Module.finrank ℝ E)) :
    (t.localFrame_coeff I b k p)
      (metricDualSection g (frameCovector (I := I) t b a) p) =
      ((Matrix.of fun r s =>
        g.inner p (t.localFrame b r p) (t.localFrame b s p))⁻¹) a k := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I p) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) p
  letI : CompleteSpace (TangentSpace I p) :=
    FiniteDimensional.complete ℝ (TangentSpace I p)
  let e := t.localFrame b
  let eps := frameCovector (I := I) t b a
  let v := metricDualSection g eps p
  let bp := t.basisAt b hp
  let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    Matrix.of fun r s => g.inner p (e r p) (e s p)
  have hdet : G.det ≠ 0 := by
    have heq : G = Matrix.gram ℝ (fun r => e r p) := by
      ext r s
      rfl
    rw [heq]
    apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    exact (t.isLocalFrameOn_localFrame_baseSet I ∞ b).linearIndependent hp
  have hsystem : ∀ j : Fin (Module.finrank ℝ E),
      ∑ r : Fin (Module.finrank ℝ E),
          G r j * (bp.repr v r) = if a = j then 1 else 0 := by
    intro j
    have hinner : g.inner p v (e j p) = if a = j then 1 else 0 := by
      change inner ℝ
        ((InnerProductSpace.toDual ℝ (TangentSpace I p)).symm
          (frameCovector (I := I) t b a p)) (t.localFrame b j p) = _
      rw [InnerProductSpace.toDual_symm_apply]
      change frameCovector (I := I) t b a p (t.localFrame b j p) = _
      rw [frameCovector_apply_frame_of_mem (I := I) t b hp a j]
    have hvsum := bp.sum_repr v
    have hvinner := congrArg (fun w => g.inner p w (e j p)) hvsum
    have hvinner' :
        ∑ r : Fin (Module.finrank ℝ E),
          (bp.repr v r) * g.inner p (bp r) (e j p) =
            g.inner p v (e j p) := by
      simp only [map_sum, map_smul] at hvinner
      simpa [inner_smul_left] using hvinner
    rw [hinner] at hvinner'
    simpa [bp, e, G, t.localFrame_apply_of_mem_baseSet b hp,
      mul_comm, mul_left_comm, mul_assoc] using hvinner'
  let c : Fin (Module.finrank ℝ E) → ℝ := fun r => bp.repr v r
  let d : Fin (Module.finrank ℝ E) → ℝ := fun j => if a = j then 1 else 0
  have hM : d = G.transpose.mulVec c := by
    funext j
    simpa [c, d, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      mul_comm] using (hsystem j).symm
  have hunitT : IsUnit G.transpose.det := by
    simpa [Matrix.det_transpose] using (isUnit_iff_ne_zero.mpr hdet)
  have hleft := Matrix.nonsing_inv_mul G.transpose hunitT
  have hsol : G.transpose⁻¹.mulVec d = c := by
    calc
      G.transpose⁻¹.mulVec d =
          G.transpose⁻¹.mulVec (G.transpose.mulVec c) := by
        rw [hM]
      _ = (G.transpose⁻¹ * G.transpose).mulVec c := by
        rw [Matrix.mulVec_mulVec]
      _ = (1 : Matrix _ _ ℝ).mulVec c := by rw [hleft]
      _ = c := by simp
  have hsolk := congrFun hsol k
  dsimp [c, d] at hsolk
  rw [t.localFrame_coeff_apply_of_mem_baseSet b hp]
  have hinvtrans : G.transpose⁻¹ = G⁻¹.transpose :=
    (Matrix.transpose_nonsing_inv G).symm
  simpa [v, e, eps, G, Matrix.mulVec, dotProduct,
    hinvtrans, Matrix.transpose_apply] using hsolk.symm

/-- At each chosen point `p ∈ t.baseSet`, the metric-dual of a frame covector
is smooth in the local trivialization. Local frame coefficients are inverse
Gram entries; determinant and adjugate calculus supplies their smoothness. -/
theorem metricDualSection_frameCovector_contMDiffAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {p : M} (hp : p ∈ t.baseSet)
    (a : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (metricDualSection g (frameCovector (I := I) t b a))) p := by
  let e := t.localFrame b
  let A : M → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    fun y => Matrix.of fun r s => g.inner y (e r y) (e s y)
  have hframe : ∀ r : Fin (Module.finrank ℝ E),
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% (e r)) p := by
    intro r
    exact contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := t) (b := b) r hp
  have hentry : ∀ r s : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => A y r s) p := by
    intro r s
    have hg : ContMDiffAt I
        (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          y (g.inner y)) p := g.contMDiff.contMDiffAt
    have h := hg.clm_bundle_apply₂ (hframe r) (hframe s)
    simp only [contMDiffAt_totalSpace] at h
    exact h.2
  have hdet : (A p).det ≠ 0 := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have heq : A p = Matrix.gram ℝ (fun r => e r p) := by
      ext r s
      rfl
    rw [heq]
    apply Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    exact (t.isLocalFrameOn_localFrame_baseSet I ∞ b).linearIndependent hp
  have hinv : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => (A y)⁻¹ a k) p := by
    intro k
    exact contMDiffAt_matrix_inv_entry_entries hentry hdet a k
  have hsection : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (T% (metricDualSection g (frameCovector (I := I) t b a))) p := by
    apply (contMDiffAt_iff_localFrame_coeff b hp).mpr
    intro k
    have hEq :
        (fun y => (t.localFrame_coeff I b k y)
          (metricDualSection g (frameCovector (I := I) t b a) y)) =ᶠ[𝓝 p]
          (fun y => (A y)⁻¹ a k) := by
      filter_upwards [t.open_baseSet.mem_nhds hp] with y hy
      simpa [A] using
        (metricDualSection_frameCovector_coeff g t b hy a k)
    exact (hinv k).congr_of_eventuallyEq hEq
  exact hsection

/-- Differentiability corollary of
`metricDualSection_frameCovector_contMDiffAt`. -/
theorem metricDualSection_frameCovector_mdifferentiableAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {p : M} (hp : p ∈ t.baseSet)
    (a : Fin (Module.finrank ℝ E)) :
    MDiffAt (T% (metricDualSection g
      (frameCovector (I := I) t b a))) p :=
  (metricDualSection_frameCovector_contMDiffAt g t b hp a).mdifferentiableAt
    (by simp)

/-- In a local frame, the metric-dual connection has the dual-action sign
`-Γ`.  The pointwise premise records the precise differentiability used by the
metric-compatibility calculation; the canonical wrapper below discharges it
on the trivialization base set.  This is the exact sign input for a future
rank-generic frame component expansion. -/
theorem dualCovariantVector_frameCovector_apply_frame
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {p : M} (hp : p ∈ t.baseSet)
    (i j a : Fin (Module.finrank ℝ E))
    (hdual : MDiffAt
      (T% (metricDualSection g (frameCovector (I := I) t b a))) p) :
    dualCovariantVector g (t.localFrame b i)
      (frameCovector (I := I) t b a) p (t.localFrame b j p) =
      - (t.basisAt b hp).repr
        (covariantVector g (t.localFrame b i) (t.localFrame b j) p) a := by
  let e := t.localFrame b
  let eps := frameCovector (I := I) t b a
  let bp := t.basisAt b hp
  have hY : MDiffAt (T% (t.localFrame b j)) p :=
    (contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := t) (b := b) j hp).mdifferentiableAt (by simp)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := dualCovariantVector_apply_formula_at g (e i) eps (e j) p hdual hY
  have hconst : directionalDerivative (e i)
      (fun y => eps y (e j y)) p = 0 := by
    have heq : (fun y => eps y (e j y)) =ᶠ[𝓝 p]
        (fun _ : M => if a = j then 1 else 0) := by
      filter_upwards [t.open_baseSet.mem_nhds hp] with y hy
      exact frameCovector_apply_frame_of_mem (I := I) t b hy a j
    simp only [directionalDerivative, mvfderiv]
    rw [heq.mfderiv_eq, mfderiv_const]
    rfl
  have hcoeff : eps p (covariantVector g (e i) (e j) p) =
      bp.repr (covariantVector g (e i) (e j) p) a := by
    dsimp [eps, frameCovector]
    change (t.localFrame_coeff I b a p)
      (covariantVector g (e i) (e j) p) = _
    rw [t.localFrame_coeff_apply_of_mem_baseSet b hp]
    rfl
  rw [h, hconst, hcoeff]
  ring

/-- The canonical local-frame bridge with its metric-dual differentiability
premise discharged by `metricDualSection_frameCovector_mdifferentiableAt`.
The lower-level theorem above remains useful when a different local witness is
already available. -/
theorem dualCovariantVector_frameCovector_apply_frame_of_mem
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    (t : Bundle.Trivialization E
      (Bundle.TotalSpace.proj : Bundle.TotalSpace E (TangentSpace I) → M))
    [MemTrivializationAtlas t]
    (b : Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {p : M} (hp : p ∈ t.baseSet)
    (i j a : Fin (Module.finrank ℝ E)) :
    dualCovariantVector g (t.localFrame b i)
      (frameCovector (I := I) t b a) p (t.localFrame b j p) =
      - (t.basisAt b hp).repr
        (covariantVector g (t.localFrame b i) (t.localFrame b j) p) a := by
  exact dualCovariantVector_frameCovector_apply_frame g t b hp i j a
    (metricDualSection_frameCovector_mdifferentiableAt g t b hp a)

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

/-- The preceding dual-frame sign bridge combined with the canonical
Christoffel formula.  This single canonical frame-covector component
statement displays every derivative term and the inverse Gram contraction, so
a swapped direction or opposite convention cannot be hidden by notation.  The
explicit `hdual` premise records the local differentiability boundary; the
`_of_mem` wrapper below discharges it for the canonical frame. -/
theorem dualCovariantVector_frameCovector_christoffel_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j a : Fin (Module.finrank ℝ E))
    (hdual : MDiffAt
      (T% (metricDualSection g (frameCovector (I := I)
        (trivializationAt E (TangentSpace I) alpha)
        (Module.finBasis ℝ E) a))) p) :
    let t := trivializationAt E (TangentSpace I) alpha
    let b := Module.finBasis ℝ E
    let e := t.localFrame b
    let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun r s => g.inner p (e r p) (e s p)
    let gij (r s : Fin (Module.finrank ℝ E)) (y : E) :=
      let q := (extChartAt I alpha).symm y
      g.inner q (e r q) (e s q)
    dualCovariantVector g (e i) (frameCovector (I := I) t b a) p (e j p) =
      -(1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        G⁻¹ a l * (fderiv ℝ (gij l j) (extChartAt I alpha p) (b i) +
          fderiv ℝ (gij i l) (extChartAt I alpha p) (b j) -
          fderiv ℝ (gij i j) (extChartAt I alpha p) (b l)) := by
  dsimp only
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  let e := t.localFrame b
  have hdualframe := dualCovariantVector_frameCovector_apply_frame
    (I := I) (H := H) g t b hp i j a hdual
  have hchrist := covariantVector_christoffel_formula (I := I) (H := H)
      g hp hinterior i j a
  change dualCovariantVector g (e i) (frameCovector (I := I) t b a) p (e j p) = _
  rw [hdualframe]
  rw [hchrist]
  ring

/-- Canonical chart-frame component formula for the dual action.  The
metric-dual differentiability premise is discharged from the inverse-Gram
coefficient theorem, leaving only the chart-domain and interior-point
hypotheses required by the pinned Christoffel API. -/
theorem dualCovariantVector_frameCovector_christoffel_formula_of_mem
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j a : Fin (Module.finrank ℝ E)) :
    let t := trivializationAt E (TangentSpace I) alpha
    let b := Module.finBasis ℝ E
    let e := t.localFrame b
    let G : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun r s => g.inner p (e r p) (e s p)
    let gij (r s : Fin (Module.finrank ℝ E)) (y : E) :=
      let q := (extChartAt I alpha).symm y
      g.inner q (e r q) (e s q)
    dualCovariantVector g (e i) (frameCovector (I := I) t b a) p (e j p) =
      -(1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        G⁻¹ a l * (fderiv ℝ (gij l j) (extChartAt I alpha p) (b i) +
          fderiv ℝ (gij i l) (extChartAt I alpha p) (b j) -
          fderiv ℝ (gij i j) (extChartAt I alpha p) (b l)) := by
  let t := trivializationAt E (TangentSpace I) alpha
  let b := Module.finBasis ℝ E
  have hbase : p ∈ t.baseSet := by
    change p ∈ (chartAt H alpha).source
    exact hp
  exact dualCovariantVector_frameCovector_christoffel_formula
    (I := I) (H := H) g hp hinterior i j a
      (metricDualSection_frameCovector_mdifferentiableAt g t b hbase a)

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

/-- Constant-scalar linearity of the raw mixed derivative.  This law is
unconditional: `directionalDerivative_const_smul` handles the only
derivative-bearing term, and the connection-action corrections are algebraic
in the tensor evaluation. -/
theorem mixedCovariantDerivativeAlong_smul_tensor {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (X : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    mixedCovariantDerivativeAlong g X (c • A) θ Y x =
      c * mixedCovariantDerivativeAlong g X A θ Y x := by
  have hdir' := directionalDerivative_const_smul X c (A θ Y) x
  have hdir : directionalDerivative X ((c • A) θ Y) x =
      c * directionalDerivative X (A θ Y) x := by
    change directionalDerivative X (c • (A θ Y)) x = _
    exact hdir'
  simp only [mixedCovariantDerivativeAlong]
  rw [hdir]
  change c * directionalDerivative X (A θ Y) x -
      ∑ i, c * A (Function.update θ i (dualCovariantVector g X (θ i))) Y x -
      ∑ i, c * A θ (Function.update Y i (covariantVector g X (Y i))) x = _
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Constant-scalar linearity of the source-ordered second derivative in its
tensor argument.  In particular, this removes the differentiability premises
from the constant-scalar law while retaining the guarded additivity theorem
below, whose hypotheses are genuinely needed by `mvfderiv_add`. -/
theorem secondCovariantDerivativeEval_smul_tensor {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    secondCovariantDerivativeEval g (c • A) θ Y X Z x =
      c * secondCovariantDerivativeEval g A θ Y X Z x := by
  have hinner : mixedCovariantDerivativeAlong g Z (c • A) =
      c • mixedCovariantDerivativeAlong g Z A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_smul_tensor g c Z A θ' Y' y
  have houter := mixedCovariantDerivativeAlong_smul_tensor g c X
    (mixedCovariantDerivativeAlong g Z A) θ Y x
  have hcorr := mixedCovariantDerivativeAlong_smul_tensor g c
    (covariantVector g X Z) A θ Y x
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z (c • A)) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) (c • A) θ Y x) = _
  rw [hinner, houter, hcorr]
  simp only [Pi.sub_apply]
  ring

/-- The source-ordered second evaluator vanishes on the zero tensor
argument, in every pair of direction extensions.  The high-priority simp
attribute keeps this typed zero normal form ahead of the generic evaluator
application rewrite. -/
@[simp high] theorem secondCovariantDerivativeEval_zero {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Z : TangentSection (I := I) (M := M))
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    secondCovariantDerivativeEval g
      (0 : MixedTensorSection (I := I) (M := M) p q) θ Y X Z x = 0 := by
  have h := secondCovariantDerivativeEval_smul_tensor g (0 : ℝ) X Z
    (0 : MixedTensorSection (I := I) (M := M) p q) θ Y x
  simpa using h

/-- Negation commutes with the source-ordered second evaluator.  The
high-priority simp attribute keeps the normal form ahead of the generic
evaluator application rewrite. -/
@[simp high] theorem secondCovariantDerivativeEval_neg {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    secondCovariantDerivativeEval g (-A) θ Y X Z x =
      -secondCovariantDerivativeEval g A θ Y X Z x := by
  have h := secondCovariantDerivativeEval_smul_tensor g (-1 : ℝ) X Z A θ Y x
  simpa using h

/-- The rank-preserving second-derivative section inherits constant-scalar
linearity pointwise from `secondCovariantDerivativeEval_smul_tensor`. -/
theorem secondCovariantDerivative_smul_tensor {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (A : MixedTensorSection (I := I) (M := M) p q) :
    secondCovariantDerivative g (c • A) =
      c • secondCovariantDerivative g A := by
  funext θ Y x
  change secondCovariantDerivativeEval g (c • A) θ
      (fun i => Y (Fin.castSucc (Fin.castSucc i)))
      (Y (Fin.castSucc (Fin.last q)))
      (Y (Fin.last (q + 1))) x = _
  rw [secondCovariantDerivativeEval_smul_tensor]
  rfl

/-- The raw metric-trace evaluator is constant-scalar linear in the tensor
argument. The frame sum remains the provisional direct evaluator described in
the module documentation; this theorem concerns only its algebraic tensor
argument. -/
theorem connectionLaplacianEval_smul {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    connectionLaplacianEval g (c • A) θ Y x =
      c * connectionLaplacianEval g A θ Y x := by
  classical
  unfold connectionLaplacianEval
  simp_rw [secondCovariantDerivativeEval_smul_tensor]
  rw [← Finset.mul_sum]

/-- The rank-preserving raw connection Laplacian inherits constant-scalar
linearity from its metric-trace evaluator. -/
theorem connectionLaplacian_smul {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (c : ℝ) (A : MixedTensorSection (I := I) (M := M) p q) :
    connectionLaplacian g (c • A) =
      c • connectionLaplacian g A := by
  funext θ Y x
  change connectionLaplacianEval g (c • A) θ Y x =
    c * connectionLaplacianEval g A θ Y x
  exact connectionLaplacianEval_smul g c A θ Y x

/-- The direct metric-trace evaluator vanishes on the zero tensor argument. -/
@[simp] theorem connectionLaplacianEval_zero {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    connectionLaplacianEval g
      (0 : MixedTensorSection (I := I) (M := M) p q) θ Y x = 0 := by
  have h := connectionLaplacianEval_smul g (0 : ℝ)
    (0 : MixedTensorSection (I := I) (M := M) p q) θ Y x
  simpa using h

/-- Negation commutes with the direct metric-trace evaluator. -/
@[simp] theorem connectionLaplacianEval_neg {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M) :
    connectionLaplacianEval g (-A) θ Y x =
      -connectionLaplacianEval g A θ Y x := by
  have h := connectionLaplacianEval_smul g (-1 : ℝ) A θ Y x
  simpa using h

/-- The rank-preserving raw connection Laplacian vanishes on the zero
tensor argument. -/
@[simp] theorem connectionLaplacian_zero {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    connectionLaplacian g (0 : MixedTensorSection (I := I) (M := M) p q) = 0 := by
  funext θ Y x
  exact connectionLaplacianEval_zero g θ Y x

/-- Negation commutes with the rank-preserving raw connection Laplacian. -/
@[simp] theorem connectionLaplacian_neg {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q) :
    connectionLaplacian g (-A) = -connectionLaplacian g A := by
  funext θ Y x
  exact connectionLaplacianEval_neg g A θ Y x

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

/-! The split multilinearity/tensoriality predicates also imply locality in
each tensor argument.  The following two lemmas make that implication
explicit.  This is needed because the raw evaluator is a function of whole
section extensions, while `TensorialAt` only compares its direction slots. -/

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- A pointwise multilinear and tensorial evaluator cannot distinguish two
covector extensions that have the same value at the evaluation point. -/
theorem isPointwiseTensorial_covector_update_eq {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q)
    (hM : IsPointwiseMultilinear A) (hT : IsPointwiseTensorial A)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (i : Fin p) {u v : CovectorSection (I := I) (M := M)} {x : M}
    (huv : u x = v x) :
    A (Function.update θ i u) Y x = A (Function.update θ i v) Y x := by
  classical
  let δ : CovectorSection (I := I) (M := M) := u - v
  let χ : M → ℝ := fun y => if δ y = 0 then 0 else 1
  have hχδ : χ • δ = δ := by
    funext y
    by_cases h : δ y = 0 <;> simp [χ, h]
  have hδx : δ x = 0 := by
    simp [δ, huv]
  have hχx : χ x = 0 := by
    simp [χ, hδx]
  have hzero : A (Function.update θ i δ) Y x = 0 := by
    have h := (hT x).1 χ (Function.update θ i δ) Y i
    simpa [Function.update, hχδ, hχx] using h
  have h := (hM x).1 (Function.update θ i v)
    (Function.update θ i δ) Y i
  have huv' : v + δ = u := by
    funext y
    simp [δ]
  have hslot : Function.update θ i (v + δ) = Function.update θ i u := by
    rw [huv']
  simpa [Function.update, hslot, hzero, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using h

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- A pointwise multilinear and tensorial evaluator cannot distinguish two
tangent extensions that have the same value at the evaluation point. -/
theorem isPointwiseTensorial_tangent_update_eq {p q : ℕ}
    (A : MixedTensorSection (I := I) (M := M) p q)
    (hM : IsPointwiseMultilinear A) (hT : IsPointwiseTensorial A)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (i : Fin q) {u v : TangentSection (I := I) (M := M)} {x : M}
    (huv : u x = v x) :
    A θ (Function.update Y i u) x = A θ (Function.update Y i v) x := by
  classical
  let δ : TangentSection (I := I) (M := M) := u - v
  let χ : M → ℝ := fun y => if δ y = 0 then 0 else 1
  have hχδ : χ • δ = δ := by
    funext y
    by_cases h : δ y = 0 <;> simp [χ, h]
  have hδx : δ x = 0 := by
    simp [δ, huv]
  have hχx : χ x = 0 := by
    simp [χ, hδx]
  have hzero : A θ (Function.update Y i δ) x = 0 := by
    have h := (hT x).2 χ θ (Function.update Y i δ) i
    simpa [Function.update, hχδ, hχx] using h
  have h := (hM x).2.1 θ (Function.update Y i v)
    (Function.update Y i δ) i
  have huv' : v + δ = u := by
    funext y
    simp [δ]
  have hslot : Function.update Y i (v + δ) = Function.update Y i u := by
    rw [huv']
  simpa [Function.update, hslot, hzero, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using h

/-- The raw mixed derivative is independent of the first-direction extension
once the tensor evaluation is pointwise multilinear/tensorial and the two
extensions agree in the tangent fibre at the evaluation point.  No
differentiability assumption on these extensions is needed: `directionalDerivative`
and the bundled connection are both evaluated at `x`. -/
theorem mixedCovariantDerivativeAlong_eq_of_eq_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X X' : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) {x : M}
    (hM : IsPointwiseMultilinear A) (hT : IsPointwiseTensorial A)
    (hXX' : X x = X' x) :
    mixedCovariantDerivativeAlong g X A θ Y x =
      mixedCovariantDerivativeAlong g X' A θ Y x := by
  classical
  have hdir : directionalDerivative X (A θ Y) x =
      directionalDerivative X' (A θ Y) x := by
    simp [directionalDerivative, hXX']
  have hdual (i : Fin p) :
      dualCovariantVector g X (θ i) x =
        dualCovariantVector g X' (θ i) x := by
    simp [dualCovariantVector, hXX']
  have hvector (i : Fin q) :
      covariantVector g X (Y i) x = covariantVector g X' (Y i) x := by
    simp [covariantVector, hXX']
  have hsumDual :
      (∑ i, A (Function.update θ i (dualCovariantVector g X (θ i))) Y x) =
        ∑ i, A (Function.update θ i (dualCovariantVector g X' (θ i))) Y x := by
    apply Finset.sum_congr rfl
    intro i hi
    apply isPointwiseTensorial_covector_update_eq A hM hT θ Y i
    exact hdual i
  have hsumVector :
      (∑ i, A θ (Function.update Y i (covariantVector g X (Y i))) x) =
        ∑ i, A θ (Function.update Y i (covariantVector g X' (Y i))) x := by
    apply Finset.sum_congr rfl
    intro i hi
    apply isPointwiseTensorial_tangent_update_eq A hM hT θ Y i
    exact hvector i
  simp only [mixedCovariantDerivativeAlong, hdir, hsumDual, hsumVector]

/-- The outer direction of the source-ordered second derivative has the same
pointwise extension independence.  The inner direction is fixed, while the
correction field `∇_X Z` is compared at `x` using the fibrewise linearity of
the bundled Levi--Civita connection. -/
theorem secondCovariantDerivativeEval_eq_of_eq_first_direction_at {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X X' Z : TangentSection (I := I) (M := M)) {x : M}
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hZA_M : IsPointwiseMultilinear (mixedCovariantDerivativeAlong g Z A))
    (hZA_T : IsPointwiseTensorial (mixedCovariantDerivativeAlong g Z A))
    (hXX' : X x = X' x) :
    secondCovariantDerivativeEval g A θ Y X Z x =
      secondCovariantDerivativeEval g A θ Y X' Z x := by
  have houter := mixedCovariantDerivativeAlong_eq_of_eq_at g X X'
    (mixedCovariantDerivativeAlong g Z A) θ Y hZA_M hZA_T hXX'
  have hconn : covariantVector g X Z x = covariantVector g X' Z x := by
    simp [covariantVector, hXX']
  have hcorrection := mixedCovariantDerivativeAlong_eq_of_eq_at g
    (covariantVector g X Z) (covariantVector g X' Z) A θ Y hA_M hA_T hconn
  change mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g Z A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X Z) A θ Y x =
    mixedCovariantDerivativeAlong g X'
      (mixedCovariantDerivativeAlong g Z A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X' Z) A θ Y x
  rw [houter, hcorrection]

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

/-! The local-differentiability variant below exposes exactly the hypotheses
required by Mathlib's `TensorialAt.smul`.  In particular, no global
differentiability of the scalar multiplier or smoothness of the direction
extension is smuggled into the second-direction contract. -/

/-- Function-scalar linearity in the inner direction from local first-order
data.  The correction term is compared only at `x`; the earlier
`mixedCovariantDerivativeAlong_eq_of_eq_at` lemma then removes any dependence
on the chosen section extension. -/
theorem secondCovariantDerivativeEval_smul_second_direction_at_of_mdifferentiableAt
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (f : ScalarSection (M := M)) (X Z : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hZ : MDiffAt (T% Z) x) (hf : MDiffAt f x) :
    secondCovariantDerivativeEval g A θ Y X (f • Z) x =
      f x * secondCovariantDerivativeEval g A θ Y X Z x := by
  have hinner : mixedCovariantDerivativeAlong g (f • Z) A =
      f • mixedCovariantDerivativeAlong g Z A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_smul_direction_at g f Z A θ' Y' y hA_T
  have hvec : covariantVector g X (f • Z) x =
      (f • covariantVector g X Z + directionalDerivative X f • Z) x := by
    simpa [directionalDerivative] using
      (covariantVector_smul_argument_at_of_mdifferentiableAt g f X Z x hZ hf)
  have hcorrection :
      mixedCovariantDerivativeAlong g (covariantVector g X (f • Z)) A θ Y x =
        mixedCovariantDerivativeAlong g
          (f • covariantVector g X Z + directionalDerivative X f • Z) A θ Y x := by
    apply mixedCovariantDerivativeAlong_eq_of_eq_at g
      (covariantVector g X (f • Z))
      (f • covariantVector g X Z + directionalDerivative X f • Z)
      A θ Y hA_M hA_T
    exact hvec
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g (f • Z) A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X (f • Z)) A θ Y x) = _
  rw [hinner]
  rw [mixedCovariantDerivativeAlong_smul_function_at g f X
      (mixedCovariantDerivativeAlong g Z A) θ Y x hf hZA]
  rw [hcorrection]
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

/-- Additivity in the inner direction from local first-order data.  The
`IsPointwiseTensorial` hypothesis is used only to replace the correction field
by another section with the same value at `x`; the smooth-section theorem
`secondCovariantDerivativeEval_add_second_direction_at` remains available for
callers that can provide a global extension. -/
theorem secondCovariantDerivativeEval_add_second_direction_at_of_mdifferentiableAt
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (X Z Z' : TangentSection (I := I) (M := M))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M)) (x : M)
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hZA : MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x)
    (hZA' : MDiffAt (mixedCovariantDerivativeAlong g Z' A θ Y) x)
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x) :
    secondCovariantDerivativeEval g A θ Y X (Z + Z') x =
      secondCovariantDerivativeEval g A θ Y X Z x +
        secondCovariantDerivativeEval g A θ Y X Z' x := by
  have hinner : mixedCovariantDerivativeAlong g (Z + Z') A =
      mixedCovariantDerivativeAlong g Z A +
        mixedCovariantDerivativeAlong g Z' A := by
    funext θ' Y' y
    exact mixedCovariantDerivativeAlong_add_direction_at g Z Z' A θ' Y' y hA_M
  have hconn : covariantVector g X (Z + Z') x =
      (covariantVector g X Z + covariantVector g X Z') x := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have h := (leviCivitaConnection g).isCovariantDerivativeOn.add
      hZ hZ' (x := x)
    have h' := congrArg (fun L => L (X x)) h
    simpa [covariantVector] using h'
  have hcorrection :
      mixedCovariantDerivativeAlong g (covariantVector g X (Z + Z')) A θ Y x =
        mixedCovariantDerivativeAlong g
          (covariantVector g X Z + covariantVector g X Z') A θ Y x := by
    apply mixedCovariantDerivativeAlong_eq_of_eq_at g
      (covariantVector g X (Z + Z'))
      (covariantVector g X Z + covariantVector g X Z')
      A θ Y hA_M hA_T
    exact hconn
  unfold secondCovariantDerivativeEval
  change (mixedCovariantDerivativeAlong g X
      (mixedCovariantDerivativeAlong g (Z + Z') A) θ Y x -
      mixedCovariantDerivativeAlong g (covariantVector g X (Z + Z')) A θ Y x) = _
  rw [hinner]
  rw [mixedCovariantDerivativeAlong_add_tensor_at g X
      (mixedCovariantDerivativeAlong g Z A)
      (mixedCovariantDerivativeAlong g Z' A) θ Y x hZA hZA']
  rw [hcorrection]
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

/-- Package the canonical inner-direction laws under the local regularity
contract expected from a future smooth tensor producer.  The contract says
that every differentiable inner-direction extension yields a differentiable
first covariant derivative at `x`; no global smoothness or hidden tensor-bundle
instance is assumed here. -/
theorem secondCovariantDerivativeEval_second_direction_tensorialAt_of_regular
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X : TangentSection (I := I) (M := M)) {x : M}
    (hA_M : IsPointwiseMultilinear A)
    (hA_T : IsPointwiseTensorial A)
    (hregular : ∀ {Z : TangentSection (I := I) (M := M)},
      MDiffAt (T% Z) x →
        MDiffAt (mixedCovariantDerivativeAlong g Z A θ Y) x) :
    TensorialAt I E (fun Z => secondCovariantDerivativeEval g A θ Y X Z x) x := by
  apply secondCovariantDerivativeEval_second_direction_tensorialAt_of_laws
  · intro f Z hf hZ
    exact secondCovariantDerivativeEval_smul_second_direction_at_of_mdifferentiableAt
      g f X Z A θ Y x hA_M hA_T (hregular hZ) hZ hf
  · intro Z Z' hZ hZ'
    exact secondCovariantDerivativeEval_add_second_direction_at_of_mdifferentiableAt
      g X Z Z' A θ Y x hA_M hA_T (hregular hZ) (hregular hZ') hZ hZ'

/-- Equal locally differentiable inner-direction extensions have the same
second-derivative evaluation once the local `TensorialAt` witness is available.
This is the pointwise locality adapter used by frame/trace consumers. -/
theorem secondCovariantDerivativeEval_eq_of_eq_second_direction_at
    {p q : ℕ}
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (A : MixedTensorSection (I := I) (M := M) p q)
    (θ : Fin p → CovectorSection (I := I) (M := M))
    (Y : Fin q → TangentSection (I := I) (M := M))
    (X : TangentSection (I := I) (M := M)) {x : M}
    (hsecond : TensorialAt I E
      (fun Z => secondCovariantDerivativeEval g A θ Y X Z x) x)
    {Z Z' : TangentSection (I := I) (M := M)}
    (hZ : MDiffAt (T% Z) x) (hZ' : MDiffAt (T% Z') x)
    (hZZ' : Z x = Z' x) :
    secondCovariantDerivativeEval g A θ Y X Z x =
      secondCovariantDerivativeEval g A θ Y X Z' x := by
  exact hsecond.pointwise hZ hZ' hZZ'

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
