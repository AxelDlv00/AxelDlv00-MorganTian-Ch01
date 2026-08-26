import MorganTianLib.Ch01.Geodesic
import MorganTianLib.Ch01.Curvature.Tensoriality

/-!
# Intrinsic Jacobi fields

This module fixes the Chapter 1 Jacobi contract.  A field along a geodesic is
represented by a dependent tangent-valued function; its two covariant
derivatives are read in the canonical chart at the current foot and then
transported back to that tangent fibre.  The chart expression is an
implementation detail of the derivative predicate; the few coordinate
expressions needed to construct certificates are available under the stable
`Jacobi.Internal` namespace, while the exported field, curvature, and
conjugacy declarations are intrinsic.

The curvature slots follow Morgan--Tian's convention
`R X Y Z = nabla_X (nabla_Y Z) - nabla_Y (nabla_X Z) - nabla_[X,Y] Z`.
Consequently the Jacobi equation is the source-ordered equation
`D_t (D_t J) + R(J, gamma') gamma' = 0`, rather than the reversed
`R(gamma', J) gamma'` form.  The interval-relative regularity and endpoint
conditions are deliberately visible because `deriv` is totalized.

The local chart predicate is a differential certificate: chart transfer and
ODE existence are not hidden behind an unproved declaration.  A
`GeodesicVariation` records
the mixed-derivative/curvature commutation certificate explicitly, so its
bridge theorem consumes that certificate rather than claiming that smoothness
alone has already supplied the variation-to-Jacobi proof.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, pp. 43--44,
especially the geodesic-family/Jacobi equation and Definition 1.19
(`morganTian2007`).  The covariant-derivative order is aligned with Mathlib's
`CovariantDerivative`, `tangentCoordChange`, `HasDerivWithinAt`, and
Picard--Lindelof/ODE APIs; do Carmo, Chapter 5, pp. 101--121
(`doCarmo1992`) is the cross-check.
-/

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace MorganTianLib
namespace Ch01
namespace Jacobi

/-! ### Stable coordinate certificate adapters

The moving-foot formulas below are intentionally exposed through this small
`Internal` namespace.  The source-facing predicates quantify over the chart,
but their elaborated types must still name stable declarations so downstream
proofs can construct and rewrite certificates without depending on generated
`private` names. -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-! ## Fields along a curve -/

/-- A tangent-valued field along a curve.  The dependent codomain is what
prevents a field from silently changing its foot point. -/
abbrev FieldAlong (γ : ℝ → M) := ∀ t : ℝ, TangentSpace I (γ t)

/-- The coordinate of a tangent field in the canonical chart at its current
foot.  This helper is private to the moving-foot differential formulas below. -/
private def selfCoord (γ : ℝ → M) (J : FieldAlong (I := I) γ) (t : ℝ) : E :=
  (trivializationAt E (TangentSpace I) (γ t)
    (⟨γ t, J t⟩ : TangentBundle I M)).2

/-- The coordinate velocity in the canonical chart at the current foot. -/
private def selfVelocity (γ : ℝ → M) (t : ℝ) : E :=
  deriv (Geodesic.chartReading (I := I) (γ t) γ) t

/-- The tangent-valued velocity used in the intrinsic curvature term.  It is
the inverse trivialization of the chart derivative, so it has the same
moving-foot convention as `Geodesic.covariantAcceleration`. -/
noncomputable def velocity
    (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  (trivializationAt E (TangentSpace I) (γ t)).symmL ℝ (γ t)
    (selfVelocity (I := I) γ t)

/-! ## The source-ordered curvature producer -/

/- The producer itself belongs to `Ch01.Curvature`; this local spelling keeps
the Jacobi equations readable without introducing a second connection or
metric instance. -/
private noncomputable def curvature
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (X Y Z : TangentSpace I p) : TangentSpace I p :=
  Curvature.curvature g p X Y Z

/-! ## Covariant derivatives along a curve -/

namespace Internal

/-- Read a tangent field in the chart at `α`, after expressing it in the
current-foot trivialization.  This is the stable coordinate function used by
the public derivative certificates; chart choice remains existential in those
certificates. -/
def fieldCoord (α : M) (γ : ℝ → M)
    (J : FieldAlong (I := I) γ) : ℝ → E :=
  fun t =>
    tangentCoordChange I (γ t) α (γ t)
      (selfCoord (I := I) γ J t)

end Internal

open Internal

omit [FiniteDimensional ℝ E] in
private lemma selfCoord_zero (γ : ℝ → M) (t : ℝ) :
    selfCoord (I := I) γ (fun _ => 0) t = 0 := by
  let tr := trivializationAt E (TangentSpace I) (γ t)
  have hbase : γ t ∈ tr.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  change (tr ⟨γ t, (0 : TangentSpace I (γ t))⟩).2 = 0
  rw [← tr.continuousLinearMapAt_apply_of_mem ℝ hbase]
  exact (tr.continuousLinearMapAt ℝ (γ t)).map_zero

omit [FiniteDimensional ℝ E] in
private lemma selfCoord_add (γ : ℝ → M) (J K : FieldAlong (I := I) γ) (t : ℝ) :
    selfCoord (I := I) γ (fun s => J s + K s) t =
      selfCoord (I := I) γ J t + selfCoord (I := I) γ K t := by
  let tr := trivializationAt E (TangentSpace I) (γ t)
  have hbase : γ t ∈ tr.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  change (tr ⟨γ t, J t + K t⟩).2 =
    (tr ⟨γ t, J t⟩).2 + (tr ⟨γ t, K t⟩).2
  rw [← tr.continuousLinearMapAt_apply_of_mem ℝ hbase,
    ← tr.continuousLinearMapAt_apply_of_mem ℝ hbase,
    ← tr.continuousLinearMapAt_apply_of_mem ℝ hbase]
  rw [map_add]

omit [FiniteDimensional ℝ E] in
private lemma selfCoord_smul (c : ℝ) (γ : ℝ → M)
    (J : FieldAlong (I := I) γ) (t : ℝ) :
    selfCoord (I := I) γ (fun s => c • J s) t =
      c • selfCoord (I := I) γ J t := by
  let tr := trivializationAt E (TangentSpace I) (γ t)
  have hbase : γ t ∈ tr.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  change (tr ⟨γ t, c • J t⟩).2 = c • (tr ⟨γ t, J t⟩).2
  rw [← tr.continuousLinearMapAt_apply_of_mem ℝ hbase,
    ← tr.continuousLinearMapAt_apply_of_mem ℝ hbase]
  rw [map_smul]

omit [FiniteDimensional ℝ E] in
@[simp] private lemma fieldCoord_zero (α : M) (γ : ℝ → M) (t : ℝ) :
    fieldCoord (I := I) α γ (fun _ => 0) t = 0 := by
  simp only [fieldCoord, selfCoord_zero, map_zero]

omit [FiniteDimensional ℝ E] in
private lemma fieldCoord_zero_fun (α : M) (γ : ℝ → M) :
    fieldCoord (I := I) α γ (fun _ => 0) = (fun _ => 0) := by
  funext t
  exact fieldCoord_zero (I := I) α γ t

omit [FiniteDimensional ℝ E] in
private lemma fieldCoord_add (α : M) (γ : ℝ → M)
    (J K : FieldAlong (I := I) γ) (t : ℝ) :
    fieldCoord (I := I) α γ (fun s => J s + K s) t =
      fieldCoord (I := I) α γ J t + fieldCoord (I := I) α γ K t := by
  simp only [fieldCoord, selfCoord_add, map_add]

omit [FiniteDimensional ℝ E] in
private lemma fieldCoord_smul (c : ℝ) (α : M) (γ : ℝ → M)
    (J : FieldAlong (I := I) γ) (t : ℝ) :
    fieldCoord (I := I) α γ (fun s => c • J s) t =
      c • fieldCoord (I := I) α γ J t := by
  simp only [fieldCoord, selfCoord_smul, map_smul]

private lemma chartConnectionContraction_right_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (y v : E) :
    Geodesic.chartConnectionContraction (I := I) g α y v 0 = 0 := by
  classical
  simp [Geodesic.chartConnectionContraction]

private lemma chartConnectionContraction_left_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (y v : E) :
    Geodesic.chartConnectionContraction (I := I) g α y 0 v = 0 := by
  classical
  simp [Geodesic.chartConnectionContraction]

private lemma chartConnectionContraction_add_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (y v w z : E) :
    Geodesic.chartConnectionContraction (I := I) g α y v (w + z) =
      Geodesic.chartConnectionContraction (I := I) g α y v w +
        Geodesic.chartConnectionContraction (I := I) g α y v z := by
  classical
  unfold Geodesic.chartConnectionContraction
  simp_rw [(Module.finBasis ℝ E).repr.map_add]
  simp only [Finsupp.add_apply]
  ring_nf
  simp only [Finset.sum_add_distrib, add_smul]

private lemma chartConnectionContraction_smul_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (y v w : E) (c : ℝ) :
    Geodesic.chartConnectionContraction (I := I) g α y v (c • w) =
      c • Geodesic.chartConnectionContraction (I := I) g α y v w := by
  classical
  unfold Geodesic.chartConnectionContraction
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [(Module.finBasis ℝ E).repr.map_smul]
  simp only [Finsupp.smul_apply]
  ring

/-- Stable coordinate expression for the first covariant derivative along a
curve.  This declaration is public only as an implementation-facing
certificate adapter; the chart itself remains an existential witness in
`HasCovariantDerivativeAlongAt`. -/
def Internal.covariantDerivativeCoord
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (t : ℝ) : E :=
  fieldCoord (I := I) α γ DJ t -
    Geodesic.chartConnectionContraction (I := I) g α
      (Geodesic.chartReading (I := I) α γ t)
      (deriv (Geodesic.chartReading (I := I) α γ) t)
      (fieldCoord (I := I) α γ J t)

/-- Stable coordinate expression for the source-ordered curvature term in the
second covariant derivative certificate. -/
def Internal.curvatureCoord
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M) (J V W : FieldAlong (I := I) γ) (t : ℝ) : E :=
  fieldCoord (I := I) α γ
    (fun s => curvature (I := I) g (γ s) (J s) (V s) (W s)) t

private lemma covariantDerivativeCoord_add
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M)
    (J₁ DJ₁ J₂ DJ₂ : FieldAlong (I := I) γ) (t : ℝ) :
    covariantDerivativeCoord (I := I) g α γ
        (fun s => J₁ s + J₂ s) (fun s => DJ₁ s + DJ₂ s) t =
      covariantDerivativeCoord (I := I) g α γ J₁ DJ₁ t +
        covariantDerivativeCoord (I := I) g α γ J₂ DJ₂ t := by
  unfold covariantDerivativeCoord
  rw [fieldCoord_add, fieldCoord_add,
    chartConnectionContraction_add_right]
  abel

private lemma curvatureCoord_add_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M)
    (J₁ J₂ V W : FieldAlong (I := I) γ) (t : ℝ) :
    curvatureCoord (I := I) g α γ (fun s => J₁ s + J₂ s) V W t =
      curvatureCoord (I := I) g α γ J₁ V W t +
        curvatureCoord (I := I) g α γ J₂ V W t := by
  have hfield :
      (fun s : ℝ => curvature (I := I) g (γ s) (J₁ s + J₂ s)
        (V s) (W s)) =
        (fun s : ℝ => curvature (I := I) g (γ s) (J₁ s) (V s) (W s) +
          curvature (I := I) g (γ s) (J₂ s) (V s) (W s)) := by
    funext s
    exact Curvature.Tensoriality.curvature_add_first (g := g) (p := γ s)
      (X := J₁ s) (Y := J₂ s) (Z := V s) (W := W s)
  unfold curvatureCoord
  rw [hfield, fieldCoord_add]

private lemma curvatureCoord_smul_left
    (c : ℝ) (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M)
    (J V W : FieldAlong (I := I) γ) (t : ℝ) :
    curvatureCoord (I := I) g α γ (fun s => c • J s) V W t =
      c • curvatureCoord (I := I) g α γ J V W t := by
  have hfield :
      (fun s : ℝ => curvature (I := I) g (γ s) (c • J s) (V s) (W s)) =
        (fun s : ℝ => c • curvature (I := I) g (γ s) (J s) (V s) (W s)) := by
    funext s
    change Curvature.curvature (I := I) g (γ s) (c • J s) (V s) (W s) =
      c • Curvature.curvature (I := I) g (γ s) (J s) (V s) (W s)
    exact Curvature.Tensoriality.curvature_smul_first (g := g) (p := γ s)
      (c := c) (X := J s) (Y := V s) (W := W s)
  unfold curvatureCoord
  rw [hfield, fieldCoord_smul]

private lemma covariantDerivativeCoord_smul
    (c : ℝ) (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M)
    (J DJ : FieldAlong (I := I) γ) (t : ℝ) :
    covariantDerivativeCoord (I := I) g α γ
        (fun s => c • J s) (fun s => c • DJ s) t =
      c • covariantDerivativeCoord (I := I) g α γ J DJ t := by
  unfold covariantDerivativeCoord
  rw [fieldCoord_smul, fieldCoord_smul,
    chartConnectionContraction_smul_right]
  module

/-- `HasCovariantDerivativeAlongAt` is the interval-relative first covariant
derivative of a tangent field.  The chart `alpha` is existential and local,
so the public predicate does not expose a chart choice.  It is an opaque
coordinate certificate; `IsJacobiFieldOnAt` and `IsJacobiFieldAlongOn` provide
the fixed-chart and source-constrained local-window interfaces. -/
def HasCovariantDerivativeAlongAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
  (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ)
    (a b t : ℝ) : Prop :=
  ∃ α : M,
    HasDerivWithinAt (Internal.fieldCoord (I := I) α γ J)
      (Internal.covariantDerivativeCoord (I := I) g α γ J DJ t) (Icc a b) t

/-- The Jacobi-equation second-derivative certificate in a local chart.

The displayed derivative is the equation's right-hand side, so this predicate
records the required second covariant derivative rather than introducing a
separate, unconnected `D^2 J` field. -/
def HasSecondCovariantDerivativeAlongAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
  (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ)
    (a b t : ℝ) : Prop :=
  ∃ α : M,
    HasDerivWithinAt (Internal.fieldCoord (I := I) α γ DJ)
      (-Internal.curvatureCoord (I := I) g α γ J
        (velocity (I := I) γ) (velocity (I := I) γ) t -
        Geodesic.chartConnectionContraction (I := I) g α
          (Geodesic.chartReading (I := I) α γ t)
          (deriv (Geodesic.chartReading (I := I) α γ) t)
          (Internal.fieldCoord (I := I) α γ DJ t)) (Icc a b) t

/-- The local Jacobi-equation certificate on `[a,b]`.  The two derivative
clauses make the order `D_t(D_t J)` explicit and keep endpoint hypotheses
visible; source confinement is supplied by `IsJacobiFieldOnAt`. -/
def IsJacobiFieldOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b, HasCovariantDerivativeAlongAt (I := I) g γ J DJ a b t) ∧
    (∀ t ∈ Icc a b,
      HasSecondCovariantDerivativeAlongAt (I := I) g γ J DJ a b t)

/-- A fixed-chart version of the Jacobi coordinate certificate.  This is the
form used by `IsJacobiFieldAlongOn`, which adds the chart-source premise; both
derivative clauses refer to the same `alpha`, so a local window cannot be
witnessed by unrelated totalized coordinate choices. -/
def IsJacobiFieldOnAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
  (α : M) (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a b : ℝ) : Prop :=
  (∀ t ∈ Icc a b,
      HasDerivWithinAt (Internal.fieldCoord (I := I) α γ J)
        (Internal.covariantDerivativeCoord (I := I) g α γ J DJ t) (Icc a b) t) ∧
    (∀ t ∈ Icc a b,
      HasDerivWithinAt (Internal.fieldCoord (I := I) α γ DJ)
        (-Internal.curvatureCoord (I := I) g α γ J
          (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            (Internal.fieldCoord (I := I) α γ DJ t)) (Icc a b) t)

/-- Restrict a fixed-chart certificate to a smaller interval. -/
theorem IsJacobiFieldOnAt.mono
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b c d : ℝ}
    (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b)
    (hcd : Icc c d ⊆ Icc a b) :
    IsJacobiFieldOnAt (I := I) g α γ J DJ c d := by
  constructor
  · intro t ht
    exact (h.1 t (hcd ht)).mono hcd
  · intro t ht
    exact (h.2 t (hcd ht)).mono hcd

/-- A fixed-chart certificate is also an existential-chart certificate. -/
theorem IsJacobiFieldOnAt.toIsJacobiFieldOn
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b) :
    IsJacobiFieldOn (I := I) g γ J DJ a b := by
  constructor
  · intro t ht
    exact ⟨α, h.1 t ht⟩
  · intro t ht
    exact ⟨α, h.2 t ht⟩

/-- Superposition for fixed-chart Jacobi certificates.  The common chart is
kept explicit so no chart-transfer theorem is smuggled into the statement. -/
theorem IsJacobiFieldOnAt.add
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M}
    {J₁ DJ₁ J₂ DJ₂ : FieldAlong (I := I) γ} {a b : ℝ}
    (h₁ : IsJacobiFieldOnAt (I := I) g α γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldOnAt (I := I) g α γ J₂ DJ₂ a b) :
    IsJacobiFieldOnAt (I := I) g α γ
      (fun t => J₁ t + J₂ t) (fun t => DJ₁ t + DJ₂ t) a b := by
  constructor
  · intro t ht
    have hd := (h₁.1 t ht).add (h₂.1 t ht)
    have hfield :
        fieldCoord (I := I) α γ (fun s => J₁ s + J₂ s) =
          fieldCoord (I := I) α γ J₁ + fieldCoord (I := I) α γ J₂ := by
      funext s
      exact fieldCoord_add (I := I) α γ J₁ J₂ s
    rw [hfield, covariantDerivativeCoord_add]
    exact hd
  · intro t ht
    have hd := (h₁.2 t ht).add (h₂.2 t ht)
    have hfield :
        fieldCoord (I := I) α γ (fun s => DJ₁ s + DJ₂ s) =
          fieldCoord (I := I) α γ DJ₁ + fieldCoord (I := I) α γ DJ₂ := by
      funext s
      exact fieldCoord_add (I := I) α γ DJ₁ DJ₂ s
    have hrhs :
        (-curvatureCoord (I := I) g α γ J₁
            (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            (fieldCoord (I := I) α γ DJ₁ t)) +
        (-curvatureCoord (I := I) g α γ J₂
            (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            (fieldCoord (I := I) α γ DJ₂ t)) =
        -curvatureCoord (I := I) g α γ (fun s => J₁ s + J₂ s)
            (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            ((fieldCoord (I := I) α γ DJ₁ +
              fieldCoord (I := I) α γ DJ₂) t) := by
      rw [curvatureCoord_add_left]
      change _ = _ - Geodesic.chartConnectionContraction (I := I) g α
        (Geodesic.chartReading (I := I) α γ t)
        (deriv (Geodesic.chartReading (I := I) α γ) t)
        (fieldCoord (I := I) α γ DJ₁ t + fieldCoord (I := I) α γ DJ₂ t)
      rw [chartConnectionContraction_add_right]
      abel
    rw [hfield, ← hrhs]
    exact hd

/-- Scalar multiplication for fixed-chart Jacobi certificates. -/
theorem IsJacobiFieldOnAt.const_smul
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (c : ℝ) (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b) :
    IsJacobiFieldOnAt (I := I) g α γ
      (fun t => c • J t) (fun t => c • DJ t) a b := by
  constructor
  · intro t ht
    have hd := (h.1 t ht).const_smul c
    have hfield :
        fieldCoord (I := I) α γ (fun s => c • J s) =
          c • fieldCoord (I := I) α γ J := by
      funext s
      simpa only [Pi.smul_apply] using
        (fieldCoord_smul (I := I) c α γ J s)
    rw [hfield, covariantDerivativeCoord_smul]
    exact hd
  · intro t ht
    have hd := (h.2 t ht).const_smul c
    have hfield :
        fieldCoord (I := I) α γ (fun s => c • DJ s) =
          c • fieldCoord (I := I) α γ DJ := by
      funext s
      simpa only [Pi.smul_apply] using
        (fieldCoord_smul (I := I) c α γ DJ s)
    have hrhs :
        c • (-curvatureCoord (I := I) g α γ J
            (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            (fieldCoord (I := I) α γ DJ t)) =
        -curvatureCoord (I := I) g α γ (fun s => c • J s)
            (velocity (I := I) γ) (velocity (I := I) γ) t -
          Geodesic.chartConnectionContraction (I := I) g α
            (Geodesic.chartReading (I := I) α γ t)
            (deriv (Geodesic.chartReading (I := I) α γ) t)
            ((c • fieldCoord (I := I) α γ DJ) t) := by
      simp only [Pi.smul_apply]
      rw [curvatureCoord_smul_left,
        chartConnectionContraction_smul_right]
      module
    rw [hfield, ← hrhs]
    exact hd

/-- The zero pair is a fixed-chart Jacobi certificate on every interval. -/
theorem isJacobiFieldOnAt_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (α : M) (γ : ℝ → M) (a b : ℝ) :
    IsJacobiFieldOnAt (I := I) g α γ (fun _ => 0) (fun _ => 0) a b := by
  constructor
  · intro t ht
    rw [fieldCoord_zero_fun (I := I) α γ]
    simp [covariantDerivativeCoord, chartConnectionContraction_right_zero]
    exact hasDerivWithinAt_const t (Icc a b) (0 : E)
  · intro t ht
    have hcurv : ∀ s : ℝ, curvature (I := I) g (γ s) 0
        (velocity (I := I) γ s) (velocity (I := I) γ s) = 0 := by
      intro s
      change Curvature.curvature (I := I) g (γ s) 0
        (velocity (I := I) γ s) (velocity (I := I) γ s) = 0
      simpa using (Curvature.Tensoriality.curvature_smul_first (g := g) (p := γ s)
        (c := (0 : ℝ)) (X := velocity (I := I) γ s)
        (Y := velocity (I := I) γ s) (W := velocity (I := I) γ s))
    have hcurv_field :
        (fun s : ℝ => curvature (I := I) g (γ s) 0
          (velocity (I := I) γ s) (velocity (I := I) γ s)) = (fun _ => 0) := by
      funext s
      exact hcurv s
    rw [fieldCoord_zero_fun (I := I) α γ]
    simp [curvatureCoord, hcurv_field,
      chartConnectionContraction_right_zero]
    exact hasDerivWithinAt_const t (Icc a b) (0 : E)

/-- Public existential-chart view of fixed-chart superposition. -/
theorem IsJacobiFieldOn.add_of_fixed_chart
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M}
    {J₁ DJ₁ J₂ DJ₂ : FieldAlong (I := I) γ} {a b : ℝ}
    (h₁ : IsJacobiFieldOnAt (I := I) g α γ J₁ DJ₁ a b)
    (h₂ : IsJacobiFieldOnAt (I := I) g α γ J₂ DJ₂ a b) :
    IsJacobiFieldOn (I := I) g γ
      (fun t => J₁ t + J₂ t) (fun t => DJ₁ t + DJ₂ t) a b :=
  IsJacobiFieldOnAt.toIsJacobiFieldOn (IsJacobiFieldOnAt.add h₁ h₂)

/-- Public existential-chart view of fixed-chart scalar multiplication. -/
theorem IsJacobiFieldOn.const_smul_of_fixed_chart
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (c : ℝ) (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b) :
    IsJacobiFieldOn (I := I) g γ
      (fun t => c • J t) (fun t => c • DJ t) a b :=
  IsJacobiFieldOnAt.toIsJacobiFieldOn (IsJacobiFieldOnAt.const_smul c h)

/-- The two local derivative clauses at one time, named separately so later
consumers can state the Jacobi equation without unpacking the interval
predicate. -/
def HasJacobiEquationAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ)
    (a b t : ℝ) : Prop :=
  HasCovariantDerivativeAlongAt (I := I) g γ J DJ a b t ∧
    HasSecondCovariantDerivativeAlongAt (I := I) g γ J DJ a b t

/-- Pointwise unpacking of the two clauses in `IsJacobiFieldOn`. -/
theorem isJacobiFieldOn_iff_hasJacobiEquationAt
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ} :
    IsJacobiFieldOn (I := I) g γ J DJ a b ↔
      ∀ t ∈ Icc a b, HasJacobiEquationAt (I := I) g γ J DJ a b t := by
  constructor
  · rintro ⟨h₁, h₂⟩ t ht
    exact ⟨h₁ t ht, h₂ t ht⟩
  · intro h
    constructor
    · intro t ht
      exact (h t ht).1
    · intro t ht
      exact (h t ht).2

/-- The first covariant derivative clause of a Jacobi field. -/
theorem IsJacobiFieldOn.hasCovariantDerivative
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b t : ℝ}
    (h : IsJacobiFieldOn (I := I) g γ J DJ a b) (ht : t ∈ Icc a b) :
    HasCovariantDerivativeAlongAt (I := I) g γ J DJ a b t :=
  h.1 t ht

/-- The second covariant derivative clause of a Jacobi field. -/
theorem IsJacobiFieldOn.hasSecondCovariantDerivative
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b t : ℝ}
    (h : IsJacobiFieldOn (I := I) g γ J DJ a b) (ht : t ∈ Icc a b) :
    HasSecondCovariantDerivativeAlongAt (I := I) g γ J DJ a b t :=
  h.2 t ht

/-! ## Elementary field operations -/

/-- The zero field is a Jacobi field on every interval. -/
theorem isJacobiFieldOn_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (a b : ℝ) :
    IsJacobiFieldOn (I := I) g γ (fun _ => 0) (fun _ => 0) a b := by
  constructor
  · intro t ht
    refine ⟨γ t, ?_⟩
    rw [fieldCoord_zero_fun (I := I) (γ t) γ]
    simp [covariantDerivativeCoord, chartConnectionContraction_right_zero]
    exact hasDerivWithinAt_const t (Icc a b) (0 : E)
  · intro t ht
    refine ⟨γ t, ?_⟩
    have hcurv : ∀ s : ℝ, curvature (I := I) g (γ s) 0
        (velocity (I := I) γ s) (velocity (I := I) γ s) = 0 := by
      intro s
      change Curvature.curvature (I := I) g (γ s) 0
        (velocity (I := I) γ s) (velocity (I := I) γ s) = 0
      simpa using (Curvature.Tensoriality.curvature_smul_first (g := g) (p := γ s)
        (c := (0 : ℝ)) (X := velocity (I := I) γ s)
        (Y := velocity (I := I) γ s) (W := velocity (I := I) γ s))
    have hcurv_field : (fun s : ℝ => curvature (I := I) g (γ s) 0
        (velocity (I := I) γ s) (velocity (I := I) γ s)) = (fun _ => 0) := by
      funext s
      exact hcurv s
    rw [fieldCoord_zero_fun (I := I) (γ t) γ]
    simp [curvatureCoord, hcurv_field,
      chartConnectionContraction_right_zero]
    exact hasDerivWithinAt_const t (Icc a b) (0 : E)

/-- Euclidean affine-field regression on a constant geodesic.

On the model manifold the preferred tangent trivialization and coordinate
change are identities.  Thus an affine field has constant first derivative,
zero second derivative, and the curvature term is evaluated at zero velocity.
This is a coordinate-level regression for the intrinsic contract, not a
claim about arbitrary manifolds. -/
theorem isJacobiFieldOn_euclidean_affine
    (g : Bundle.ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E
      (TangentSpace (𝓘(ℝ, E)) : E → Type _))
    (p u w : E) (a b : ℝ) :
    IsJacobiFieldOn (I := 𝓘(ℝ, E)) g
      (fun _ : ℝ => p) (fun t => u + t • w) (fun _ => w) a b := by
  have hconst (s : ℝ) :
      HasDerivAt (Geodesic.chartReading (I := 𝓘(ℝ, E)) p (fun _ : ℝ => p))
        0 s := by
    change HasDerivAt (fun _ : ℝ => extChartAt (𝓘(ℝ, E)) p p) 0 s
    exact hasDerivAt_const (x := s) (c := extChartAt (𝓘(ℝ, E)) p p)
  have hderiv :
      deriv (Geodesic.chartReading (I := 𝓘(ℝ, E)) p (fun _ : ℝ => p)) =
        (fun _ : ℝ => (0 : E)) := by
    funext s
    exact (hconst s).deriv
  have hfield :
      fieldCoord (I := 𝓘(ℝ, E)) p (fun _ : ℝ => p)
          (fun t => u + t • w) = (fun t => u + t • w) := by
    funext s
    simp [fieldCoord, selfCoord, tangentCoordChange]
  have hfieldD :
      fieldCoord (I := 𝓘(ℝ, E)) p (fun _ : ℝ => p)
          (fun _ => w) = (fun _ : ℝ => w) := by
    funext s
    simp [fieldCoord, selfCoord, tangentCoordChange]
  have hvel : velocity (I := 𝓘(ℝ, E)) (fun _ : ℝ => p) =
      (fun _ : ℝ => (0 : TangentSpace (𝓘(ℝ, E)) p)) := by
    funext s
    simp [velocity, selfVelocity, hderiv]
  constructor
  · intro t ht
    refine ⟨p, ?_⟩
    unfold covariantDerivativeCoord
    rw [hfieldD, hfield, hderiv]
    simp only [chartConnectionContraction_left_zero, sub_zero]
    simpa only [id, one_smul] using
      ((hasDerivWithinAt_id t (Icc a b)).smul_const w).const_add u
  · intro t ht
    refine ⟨p, ?_⟩
    unfold curvatureCoord
    rw [hfieldD, hvel, hderiv]
    have hcurv : ∀ x : TangentSpace (𝓘(ℝ, E)) p,
        curvature (I := 𝓘(ℝ, E)) g p x 0 0 = 0 := by
      intro x
      change Curvature.curvature (I := 𝓘(ℝ, E)) g p x 0 0 = 0
      simpa using
        (Curvature.Tensoriality.curvature_smul_second (g := g) (p := p)
          (c := (0 : ℝ)) (X := x) (Y := 0) (W := 0))
    have hcurv_field :
        (fun s : ℝ => curvature (I := 𝓘(ℝ, E)) g p
          (u + s • w) (0 : TangentSpace (𝓘(ℝ, E)) p)
          (0 : TangentSpace (𝓘(ℝ, E)) p)) = (fun _ => 0) := by
      funext s
      exact hcurv (u + s • w)
    rw [hcurv_field, fieldCoord_zero_fun]
    simp only [chartConnectionContraction_left_zero, neg_zero, sub_zero]
    exact hasDerivWithinAt_const t (Icc a b) w

/-- Restriction to a subinterval preserves a Jacobi certificate. -/
theorem IsJacobiFieldOn.mono
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b c d : ℝ}
    (h : IsJacobiFieldOn (I := I) g γ J DJ a b)
    (hcd : Icc c d ⊆ Icc a b) :
    IsJacobiFieldOn (I := I) g γ J DJ c d := by
  constructor
  · intro t ht
    rcases h.1 t (hcd ht) with ⟨α, hderiv⟩
    exact ⟨α, hderiv.mono hcd⟩
  · intro t ht
    rcases h.2 t (hcd ht) with ⟨α, hderiv⟩
    exact ⟨α, hderiv.mono hcd⟩

/-! ## Initial data and geodesic variations -/

/-- The ordered initial data of a field and its covariant first derivative.

The two entries live in the same dependent tangent fibre, so this map is the
linear initial-data interface used by later ODE and exponential consumers. -/
def initialData
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a : ℝ) :
    TangentSpace I (γ a) × TangentSpace I (γ a) := (J a, DJ a)

/-- The linear initial-data evaluation map for a fixed base curve and time. -/
def initialDataLinearMap
    (γ : ℝ → M) (a : ℝ) :
    (FieldAlong (I := I) γ × FieldAlong (I := I) γ) →ₗ[ℝ]
      (TangentSpace I (γ a) × TangentSpace I (γ a)) :=
  { toFun := fun X => (X.1 a, X.2 a)
    map_add' := by
      intro X Y
      rfl
    map_smul' := by
      intro c X
      rfl }

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Evaluation of `initialData` agrees with its bundled linear map. -/
theorem initialData_eq_linearMap
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a : ℝ) :
    initialData (I := I) γ J DJ a =
      initialDataLinearMap (I := I) γ a (J, DJ) := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- First projection of ordered initial data. -/
@[simp] theorem initialData_fst
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a : ℝ) :
    (initialData (I := I) γ J DJ a).1 = J a := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Second projection of ordered initial data. -/
@[simp] theorem initialData_snd
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a : ℝ) :
    (initialData (I := I) γ J DJ a).2 = DJ a := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Initial data of the zero pair. -/
@[simp] theorem initialData_zero
    (γ : ℝ → M) (a : ℝ) :
    initialData (I := I) γ (fun _ => 0) (fun _ => 0) a = (0, 0) := rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Additivity of ordered initial data. -/
theorem initialData_add
    (γ : ℝ → M) (J₁ DJ₁ J₂ DJ₂ : FieldAlong (I := I) γ) (a : ℝ) :
    initialData (I := I) γ (fun t => J₁ t + J₂ t) (fun t => DJ₁ t + DJ₂ t) a =
      initialData (I := I) γ J₁ DJ₁ a + initialData (I := I) γ J₂ DJ₂ a := by
  rfl

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Homogeneity of ordered initial data. -/
theorem initialData_smul
    (c : ℝ) (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a : ℝ) :
    initialData (I := I) γ (fun t => c • J t) (fun t => c • DJ t) a =
      c • initialData (I := I) γ J DJ a := by
  rfl

/-! ## Intrinsic windows and conjugacy -/

/-- A local intrinsic Jacobi certificate around every time in an interval.

The outer `a < b` conjunct is part of the source-facing segment contract, so
reversed or degenerate endpoints cannot be certified vacuously.  The chart,
the nondegenerate subinterval, its relative-neighborhood property, and the
chart-source confinement are all witnesses.  This is the local
(`sheaf`-style) form used when a geodesic crosses charts; the derivative
equation itself is supplied by `IsJacobiFieldOnAt` in that same chart. -/
def IsJacobiFieldAlongOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a b : ℝ) : Prop :=
  a < b ∧
    ∀ t ∈ Icc a b, ∃ (α : M) (c d : ℝ),
      c < d ∧ t ∈ Icc c d ∧ Icc c d ⊆ Icc a b ∧
      Icc c d ∈ 𝓝[Icc a b] t ∧
        (∀ s ∈ Icc c d, γ s ∈ (chartAt H α).source) ∧
        IsJacobiFieldOnAt (I := I) g α γ J DJ c d

/-- Extract the nondegeneracy invariant from a source-facing Jacobi segment. -/
theorem IsJacobiFieldAlongOn.interval_nonempty
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b) : a < b := h.1

/-- A fixed-chart certificate on the whole interval gives the intrinsic local
certificate.  The source hypothesis is explicit because the coordinate
expressions are totalized outside a chart source. -/
theorem isJacobiFieldAlongOn_of_fixed_chart
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (hab : a < b)
    (hsource : ∀ s ∈ Icc a b, γ s ∈ (chartAt H α).source)
    (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b) :
    IsJacobiFieldAlongOn (I := I) g γ J DJ a b := by
  refine ⟨hab, ?_⟩
  intro t ht
  refine ⟨α, a, b, hab, ht, subset_rfl, ?_, hsource, h⟩
  exact self_mem_nhdsWithin

/-- The geodesic and continuity hypotheses paired with a local intrinsic
Jacobi certificate.  Keeping them separate from `IsJacobiFieldAlongOn` lets
the latter serve as a reusable local differential predicate. -/
def IsGeodesicJacobiFieldOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a b : ℝ) : Prop :=
  Geodesic.isGeodesicOn (I := I) g γ (Icc a b) ∧
    ContinuousOn γ (Icc a b) ∧
    IsJacobiFieldAlongOn (I := I) g γ J DJ a b

/-- The public Jacobi-field contract on a geodesic segment.

This spelling deliberately points at the source-constrained geodesic contract,
not the existential-chart differential certificate.  The latter remains
available as `IsJacobiFieldOn` for local proof construction, while
`IsJacobiFieldAlongOn` exposes the source-safe differential layer without
requiring geodesicity.  Consequently every value certified by `JacobiField`
has a geodesic base curve, continuity, a common source-safe local window, and
the source-ordered equation. -/
abbrev JacobiField
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J DJ : FieldAlong (I := I) γ) (a b : ℝ) : Prop :=
  IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b

/-- Extract the geodesic hypothesis from a geodesic Jacobi certificate. -/
theorem IsGeodesicJacobiFieldOn.isGeodesic
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b) :
    Geodesic.isGeodesicOn (I := I) g γ (Icc a b) := h.1

/-- Extract continuity of the base curve from a geodesic Jacobi certificate. -/
theorem IsGeodesicJacobiFieldOn.continuousOn
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b) :
    ContinuousOn γ (Icc a b) := h.2.1

/-- Extract the source-constrained Jacobi certificate. -/
theorem IsGeodesicJacobiFieldOn.jacobiAlongOn
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b) :
    IsJacobiFieldAlongOn (I := I) g γ J DJ a b := h.2.2

/-- Extract the nondegenerate interval invariant from a geodesic Jacobi
certificate without unfolding its source-facing conjunction. -/
theorem IsGeodesicJacobiFieldOn.interval_nonempty
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (h : IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b) : a < b :=
  h.jacobiAlongOn.interval_nonempty

/-- Build the geodesic Jacobi contract from a source-safe fixed-chart witness. -/
theorem isGeodesicJacobiFieldOn_of_fixed_chart
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {α : M} {γ : ℝ → M} {J DJ : FieldAlong (I := I) γ} {a b : ℝ}
    (hgeo : Geodesic.isGeodesicOn (I := I) g γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a < b)
    (hsource : ∀ s ∈ Icc a b, γ s ∈ (chartAt H α).source)
    (h : IsJacobiFieldOnAt (I := I) g α γ J DJ a b) :
    IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b :=
  ⟨hgeo, hcont, isJacobiFieldAlongOn_of_fixed_chart hab hsource h⟩

/-- A smooth two-parameter family of curves together with the intrinsic
variation field and an explicit commutation certificate.

The `commutation` field is the theorem-facing bridge supplied by the
torsion-free/curvature calculation.  Keeping it as data makes the current
module honest: smoothness and the slice geodesic equations alone do not make
Lean infer that calculation. -/
structure GeodesicVariation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (a b : ℝ) where
  /-- The declared time segment is nondegenerate. -/
  interval_nonempty : a < b
  /-- The total two-parameter family, with the first parameter varying the
  geodesic and the second parameter varying time. -/
  family : ℝ → ℝ → M
  /-- Joint smoothness of the family. -/
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ (Function.uncurry family)
  /-- Every parameter slice is geodesic on the declared interval. -/
  slice_geodesic : ∀ s, Geodesic.isGeodesicOn (I := I) g
    (fun t => family s t) (Icc a b)
  /-- Continuity of every parameter slice on the declared interval. -/
  slice_continuous : ∀ s, ContinuousOn (fun t => family s t) (Icc a b)
  /-- The variational field, valued in the tangent fibre of the base slice. -/
  variationalField : FieldAlong (I := I) (fun t => family 0 t)
  /-- A chosen covariant first derivative of the variational field. -/
  covariantVariationalField : FieldAlong (I := I) (fun t => family 0 t)
  /-- The variational field is the derivative in the family parameter. -/
  variationalField_eq_mfderiv : ∀ t,
    variationalField t =
      mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => family s t) 0 (1 : ℝ)
  /-- The mixed-derivative/curvature commutation certificate. -/
  commutation : IsJacobiFieldAlongOn (I := I) g
    (fun t => family 0 t) variationalField covariantVariationalField a b

/-- The base curve of a geodesic variation. -/
def GeodesicVariation.baseCurve
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {a b : ℝ} (V : GeodesicVariation (I := I) g a b) : ℝ → M :=
  fun t => V.family 0 t

/-- Project the recorded variation field and the supplied commutation certificate
to the intrinsic geodesic/continuity/Jacobi contract.  The mixed-derivative
calculation itself is the `commutation` field of `GeodesicVariation`; this
adapter does not derive it from smoothness alone. -/
theorem GeodesicVariation.variationField_isJacobi
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {a b : ℝ} (V : GeodesicVariation (I := I) g a b) :
    IsGeodesicJacobiFieldOn (I := I) g V.baseCurve
      V.variationalField V.covariantVariationalField a b := by
  change IsGeodesicJacobiFieldOn (I := I) g
    (fun t => V.family 0 t) V.variationalField
      V.covariantVariationalField a b
  exact ⟨V.slice_geodesic 0, V.slice_continuous 0, V.commutation⟩

/-- The base slice of a geodesic variation is geodesic. -/
theorem GeodesicVariation.base_isGeodesic
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {a b : ℝ} (V : GeodesicVariation (I := I) g a b) :
    Geodesic.isGeodesicOn (I := I) g V.baseCurve (Icc a b) := by
  change Geodesic.isGeodesicOn (I := I) g
    (fun t => V.family 0 t) (Icc a b)
  exact V.slice_geodesic 0

/-- Project the local Jacobi component of a variation certificate. -/
theorem GeodesicVariation.variationField_isJacobiAlongOn
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {a b : ℝ} (V : GeodesicVariation (I := I) g a b) :
    IsJacobiFieldAlongOn (I := I) g V.baseCurve
      V.variationalField V.covariantVariationalField a b := by
  change IsJacobiFieldAlongOn (I := I) g
    (fun t => V.family 0 t) V.variationalField
      V.covariantVariationalField a b
  exact V.commutation

/-- Conjugacy on a fixed geodesic segment means that a nonzero intrinsic
Jacobi field vanishes at both endpoints.  The explicit interior witness rules
out the zero field, including degenerate or zero-dimensional tangent fibres. -/
def IsConjugate
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∃ J DJ : FieldAlong (I := I) γ,
    IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b ∧
      J a = 0 ∧ J b = 0 ∧ ∃ t ∈ Icc a b, J t ≠ 0

/-- The source's fixed-start spelling of conjugacy. -/
def IsConjugatePointAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (t₁ : ℝ) : Prop :=
  IsConjugate (I := I) g γ 0 t₁

/-- Conjugacy carries the same nondegenerate segment invariant as its Jacobi
field witness. -/
theorem IsConjugate.interval_nonempty
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {a b : ℝ}
    (h : IsConjugate (I := I) g γ a b) : a < b := by
  rcases h with ⟨J, DJ, hJ, _, _, _⟩
  exact hJ.interval_nonempty

/-- The fixed-start notation is definitionally the zero-time instance. -/
theorem isConjugatePointAt_iff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (t₁ : ℝ) :
    IsConjugatePointAt (I := I) g γ t₁ ↔ IsConjugate (I := I) g γ 0 t₁ := Iff.rfl

/-- Extract a nonzero field and a segment witness from conjugacy. -/
theorem IsConjugate.nonzero
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {a b : ℝ} (h : IsConjugate (I := I) g γ a b) :
    ∃ J : FieldAlong (I := I) γ, ∃ t ∈ Icc a b, J t ≠ 0 := by
  rcases h with ⟨J, _, _, _, _, ht, hJ⟩
  exact ⟨J, ht, hJ⟩

/-- The nonzero witness is genuinely interior because both endpoint values are
zero. -/
theorem IsConjugate.nonzero_interior
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {a b : ℝ} (h : IsConjugate (I := I) g γ a b) :
    ∃ J : FieldAlong (I := I) γ, ∃ t ∈ Ioo a b, J t ≠ 0 := by
  rcases h with ⟨J, _, _, hza, hzb, t, ht, hJ⟩
  have hta : t ≠ a := by
    intro hta
    subst t
    exact hJ hza
  have htb : t ≠ b := by
    intro htb
    subst t
    exact hJ hzb
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have htb' : t < b := lt_of_le_of_ne ht.2 htb
  exact ⟨J, t, ⟨hat, htb'⟩, hJ⟩

/-- Extract the endpoint-vanishing geodesic Jacobi witness. -/
theorem IsConjugate.endpoint_values
    {g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)}
    {γ : ℝ → M} {a b : ℝ} (h : IsConjugate (I := I) g γ a b) :
    ∃ J DJ : FieldAlong (I := I) γ,
      IsGeodesicJacobiFieldOn (I := I) g γ J DJ a b ∧
      J a = 0 ∧ J b = 0 := by
  rcases h with ⟨J, DJ, hJ, hJ0, hJ1, _⟩
  exact ⟨J, DJ, hJ, hJ0, hJ1⟩

end Jacobi
end Ch01
end MorganTianLib
