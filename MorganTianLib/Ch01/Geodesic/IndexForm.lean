import MorganTianLib.Ch01.Geodesic.Variation
import MorganTianLib.Ch01.Jacobi
import MorganTianLib.Ch01.Curvature.Model
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The intrinsic index form and second variation

This module records the one-dimensional analytic core of the second variation
on a geodesic segment. A field is a dependent tangent-valued function along
the base curve (Jacobi.FieldAlong); no coordinate field or second connection
is introduced. The interval is always the named compact segment
ClosedInterval a b, represented by Set.Icc a b.

For fields Y₁, Y₂ and base velocity V, the integrand is
g(DₜY₁,DₜY₂) - g(R(Y₁,V)V,Y₂). The order is the source order in
Ch01.Curvature: curvature4 puts the metric pairing in the third argument,
so the curvature term is
curvature4 g (γ t) (Y₁ t) (V t) (Y₂ t) (V t). The interval integral is
Mathlib's oriented `intervalIntegral`; the proofs use the pinned
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` and
`intervalIntegral.integral_congr_Ioo_of_le` APIs. All continuity, derivative,
and integrability assumptions used by FTC are fields of the records below.
The derivative fields are linked to the canonical
`Jacobi.HasCovariantDerivativeAlongAt` certificates, the base speed is the
`Variation.velocity` accessor, and curvature is read through
`Curvature.Provisional.curvature4`.

The second-variation records expose the mixed derivative and transverse
endpoint acceleration separately. Thus the free-end formula retains both
boundary terms, while the endpoint-fixed theorem explicitly asks for the
endpoint family maps to be constant. The records are analytic assembly
contracts: the current connection API does not yet derive their
differentiation-under-the-integral and mixed-partial witnesses for an
arbitrary smooth family.

Sources: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, pp. 43--45,
especially the one- and two-field formulas and endpoint-zero specialization
(`morganTian2007`); do Carmo, Ch. 9, pp. 185--201, especially the nonproper
second-variation formula and its endpoint-fixed specialization
(`doCarmo1992`); Lee, Theorem 10.22 and Proposition 10.24 (`lee2018`).
-/

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set
open scoped Bundle ContDiff ENNReal Interval Manifold RealInnerProductSpace Topology

namespace MorganTianLib
namespace Ch01
namespace Geodesic
namespace IndexForm

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-! ## Compact intervals and fields -/

/-- A compact oriented interval used by the index-form API. -/
structure ClosedInterval where
  /-- Left endpoint. -/
  a : ℝ
  /-- Right endpoint. -/
  b : ℝ
  /-- The interval is nonempty (possibly a point). -/
  a_le_b : a ≤ b

namespace ClosedInterval

/-- The underlying compact set of a ClosedInterval. -/
def set (J : ClosedInterval) : Set ℝ := Icc J.a J.b

@[simp] theorem mem_set {J : ClosedInterval} {t : ℝ} :
    t ∈ J.set ↔ t ∈ Icc J.a J.b := Iff.rfl

/-- The named set is compact. -/
theorem isCompact_set (J : ClosedInterval) : IsCompact J.set := by
  exact isCompact_Icc

/-- The named set is nonempty, including the degenerate interval case. -/
theorem nonempty_set (J : ClosedInterval) : J.set.Nonempty := by
  exact nonempty_Icc.mpr J.a_le_b

end ClosedInterval

/-! ## Intrinsic operators -/

/-- The velocity field used by the intrinsic curvature term. -/
noncomputable def baseVelocity (γ : ℝ → M) : Jacobi.FieldAlong (I := I) γ :=
  fun t => Variation.velocity (I := I) γ t

/-- The source-ordered Jacobi operator Dₜ(DₜY) + R(Y,V)V, with the two
covariant derivatives supplied by the field data. -/
noncomputable def jacobiOperator
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (Y D2Y : Jacobi.FieldAlong (I := I) γ) :
    Jacobi.FieldAlong (I := I) γ :=
  fun t => D2Y t + Curvature.Provisional.curvature g (γ t) (Y t)
    (baseVelocity (I := I) γ t) (baseVelocity (I := I) γ t)

/-- The scalar curvature contribution in the index integrand. The third
argument of curvature4 is the metric pairing slot. -/
noncomputable def curvaturePairing
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (Y₁ Y₂ : Jacobi.FieldAlong (I := I) γ) (t : ℝ) : ℝ :=
  Curvature.Provisional.curvature4 g (γ t) (Y₁ t) (baseVelocity (I := I) γ t)
    (Y₂ t) (baseVelocity (I := I) γ t)

/-- The scalar integrand of the bilinear index form. -/
noncomputable def indexIntegrand
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ)
    (t : ℝ) : ℝ :=
  g.inner (γ t) (DY₁ t) (DY₂ t) - curvaturePairing (I := I) g γ Y₁ Y₂ t

/-- The bilinear index form on a ClosedInterval. -/
noncomputable def indexForm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval)
    (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ) : ℝ :=
  ∫ t in J.a..J.b, indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t

/-- The quadratic index form. -/
noncomputable def indexFormSelf
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval)
    (Y DY : Jacobi.FieldAlong (I := I) γ) : ℝ :=
  indexForm (I := I) g γ J Y DY Y DY

/-! ## Regularity records -/

/-- Regularity and integration data for two fields along a geodesic. The
covariant derivatives are canonical Jacobi.FieldAlong values; the derivative
identity is stated for the scalar pairing to which interval FTC is applied. -/
structure BilinearFieldData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval)
    (Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ) : Prop where
  /-- Coherence between the S20 manifold derivative and the moving-chart
  velocity used by the Jacobi derivative certificates. -/
  velocity_coherence : ∀ t ∈ J.set,
    baseVelocity (I := I) γ t = Jacobi.velocity (I := I) γ t
  /-- The first field's derivative pairing is continuous on the segment. -/
  pairing_continuous :
    ContinuousOn (fun t => g.inner (γ t) (DY₁ t) (Y₂ t)) J.set
  /-- Interior derivative of the first boundary pairing. -/
  pairing_deriv : ∀ t ∈ Ioo J.a J.b,
    HasDerivAt (fun s => g.inner (γ s) (DY₁ s) (Y₂ s))
      (g.inner (γ t) (D2Y₁ t) (Y₂ t) +
        g.inner (γ t) (DY₁ t) (DY₂ t)) t
  /-- The first covariant derivative is the one from the canonical Jacobi
  chart certificate. -/
  first_covariant_derivative : ∀ t ∈ J.set,
    Jacobi.HasCovariantDerivativeAlongAt (I := I) g γ Y₁ DY₁ J.a J.b t
  /-- The second covariant derivative is obtained by applying the same
  canonical certificate to the derivative field. -/
  second_covariant_derivative : ∀ t ∈ J.set,
    Jacobi.HasCovariantDerivativeAlongAt (I := I) g γ DY₁ D2Y₁ J.a J.b t
  /-- The second field has the supplied first covariant derivative. -/
  secondField_first_covariant_derivative : ∀ t ∈ J.set,
    Jacobi.HasCovariantDerivativeAlongAt (I := I) g γ Y₂ DY₂ J.a J.b t
  /-- The second field's derivative has the supplied second covariant
  derivative. -/
  secondField_second_covariant_derivative : ∀ t ∈ J.set,
    Jacobi.HasCovariantDerivativeAlongAt (I := I) g γ DY₂ D2Y₂ J.a J.b t
  /-- The derivative-square pairing is interval integrable. -/
  derivative_pair_integrable :
    IntervalIntegrable (fun t => g.inner (γ t) (DY₁ t) (DY₂ t)) volume J.a J.b
  /-- The first Jacobi pairing is interval integrable. -/
  jacobi_pair_integrable :
    IntervalIntegrable
      (fun t => g.inner (γ t) (D2Y₁ t) (Y₂ t)) volume J.a J.b
  /-- The curvature pairing is interval integrable. -/
  curvature_pair_integrable :
    IntervalIntegrable (curvaturePairing (I := I) g γ Y₁ Y₂) volume J.a J.b
  /-- The swapped derivative-square pairing is interval integrable. -/
  swapped_derivative_pair_integrable :
    IntervalIntegrable (fun t => g.inner (γ t) (DY₂ t) (DY₁ t)) volume J.a J.b

/-- Endpoint-zero fields. -/
def EndpointZero (γ : ℝ → M) (J : ClosedInterval)
    (Y₁ Y₂ : Jacobi.FieldAlong (I := I) γ) : Prop :=
  Y₁ J.a = 0 ∧ Y₁ J.b = 0 ∧ Y₂ J.a = 0 ∧ Y₂ J.b = 0

/-- A self-adjointness witness for the Jacobi curvature operator on the chosen
fields. The current curvature API does not yet export pair-interchange
symmetry, so this hypothesis is explicit. -/
def CurvatureSelfAdjoint
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval)
    (Y₁ Y₂ : Jacobi.FieldAlong (I := I) γ) : Prop :=
  ∀ t ∈ J.set,
    curvaturePairing (I := I) g γ Y₁ Y₂ t =
      curvaturePairing (I := I) g γ Y₂ Y₁ t

/-! ## Integration by parts -/

/-- The endpoint integration-by-parts identity for the scalar covariant
pairing. -/
theorem pairing_integral_eq_sub
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    (D : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂) :
    (∫ t in J.a..J.b, g.inner (γ t) (D2Y₁ t) (Y₂ t) +
        g.inner (γ t) (DY₁ t) (DY₂ t)) =
      g.inner (γ J.b) (DY₁ J.b) (Y₂ J.b) -
        g.inner (γ J.a) (DY₁ J.a) (Y₂ J.a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    J.a_le_b D.pairing_continuous D.pairing_deriv
      (D.jacobi_pair_integrable.add D.derivative_pair_integrable)

/-- The intrinsic integration-by-parts form of the index form. -/
theorem indexForm_eq_boundary_sub_jacobi
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    (D : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂) :
    indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ =
      g.inner (γ J.b) (DY₁ J.b) (Y₂ J.b) -
        g.inner (γ J.a) (DY₁ J.a) (Y₂ J.a) -
      ∫ t in J.a..J.b,
        g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t) := by
  unfold indexForm indexIntegrand
  have hparts := pairing_integral_eq_sub (I := I) g D
  have hcurv := D.curvature_pair_integrable
  rw [intervalIntegral.integral_sub D.derivative_pair_integrable hcurv]
  unfold jacobiOperator
  have hsplit :
      (∫ t in J.a..J.b, g.inner (γ t)
        (D2Y₁ t + Curvature.Provisional.curvature g (γ t) (Y₁ t)
          (baseVelocity (I := I) γ t) (baseVelocity (I := I) γ t)) (Y₂ t)) =
        (∫ t in J.a..J.b, g.inner (γ t) (D2Y₁ t) (Y₂ t)) +
          ∫ t in J.a..J.b, curvaturePairing (I := I) g γ Y₁ Y₂ t := by
    rw [← intervalIntegral.integral_add D.jacobi_pair_integrable hcurv]
    apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
    intro t ht
    change g.inner (γ t)
        (D2Y₁ t + Curvature.Provisional.curvature g (γ t) (Y₁ t)
          (baseVelocity (I := I) γ t) (baseVelocity (I := I) γ t)) (Y₂ t) = _
    rw [map_add]
    simp only [add_apply, curvaturePairing, Curvature.Provisional.curvature4_def]
  rw [hsplit]
  have hparts' := hparts
  rw [intervalIntegral.integral_add D.jacobi_pair_integrable
    D.derivative_pair_integrable] at hparts'
  linarith

/-- Endpoint-zero fields satisfy the familiar negative integral of the Jacobi
operator formula. -/
theorem indexForm_eq_neg_integral_jacobi_of_endpointZero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    (D : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂)
    (hzero : EndpointZero (I := I) γ J Y₁ Y₂) :
    indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ =
      -∫ t in J.a..J.b,
        g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t) := by
  have h := indexForm_eq_boundary_sub_jacobi (I := I) g D
  have hleft : g.inner (γ J.a) (DY₁ J.a) (Y₂ J.a) = 0 := by
    rw [hzero.2.2.1]
    simp
  have hright : g.inner (γ J.b) (DY₁ J.b) (Y₂ J.b) = 0 := by
    rw [hzero.2.2.2]
    simp
  rw [h, hleft, hright]
  ring

/-! ## Bilinearity and symmetry -/

/-- Additivity in the first field, with all derivative witnesses added
pointwise. -/
theorem indexForm_add_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    (Y₁ DY₁ D2Y₁ Y₁' DY₁' D2Y₁' Y₂ DY₂ D2Y₂ :
      Jacobi.FieldAlong (I := I) γ)
    (D : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂)
    (D' : BilinearFieldData (I := I) g γ J Y₁' DY₁' D2Y₁' Y₂ DY₂ D2Y₂)
    (_ : BilinearFieldData (I := I) g γ J
      (fun t => Y₁ t + Y₁' t) (fun t => DY₁ t + DY₁' t)
      (fun t => D2Y₁ t + D2Y₁' t) Y₂ DY₂ D2Y₂) :
    indexForm (I := I) g γ J
        (fun t => Y₁ t + Y₁' t) (fun t => DY₁ t + DY₁' t) Y₂ DY₂ =
      indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ +
        indexForm (I := I) g γ J Y₁' DY₁' Y₂ DY₂ := by
  unfold indexForm
  have h₁ := D.derivative_pair_integrable.sub D.curvature_pair_integrable
  have h₂ := D'.derivative_pair_integrable.sub D'.curvature_pair_integrable
  calc
    (∫ t in J.a..J.b,
        indexIntegrand (I := I) g γ
          (fun s => Y₁ s + Y₁' s) (fun s => DY₁ s + DY₁' s) Y₂ DY₂ t) =
        ∫ t in J.a..J.b,
          (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t +
            indexIntegrand (I := I) g γ Y₁' DY₁' Y₂ DY₂ t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
      intro t ht
      simp only [indexIntegrand, curvaturePairing]
      rw [map_add, add_apply, Curvature.Provisional.curvature4_add_first]
      ring
    _ = _ := intervalIntegral.integral_add h₁ h₂


/-- Homogeneity in the first field. -/
theorem indexForm_smul_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval} (c : ℝ)
    (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ) :
    indexForm (I := I) g γ J (fun t => c • Y₁ t) (fun t => c • DY₁ t) Y₂ DY₂ =
      c * indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ := by
  unfold indexForm
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
  intro t ht
  change g.inner (γ t) (c • DY₁ t) (DY₂ t) -
      curvaturePairing (I := I) g γ (fun s => c • Y₁ s) Y₂ t = _
  simp only [indexIntegrand]
  rw [map_smul, smul_apply]
  unfold curvaturePairing
  rw [Curvature.Provisional.curvature4_smul_first]
  ring

/-- Additivity in the second field, with all derivative witnesses added
pointwise. -/
theorem indexForm_add_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    (Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ Y₂' DY₂' D2Y₂' :
      Jacobi.FieldAlong (I := I) γ)
    (D : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂)
    (D' : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂' DY₂' D2Y₂')
    (_ : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁
      (fun t => Y₂ t + Y₂' t) (fun t => DY₂ t + DY₂' t)
      (fun t => D2Y₂ t + D2Y₂' t)) :
    indexForm (I := I) g γ J Y₁ DY₁
        (fun t => Y₂ t + Y₂' t) (fun t => DY₂ t + DY₂' t) =
      indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ +
        indexForm (I := I) g γ J Y₁ DY₁ Y₂' DY₂' := by
  unfold indexForm
  have h₁ := D.derivative_pair_integrable.sub D.curvature_pair_integrable
  have h₂ := D'.derivative_pair_integrable.sub D'.curvature_pair_integrable
  calc
    (∫ t in J.a..J.b,
        indexIntegrand (I := I) g γ Y₁ DY₁
          (fun s => Y₂ s + Y₂' s) (fun s => DY₂ s + DY₂' s) t) =
        ∫ t in J.a..J.b,
          (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t +
            indexIntegrand (I := I) g γ Y₁ DY₁ Y₂' DY₂' t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
      intro t ht
      simp only [indexIntegrand, curvaturePairing]
      rw [map_add,
        Curvature.Provisional.curvature4_add_third]
      ring
    _ = _ := intervalIntegral.integral_add h₁ h₂

/-- Homogeneity in the second field. -/
theorem indexForm_smul_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval} (c : ℝ)
    (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ) :
    indexForm (I := I) g γ J Y₁ DY₁ (fun t => c • Y₂ t)
        (fun t => c • DY₂ t) =
      c * indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ := by
  unfold indexForm
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
  intro t ht
  simp only [indexIntegrand, curvaturePairing]
  rw [map_smul, Curvature.Provisional.curvature4_smul_third]
  ring

/-- Symmetry under the explicit curvature self-adjointness witness. -/
theorem indexForm_symm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ}
    (hsa : CurvatureSelfAdjoint (I := I) g γ J Y₁ Y₂) :
    indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ =
      indexForm (I := I) g γ J Y₂ DY₂ Y₁ DY₁ := by
  unfold indexForm
  apply intervalIntegral.integral_congr_Ioo_of_le J.a_le_b
  intro t ht
  have ht' : t ∈ J.set := by
    exact ⟨ht.1.le, ht.2.le⟩
  have hcurv := hsa t ht'
  change indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t =
    indexIntegrand (I := I) g γ Y₂ DY₂ Y₁ DY₁ t
  simp only [indexIntegrand, curvaturePairing]
  have hcurv' :
      Curvature.Provisional.curvature4 g (γ t) (Y₁ t) (baseVelocity (I := I) γ t)
          (Y₂ t) (baseVelocity (I := I) γ t) =
        Curvature.Provisional.curvature4 g (γ t) (Y₂ t) (baseVelocity (I := I) γ t)
          (Y₁ t) (baseVelocity (I := I) γ t) := by
    simpa only [curvaturePairing] using hcurv
  rw [g.symm (γ t) (DY₁ t) (DY₂ t), hcurv']

/-- The quadratic form is the self-index form. -/
theorem indexFormSelf_eq_indexForm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval} (Y DY : Jacobi.FieldAlong (I := I) γ) :
    indexFormSelf (I := I) g γ J Y DY = indexForm (I := I) g γ J Y DY Y DY := rfl

/-- Additivity under subdivision of the oriented interval.  This is the
positive-order restriction compatibility used by later Jacobi consumers. -/
theorem indexForm_add_adjacent_of_integrable
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} (J₁ J₂ : ClosedInterval)
    (hjoin : J₁.b = J₂.a)
    (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ)
    (h₁ : IntervalIntegrable
      (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂) volume J₁.a J₁.b)
    (h₂ : IntervalIntegrable
      (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂) volume J₂.a J₂.b) :
    indexForm (I := I) g γ
        { a := J₁.a, b := J₂.b,
          a_le_b := J₁.a_le_b.trans (hjoin ▸ J₂.a_le_b) }
        Y₁ DY₁ Y₂ DY₂ =
      indexForm (I := I) g γ J₁ Y₁ DY₁ Y₂ DY₂ +
        indexForm (I := I) g γ J₂ Y₁ DY₁ Y₂ DY₂ := by
  unfold indexForm
  have h₂' : IntervalIntegrable
      (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂) volume J₁.b J₂.b := by
    simpa [hjoin] using h₂
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := J₁.a) (b := J₁.b) (c := J₂.b) h₁ h₂'
  simpa [hjoin] using h.symm

/-- Positive affine reparameterization at the analytic index-density level.
The displayed `density_eq` is the explicit chain-rule witness relating the
reparameterized fields to the original fields.  Once a geometric producer
supplies that witness, Mathlib's oriented interval change of variables gives
the expected factor `alpha`; no hidden parameter convention is introduced. -/
theorem indexForm_affine_reparam_of_density
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma delta : ℝ → M} (J : ClosedInterval) (alpha beta : ℝ)
    (halpha : 0 < alpha)
    (Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) gamma)
    (Y₁' DY₁' Y₂' DY₂' : Jacobi.FieldAlong (I := I) delta)
    (density_eq : ∀ t ∈ uIcc J.a J.b,
      indexIntegrand (I := I) g delta Y₁' DY₁' Y₂' DY₂' t =
        alpha ^ 2 * indexIntegrand (I := I) g gamma Y₁ DY₁ Y₂ DY₂
          (alpha * t + beta)) :
    indexForm (I := I) g delta J Y₁' DY₁' Y₂' DY₂' =
      alpha * indexForm (I := I) g gamma
        { a := alpha * J.a + beta
          b := alpha * J.b + beta
          a_le_b := by nlinarith [J.a_le_b, halpha] }
        Y₁ DY₁ Y₂ DY₂ := by
  unfold indexForm
  have hEq : EqOn
      (indexIntegrand (I := I) g delta Y₁' DY₁' Y₂' DY₂')
      (fun t : ℝ => alpha ^ 2 *
        indexIntegrand (I := I) g gamma Y₁ DY₁ Y₂ DY₂ (alpha * t + beta))
      (uIcc J.a J.b) := by
    intro t ht
    exact density_eq t ht
  rw [intervalIntegral.integral_congr hEq]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_add _ (ne_of_gt halpha) beta]
  have hne : alpha ≠ 0 := ne_of_gt halpha
  have hα : alpha ^ 2 * alpha⁻¹ = alpha := by
    field_simp [hne]
  simp only [smul_eq_mul]
  rw [← mul_assoc, hα]

/-- Pointwise zero-field regression. -/
theorem indexIntegrand_zero_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {Y₁ DY₁ Y₂ DY₂ : Jacobi.FieldAlong (I := I) γ} {t : ℝ}
    (hY : Y₁ t = 0) (hDY : DY₁ t = 0) :
    indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t = 0 := by
  simp only [indexIntegrand, hDY, map_zero, zero_apply]
  unfold curvaturePairing
  rw [hY]
  have hcurv := Curvature.Provisional.curvature4_smul_first
    g (γ t) (0 : ℝ) (baseVelocity (I := I) γ t)
      (baseVelocity (I := I) γ t) (Y₂ t)
      (baseVelocity (I := I) γ t)
  simpa using hcurv

/-- The completely zero field has zero index form, including on a degenerate
interval. This is the concrete zero/affine normalization regression. -/
@[simp] theorem indexForm_zero_fields
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval) :
    indexForm (I := I) g γ J (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) = 0 := by
  unfold indexForm
  have hEq : EqOn
      (indexIntegrand (I := I) g γ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0))
      (fun _ : ℝ => 0) (uIcc J.a J.b) := by
    intro t ht
    simp [indexIntegrand, curvaturePairing]
  rw [intervalIntegral.integral_congr hEq]
  simp

/-- The source-order curvature slot probe used by the Euclidean and
constant-curvature regressions. -/
theorem curvaturePairing_source_order
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} (Y₁ Y₂ : Jacobi.FieldAlong (I := I) γ) (t : ℝ) :
    curvaturePairing (I := I) g γ Y₁ Y₂ t =
      g.inner (γ t)
        (Curvature.Provisional.curvature g (γ t) (Y₁ t)
          (baseVelocity (I := I) γ t) (baseVelocity (I := I) γ t)) (Y₂ t) := by
  rfl

omit [FiniteDimensional ℝ E] in
/-- The intrinsic base-velocity component is nonnegative for every supplied
Riemannian metric, including metrics whose coefficients vary with the foot. -/
theorem baseVelocity_inner_self_nonneg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (t : ℝ) :
    0 ≤ g.inner (γ t) (baseVelocity (I := I) γ t)
      (baseVelocity (I := I) γ t) := by
  exact Variation.speedSq_nonneg (I := I) g γ t

omit [FiniteDimensional ℝ E] in
/-- Strict positivity of the same component when the velocity is nonzero. This
is the metric-component sign probe used to catch a reversed energy sign. -/
theorem baseVelocity_inner_self_pos
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (t : ℝ)
    (hv : baseVelocity (I := I) γ t ≠ 0) :
    0 < g.inner (γ t) (baseVelocity (I := I) γ t)
      (baseVelocity (I := I) γ t) := by
  exact g.pos (γ t) _ hv

omit [FiniteDimensional ℝ E] in
/-- The metric-component probe is definitionally the S20 speed-square
accessor, so a varying metric cannot change the sign convention silently. -/
theorem metric_component_sign_probe
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (t : ℝ) :
    g.inner (γ t) (baseVelocity (I := I) γ t)
        (baseVelocity (I := I) γ t) =
      Variation.speedSq (I := I) g γ t := rfl

/-! ## Second-variation contracts -/

/--
The analytic data used to assemble a second variation.  This record is
deliberately finer grained than a certificate for the final answer:
`energyTrace_deriv` is the second energy derivative, `density_eq` is the
pointwise second-variation density identity, and `boundaryPairing_eq` records
the two free-end contributions.  The remaining differentiation-under-the-
integral statement is `energyTrace_eq_integral`; it is the producer boundary
for the current S20/S21 contracts.

The field `transverseAcceleration` is the ordered mixed field
`D_{Y₁}(partial_{u₂} F)` in Morgan--Tian's notation (and is `D_Y(partial_Y F)`
in the quadratic case). The `boundaryPairing` field records its contribution
`g(V,D_Y1 (partial_Y2 F))`; the other free-end term
`g(D_t Y1,Y2)` is supplied by the integration-by-parts identity for
`indexForm`.  Thus the source formula below displays both terms explicitly,
with a plus sign at the right endpoint and a minus sign at the left endpoint.
-/
structure SecondVariationCore
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (J : ClosedInterval)
    (Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ)
  (energyTrace : ℝ → ℝ) : Type _ where
  /-- The base curve is geodesic on the named compact segment. -/
  base_geodesic : Geodesic.isGeodesicOn (I := I) g γ J.set
  /-- Covariant-derivative, curvature, and interval-integrability data. -/
  regularity : BilinearFieldData (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂
  /-- The ordered transverse acceleration `A₁₂ = D_{Y₁}(partial_{u₂} F)` of
  the second variation field. In the quadratic adapter this is `A₁₁`; for a
  mixed variation it is supplied for the ordered pair `(Y₁,Y₂)`. -/
  transverseAcceleration : Jacobi.FieldAlong (I := I) γ
  /-- Scalar transverse-acceleration boundary pairing. -/
  boundaryPairing : ℝ → ℝ
  /-- Its derivative on the interior of the interval. -/
  boundaryDerivative : ℝ → ℝ
  /-- The density obtained after differentiating the energy. -/
  density : ℝ → ℝ
  /-- The value of the second energy derivative. -/
  mixedDerivative : ℝ
  /-- The energy trace has the recorded second derivative. -/
  energyTrace_deriv : HasDerivAt energyTrace mixedDerivative 0
  /-- Differentiation under the integral, before endpoint assembly. -/
  energyTrace_eq_integral :
    mixedDerivative = ∫ t in J.a..J.b, density t
  /-- Pointwise second-variation density identity. -/
  density_eq : ∀ t,
    density t = boundaryDerivative t +
      indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t
  /-- The transverse-acceleration pairing in terms of covariant fields. -/
  boundaryPairing_eq : ∀ t ∈ J.set,
    boundaryPairing t =
      g.inner (γ t) (baseVelocity (I := I) γ t)
        (transverseAcceleration t)
  boundary_continuous : ContinuousOn boundaryPairing J.set
  boundary_deriv : ∀ t ∈ Ioo J.a J.b,
    HasDerivAt boundaryPairing (boundaryDerivative t) t
  boundaryDerivative_integrable :
    IntervalIntegrable boundaryDerivative volume J.a J.b
  density_integrable :
    IntervalIntegrable density volume J.a J.b

/-- The free-end second-variation assembly for any `SecondVariationCore`.
The signs are `+` at `b` and `-` at `a`; the interior term is the bilinear
index form. -/
theorem secondVariationCore
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    {energyTrace : ℝ → ℝ}
    (D : SecondVariationCore (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂
      energyTrace) :
    HasDerivAt energyTrace
      (D.boundaryPairing J.b - D.boundaryPairing J.a +
        indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂) 0 := by
  have hindex :
      IntervalIntegrable
        (indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂) volume J.a J.b :=
    D.regularity.derivative_pair_integrable.sub
      D.regularity.curvature_pair_integrable
  have hdensity :
      (∫ t in J.a..J.b, D.density t) =
        (∫ t in J.a..J.b, D.boundaryDerivative t) +
          ∫ t in J.a..J.b,
            indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t := by
    have heq : (fun t => D.density t) =
        (fun t => D.boundaryDerivative t +
          indexIntegrand (I := I) g γ Y₁ DY₁ Y₂ DY₂ t) := by
      funext t
      exact D.density_eq t
    rw [heq, intervalIntegral.integral_add D.boundaryDerivative_integrable hindex]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    J.a_le_b D.boundary_continuous D.boundary_deriv
      D.boundaryDerivative_integrable
  have hvalue : D.mixedDerivative =
      D.boundaryPairing J.b - D.boundaryPairing J.a +
        indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ := by
    rw [D.energyTrace_eq_integral, hdensity, hFTC]
    rfl
  have hderiv := D.energyTrace_deriv
  rw [hvalue] at hderiv
  exact hderiv

/-- The same assembly written with the intrinsic Jacobi operator.  This is the
Morgan--Tian free-end formula: the boundary pairing is retained at both ends,
and integration by parts changes the index integral to `- integral <Jac Y1,Y2>`.
-/
theorem secondVariationCore_source_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    {energyTrace : ℝ → ℝ}
    (D : SecondVariationCore (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂
      energyTrace) :
    deriv energyTrace 0 =
      (g.inner (γ J.b) (DY₁ J.b) (Y₂ J.b) +
          g.inner (γ J.b) (baseVelocity (I := I) γ J.b)
            (D.transverseAcceleration J.b)) -
      (g.inner (γ J.a) (DY₁ J.a) (Y₂ J.a) +
          g.inner (γ J.a) (baseVelocity (I := I) γ J.a)
            (D.transverseAcceleration J.a)) -
      ∫ t in J.a..J.b,
        g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t) := by
  have hmain := (secondVariationCore (I := I) g D).deriv
  have hindex := indexForm_eq_boundary_sub_jacobi (I := I) g D.regularity
  have ha : J.a ∈ J.set := ⟨le_rfl, J.a_le_b⟩
  have hb : J.b ∈ J.set := ⟨J.a_le_b, le_rfl⟩
  have hba := D.boundaryPairing_eq J.a ha
  have hbb := D.boundaryPairing_eq J.b hb
  calc
    deriv energyTrace 0 =
        D.boundaryPairing J.b - D.boundaryPairing J.a +
          indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ := hmain
    _ =
      (g.inner (γ J.b) (DY₁ J.b) (Y₂ J.b) +
          g.inner (γ J.b) (baseVelocity (I := I) γ J.b)
            (D.transverseAcceleration J.b)) -
      (g.inner (γ J.a) (DY₁ J.a) (Y₂ J.a) +
          g.inner (γ J.a) (baseVelocity (I := I) γ J.a)
            (D.transverseAcceleration J.a)) -
      ∫ t in J.a..J.b,
        g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t) := by
        rw [hba, hbb, hindex]
        ring

/-- Endpoint-fixed specialization in the source form.  The endpoint field
values remove the `D_t Y1,Y2` terms, while the explicitly supplied transverse
acceleration endpoint values remove the second free-end terms. -/
theorem secondVariationCore_fixed_endpoints_source
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    {energyTrace : ℝ → ℝ}
    (D : SecondVariationCore (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂
      energyTrace)
    (hY₁a : Y₁ J.a = 0) (hY₁b : Y₁ J.b = 0)
    (hY₂a : Y₂ J.a = 0) (hY₂b : Y₂ J.b = 0)
    (hAa : D.transverseAcceleration J.a = 0)
    (hAb : D.transverseAcceleration J.b = 0) :
    HasDerivAt energyTrace
      (-∫ t in J.a..J.b,
        g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t)) 0 := by
  have hmain := secondVariationCore (I := I) g D
  have hindex := indexForm_eq_neg_integral_jacobi_of_endpointZero
    (I := I) g D.regularity
      ⟨hY₁a, hY₁b, hY₂a, hY₂b⟩
  have ha : J.a ∈ J.set := ⟨le_rfl, J.a_le_b⟩
  have hb : J.b ∈ J.set := ⟨J.a_le_b, le_rfl⟩
  have hleft : D.boundaryPairing J.a = 0 := by
    rw [D.boundaryPairing_eq J.a ha, hAa]
    simp
  have hright : D.boundaryPairing J.b = 0 := by
    rw [D.boundaryPairing_eq J.b hb, hAb]
    simp
  have hvalue :
      D.boundaryPairing J.b - D.boundaryPairing J.a +
          indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂ =
        -∫ t in J.a..J.b,
          g.inner (γ t) (jacobiOperator (I := I) g γ Y₁ D2Y₁ t) (Y₂ t) := by
    rw [hleft, hright, hindex]
    ring
  rw [hvalue] at hmain
  exact hmain

/-- Endpoint-fixed specialization of the analytic core in index-form form. -/
theorem secondVariationCore_fixed_endpoints
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {γ : ℝ → M} {J : ClosedInterval}
    {Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂ : Jacobi.FieldAlong (I := I) γ}
    {energyTrace : ℝ → ℝ}
    (D : SecondVariationCore (I := I) g γ J Y₁ DY₁ D2Y₁ Y₂ DY₂ D2Y₂
      energyTrace)
    (hY₁a : Y₁ J.a = 0) (hY₁b : Y₁ J.b = 0)
    (hY₂a : Y₂ J.a = 0) (hY₂b : Y₂ J.b = 0)
    (hAa : D.transverseAcceleration J.a = 0)
    (hAb : D.transverseAcceleration J.b = 0) :
    HasDerivAt energyTrace
      (indexForm (I := I) g γ J Y₁ DY₁ Y₂ DY₂) 0 := by
  have hsource := secondVariationCore_fixed_endpoints_source
    (I := I) g D hY₁a hY₁b hY₂a hY₂b hAa hAb
  have hneg := indexForm_eq_neg_integral_jacobi_of_endpointZero
    (I := I) g D.regularity
      ⟨hY₁a, hY₁b, hY₂a, hY₂b⟩
  rw [← hneg] at hsource
  exact hsource

/-! ### Smooth-variation adapter -/

/--
The second-variation contract attached to an existing
`Variation.SmoothVariation`.  Its `firstVariation` field is the accepted S20
contract, while `core` records the second-order fields on the zero slice.
The equalities to `variationalVectorField` and `covariantDerivative` keep the
family connection visible.  In particular, the transverse acceleration is
not identified with `FirstVariationData.acceleration`: that S20 field is the
longitudinal base-curve acceleration, whereas the second-variation boundary
term uses `D_Y (partial_Y F)`.  The latter remains an explicit field in `core`,
as required by the free-end formula.

The endpoint velocity equalities account for the fact that S20 uses the
one-sided `velocityWithin` in its boundary pairing, whereas the intrinsic
index form uses the unrestricted `Variation.velocity`.
-/
structure SecondVariationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} (J : ClosedInterval) (epsilon : ℝ)
    (V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon) : Type _ where
  firstVariation : Variation.FirstVariationData (I := I) g V
  field : Jacobi.FieldAlong (I := I) (Variation.baseCurve V)
  derivative : Jacobi.FieldAlong (I := I) (Variation.baseCurve V)
  secondDerivative : Jacobi.FieldAlong (I := I) (Variation.baseCurve V)
  core : SecondVariationCore (I := I) g (Variation.baseCurve V) J
      field derivative secondDerivative field derivative secondDerivative
      (fun s => deriv (Variation.variationEnergy (I := I) g V) s)
  /-- The zero slice equality, restated on the named interval. -/
  baseCurve_eq_gamma : ∀ t ∈ J.set, Variation.baseCurve V t = gamma t
  /-- The first field is the parameter derivative of the family. -/
  field_eq_variational : ∀ t ∈ J.set,
    field t = Variation.variationalVectorField V t
  /-- The supplied first covariant derivative agrees with S20 data. -/
  derivative_eq_first : ∀ t ∈ J.set,
    derivative t = firstVariation.covariantDerivative t
  /-- Coherence of the unrestricted and endpoint velocity accessors at `a`. -/
  endpoint_velocity_left :
    Variation.velocityWithin (I := I) (Variation.baseCurve V) J.a J.b J.a =
      baseVelocity (I := I) (Variation.baseCurve V) J.a
  /-- Coherence of the unrestricted and endpoint velocity accessors at `b`. -/
  endpoint_velocity_right :
    Variation.velocityWithin (I := I) (Variation.baseCurve V) J.a J.b J.b =
      baseVelocity (I := I) (Variation.baseCurve V) J.b

/-! The following projections make the S20 boundary conventions usable by
downstream consumers. They do not identify the longitudinal acceleration in
`FirstVariationData` with the transverse acceleration in `core`. -/

/-- At the left endpoint, the S20 variation pairing agrees with the intrinsic
pairing using the unrestricted base velocity. -/
theorem SecondVariationData.variationPairing_eq_field_baseVelocity_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    Variation.variationPairing (I := I) g V J.a =
      g.inner (Variation.baseCurve V J.a) (D.field J.a)
        (baseVelocity (I := I) (Variation.baseCurve V) J.a) := by
  have ha : J.a ∈ J.set := ⟨le_rfl, J.a_le_b⟩
  unfold Variation.variationPairing
  rw [← D.field_eq_variational J.a ha, D.endpoint_velocity_left]

/-- At the right endpoint, the S20 variation pairing agrees with the intrinsic
pairing using the unrestricted base velocity. -/
theorem SecondVariationData.variationPairing_eq_field_baseVelocity_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    Variation.variationPairing (I := I) g V J.b =
      g.inner (Variation.baseCurve V J.b) (D.field J.b)
        (baseVelocity (I := I) (Variation.baseCurve V) J.b) := by
  have hb : J.b ∈ J.set := ⟨J.a_le_b, le_rfl⟩
  unfold Variation.variationPairing
  rw [← D.field_eq_variational J.b hb, D.endpoint_velocity_right]

/-- On the named interval, the covariant derivative stored by S20 is the
derivative field used by the intrinsic index form. -/
theorem SecondVariationData.covariantPairing_eq_derivative_baseVelocity
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) {t : ℝ}
    (ht : t ∈ J.set) :
    Variation.covariantPairing (I := I) g V D.firstVariation.covariantDerivative t =
      g.inner (Variation.baseCurve V t) (D.derivative t)
        (baseVelocity (I := I) (Variation.baseCurve V) t) := by
  unfold Variation.covariantPairing
  rw [← D.derivative_eq_first t ht]
  rfl

/-- The first-variation contract attached to `D` still supplies the complete
S20 endpoint formula. This projection keeps that lower-order bridge available
without conflating its longitudinal acceleration with `core`'s transverse one. -/
theorem SecondVariationData.first_energy_variation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    HasDerivAt (Variation.variationEnergy (I := I) g V)
      (Variation.variationPairing (I := I) g V J.b -
        Variation.variationPairing (I := I) g V J.a -
        ∫ t in J.a..J.b,
          Variation.accelerationPairing (I := I) g V D.firstVariation.acceleration t) 0 := by
  simpa using Variation.firstEnergyVariation (I := I) g D.firstVariation

/-- The free-end second variation for a smooth variation.  The right-hand side
is the transverse-acceleration boundary term at `b` minus that at `a`, plus
the intrinsic index form. This is an assembly theorem over the explicit
`SecondVariationData` contract; deriving that contract from arbitrary `C^3`
family data remains a separate producer obligation. -/
theorem secondVariation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    HasDerivAt
      (fun s => deriv (Variation.variationEnergy (I := I) g V) s)
      (D.core.boundaryPairing J.b - D.core.boundaryPairing J.a +
        indexFormSelf (I := I) g (Variation.baseCurve V) J D.field D.derivative) 0 := by
  simpa [indexFormSelf] using secondVariationCore (I := I) g D.core

/-- The scalar derivative form of `secondVariation`. -/
theorem secondVariation_deriv
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    deriv (fun s => deriv (Variation.variationEnergy (I := I) g V) s) 0 =
      D.core.boundaryPairing J.b - D.core.boundaryPairing J.a +
        indexFormSelf (I := I) g (Variation.baseCurve V) J D.field D.derivative :=
  (secondVariation (I := I) g D).deriv

/-- The smooth-variation formula in Morgan--Tian's source order.  Both
free-end summands are visible: `g(D_tY,Y)` comes from the index-form
integration by parts and `g(V,D_Y (partial_Y F))` is the transverse boundary
pairing recorded by `SecondVariationCore`. -/
theorem secondVariation_source_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V) :
    deriv (fun s => deriv (Variation.variationEnergy (I := I) g V) s) 0 =
      (g.inner (Variation.baseCurve V J.b) (D.derivative J.b) (D.field J.b) +
          g.inner (Variation.baseCurve V J.b)
            (baseVelocity (I := I) (Variation.baseCurve V) J.b)
            (D.core.transverseAcceleration J.b)) -
      (g.inner (Variation.baseCurve V J.a) (D.derivative J.a) (D.field J.a) +
          g.inner (Variation.baseCurve V J.a)
            (baseVelocity (I := I) (Variation.baseCurve V) J.a)
            (D.core.transverseAcceleration J.a)) -
      ∫ t in J.a..J.b,
        g.inner (Variation.baseCurve V t)
          (jacobiOperator (I := I) g (Variation.baseCurve V)
            D.field D.secondDerivative t) (D.field t) := by
  simpa using secondVariationCore_source_formula (I := I) g D.core

/-- Endpoint-fixed smooth variations have the index-form second variation when
the transverse acceleration is also zero at both endpoints.  The latter
condition is intentionally explicit: `EndpointVectorsZero` alone only kills
the first free-end summand. -/
theorem secondVariation_fixed_endpoints
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V)
    (hend : Variation.EndpointVectorsZero (I := I) V)
    (hacc : D.core.transverseAcceleration J.a = 0 ∧
      D.core.transverseAcceleration J.b = 0) :
    HasDerivAt
      (fun s => deriv (Variation.variationEnergy (I := I) g V) s)
      (indexFormSelf (I := I) g (Variation.baseCurve V) J D.field D.derivative) 0 := by
  have ha : J.a ∈ J.set := ⟨le_rfl, J.a_le_b⟩
  have hb : J.b ∈ J.set := ⟨J.a_le_b, le_rfl⟩
  have hYa : D.field J.a = 0 := by
    rw [D.field_eq_variational J.a ha]
    exact hend.1
  have hYb : D.field J.b = 0 := by
    rw [D.field_eq_variational J.b hb]
    exact hend.2
  have h := secondVariationCore_fixed_endpoints (I := I) g D.core
    hYa hYb hYa hYb hacc.1 hacc.2
  simpa [indexFormSelf] using h

/-- The endpoint-fixed theorem using the family-constant hypotheses already
provided by `Variation.endpointVectorsZero_of_fixed_endpoints`. -/
theorem secondVariation_fixed_family_endpoints
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {gamma : ℝ → M} {J : ClosedInterval} {epsilon : ℝ}
    {V : Variation.SmoothVariation (I := I) gamma J.a J.b epsilon}
    (D : SecondVariationData (I := I) g J epsilon V)
    (hleft : ∀ s ∈ Icc (-epsilon) epsilon, V.family s J.a = V.family 0 J.a)
    (hright : ∀ s ∈ Icc (-epsilon) epsilon, V.family s J.b = V.family 0 J.b)
    (hacc : D.core.transverseAcceleration J.a = 0 ∧
      D.core.transverseAcceleration J.b = 0) :
    HasDerivAt
      (fun s => deriv (Variation.variationEnergy (I := I) g V) s)
      (indexFormSelf (I := I) g (Variation.baseCurve V) J D.field D.derivative) 0 := by
  exact secondVariation_fixed_endpoints (I := I) g D
    (Variation.endpointVectorsZero_of_fixed_endpoints (I := I) V hleft hright) hacc

/-! ### Geodesic-variation and model probes -/

/-- Assembly data for the one-family `(s,t)` `Jacobi.GeodesicVariation`.
`GV` supplies one variation direction over time, so this record does not
manufacture a second independent variation parameter. `firstField` is tied to
`GV`'s variational field; the second field, its derivative data, and the mixed
trace remain explicit producer inputs. The density identity stays in `core`,
so the theorem below is an assembly result rather than an opaque final
equality. -/
structure GeodesicSecondVariationData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} (GV : Jacobi.GeodesicVariation (I := I) g a b)
    (J : ClosedInterval) (mixedTrace : ℝ → ℝ) : Type _ where
  interval_eq_left : J.a = a
  interval_eq_right : J.b = b
  firstField : Jacobi.FieldAlong (I := I) GV.baseCurve
  firstDerivative : Jacobi.FieldAlong (I := I) GV.baseCurve
  firstSecondDerivative : Jacobi.FieldAlong (I := I) GV.baseCurve
  secondField : Jacobi.FieldAlong (I := I) GV.baseCurve
  secondDerivative : Jacobi.FieldAlong (I := I) GV.baseCurve
  secondSecondDerivative : Jacobi.FieldAlong (I := I) GV.baseCurve
  core : SecondVariationCore (I := I) g GV.baseCurve J
      firstField firstDerivative firstSecondDerivative
      secondField secondDerivative secondSecondDerivative mixedTrace
  firstField_eq_variation : ∀ t ∈ J.set,
    firstField t = GV.variationalField t
  firstDerivative_eq_variation : ∀ t ∈ J.set,
    firstDerivative t = GV.covariantVariationalField t

/-- The geodesic-variation contract exposes the intrinsic Jacobi field before
the second-variation assembly. -/
theorem geodesicVariation_has_jacobi_field
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} (GV : Jacobi.GeodesicVariation (I := I) g a b) :
    Jacobi.IsGeodesicJacobiFieldOn (I := I) g GV.baseCurve
      GV.variationalField GV.covariantVariationalField a b :=
  GV.variationField_isJacobi

/-- Mixed second variation for the geodesic-variation contract. -/
theorem secondVariation_mixed
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} {GV : Jacobi.GeodesicVariation (I := I) g a b}
    {J : ClosedInterval} {mixedTrace : ℝ → ℝ}
    (D : GeodesicSecondVariationData (I := I) g GV J mixedTrace) :
    HasDerivAt mixedTrace
      (D.core.boundaryPairing J.b - D.core.boundaryPairing J.a +
        indexForm (I := I) g GV.baseCurve J D.firstField D.firstDerivative
          D.secondField D.secondDerivative) 0 := by
  exact secondVariationCore (I := I) g D.core

/-- The mixed geodesic-variation formula in the source order, with both
free-end contributions displayed. -/
theorem secondVariation_mixed_source_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {a b : ℝ} {GV : Jacobi.GeodesicVariation (I := I) g a b}
    {J : ClosedInterval} {mixedTrace : ℝ → ℝ}
    (D : GeodesicSecondVariationData (I := I) g GV J mixedTrace) :
    deriv mixedTrace 0 =
      (g.inner (GV.baseCurve J.b) (D.firstDerivative J.b)
          (D.secondField J.b) +
        g.inner (GV.baseCurve J.b) (baseVelocity (I := I) GV.baseCurve J.b)
          (D.core.transverseAcceleration J.b)) -
      (g.inner (GV.baseCurve J.a) (D.firstDerivative J.a)
          (D.secondField J.a) +
        g.inner (GV.baseCurve J.a) (baseVelocity (I := I) GV.baseCurve J.a)
          (D.core.transverseAcceleration J.a)) -
      ∫ t in J.a..J.b,
        g.inner (GV.baseCurve t)
          (jacobiOperator (I := I) g GV.baseCurve D.firstField
            D.firstSecondDerivative t) (D.secondField t) := by
  simpa using secondVariationCore_source_formula (I := I) g D.core

/-! ### Algebraic sign and dimension regressions -/

section ModelRegression

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Euclidean straight-line regression: the zero-curvature model contributes no
curvature term to the index integrand. -/
theorem modelIndexIntegrand_zero_curvature (DY : F) :
    inner ℝ DY DY - inner ℝ (Curvature.modelCurvature (0 : ℝ) DY DY DY) DY =
      inner ℝ DY DY := by
  simp [Curvature.modelCurvature]

/-- Flat affine-field regression: in the zero-curvature model, the affine field
`t • A + B` contributes only the derivative-square term. -/
theorem modelIndexForm_zero_affine (A B V : F) (a b : ℝ) :
    (∫ t in a..b,
      inner ℝ A A - inner ℝ (Curvature.modelCurvature 0 (t • A + B) V V)
        (t • A + B)) =
      (b - a) * inner ℝ A A := by
  have hEq :
      (fun t : ℝ => inner ℝ A A - inner ℝ
        (Curvature.modelCurvature 0 (t • A + B) V V) (t • A + B)) =
        (fun _ : ℝ => inner ℝ A A) := by
    funext t
    simp [Curvature.modelCurvature]
  rw [hEq, intervalIntegral.integral_const]
  simp [smul_eq_mul]

/-- Constant-curvature Jacobi sign regression, restated at the index-form
integrand level. -/
theorem modelIndexIntegrand_unit_orthogonal (K : ℝ) (Y V DY : F)
    (hV : ‖V‖ = 1) (hYV : inner ℝ Y V = 0) :
    inner ℝ DY DY - inner ℝ (Curvature.modelCurvature K Y V V) Y =
      inner ℝ DY DY - K * ‖Y‖ ^ 2 := by
  have hcurv := Curvature.neg_inner_modelCurvature_apply_unit_orthogonal
    K Y V hV hYV
  linarith [hcurv, real_inner_self_eq_norm_sq Y]

/-- Non-orthogonal constant-curvature probe. The fully contracted expression
retains the source slots (and therefore detects replacing `R(Y,V)V` by
`R(V,Y)V`) without imposing an orthogonality hypothesis. -/
theorem modelIndexIntegrand_source_order (K : ℝ) (Y V DY : F) :
    inner ℝ DY DY - inner ℝ (Curvature.modelCurvature K Y V V) Y =
      inner ℝ DY DY - K *
        (inner ℝ V V * inner ℝ Y Y - (inner ℝ Y V) ^ 2) := by
  have hcurv : inner ℝ (Curvature.modelCurvature K Y V V) Y =
      K * (inner ℝ V V * inner ℝ Y Y - (inner ℝ Y V) ^ 2) := by
    simp only [Curvature.modelCurvature, real_inner_smul_left, inner_sub_left]
    rw [real_inner_comm V Y]
    ring
  rw [hcurv]

/-- The first curvature slots are skew in the model probe. -/
theorem modelCurvature_reversed_first_slot_neg (K : ℝ) (Y V : F) :
    inner ℝ (Curvature.modelCurvature K V Y V) Y =
      -inner ℝ (Curvature.modelCurvature K Y V V) Y := by
  simp only [Curvature.modelCurvature, real_inner_smul_left, inner_sub_left]
  rw [real_inner_comm V Y]
  ring

/-- Zero and one dimensional contractions are covered uniformly by the model
orthonormal-basis theorem: in dimension zero the inner product vanishes, and
in dimension one the coefficient `finrank - 1` is zero. -/
theorem modelIndex_dimension_zero_one_note {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ F) (K : ℝ) (X Y : F) :
    ∑ i, Curvature.modelCurvature4 K X (b i) Y (b i) =
      ((Module.finrank ℝ F : ℝ) - 1) * K * inner ℝ X Y :=
  Curvature.sum_modelCurvature4_orthonormalBasis b K X Y

end ModelRegression
