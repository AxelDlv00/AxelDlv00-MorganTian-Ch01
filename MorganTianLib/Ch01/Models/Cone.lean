import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import MorganTianLib.Ch01.Curvature.Operator

/-!
# The open-cone model boundary

This module records the part of Morgan--Tian Chapter 1, Definitions 1.14--1.16
(`morganTian2007`), which is independent of a pointwise curvature producer.
For a real vector space `V`, the tangent model of the open cone is written
`V × ℝ`; the second factor is the radial direction.  The exterior square has
the intrinsic splitting

`Λ² (V × ℝ) ≃ₗ Λ² V × V`.

The exported block form is the exact algebraic bilinear shape of the cone
curvature calculation in the source convention: `s² A` on the horizontal block
and zero on the mixed block (the pure radial wedge is vacuous in `Λ²`).  `A` is
deliberately an input bilinear form, rather than a new curvature
representation.  In this checkout the bundled manifold curvature producer is
still selected-extension/provisional (the S06 and S07 boundary), and
`Curvature.curvatureOperator` is a bilinear form rather than a Riesz
endomorphism.  Consequently the pointwise Levi--Civita curvature calculation
and the eigenvalue statement `s⁻² (λ - 1)` are not asserted here; this module is
the reusable algebraic consumer for that later interface.

The decomposition and normalization follow Morgan--Tian, Definitions 1.14--
1.16, printed pp. 40--41, with the exterior-power universal property from the
pinned Mathlib `LinearAlgebra.ExteriorPower.Basic` API.  The product tangent
projection uses Mathlib's `mfderiv_fst`/`mfderiv_snd` declarations; the
pointwise form is not yet assembled into a `Bundle.ContMDiffRiemannianMetric`
because the pinned bundle API has no prescribed pullback/product
bilinear-section constructor.  The S08 consumer below is intentionally a
fixed inner-product-space model: bundled tangent fibres do not install a
global `InnerProductSpace`, so a future manifold adapter must use the existing
bilinear-form interface rather than treating this model as that adapter.  Its
connection-side dependency is the deferred `Ch01.Connection` /
`Connection.Christoffel` API.  No Do Carmo or coordinate-only metric
dependency is imported.
-/

noncomputable section

open exteriorPower
open Bundle Manifold Set
open scoped Bundle ContDiff Manifold Topology

namespace MorganTianLib
namespace Ch01
namespace Models

/-! ## The positive radial domain and its form -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N]

/-- The positive radial interval `(0, ∞)` as an open subtype of `ℝ`.

Using an `Opens ℝ` subtype keeps the radial-domain condition intrinsic to the
base of the product manifold. -/
def positiveReal : TopologicalSpace.Opens ℝ :=
  ⟨Set.Ioi 0, isOpen_Ioi⟩

/-- The open cone carrier over a type `N`. -/
abbrev Cone (N : Type*) := N × ↥positiveReal

/-- The radial coordinate of a point of `Cone N`. -/
def coneRadius {N : Type*} (q : Cone N) : ℝ := q.2

@[simp] theorem coneRadius_apply {N : Type*} (q : Cone N) :
    coneRadius q = (q.2 : ℝ) :=
  rfl

theorem coneRadius_pos {N : Type*} (q : Cone N) : 0 < coneRadius q :=
  q.2.property

/-- The radial coordinate is smooth on the product manifold. -/
theorem coneRadius_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (coneRadius (N := N)) := by
  exact contMDiff_subtype_val.comp contMDiff_snd

/-- Private bridge to the product model used while constructing the pointwise
form.  Public statements use the canonical tangent projection below. -/
private def coneHorizontalComponentModel (q : Cone N) (u : E × ℝ) :
    TangentSpace I q.1 := by
  change E
  exact u.1

private theorem coneHorizontalComponentModel_add (q : Cone N) (u v : E × ℝ) :
    coneHorizontalComponentModel (I := I) q (u + v) =
      coneHorizontalComponentModel (I := I) q u + coneHorizontalComponentModel (I := I) q v := by
  rfl

private theorem coneHorizontalComponentModel_smul (q : Cone N) (c : ℝ) (u : E × ℝ) :
    coneHorizontalComponentModel (I := I) q (c • u) =
      c • coneHorizontalComponentModel (I := I) q u := by
  rfl

private theorem coneHorizontalComponentModel_ne_zero (q : Cone N) {u : E × ℝ}
    (hu : u.1 ≠ 0) : coneHorizontalComponentModel (I := I) q u ≠ 0 := by
  intro h
  apply hu
  exact h

variable [IsManifold I ∞ N] [FiniteDimensional ℝ E]

private def radialTangentToReal (r : positiveReal) :
    TangentSpace 𝓘(ℝ, ℝ) r →L[ℝ] ℝ := by
  change ℝ →L[ℝ] ℝ
  exact ContinuousLinearMap.id ℝ ℝ

/-- The canonical horizontal/radial tangent projection of the product.

The two components are the Mathlib manifold derivatives of the product
projections; the radial tangent fibre is identified with `ℝ` by its standard
model equivalence. -/
def coneTangentProjection (q : Cone N) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) q →L[ℝ]
      (TangentSpace I q.1 × ℝ) :=
  (mfderiv (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : Cone N → N) q).prod
    ((radialTangentToReal q.2).comp
      (mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (Prod.snd : Cone N → (positiveReal : Type _)) q))

omit [IsManifold I ∞ N] [FiniteDimensional ℝ E] in
private theorem coneTangentProjection_apply_model (q : Cone N)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneTangentProjection (I := I) q u =
      (coneHorizontalComponentModel (I := I) q (show E × ℝ from u),
        (show E × ℝ from u).2) := by
  change E × ℝ at u
  rw [coneTangentProjection, ContinuousLinearMap.prod_apply, mfderiv_fst,
    mfderiv_snd]
  rfl

/-- The pointwise open-cone bilinear form.

At `(x,s)` it is `s² g_x` on horizontal components plus the standard radial
term.  The definition is kept as a pointwise form until the hom-bundle
smoothness constructor and intrinsic cone curvature producer are available.
The explicit finite-dimensional hypothesis is used only by
`LinearMap.toContinuousBilinearMap` to package this pointwise bilinear map. -/
noncomputable def coneForm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) q →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) q →L[ℝ] ℝ :=
  by
    change (E × ℝ) →L[ℝ] (E × ℝ) →L[ℝ] ℝ
    exact (LinearMap.mk₂ ℝ
    (fun u v =>
      (coneRadius q) ^ 2 *
          g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
            (coneHorizontalComponentModel (I := I) q v) +
        u.2 * v.2)
    (by
      intro u₁ u₂ v
      change (coneRadius q) ^ 2 *
          g.inner q.1
            (coneHorizontalComponentModel (I := I) q (u₁ + u₂))
              (coneHorizontalComponentModel (I := I) q v) +
          (u₁.2 + u₂.2) * v.2 =
        (coneRadius q) ^ 2 *
            g.inner q.1 (coneHorizontalComponentModel (I := I) q u₁)
              (coneHorizontalComponentModel (I := I) q v) +
          u₁.2 * v.2 +
          ((coneRadius q) ^ 2 *
              g.inner q.1 (coneHorizontalComponentModel (I := I) q u₂)
                (coneHorizontalComponentModel (I := I) q v) +
            u₂.2 * v.2)
      simp only [coneHorizontalComponentModel_add (I := I), map_add, add_apply]
      ring)
    (by
      intro c u v
      change (coneRadius q) ^ 2 *
          g.inner q.1 (coneHorizontalComponentModel (I := I) q (c • u))
            (coneHorizontalComponentModel (I := I) q v) +
            (c • u.2) * v.2 =
        c • ((coneRadius q) ^ 2 *
            g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
              (coneHorizontalComponentModel (I := I) q v) + u.2 * v.2)
      simp only [coneHorizontalComponentModel_smul (I := I), map_smul, smul_apply,
        smul_eq_mul]
      ring)
    (by
      intro u v₁ v₂
      change (coneRadius q) ^ 2 *
          g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
            (coneHorizontalComponentModel (I := I) q (v₁ + v₂)) +
          u.2 * (v₁.2 + v₂.2) =
        (coneRadius q) ^ 2 *
            g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
              (coneHorizontalComponentModel (I := I) q v₁) +
          u.2 * v₁.2 +
          ((coneRadius q) ^ 2 *
              g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
                (coneHorizontalComponentModel (I := I) q v₂) +
            u.2 * v₂.2)
      simp only [coneHorizontalComponentModel_add (I := I), map_add]
      ring)
    (by
      intro c u v
      change (coneRadius q) ^ 2 *
          g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
            (coneHorizontalComponentModel (I := I) q (c • v)) + u.2 * (c • v.2) =
        c • ((coneRadius q) ^ 2 *
            g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
              (coneHorizontalComponentModel (I := I) q v) + u.2 * v.2)
      simp only [coneHorizontalComponentModel_smul (I := I), map_smul, smul_eq_mul]
      ring)).toContinuousBilinearMap

/-- Model-fibre expansion used internally by the pointwise positivity proofs. -/
private theorem coneForm_apply_model
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneForm g q u v =
      (coneRadius q) ^ 2 *
          g.inner q.1 (coneHorizontalComponentModel (I := I) q
            (show E × ℝ from u))
            (coneHorizontalComponentModel (I := I) q (show E × ℝ from v)) +
        (show E × ℝ from u).2 * (show E × ℝ from v).2 := by
  change E × ℝ at u v
  rfl

/-- Intrinsic pointwise evaluation of the cone form through the canonical
product tangent projection. -/
@[simp] theorem coneForm_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneForm g q u v =
      (coneRadius q) ^ 2 *
          g.inner q.1 (coneTangentProjection (I := I) q u).1
            (coneTangentProjection (I := I) q v).1 +
        (coneTangentProjection (I := I) q u).2 *
          (coneTangentProjection (I := I) q v).2 :=
  by
    rw [coneTangentProjection_apply_model (I := I),
      coneTangentProjection_apply_model (I := I)]
    exact coneForm_apply_model (I := I) g q u v

/-! The following component probes use the standard product tangent
constructor.  They keep the base metric arbitrary, so they also serve as a
small sign/component regression for a nonconstant base metric family. -/

/-- Horizontal vectors pair by the scaled base metric. -/
theorem coneForm_horizontal_horizontal
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N) (u v : TangentSpace I q.1) :
    coneForm g q (u, (0 : ℝ)) (v, (0 : ℝ)) =
      (coneRadius q) ^ 2 * g.inner q.1 u v := by
  change E at u v
  rw [coneForm_apply_model]
  change (coneRadius q) ^ 2 * g.inner q.1 u v + (0 : ℝ) * 0 =
    (coneRadius q) ^ 2 * g.inner q.1 u v
  ring

/-- A horizontal vector is orthogonal to a radial vector. -/
theorem coneForm_horizontal_radial
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N) (u : TangentSpace I q.1) (a : ℝ) :
    coneForm g q (u, (0 : ℝ)) (0, a) = 0 := by
  change E at u
  rw [coneForm_apply_model]
  change (coneRadius q) ^ 2 * g.inner q.1 u 0 + (0 : ℝ) * a = 0
  simp only [map_zero, mul_zero, zero_mul, add_zero]

/-- Radial vectors pair by the standard real product metric. -/
theorem coneForm_radial_radial
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N) (a b : ℝ) :
    coneForm g q (0, a) (0, b) = a * b := by
  rw [coneForm_apply_model]
  change (coneRadius q) ^ 2 * g.inner q.1 0 0 + a * b = a * b
  simp only [map_zero]
  ring

/-- Symmetry of the pointwise cone form. -/
theorem coneForm_symm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N)
    (u v : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    coneForm g q u v = coneForm g q v u := by
  rw [coneForm_apply_model, coneForm_apply_model, g.symm]
  ring

/-- Nonnegativity of the pointwise cone form on a self-pair. -/
theorem coneForm_self_nonneg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q) :
    0 ≤ coneForm g q u u := by
  change E × ℝ at u
  rw [coneForm_apply_model]
  have hbase : 0 ≤ g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
      (coneHorizontalComponentModel (I := I) q u) := by
    by_cases hu : u.1 = 0
    · have hzero : coneHorizontalComponentModel (I := I) q u = 0 := by
        change (u.1 : E) = 0
        exact hu
      rw [hzero]
      simp only [map_zero]
      exact le_rfl
    · exact (g.pos q.1 (coneHorizontalComponentModel (I := I) q u)
        (coneHorizontalComponentModel_ne_zero (I := I) q hu)).le
  exact add_nonneg (mul_nonneg (sq_nonneg (coneRadius q)) hbase)
    (mul_self_nonneg u.2)

/-- Positive definiteness of the pointwise cone form. -/
theorem coneForm_self_pos
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E
      (TangentSpace I : N → Type _))
    (q : Cone N)
    (u : TangentSpace (I.prod 𝓘(ℝ, ℝ)) q)
    (hu : u ≠ 0) :
    0 < coneForm g q u u := by
  change E × ℝ at u
  rw [coneForm_apply_model]
  have hrad : 0 < (coneRadius q) ^ 2 := sq_pos_of_pos (coneRadius_pos q)
  have hbase : 0 ≤ g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
      (coneHorizontalComponentModel (I := I) q u) := by
    by_cases h : u.1 = 0
    · have hzero : coneHorizontalComponentModel (I := I) q u = 0 := by
        change (u.1 : E) = 0
        exact h
      rw [hzero]
      simp only [map_zero]
      exact le_rfl
    · exact (g.pos q.1 (coneHorizontalComponentModel (I := I) q u)
        (coneHorizontalComponentModel_ne_zero (I := I) q h)).le
  have hsplit : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]
    intro h
    exact hu (Prod.ext h.1 h.2)
  rcases hsplit with hbase_ne | hrad_ne
  · have hpos : 0 < (coneRadius q) ^ 2 *
      g.inner q.1 (coneHorizontalComponentModel (I := I) q u)
        (coneHorizontalComponentModel (I := I) q u) :=
      mul_pos hrad (g.pos q.1 (coneHorizontalComponentModel (I := I) q u)
        (coneHorizontalComponentModel_ne_zero (I := I) q hbase_ne))
    nlinarith [sq_nonneg u.2]
  · have hpos : 0 < u.2 * u.2 := mul_self_pos.mpr hrad_ne
    nlinarith [mul_nonneg (sq_nonneg (coneRadius q)) hbase]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## The horizontal/mixed exterior-square decomposition -/

/- The mixed component of `(x,a) ∧ (y,b)` is `b x - a y`. -/
/-- The alternating mixed coefficient of a decomposable cone bivector. -/
def coneMixedAlternating : (V × ℝ) [⋀^Fin 2]→ₗ[ℝ] V where
  toFun x := (x 1).2 • (x 0).1 - (x 0).2 • (x 1).1
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp <;> module
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp <;> module
  map_eq_zero_of_eq' := by
    intro x i j hij hne
    have h01 : x 0 = x 1 := by
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hne | exact hij | exact hij.symm
    rw [h01]
    module

/-- The mixed projection `Λ²(V × ℝ) → V`. -/
def coneWedgeMixedPart : ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] V :=
  alternatingMapLinearEquiv coneMixedAlternating

@[simp] theorem coneWedgeMixedPart_iMulti (x y : V × ℝ) :
    coneWedgeMixedPart (ιMulti ℝ 2 ![x, y]) = y.2 • x.1 - x.2 • y.1 := by
  rw [coneWedgeMixedPart, alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The forward map projects to the horizontal exterior square and records the
mixed coefficient. -/
def coneWedgeSplit : ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] (⋀[ℝ]^2 V) × V :=
  (exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).prod coneWedgeMixedPart

@[simp] theorem coneWedgeSplit_iMulti (x y : V × ℝ) :
    coneWedgeSplit (ιMulti ℝ 2 ![x, y]) =
      (ιMulti ℝ 2 ![x.1, y.1], y.2 • x.1 - x.2 • y.1) := by
  apply Prod.ext
  · simp only [coneWedgeSplit, LinearMap.prod_apply, Function.prod_apply,
      exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    fin_cases i <;> rfl
  · simp [coneWedgeSplit]

private def coneWedgeWithRadial : (V × ℝ) →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  (ιMulti ℝ 2).toMultilinearMap.toLinearMap
    ![((0 : V), (0 : ℝ)), ((0 : V), (1 : ℝ))] 0

/-- The mixed inclusion `u ↦ (u,0) ∧ (0,1)`. -/
def coneWedgeMixed : V →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  coneWedgeWithRadial.comp (LinearMap.inl ℝ V ℝ)

@[simp] theorem coneWedgeMixed_apply (u : V) :
    coneWedgeMixed u =
      ιMulti ℝ 2 ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] := by
  simp only [coneWedgeMixed, LinearMap.comp_apply, LinearMap.inl_apply,
    coneWedgeWithRadial, MultilinearMap.toLinearMap_apply]
  have h : Function.update
      ![((0 : V), (0 : ℝ)), ((0 : V), (1 : ℝ))] 0 (u, 0) =
        ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  rfl

/-- The inverse map sends `(φ,u)` to the horizontal image of `φ` plus the mixed
term `u ∧ ∂r`. -/
def coneWedgeUnsplit : (⋀[ℝ]^2 V) × V →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) :=
  (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)).comp
      (LinearMap.fst ℝ (⋀[ℝ]^2 V) V) +
    coneWedgeMixed.comp (LinearMap.snd ℝ (⋀[ℝ]^2 V) V)

@[simp] theorem coneWedgeUnsplit_apply (φ : ⋀[ℝ]^2 V) (u : V) :
    coneWedgeUnsplit (φ, u) =
      exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) φ + coneWedgeMixed u := by
  simp [coneWedgeUnsplit]

private lemma exteriorAlgebra_iMulti_two (A B : V × ℝ) :
    ExteriorAlgebra.ιMulti ℝ 2 ![A, B] =
      ExteriorAlgebra.ι ℝ A * ExteriorAlgebra.ι ℝ B := by
  simp [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail]

private lemma exteriorPair_expand (X Y R : V × ℝ) (a b : ℝ) :
    ExteriorAlgebra.ιMulti ℝ 2 ![X + a • R, Y + b • R] =
      ExteriorAlgebra.ιMulti ℝ 2 ![X, Y] +
        ExteriorAlgebra.ιMulti ℝ 2 ![b • X - a • Y, R] := by
  simp_rw [exteriorAlgebra_iMulti_two]
  simp only [map_add, map_smul, map_sub, add_mul, mul_add, sub_mul,
    smul_mul_assoc, mul_smul_comm]
  have hswap : ExteriorAlgebra.ι ℝ R * ExteriorAlgebra.ι ℝ Y =
      -(ExteriorAlgebra.ι ℝ Y * ExteriorAlgebra.ι ℝ R) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap R Y)
  have hsq : ExteriorAlgebra.ι ℝ R * ExteriorAlgebra.ι ℝ R = 0 :=
    ExteriorAlgebra.ι_sq_zero R
  rw [hswap, hsq]
  simp
  module

/-- Decomposition of a decomposable bivector into horizontal and mixed parts. -/
theorem coneWedge_iMulti_decomp (x y : V × ℝ) :
    ιMulti ℝ 2 ![x, y] =
      exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)
          (ιMulti ℝ 2 ![x.1, y.1]) +
        coneWedgeMixed (y.2 • x.1 - x.2 • y.1) := by
  rw [exteriorPower.map_apply_ιMulti]
  have hc : (LinearMap.inl ℝ V ℝ) ∘ ![x.1, y.1] =
      ![(x.1, (0 : ℝ)), (y.1, (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [hc, coneWedgeMixed_apply]
  let R : V × ℝ := ((0 : V), (1 : ℝ))
  let X : V × ℝ := (x.1, (0 : ℝ))
  let Y : V × ℝ := (y.1, (0 : ℝ))
  have hx : x = X + x.2 • R := by
    ext <;> simp [X, R]
  have hy : y = Y + y.2 • R := by
    ext <;> simp [Y, R]
  have hvec : ![x, y] = ![X + x.2 • R, Y + y.2 • R] := by
    funext i
    fin_cases i
    · exact hx
    · exact hy
  have hm : ((y.2 • x.1 - x.2 • y.1, (0 : ℝ)) : V × ℝ) =
      y.2 • X - x.2 • Y := by
    ext <;> simp [X, Y]
  rw [hvec, hm]
  apply Subtype.ext
  simpa only [X, Y, R, exteriorPower.ιMulti_apply_coe, Submodule.coe_add] using
    exteriorPair_expand X Y R x.2 y.2

private theorem map_fst_inl :
    (exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).comp
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)) =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.id_apply]
  congr 1

private theorem mixedPart_map_inl :
    (coneWedgeMixedPart (V := V)).comp
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ)) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.zero_apply]
  have hc : (LinearMap.inl ℝ V ℝ) ∘ ![v 0, v 1] =
      ![((v 0), (0 : ℝ)), ((v 1), (0 : ℝ))] := by
    funext i
    fin_cases i <;> rfl
  rw [hc, coneWedgeMixedPart_iMulti]
  simp

@[simp] theorem coneWedgeSplit_horizontal (φ : ⋀[ℝ]^2 V) :
    coneWedgeSplit
        (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) φ) = (φ, 0) := by
  apply Prod.ext
  · change ((exteriorPower.map 2 (LinearMap.fst ℝ V ℝ)).comp
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ))) φ = φ
    rw [map_fst_inl]
    rfl
  · change ((coneWedgeMixedPart (V := V)).comp
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ))) φ = 0
    rw [mixedPart_map_inl]
    rfl

@[simp] theorem map_fst_coneWedgeMixed (u : V) :
    exteriorPower.map 2 (LinearMap.fst ℝ V ℝ) (coneWedgeMixed u) = 0 := by
  rw [coneWedgeMixed_apply, exteriorPower.map_apply_ιMulti]
  have h : (LinearMap.fst ℝ V ℝ) ∘
      ![(u, (0 : ℝ)), ((0 : V), (1 : ℝ))] = ![u, (0 : V)] := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact (ιMulti ℝ 2).map_coord_zero 1 rfl

@[simp] theorem coneWedgeMixedPart_mixed (u : V) :
    coneWedgeMixedPart (coneWedgeMixed u) = u := by
  rw [coneWedgeMixed_apply, coneWedgeMixedPart_iMulti]
  simp

@[simp] theorem coneWedgeSplit_mixed (u : V) :
    coneWedgeSplit (coneWedgeMixed u) = (0, u) := by
  apply Prod.ext
  · exact map_fst_coneWedgeMixed u
  · exact coneWedgeMixedPart_mixed u

/-- The inverse law for the horizontal/mixed splitting. -/
theorem coneWedgeUnsplit_split :
    (coneWedgeUnsplit (V := V)).comp (coneWedgeSplit (V := V)) =
      LinearMap.id := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    coneWedgeSplit_iMulti, coneWedgeUnsplit_apply, LinearMap.id_apply]
  exact congrArg Subtype.val (coneWedge_iMulti_decomp (v 0) (v 1)).symm

/-- The forward inverse law for the horizontal/mixed splitting. -/
theorem coneWedgeSplit_unsplit :
    (coneWedgeSplit (V := V)).comp (coneWedgeUnsplit (V := V)) =
      LinearMap.id := by
  apply LinearMap.ext
  intro z
  rcases z with ⟨φ, u⟩
  simp only [LinearMap.comp_apply, coneWedgeUnsplit_apply, map_add,
    coneWedgeSplit_horizontal, coneWedgeSplit_mixed, LinearMap.id_apply]
  ext <;> simp

/-- The canonical cone splitting `Λ²(V × ℝ) ≃ₗ Λ²V × V`. -/
def coneWedgeEquiv : ⋀[ℝ]^2 (V × ℝ) ≃ₗ[ℝ] (⋀[ℝ]^2 V) × V where
  toLinearMap := coneWedgeSplit
  invFun := coneWedgeUnsplit
  left_inv φ := by
    have h := LinearMap.congr_fun (coneWedgeUnsplit_split (V := V)) φ
    simpa using h
  right_inv z := by
    have h := LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) z
    simpa using h

@[simp] theorem coneWedgeEquiv_apply (φ : ⋀[ℝ]^2 (V × ℝ)) :
    coneWedgeEquiv φ = coneWedgeSplit φ :=
  rfl

@[simp] theorem coneWedgeEquiv_symm_apply (z : (⋀[ℝ]^2 V) × V) :
    (coneWedgeEquiv (V := V)).symm z = coneWedgeUnsplit z :=
  rfl

/-! ## The diagonal block form -/

/-- The block bilinear form `diag(s² A, 0)` in the cone splitting. -/
def coneWedgeBlockForm (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :
    ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun φ ψ => s ^ 2 * A (coneWedgeSplit φ).1 (coneWedgeSplit ψ).1)
    (by intro φ₁ φ₂ ψ; simp; ring)
    (by intro c φ ψ; simp; ring)
    (by intro φ ψ₁ ψ₂; simp; ring)
    (by intro c φ ψ; simp; ring)

@[simp] theorem coneWedgeBlockForm_apply (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 (V × ℝ)) :
    coneWedgeBlockForm s A φ ψ =
      s ^ 2 * A (coneWedgeSplit φ).1 (coneWedgeSplit ψ).1 :=
  rfl

@[simp] theorem coneWedgeBlockForm_equiv (s : ℝ)
    (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 V) (u v : V) :
    coneWedgeBlockForm s A
        ((coneWedgeEquiv (V := V)).symm (φ, u))
        ((coneWedgeEquiv (V := V)).symm (ψ, v)) = s ^ 2 * A φ ψ := by
  rw [coneWedgeBlockForm_apply, coneWedgeEquiv_symm_apply,
    coneWedgeEquiv_symm_apply]
  have hφ : coneWedgeSplit (coneWedgeUnsplit (φ, u)) = (φ, u) := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) (φ, u)
  have hψ : coneWedgeSplit (coneWedgeUnsplit (ψ, v)) = (ψ, v) := by
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
      LinearMap.congr_fun (coneWedgeSplit_unsplit (V := V)) (ψ, v)
  rw [hφ, hψ]

/-- A cone block supplied by a curvature-operator bilinear form.

The operator itself remains owned by `Curvature.Operator`; this declaration is
only its cone-block transport. -/
def coneCurvatureBlock
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :
    ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ⋀[ℝ]^2 (V × ℝ) →ₗ[ℝ] ℝ :=
  coneWedgeBlockForm s A

@[simp] theorem coneCurvatureBlock_apply
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 (V × ℝ)) :
    coneCurvatureBlock s A φ ψ =
      s ^ 2 * A (coneWedgeSplit φ).1 (coneWedgeSplit ψ).1 :=
  rfl

/-- The mixed/radial block vanishes in the first argument. -/
theorem coneCurvatureBlock_mixed_left
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (u : V) (φ : ⋀[ℝ]^2 (V × ℝ)) :
    coneCurvatureBlock s A (coneWedgeMixed u) φ = 0 := by
  rw [coneCurvatureBlock_apply, coneWedgeSplit_mixed]
  simp

/-- The mixed/radial block vanishes in the second argument. -/
theorem coneCurvatureBlock_mixed_right
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ : ⋀[ℝ]^2 (V × ℝ)) (u : V) :
    coneCurvatureBlock s A φ (coneWedgeMixed u) = 0 := by
  rw [coneCurvatureBlock_apply, coneWedgeSplit_mixed]
  simp

/-- The horizontal block is the scaled input bilinear form. -/
theorem coneCurvatureBlock_horizontal
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 V) :
    coneCurvatureBlock s A
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) φ)
      (exteriorPower.map 2 (LinearMap.inl ℝ V ℝ) ψ) = s ^ 2 * A φ ψ := by
  simp [coneCurvatureBlock]

/-- A symmetric input bilinear form gives a symmetric cone block. -/
theorem coneCurvatureBlock_symm
    (s : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (hA : ∀ φ ψ, A φ ψ = A ψ φ)
    (φ ψ : ⋀[ℝ]^2 (V × ℝ)) :
    coneCurvatureBlock s A φ ψ = coneCurvatureBlock s A ψ φ := by
  rw [coneCurvatureBlock_apply, coneCurvatureBlock_apply]
  rw [hA]

/-- Radial rescaling of a cone block is quadratic in the scale factor. -/
theorem coneCurvatureBlock_scale
    (s c : ℝ) (A : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ)
    (φ ψ : ⋀[ℝ]^2 (V × ℝ)) :
    coneCurvatureBlock (c * s) A φ ψ =
      c ^ 2 * coneCurvatureBlock s A φ ψ := by
  rw [coneCurvatureBlock_apply, coneCurvatureBlock_apply]
  ring

/-! ## The S08 curvature-operator consumer

The next declarations specialize the abstract block to the exact operator
owned by `Ch01.Curvature.Operator`.  They are deliberately algebraic: the
missing S06/S07 pointwise producer is an input to a later module, not silently
reconstructed here.
-/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable {B : W → W → W → W → ℝ}

/-- The source-ordered horizontal cone curvature form `Rm - wedge² g`.

This is the algebraic `(0,4)` form appearing in Morgan--Tian Proposition 1.15
(`morganTian2007`, pp. 40--41).  Here `W` is a fixed inner-product-space
model, so `Curvature.wedgeInner` is the model pairing; it is not an implicit
claim that this form has already been built from a bundled manifold metric. -/
def coneBaseCurvatureDifference (B : W → W → W → W → ℝ) :
    W → W → W → W → ℝ :=
  fun x y z w => B x y z w - Curvature.wedgeInner x y z w

/-- The difference form is algebraic whenever the supplied base form is. -/
theorem isAlgebraicCurvature_coneBaseCurvatureDifference
    (hB : Curvature.IsAlgebraicCurvature B) :
    Curvature.IsAlgebraicCurvature (coneBaseCurvatureDifference B) := by
  exact hB.sub (Curvature.isAlgebraicCurvature_wedgeInner (W := W))

/-- The canonical S08 bilinear curvature operator of the difference form. -/
noncomputable def coneCurvatureDifferenceOperator
    (hB : Curvature.IsAlgebraicCurvature B) :
    (⋀[ℝ]^2 W) →ₗ[ℝ] (⋀[ℝ]^2 W →ₗ[ℝ] ℝ) :=
  Curvature.curvatureOperator
    (isAlgebraicCurvature_coneBaseCurvatureDifference hB)

/-- Decomposable evaluation of the transported difference operator. -/
@[simp] theorem coneCurvatureDifferenceOperator_ιMulti
    (hB : Curvature.IsAlgebraicCurvature B)
    (x y z w : W) :
    coneCurvatureDifferenceOperator hB
        (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, w]) =
      B x y z w - Curvature.wedgeInner x y z w := by
  rw [coneCurvatureDifferenceOperator,
    Curvature.curvatureOperator_ιMulti]
  rfl

/-- The stable algebraic cone-curvature core obtained from the accepted S08
bilinear form.  It is `s² (Rm_N - wedge² g_N)` on horizontal bivectors and
zero on mixed bivectors; the pure radial-radial wedge is already zero in `Λ²`.
The witness `hB` is an algebraic fixed-inner-product-space input, not yet the
selected-extension manifold curvature producer. -/
noncomputable def coneCurvature
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B) :
    (⋀[ℝ]^2 (W × ℝ)) →ₗ[ℝ] (⋀[ℝ]^2 (W × ℝ) →ₗ[ℝ] ℝ) :=
  coneCurvatureBlock s (coneCurvatureDifferenceOperator hB)

/-- Symmetry of the algebraic cone block inherited from the S08 operator. -/
theorem coneCurvature_symm
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (φ ψ : ⋀[ℝ]^2 (W × ℝ)) :
    coneCurvature s hB φ ψ = coneCurvature s hB ψ φ := by
  change coneCurvatureBlock s (coneCurvatureDifferenceOperator hB) φ ψ =
    coneCurvatureBlock s (coneCurvatureDifferenceOperator hB) ψ φ
  apply coneCurvatureBlock_symm
  intro a b
  exact Curvature.curvatureOperator_symm
    (isAlgebraicCurvature_coneBaseCurvatureDifference hB) a b

/-- The complete horizontal block of the S08-backed cone operator. -/
theorem coneCurvature_horizontal
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (φ ψ : ⋀[ℝ]^2 W) :
    coneCurvature s hB
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ) φ)
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ) ψ) =
      s ^ 2 * coneCurvatureDifferenceOperator hB φ ψ := by
  exact coneCurvatureBlock_horizontal s
    (coneCurvatureDifferenceOperator hB) φ ψ

/-- Horizontal decomposable evaluation of the algebraic cone block. -/
@[simp] theorem coneCurvature_horizontal_ιMulti
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (x y z w : W) :
    coneCurvature s hB
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![z, w])) =
      s ^ 2 * (B x y z w - Curvature.wedgeInner x y z w) := by
  rw [coneCurvature, coneCurvatureBlock_horizontal,
    coneCurvatureDifferenceOperator_ιMulti]

/-- Radial rescaling law for the S08-backed cone block. -/
theorem coneCurvature_scale
    (s c : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (φ ψ : ⋀[ℝ]^2 (W × ℝ)) :
    coneCurvature (c * s) hB φ ψ =
      c ^ 2 * coneCurvature s hB φ ψ := by
  exact coneCurvatureBlock_scale s c
    (coneCurvatureDifferenceOperator hB) φ ψ

/-- Flat-base component probe: setting the supplied base curvature form to zero
leaves exactly the negative metric-wedge term. -/
theorem coneCurvature_flat_horizontal_ιMulti
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (hflat : ∀ x y z w, B x y z w = 0)
    (x y z w : W) :
    coneCurvature s hB
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![z, w])) =
      -s ^ 2 * Curvature.wedgeInner x y z w := by
  rw [coneCurvature_horizontal_ιMulti, hflat]
  ring

/-- Constant-curvature component probe: if the supplied base form is `K` times
the metric wedge form, the cone horizontal coefficient is `K - 1`. -/
theorem coneCurvature_constant_horizontal_ιMulti
    (s K : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (hK : ∀ x y z w, B x y z w = K * Curvature.wedgeInner x y z w)
    (x y z w : W) :
    coneCurvature s hB
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![z, w])) =
      s ^ 2 * ((K - 1) * Curvature.wedgeInner x y z w) := by
  rw [coneCurvature_horizontal_ιMulti, hK]
  ring

/-- Constant-curvature model specialization of the horizontal block. -/
theorem coneCurvature_model_horizontal_ιMulti
    (s K : ℝ) (x y z w : W) :
    coneCurvature s
        (Curvature.isAlgebraicCurvature_modelCurvature4 (W := W) K)
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ W ℝ)
          (ιMulti ℝ 2 ![z, w])) =
      s ^ 2 * ((K - 1) * Curvature.wedgeInner x y z w) := by
  apply coneCurvature_constant_horizontal_ιMulti s K
    (Curvature.isAlgebraicCurvature_modelCurvature4 (W := W) K)
  intro a b c d
  rfl

/-! ### Finite-dimensional model probes

These are component-level checks rather than claims that a manifold has been
constructed.  In particular, dimension one removes the horizontal exterior
square, while the cone's mixed factor is handled separately by the mixed-block
theorems below. -/

/-- The horizontal model component is zero in base dimension zero. -/
theorem coneCurvature_model_fin_zero_horizontal_ιMulti
    (s K : ℝ) (x y z w : EuclideanSpace ℝ (Fin 0)) :
    coneCurvature s
        (Curvature.isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 0)) K)
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 0)) ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 0)) ℝ)
          (ιMulti ℝ 2 ![z, w])) = 0 := by
  rw [coneCurvature_model_horizontal_ιMulti]
  simp [Curvature.wedgeInner,
    Subsingleton.elim x (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim y (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim z (0 : EuclideanSpace ℝ (Fin 0)),
    Subsingleton.elim w (0 : EuclideanSpace ℝ (Fin 0))]

/-- The horizontal model component is zero in base dimension one. -/
theorem coneCurvature_model_fin_one_horizontal_ιMulti
    (s K : ℝ) (x y z w : EuclideanSpace ℝ (Fin 1)) :
    coneCurvature s
        (Curvature.isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 1)) K)
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (ιMulti ℝ 2 ![x, y]))
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 1)) ℝ)
          (ιMulti ℝ 2 ![z, w])) = 0 := by
  have hW : Curvature.wedgeInner x y z w = 0 := by
    simpa [Curvature.modelCurvature4, Curvature.wedgeInner] using
      (Curvature.modelCurvature4_fin_one 1 x y z w)
  rw [coneCurvature_model_horizontal_ιMulti, hW]
  ring

/-- A two-dimensional model probe records the horizontal scale and the
reversed-last-slot sign. -/
theorem coneCurvature_model_fin_two_component_probe (s K : ℝ) :
    let e₀ := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
    let e₁ := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
    coneCurvature s
        (Curvature.isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 2)) K)
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (ιMulti ℝ 2 ![((2 : ℝ) • e₀), e₁]))
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (ιMulti ℝ 2 ![e₀, e₁])) = 2 * s ^ 2 * (K - 1) ∧
    coneCurvature s
        (Curvature.isAlgebraicCurvature_modelCurvature4
          (W := EuclideanSpace ℝ (Fin 2)) K)
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (ιMulti ℝ 2 ![((2 : ℝ) • e₀), e₁]))
        (exteriorPower.map 2 (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
          (ιMulti ℝ 2 ![e₁, e₀])) = -(2 * s ^ 2 * (K - 1)) := by
  dsimp
  let e₀ := (EuclideanSpace.basisFun (Fin 2) ℝ) 0
  let e₁ := (EuclideanSpace.basisFun (Fin 2) ℝ) 1
  have h00 : inner ℝ e₀ e₀ = 1 := by
    simpa only [e₀] using (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_one 0
  have h11 : inner ℝ e₁ e₁ = 1 := by
    simpa only [e₁] using (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_one 1
  have h01 : inner ℝ e₀ e₁ = 0 := by
    simpa [e₀, e₁] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).inner_eq_zero
        (by decide : (0 : Fin 2) ≠ 1)
  have h10 : inner ℝ e₁ e₀ = 0 := by
    rw [real_inner_comm, h01]
  have h₁ : Curvature.wedgeInner ((2 : ℝ) • e₀) e₁ e₀ e₁ = 2 := by
    simp only [Curvature.wedgeInner, real_inner_smul_left, h00, h11, h01, h10,
      mul_zero]
    ring
  have h₂ : Curvature.wedgeInner ((2 : ℝ) • e₀) e₁ e₁ e₀ = -2 := by
    simp only [Curvature.wedgeInner, real_inner_smul_left, h00, h11, h01, h10,
      mul_zero]
    ring
  constructor
  · rw [coneCurvature_model_horizontal_ιMulti, h₁]
    ring
  · rw [coneCurvature_model_horizontal_ιMulti, h₂]
    ring

/-- The algebraic cone block vanishes on a mixed first argument. -/
theorem coneCurvature_mixed_left
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (u : W) (φ : ⋀[ℝ]^2 (W × ℝ)) :
    coneCurvature s hB (coneWedgeMixed u) φ = 0 := by
  exact coneCurvatureBlock_mixed_left s
    (coneCurvatureDifferenceOperator hB) u φ

/-- The algebraic cone block vanishes on a mixed second argument. -/
theorem coneCurvature_mixed_right
    (s : ℝ) (hB : Curvature.IsAlgebraicCurvature B)
    (φ : ⋀[ℝ]^2 (W × ℝ)) (u : W) :
    coneCurvature s hB φ (coneWedgeMixed u) = 0 := by
  exact coneCurvatureBlock_mixed_right s
    (coneCurvatureDifferenceOperator hB) φ u

end Models
end Ch01
end MorganTianLib
