import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Pullback bilinear forms

This file supplies the bundle-valued pullback operation needed by the open-cone
metric.  For a family `b` of bilinear forms on a target manifold and a smooth
map `F`, the form at `x` is

`b (F x) (dF_x v) (dF_x w)`.

The pinned Mathlib bundle API exposes smooth sections and their coordinate
criteria, but does not provide this pullback constructor.  The local
trivialization proof below is therefore kept here as a reusable Chapter 1
helper.  It uses only the canonical tangent-bundle and hom-bundle APIs; no
coordinate metric or competing Riemannian structure is introduced.

The construction is the standard pullback metric operation (Morgan--Tian,
Definition 1.1 and the pullback discussion following it, `morganTian2007`).
The local-coordinate argument follows the analogous Mathlib-oriented
development in Lee's pullback metric construction, while remaining a native
consumer of the pinned Mathlib declarations.
-/

noncomputable section

open Bundle Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace MorganTianLib
namespace Ch01

section Pullback

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- Pull a family of bilinear forms back along the differential of a map. -/
noncomputable def pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' F p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem pullbackFormOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (F : M → M') (p : M) (v w : TangentSpace I p) :
    pullbackFormOf b F p v w =
      b (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

/-- A bilinear family transported by an arbitrary family of bundle maps.

`pullbackFormOf` is the special case in which `A p` is the differential of a
map.  Keeping the family abstract makes the smoothness lemma useful for later
bundle constructions as well. -/
noncomputable def bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A' : E →L[ℝ] E' := A p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A' A' : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem bilinearCompOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M)
    (v w : TangentSpace I p) :
    bilinearCompOf b A p v w = b (F p) (A p v) (A p w) :=
  rfl

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- `pullbackFormOf` is `bilinearCompOf` for the differential family. -/
theorem pullbackFormOf_eq_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (F : M → M') (p : M) :
    pullbackFormOf b F p = bilinearCompOf b (fun x => mfderiv I I' F x) p :=
  rfl
/-! ### Smoothness of transported forms -/

/-- A smooth bilinear family remains smooth after transport by a smooth family
of tangent-space linear maps whose coordinate representation is smooth. -/
theorem contMDiffAt_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I'
      (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y => (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y => TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} {x₀ : M}
    (hF : ContMDiffAt I I' ∞ F x₀)
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x))
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞
      (inTangentCoordinates I I' id F A x₀) x₀) :
    ContMDiffAt I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, bilinearCompOf b A x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (F x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : F x₀ ∈ tT.baseSet :=
    mem_baseSet_trivializationAt E' (TangentSpace I') (F x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id F A x₀ with hD
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I') (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ)
      (F x₀) y (F x₀) y (b y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (F x₀) :=
    ((contMDiffAt_hom_bundle _).mp hb.contMDiffAt).2
  have hPsi : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (F x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (F x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hF).clm_comp hA
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hA).clm_comp h1
  refine hPsi.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | F x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hF.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b' => ?_
  have hRHS :
      (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (F x)).comp (D x))) a) b' =
        G (F x) (D x a) (D x b') := rfl
  have hkey : ∀ u : E, tT.symm (F x) (D x u) = A x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (F x) hfx
        (A x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (F x) : E' → TangentSpace I' (F x)) =
        ⇑(tT.continuousLinearEquivAt ℝ (F x) hfx).symm := rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x) =
        ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' :
      trivializationAt ℝ (Bundle.Trivial M' ℝ) (F x₀) =
        Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM :
      trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ =
        Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization,
    LinearMap.id_coe, id_eq, bilinearCompOf_apply, ← htT, ← hsT, hkey]

/-- Pullback along a smooth map is a smooth bundle section. -/
theorem contMDiff_pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I'
      (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y => (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y => TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} (hF : ContMDiff I I' ∞ F) :
    ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, pullbackFormOf b F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := fun x₀ =>
  contMDiffAt_bilinearCompOf b hb hF.contMDiffAt
    (fun x => mfderiv I I' F x)
    (hF.contMDiffAt.mfderiv_const (by simp))

/-- The Riemannian specialization of `contMDiff_pullbackFormOf`. -/
theorem pullbackForm_contMDiff
    (g' : Bundle.ContMDiffRiemannianMetric I' ∞ E'
      (TangentSpace I' : M' → Type _))
    {F : M → M'} (hF : ContMDiff I I' ∞ F) :
    ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => (⟨x, pullbackFormOf (fun y => g'.inner y) F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
  contMDiff_pullbackFormOf (fun y => g'.inner y) g'.contMDiff hF

end Pullback

end Ch01
end MorganTianLib
