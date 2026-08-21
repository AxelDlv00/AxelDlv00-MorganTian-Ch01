/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Michael Rothgang, Dominic Steinitz

This file contains modified code adapted from Mathlib PR #33714 at revision
c4cbb8b896a4db75bf49cf1ab0a898232cede01e.  The adaptation keeps all
construction data private, works at smooth rather than analytic regularity,
and adds the finite-dimensional tangent-bundle corollary.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Existence of smooth Riemannian metrics

This module constructs a smooth Riemannian metric on a smooth real vector
bundle by averaging the pullbacks of a fixed positive-definite form on the
model fiber against a smooth partition of unity.  It then applies the same
construction to tangent bundles of arbitrary finite-dimensional manifolds.

For the tangent-bundle result, the manifold model is not assumed to be an
inner product space.  Instead, Mathlib's finite-dimensional continuous linear
equivalence identifies it with a Euclidean space, whose inner product is pulled
back only as an auxiliary continuous bilinear form.  In particular, the
construction does not assert that the given norm is induced by an inner product.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Definition 1.1
and the following finite-dimensional existence paragraph, printed p. 35.
The repository bibliography records this source as `morganTian2007`.

The bundle construction is modified from the Apache-licensed Mathlib PR
[#33714](https://github.com/leanprover-community/mathlib4/pull/33714), exact
head `c4cbb8b896a4db75bf49cf1ab0a898232cede01e`.  That PR is prior art and is
absent from the pinned Mathlib dependency; it is not imported by this project.
-/

open Set Bundle ContDiff Manifold Module Trivialization SmoothPartitionOfUnity

namespace MorganTianLib
namespace Ch01
namespace MetricExistence

-- The hom-bundle instances below are deeply nested continuous-linear-map instances; the
-- corresponding performance exception is recorded in the E1 roadmap audit.
set_option synthInstance.maxHeartbeats 400000

/-! ## A private metric on the model fiber -/

private structure ModelMetric (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  inner : F →L[ℝ] F →L[ℝ] ℝ
  symm : ∀ u v, inner u v = inner v u
  pos : ∀ v, v ≠ 0 → 0 < inner v v
  normSqBound : ℝ
  normSqBound_pos : 0 < normSqBound
  norm_sq_le : ∀ v, ‖v‖ ^ 2 ≤ normSqBound * inner v v

private lemma ModelMetric.nonneg
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ModelMetric F) (v : F) : 0 ≤ g.inner v v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact (g.pos v hv).le

private noncomputable def innerProductModelMetric
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] : ModelMetric F where
  inner := innerSL ℝ
  symm := by
    intro u v
    rw [innerSL_apply_apply ℝ]
    exact real_inner_comm _ _
  pos := by
    intro v hv
    rw [innerSL_apply_apply ℝ]
    exact real_inner_self_pos.mpr hv
  normSqBound := 1
  normSqBound_pos := zero_lt_one
  norm_sq_le := by
    intro v
    rw [innerSL_apply_apply ℝ, real_inner_self_eq_norm_sq]
    simp

private noncomputable def pullbackInner
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (e : F ≃L[ℝ] G) :
    F →L[ℝ] F →L[ℝ] ℝ :=
  (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).symm (innerSL ℝ)

private lemma pullbackInner_apply
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (e : F ≃L[ℝ] G) (u v : F) :
    pullbackInner e u v = inner ℝ (e u) (e v) := by
  simp only [pullbackInner, ContinuousLinearEquiv.arrowCongr_symm,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl', id_eq]
  rw [innerSL_apply_apply]

private noncomputable def pullbackModelMetric
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] (e : F ≃L[ℝ] G) : ModelMetric F where
  inner := pullbackInner e
  symm := by
    intro u v
    rw [pullbackInner_apply, pullbackInner_apply]
    exact real_inner_comm _ _
  pos := by
    intro v hv
    rw [pullbackInner_apply]
    exact real_inner_self_pos.mpr (by simpa only [map_zero] using e.injective.ne hv)
  normSqBound := ‖(e.symm : G →L[ℝ] F)‖ ^ 2 + 1
  normSqBound_pos := by positivity
  norm_sq_le := by
    intro v
    rw [pullbackInner_apply, real_inner_self_eq_norm_sq]
    have hnorm : ‖v‖ ≤ ‖(e.symm : G →L[ℝ] F)‖ * ‖e v‖ := by
      simpa using (e.symm : G →L[ℝ] F).le_opNorm (e v)
    calc
      ‖v‖ ^ 2 ≤ (‖(e.symm : G →L[ℝ] F)‖ * ‖e v‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
      _ = ‖(e.symm : G →L[ℝ] F)‖ ^ 2 * ‖e v‖ ^ 2 := by ring
      _ ≤ (‖(e.symm : G →L[ℝ] F)‖ ^ 2 + 1) * ‖e v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg _)

/-! ## Partition-of-unity construction -/

variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] [ChartedSpace HB B]
  {IB : ModelWithCorners ℝ EB HB}

noncomputable section

section Smooth

variable [ContMDiffVectorBundle ∞ F V IB]

private def localForm (model : ModelMetric F) (i b : B) :
    TotalSpace (F →L[ℝ] F →L[ℝ] ℝ) (fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) :=
  ⟨b, (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
    (fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) i).symm b model.inner⟩

private def globalForm (model : ModelMetric F) (f : SmoothPartitionOfUnity B IB B) (b : B) :
    V b →L[ℝ] V b →L[ℝ] ℝ :=
  ∑ᶠ j : B, f j b • (localForm (V := V) model j b).2

private lemma localForm_contMDiffOn (model : ModelMetric F) (i : B) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (localForm (V := V) model i)
      ((trivializationAt F V i).baseSet ∩ (chartAt HB i).source) := by
  unfold localForm
  intro b hb
  letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
    (fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) i
  let innerAt : B → F →L[ℝ] F →L[ℝ] ℝ := fun _ ↦ model.inner
  have hsmooth : ContMDiffOn IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun c ↦ (c, innerAt c))
      ((trivializationAt F V i).baseSet ∩ (chartAt HB i).source) :=
    contMDiffOn_id.prodMk contMDiffOn_const
  have htarget : (trivializationAt F V i).baseSet ∩ (chartAt HB i).source ⊆
      (fun c ↦ (c, innerAt c)) ⁻¹' ψ.target := by
    intro c hc
    simp only [Set.mem_preimage]
    rw [ψ.target_eq]
    simp only [Set.mem_prod, Set.mem_univ, and_true]
    have hbase : (trivializationAt F V i).baseSet =
        (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
          (fun x : B ↦ V x →L[ℝ] V x →L[ℝ] ℝ) i).baseSet := by
      simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
        Trivial.trivialization_baseSet, Set.inter_univ, Set.inter_self]
    rw [← hbase]
    exact hc.1
  refine (ContMDiffOn.congr ((contMDiffOn_symm _).comp hsmooth htarget) ?_) b hb
  intro y hy
  simp only [Function.comp_apply]
  ext
  · rfl
  · simp only [innerAt]
    rw [Trivialization.symm_apply ψ _ model.inner]
    · simp
    · exact (mk_mem_target ψ).mp (htarget hy)

private lemma globalForm_contMDiff (model : ModelMetric F) (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source)) :
    ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x
        (globalForm (V := V) model f x)) := by
  let sLoc : (i : B) → (b : B) → V b →L[ℝ] V b →L[ℝ] Trivial B ℝ b :=
    fun i b ↦ (localForm (V := V) model i b).2
  have hterm (j : B) : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (f j x • sLoc j x)) := by
    refine ContMDiffOn.smul_section_of_tsupport ?_
      ((trivializationAt F V j).open_baseSet.inter (chartAt HB j).open_source) (hf j)
      (localForm_contMDiffOn model j)
    exact (f j).contMDiff.contMDiffOn
  unfold globalForm
  apply ContMDiff.finsum_section_of_locallyFinite ?_ hterm
  apply f.locallyFinite.subset fun i x hx ↦ ?_
  change f i x ≠ 0
  intro hzero
  apply hx
  ext u v
  simp [hzero]

end Smooth

section Algebraic

open scoped Classical in
private def localFormAux (model : ModelMetric F) (i p : B) : V p →L[ℝ] V p →L[ℝ] ℝ :=
  if hp : p ∈ (trivializationAt F V i).baseSet then
    let e : V p ≃L[ℝ] F := (trivializationAt F V i).continuousLinearEquivAt ℝ p hp
    (e.arrowCongr (e.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))).symm model.inner
  else 0

private def globalFormAux (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (p : B) : V p →L[ℝ] V p →L[ℝ] ℝ :=
  ∑ᶠ j : B, f j p • localFormAux (V := V) model j p

private lemma localFormAux_apply (model : ModelMetric F) {i p : B}
    (hp : p ∈ (trivializationAt F V i).baseSet) (u v : V p) :
    localFormAux (V := V) model i p u v =
      model.inner ((trivializationAt F V i).continuousLinearEquivAt ℝ p hp u)
        ((trivializationAt F V i).continuousLinearEquivAt ℝ p hp v) := by
  unfold localFormAux
  rw [dif_pos hp]
  simp only [ContinuousLinearEquiv.arrowCongr_symm, ContinuousLinearEquiv.arrowCongr_apply,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearEquiv.refl_symm,
    ContinuousLinearEquiv.coe_refl', id_eq]

private lemma localFormAux_of_not_mem (model : ModelMetric F) {i p : B}
    (hp : p ∉ (trivializationAt F V i).baseSet) :
    localFormAux (V := V) model i p = 0 := by
  unfold localFormAux
  rw [dif_neg hp]

private lemma localFormAux_nonneg (model : ModelMetric F) {j b : B} (v : V b) :
    0 ≤ localFormAux (V := V) model j b v v := by
  by_cases hb : b ∈ (trivializationAt F V j).baseSet
  · rw [localFormAux_apply model hb]
    exact model.nonneg _
  · rw [localFormAux_of_not_mem model hb]
    simp

private lemma localFormAux_pos (model : ModelMetric F) {i b : B}
    (hb : b ∈ (trivializationAt F V i).baseSet ∩ (chartAt HB i).source)
    (v : V b) (hv : v ≠ 0) : 0 < localFormAux (V := V) model i b v v := by
  rw [localFormAux_apply model hb.1]
  apply model.pos
  simpa only [map_zero] using
    ((trivializationAt F V i).continuousLinearEquivAt ℝ b hb.1).injective.ne hv

private lemma localFormAux_symm (model : ModelMetric F) (i p : B) (v w : V p) :
    localFormAux (V := V) model i p v w = localFormAux (V := V) model i p w v := by
  by_cases hp : p ∈ (trivializationAt F V i).baseSet
  · rw [localFormAux_apply model hp, localFormAux_apply model hp]
    exact model.symm _ _
  · rw [localFormAux_of_not_mem model hp]
    rfl

private def evalAt (b : B) (v w : V b) : (V b →L[ℝ] V b →L[ℝ] ℝ) →+ ℝ where
  toFun φ := (φ.toFun v).toFun w
  map_zero' := by simp
  map_add' _ _ := rfl

private lemma globalFormAux_support_finite (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (b : B) :
    (Function.support fun j ↦ (f j b • localFormAux (V := V) model j b :
      V b →L[ℝ] V b →L[ℝ] ℝ)).Finite :=
  (f.locallyFinite.point_finite b).subset (fun i hi ↦ by
    have hne : f i b • localFormAux (V := V) model i b ≠ 0 := hi
    have hfi : f i b ≠ 0 := by
      intro h
      apply hne
      ext y z
      simp [h]
    change f i b ≠ 0
    exact hfi)

set_option maxHeartbeats 800000 in
private lemma globalFormAux_symm (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (b : B) (v w : V b) :
    ((globalFormAux (V := V) model f b).toFun v).toFun w =
      ((globalFormAux (V := V) model f b).toFun w).toFun v := by
  unfold globalFormAux
  have hfinite := globalFormAux_support_finite (V := V) model f b
  have hfinite' : Function.HasFiniteSupport
      (fun j : B ↦ (f j b • localFormAux (V := V) model j b :
        V b →L[ℝ] V b →L[ℝ] ℝ)) := hfinite
  change evalAt b v w (∑ᶠ j : B, f j b • localFormAux (V := V) model j b) =
    evalAt b w v (∑ᶠ j : B, f j b • localFormAux (V := V) model j b)
  rw [(evalAt b v w).map_finsum
      (f := fun j : B ↦ (f j b • localFormAux (V := V) model j b :
        V b →L[ℝ] V b →L[ℝ] ℝ)) hfinite',
    (evalAt b w v).map_finsum
      (f := fun j : B ↦ (f j b • localFormAux (V := V) model j b :
        V b →L[ℝ] V b →L[ℝ] ℝ)) hfinite']
  apply finsum_congr
  intro j
  exact congrArg (HMul.hMul (f j b)) (localFormAux_symm (V := V) model j b v w)

omit [TopologicalSpace B] in
private lemma smul_apply_self {b : B} (c : ℝ) (φ : V b →L[ℝ] V b →L[ℝ] ℝ) (v : V b) :
    ((c • φ).toFun v).toFun v = c * ((φ.toFun v).toFun v) := by simp

private lemma globalFormAux_apply_self (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (b : B) (v : V b) :
    ((globalFormAux (V := V) model f b).toFun v).toFun v =
      ∑ᶠ j : B, (((f j b • localFormAux (V := V) model j b).toFun v).toFun v) := by
  have hfinite := globalFormAux_support_finite (V := V) model f b
  have hmap := (evalAt b v v).map_finsum
    (f := fun j : B ↦ f j b • localFormAux (V := V) model j b) hfinite
  unfold globalFormAux
  simpa only [evalAt, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddHom.coe_mk] using hmap

private lemma globalFormAux_term_support_finite (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (b : B) (v : V b) :
    (Function.support fun j ↦ (f j b • localFormAux (V := V) model j b) v v).Finite := by
  apply (globalFormAux_support_finite (V := V) model f b).subset
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj ⊢
  exact fun hz ↦ hj (by rw [hz]; simp)

set_option maxHeartbeats 800000 in
private lemma globalFormAux_pos (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (b : B) {v : V b} (hv : v ≠ 0) : 0 < globalFormAux (V := V) model f b v v := by
  change 0 < ((globalFormAux (V := V) model f b).toFun v).toFun v
  rw [globalFormAux_apply_self]
  have hnonneg : ∀ j, 0 ≤ (f j b • localFormAux (V := V) model j b) v v := fun j ↦ by
    change 0 ≤ f j b * localFormAux (V := V) model j b v v
    exact mul_nonneg (f.nonneg j b) (localFormAux_nonneg model v)
  obtain ⟨i, hi⟩ : ∃ i, 0 < f i b := f.exists_pos_of_mem trivial
  have hib : b ∈ (trivializationAt F V i).baseSet ∩ (chartAt HB i).source :=
    hf i (subset_closure (Function.mem_support.mpr hi.ne'))
  refine finsum_pos hnonneg ⟨i, ?_⟩ (globalFormAux_term_support_finite model f b v)
  rw [smul_apply_self]
  exact mul_pos hi (localFormAux_pos model hib v hv)

set_option maxHeartbeats 800000 in
private lemma localTerm_le_globalFormAux (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B) (b i : B) (v : V b) :
    f i b * localFormAux (V := V) model i b v v ≤ globalFormAux (V := V) model f b v v := by
  change f i b * ((localFormAux (V := V) model i b).toFun v).toFun v ≤
    ((globalFormAux (V := V) model f b).toFun v).toFun v
  rw [globalFormAux_apply_self, ← smul_apply_self (f i b)]
  refine single_le_finsum i (globalFormAux_term_support_finite model f b v) (fun j ↦ ?_)
  change 0 ≤ f j b * localFormAux (V := V) model j b v v
  exact mul_nonneg (f.nonneg j b) (localFormAux_nonneg model v)

set_option maxHeartbeats 800000 in
private lemma globalFormAux_unitBall_bounded (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (b : B) :
    Bornology.IsVonNBounded ℝ {v : V b | globalFormAux (V := V) model f b v v < 1} := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < f i b := f.exists_pos_of_mem trivial
  have hib : b ∈ (trivializationAt F V i).baseSet ∩ (chartAt HB i).source :=
    hf i (subset_closure (Function.mem_support.mpr hi.ne'))
  set e := (trivializationAt F V i).continuousLinearEquivAt ℝ b hib.1 with he
  have hball : Bornology.IsVonNBounded ℝ
      (Metric.closedBall (0 : F) (Real.sqrt (model.normSqBound / f i b))) :=
    (NormedSpace.isVonNBounded_iff ℝ).2 Metric.isBounded_closedBall
  apply (hball.image (e.symm : F →L[ℝ] V b)).subset
  intro v hv
  change globalFormAux (V := V) model f b v v < 1 at hv
  refine ⟨e v, ?_, e.symm_apply_apply v⟩
  rw [mem_closedBall_zero_iff]
  have hterm := localTerm_le_globalFormAux (V := V) model f b i v
  rw [localFormAux_apply model hib.1, ← he] at hterm
  have hlt : f i b * model.inner (e v) (e v) < 1 := lt_of_le_of_lt hterm hv
  have hscaled : f i b * ‖e v‖ ^ 2 < model.normSqBound := by
    calc
      f i b * ‖e v‖ ^ 2 ≤ f i b * (model.normSqBound * model.inner (e v) (e v)) :=
        mul_le_mul_of_nonneg_left (model.norm_sq_le (e v)) hi.le
      _ = model.normSqBound * (f i b * model.inner (e v) (e v)) := by ring
      _ < model.normSqBound * 1 := mul_lt_mul_of_pos_left hlt model.normSqBound_pos
      _ = model.normSqBound := mul_one _
  have hnormSq : ‖e v‖ ^ 2 ≤ model.normSqBound / f i b :=
    (le_div_iff₀ hi).2 (by simpa [mul_comm] using hscaled.le)
  calc
    ‖e v‖ = Real.sqrt (‖e v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (model.normSqBound / f i b) := Real.sqrt_le_sqrt hnormSq

end Algebraic

section Agreement

private lemma inCoordinates_apply_bilinear
    {x₀ x : B} {φ : V x →L[ℝ] V x →L[ℝ] ℝ} {v w : F}
    (hx : x ∈ (trivializationAt F V x₀).baseSet) :
    ContinuousLinearMap.inCoordinates F V (F →L[ℝ] ℝ) (fun y ↦ V y →L[ℝ] ℝ)
      x₀ x x₀ x φ v w =
      φ ((trivializationAt F V x₀).symm x v) ((trivializationAt F V x₀).symm x w) := by
  rw [inCoordinates_apply_eq₂ hx hx (by simp [Trivial.fiberBundle_trivializationAt'])]
  simp [Trivial.fiberBundle_trivializationAt', Trivial.linearMapAt_trivialization]

set_option maxHeartbeats 800000 in
private lemma homTrivialization_symm_apply
    (x₀ x : B) (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (φ : F →L[ℝ] F →L[ℝ] ℝ) (u v : V x) :
    (trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
      (fun y : B ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x₀).symm x φ u v =
      φ ((trivializationAt F V x₀).continuousLinearMapAt ℝ x u)
        ((trivializationAt F V x₀).continuousLinearMapAt ℝ x v) := by
  letI ψ := trivializationAt (F →L[ℝ] F →L[ℝ] ℝ)
    (fun y : B ↦ V y →L[ℝ] V y →L[ℝ] ℝ) x₀
  letI χ := trivializationAt F V x₀
  letI w := ψ.symm x φ
  have hc : x ∈ ψ.baseSet := by
    rw [hom_trivializationAt_baseSet]
    simp only [hom_trivializationAt_baseSet, Trivial.fiberBundle_trivializationAt',
      Trivial.trivialization_baseSet, inter_univ, inter_self]
    exact hx
  have h₁ :
      (continuousLinearMapAt
          (E := fun y : B ↦ V y →L[ℝ] V y →L[ℝ] ℝ) ℝ ψ x)
        (ψ.symmL ℝ x φ) = φ :=
    continuousLinearMapAt_symmL ψ hc φ
  have h₂ : ∀ a b, φ a b = w (χ.symm x a) (χ.symm x b) := fun a b ↦ by
    rw [← h₁, continuousLinearMapAt_apply, linearMapAt_apply, hom_trivializationAt_apply,
      if_pos hc, ← inCoordinates_apply_bilinear hx, symmL_apply]
    exact hc
  have hu := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F V x₀) hx u
  rw [symmL_apply] at hu
  · have hv := symmL_continuousLinearMapAt (R := ℝ) (trivializationAt F V x₀) hx v
    rw [symmL_apply] at hv
    · rw [show w u v = φ (χ.continuousLinearMapAt ℝ x u)
          (χ.continuousLinearMapAt ℝ x v) from by
        rw [h₂ (χ.continuousLinearMapAt ℝ x u) (χ.continuousLinearMapAt ℝ x v), hu, hv]]
    · exact hx
  · exact hx

private lemma globalForm_eq_aux (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (p : B) (u v : V p) :
    globalForm (V := V) model f p u v = globalFormAux (V := V) model f p u v := by
  have heq : globalForm (V := V) model f p = globalFormAux (V := V) model f p := by
    unfold globalForm globalFormAux
    congr 1
    ext j
    congr 2
    ext a b
    by_cases hj : f j p = 0
    · have h₁ : f j p • (localForm (V := V) model j p).2 = 0 := by
        ext x y
        simp [hj]
      have h₂ : f j p • localFormAux (V := V) model j p = 0 := by
        ext x y
        simp [hj]
      rw [h₁, h₂]
      rfl
    · have hp : p ∈ tsupport (f j) := subset_closure hj
      have hsupp : p ∈ (trivializationAt F V j).baseSet ∩ (chartAt HB j).source := hf j hp
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      congr 1
      change (localForm (V := V) model j p).2 a b = localFormAux (V := V) model j p a b
      rw [localFormAux_apply model hsupp.1]
      unfold localForm
      conv_lhs => rw [homTrivialization_symm_apply j p hsupp.1 model.inner a b]
      rw [coe_continuousLinearEquivAt_eq _ hsupp.1]
  rw [heq]

private lemma globalForm_symm (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v w : V b) :
    globalForm (V := V) model f b v w = globalForm (V := V) model f b w v := by
  rw [globalForm_eq_aux model f hf b v w, globalForm_eq_aux model f hf b w v]
  exact globalFormAux_symm model f b v w

private lemma globalForm_pos (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (b : B) (v : V b) (hv : v ≠ 0) : 0 < globalForm (V := V) model f b v v := by
  rw [globalForm_eq_aux model f hf b v v]
  exact globalFormAux_pos model f hf b hv

private lemma globalForm_unitBall_bounded (model : ModelMetric F)
    (f : SmoothPartitionOfUnity B IB B)
    (hf : f.IsSubordinate
      (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source))
    (b : B) :
    Bornology.IsVonNBounded ℝ {v : V b | globalForm (V := V) model f b v v < 1} := by
  simp_rw [fun v ↦ globalForm_eq_aux model f hf b v v]
  exact globalFormAux_unitBall_bounded model f hf b

end Agreement

private theorem nonempty_contMDiffRiemannianMetric_of_modelMetric
    [FiniteDimensional ℝ EB] [SigmaCompactSpace B] [T2Space B]
    [IsManifold IB ∞ B] [ContMDiffVectorBundle ∞ F V IB]
    (model : ModelMetric F) : Nonempty (Bundle.ContMDiffRiemannianMetric IB ∞ F V) :=
  let ⟨f, hf⟩ : ∃ f : SmoothPartitionOfUnity B IB B,
      f.IsSubordinate
        (fun x ↦ (trivializationAt F V x).baseSet ∩ (chartAt HB x).source) := by
    apply SmoothPartitionOfUnity.exists_isSubordinate
    · exact isClosed_univ
    · intro i
      exact (trivializationAt F V i).open_baseSet.inter (chartAt HB i).open_source
    · intro b _
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨b, FiberBundle.mem_baseSet_trivializationAt' b, mem_chart_source HB b⟩
  ⟨{
    inner := globalForm (V := V) model f
    symm := globalForm_symm model f hf
    pos := globalForm_pos model f hf
    isVonNBounded := globalForm_unitBall_bounded model f hf
    contMDiff := globalForm_contMDiff model f hf
  }⟩

end

/-! ## Public existence theorems -/

/--
A smooth real vector bundle over a finite-dimensional, sigma-compact Hausdorff
smooth manifold admits a smooth Riemannian metric when its model fiber has a
topology-compatible real inner product.

This is the bundle form of the finite-dimensional existence paragraph after
Morgan--Tian Definition 1.1, printed p. 35.  The base model, but not the model
fiber, is required to be finite-dimensional.  The bibliography key is
`morganTian2007`.
-/
theorem nonempty_contMDiffRiemannianMetric
    {B : Type*} [TopologicalSpace B]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {HB : Type*} [TopologicalSpace HB]
    {IB : ModelWithCorners ℝ EB HB}
    [ChartedSpace HB B] [IsManifold IB ∞ B]
    [ContMDiffVectorBundle ∞ F V IB] [SigmaCompactSpace B] [T2Space B] :
    Nonempty (Bundle.ContMDiffRiemannianMetric IB ∞ F V) :=
  nonempty_contMDiffRiemannianMetric_of_modelMetric (innerProductModelMetric F)

private noncomputable def euclideanModelEquiv
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  toEuclidean

private noncomputable def finiteDimensionalModelMetric
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ModelMetric E :=
  pullbackModelMetric (euclideanModelEquiv E)

/--
Every finite-dimensional, sigma-compact Hausdorff smooth manifold admits a
smooth Riemannian metric on its tangent bundle.

No inner product is assumed on the manifold model.  The proof transports the
Euclidean inner product through Mathlib's finite-dimensional continuous linear
equivalence, and uses the resulting form only inside the partition-of-unity
construction.  This is the source-strength tangent-bundle corollary of the
existence paragraph after Morgan--Tian Definition 1.1, printed p. 35; the
bibliography key is `morganTian2007`.
-/
theorem nonempty_contMDiffRiemannianMetric_tangentSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] :
    Nonempty (Bundle.ContMDiffRiemannianMetric I ∞ E
      (fun x : M ↦ TangentSpace (M := M) I x)) :=
  nonempty_contMDiffRiemannianMetric_of_modelMetric
    (B := M) (F := E) (V := fun x : M ↦ TangentSpace (M := M) I x)
    (EB := E) (HB := H) (IB := I)
    (finiteDimensionalModelMetric E)

/-! ## Typeclass synthesis checks -/

example : Nonempty (Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
    (Bundle.Trivial ℝ ℝ)) :=
  nonempty_contMDiffRiemannianMetric

example : Nonempty (Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ) ∞ ℝ
    (fun x : ℝ ↦ TangentSpace 𝓘(ℝ, ℝ) x)) :=
  nonempty_contMDiffRiemannianMetric_tangentSpace

example : Nonempty (Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, ℝ × ℝ) ∞ (ℝ × ℝ)
    (fun x : ℝ × ℝ ↦ TangentSpace 𝓘(ℝ, ℝ × ℝ) x)) :=
  nonempty_contMDiffRiemannianMetric_tangentSpace

end MetricExistence
end Ch01
end MorganTianLib
