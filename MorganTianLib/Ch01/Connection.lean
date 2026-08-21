/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth

This file contains modified code adapted from Mathlib PR #36845 at revision
41e2b25a520d7a24f37062855d2b091dab7a5d9d and smooth-frame material adapted
from Mathlib PR #36036 at revision 31613e7e48c4559a8be4de48121c911d74586744.
The adaptation makes the metric an explicit argument, keeps construction
helpers private, and completes the Chapter 1 public API and regularity proof.
-/
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# The Levi--Civita connection

This module constructs the Levi--Civita connection of an explicit smooth
Riemannian metric as Mathlib's bundled
`CovariantDerivative I E (TangentSpace I)`.  It proves metric compatibility,
vanishing torsion, the source-ordered Koszul formula, uniqueness on vector
fields differentiable at the point of evaluation, and smooth covariant-
derivative regularity.

The construction uses the Koszul formula and the fibrewise Riesz isomorphism.
Values on vector fields that are not differentiable at the evaluation point
are deliberately set to zero: Mathlib's bundled connection axioms do not
constrain those values, so no unrestricted extensional uniqueness is claimed.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Theorem 1.2,
printed pp. 35--36.  Cross-checks: do Carmo (1992), Theorem 3.6 and Remark
3.7/formula (10), printed pp. 55--56, and Lee (2018), Theorem 5.10 and
Corollary 5.11(b), equation (5.10), printed pp. 123--124.

The producer is modified from the Apache-licensed Mathlib PR
[#36845](https://github.com/leanprover-community/mathlib4/pull/36845), exact
head `41e2b25a520d7a24f37062855d2b091dab7a5d9d`; that PR is prior art and is
not imported by this project.  The private smooth-frame argument is modified
from Apache-licensed Mathlib PR
[#36036](https://github.com/leanprover-community/mathlib4/pull/36036), exact
head `31613e7e48c4559a8be4de48121c911d74586744`.
-/

open Bundle FiberBundle Filter Function Module NormedSpace VectorField
open scoped Bundle ContDiff Manifold RealInnerProductSpace

namespace MorganTianLib
namespace Ch01
namespace Connection

attribute [local fun_prop] MDifferentiable MDifferentiableAt
  MDifferentiable.add MDifferentiableAt.add
  mdifferentiableAt_add_section MDifferentiableAt.smul_section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ## Private smooth-frame infrastructure -/

section SmoothFrame

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
  [(y : M) → NormedAddCommGroup (V y)] [(y : M) → InnerProductSpace ℝ (V y)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {ι : Type*} {i : ι} {s : ι → (x : M) → V x} {u : Set M} {x : M}

variable [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

attribute [local instance] IsWellOrder.toHasWellFounded

private noncomputable def gramSchmidtSection
    (s : ι → (x : M) → V x) (i : ι) (x : M) : V x :=
  InnerProductSpace.gramSchmidt ℝ (s · x) i

private noncomputable def gramSchmidtNormedSection
    (s : ι → (x : M) → V x) (i : ι) (x : M) : V x :=
  InnerProductSpace.gramSchmidtNormed ℝ (s · x) i

omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma contMDiffWithinAt_inner_div_norm_sq
    {v w : (x : M) → V x}
    (hv : CMDiffAt[u] ∞ (T% v) x) (hw : CMDiffAt[u] ∞ (T% w) x) (hv₀ : v x ≠ 0) :
    CMDiffAt[u] ∞ (fun y ↦ inner ℝ (v y) (w y) / ‖v y‖ ^ 2) x := by
  have h := (hv.inner_bundle hw).smul ((hv.inner_bundle hv).inv₀ (inner_self_ne_zero.mpr hv₀))
  apply h.congr
  · intro y hy
    congr
    simp [inner_self_eq_norm_sq_to_K]
  · congr
    rw [← real_inner_self_eq_norm_sq]

omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma ContMDiffWithinAt.orthogonalProjection_section
    {v w : (x : M) → V x}
    (hv : CMDiffAt[u] ∞ (T% v) x) (hw : CMDiffAt[u] ∞ (T% w) x) (hv₀ : v x ≠ 0) :
    CMDiffAt[u] ∞
      (T% (fun y ↦ (Submodule.span ℝ {v y}).starProjection (w y))) x := by
  simp_rw [Submodule.starProjection_singleton]
  exact (contMDiffWithinAt_inner_div_norm_sq hv hw hv₀).smul_section hv

omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma contMDiffWithinAt_norm_section
    {v : (x : M) → V x}
    (hv : CMDiffAt[u] ∞ (T% v) x) (hv₀ : v x ≠ 0) :
    CMDiffAt[u] ∞ (‖v ·‖) x := by
  let f (y : M) := inner ℝ (v y) (v y)
  have h : CMDiffAt[u] ∞ (Real.sqrt ∘ f) x := by
    have hsqrt : CMDiffAt[(f '' u)] ∞ Real.sqrt (f x) := by
      apply ContMDiffAt.contMDiffWithinAt
      rw [contMDiffAt_iff_contDiffAt]
      exact Real.contDiffAt_sqrt (by simp [f, hv₀])
    exact hsqrt.comp x (hv.inner_bundle hv) (Set.mapsTo_image _ u)
  convert h
  simp [f]

set_option backward.isDefEq.respectTransparency.types false in
omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma gramSchmidtSection_contMDiffWithinAt
    (hs : ∀ j, CMDiffAt[u] ∞ (T% (s j)) x) {i : ι}
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt[u] ∞ (T% (gramSchmidtSection s i)) x := by
  suffices CMDiffAt[u] ∞ (T% (fun y ↦ s i y - ∑ j ∈ Finset.Iio i,
      (ℝ ∙ gramSchmidtSection s j y).starProjection (s i y))) x by
    simp_rw [gramSchmidtSection]
    apply this.congr
    · intro y _
      rw [InnerProductSpace.gramSchmidt_def]
      simp [gramSchmidtSection]
    · rw [InnerProductSpace.gramSchmidt_def]
      simp [gramSchmidtSection]
  apply (hs i).sub_section
  apply ContMDiffWithinAt.sum_section
  intro j hj
  let inclusion : {k // k ∈ Set.Iic j} → {k // k ∈ Set.Iic i} :=
    fun ⟨k, hk⟩ ↦ ⟨k, hk.trans (Finset.mem_Iio.mp hj).le⟩
  have hli : LinearIndependent ℝ
      ((fun k ↦ s k x) ∘ @Subtype.val ι fun k ↦ k ∈ Set.Iic j) := by
    apply hs'.comp inclusion
    intro ⟨k, hk⟩ ⟨l, hl⟩ hkl
    simp_all only [Subtype.mk.injEq, inclusion]
  apply ContMDiffWithinAt.orthogonalProjection_section
    (gramSchmidtSection_contMDiffWithinAt (i := j) hs hli) (hs i)
  exact InnerProductSpace.gramSchmidt_ne_zero_coe j hli
termination_by i
decreasing_by exact (LocallyFiniteOrderBot.finset_mem_Iio i j).mp hj

omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma gramSchmidtNormedSection_contMDiffWithinAt
    (hs : ∀ j, CMDiffAt[u] ∞ (T% (s j)) x) {i : ι}
    (hs' : LinearIndependent ℝ ((s · x) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiffAt[u] ∞ (T% (gramSchmidtNormedSection s i)) x := by
  have h : CMDiffAt[u] ∞ (T% (fun y ↦
      ‖gramSchmidtSection s i y‖⁻¹ • gramSchmidtSection s i y)) x := by
    refine ContMDiffWithinAt.smul_section ?_ (gramSchmidtSection_contMDiffWithinAt hs hs')
    refine ContMDiffWithinAt.inv₀ ?_ ?_
    · exact contMDiffWithinAt_norm_section
        (gramSchmidtSection_contMDiffWithinAt hs hs')
        (InnerProductSpace.gramSchmidt_ne_zero_coe i hs')
    · exact norm_ne_zero_iff.mpr (InnerProductSpace.gramSchmidt_ne_zero_coe i hs')
  exact h.congr (fun _ _ ↦ rfl) rfl

omit [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] in
private lemma gramSchmidtNormedSection_contMDiffOn
    (hs : ∀ j, CMDiff[u] ∞ (T% (s j))) {i : ι}
    (hs' : ∀ y ∈ u, LinearIndependent ℝ ((s · y) ∘ ((↑) : Set.Iic i → ι))) :
    CMDiff[u] ∞ (T% (gramSchmidtNormedSection s i)) :=
  fun y hy ↦ gramSchmidtNormedSection_contMDiffWithinAt
    (fun j ↦ hs j y hy) (hs' y hy)

private noncomputable def orthonormalFrame
    (t : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas t]
    (b : Basis ι ℝ F) : ι → (x : M) → V x :=
  gramSchmidtNormedSection (t.localFrame b)

omit [IsManifold I ∞ M] in
private theorem isLocalFrameOn_orthonormalFrame
    [Fintype ι]
    (t : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas t] (b : Basis ι ℝ F) :
    IsLocalFrameOn I F ∞ (orthonormalFrame t b) t.baseSet := by
  let hlocal := t.isLocalFrameOn_localFrame_baseSet I ∞ b
  refine
    { linearIndependent := fun hy ↦ ?_
      generating := fun hy ↦ ?_
      contMDiffOn := fun i ↦ ?_ }
  · exact InnerProductSpace.gramSchmidtNormed_linearIndependent (hlocal.linearIndependent hy)
  · change ⊤ ≤ Submodule.span ℝ
      (Set.range (InnerProductSpace.gramSchmidtNormed ℝ (t.localFrame b · _)))
    rw [InnerProductSpace.span_gramSchmidtNormed_range,
      InnerProductSpace.span_gramSchmidt]
    exact hlocal.generating hy
  · apply gramSchmidtNormedSection_contMDiffOn
    · exact fun j ↦ hlocal.contMDiffOn j
    · intro y hy
      exact (hlocal.linearIndependent hy).comp _ Subtype.coe_injective

private theorem orthonormal_orthonormalFrame
    [Fintype ι]
    (t : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas t] (b : Basis ι ℝ F) {y : M} (hy : y ∈ t.baseSet) :
    Orthonormal ℝ (orthonormalFrame t b · y) :=
  InnerProductSpace.gramSchmidtNormed_orthonormal
    (by
      convert (t.basisAt b hy).linearIndependent
      simp [t.localFrame_apply_of_mem_baseSet b hy])

omit [IsManifold I ∞ M] in
private theorem orthonormalFrame_coeff_eq_inner
    [Fintype ι]
    (t : Trivialization F (Bundle.TotalSpace.proj : Bundle.TotalSpace F V → M))
    [MemTrivializationAtlas t] (b : Basis ι ℝ F) {y : M} (hy : y ∈ t.baseSet)
    (W : (y : M) → V y) (i : ι) :
    let hs := isLocalFrameOn_orthonormalFrame (I := I) t b
    hs.coeff i y (W y) = inner ℝ (orthonormalFrame t b i y) (W y) := by
  dsimp only
  let hs := isLocalFrameOn_orthonormalFrame (I := I) t b
  let basis := hs.toBasisAt hy
  have hbasis : Orthonormal ℝ basis := by
    rw [show (basis : ι → V y) = (orthonormalFrame t b · y) by
      funext j
      exact hs.toBasisAt_coe hy j]
    exact orthonormal_orthonormalFrame t b hy
  let ob := basis.toOrthonormalBasis hbasis
  have hrepr := ob.repr_apply_apply (W y) i
  rw [hs.coeff_apply_of_mem hy W i]
  simpa [ob, basis] using hrepr

end SmoothFrame

/-! ## Private Koszul construction -/

section Construction

variable [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E]
  {X X' Y Y' Z : ∀ x : M, TangentSpace I x} {x : M}

local notation "⟪" X ", " Y "⟫" => fun x ↦ inner ℝ (X x) (Y x)

omit [FiniteDimensional ℝ E] in
private lemma mdifferentiable_inner
    {U V : ∀ x : M, TangentSpace I x}
    (hU : MDiff (T% U)) (hV : MDiff (T% V)) : MDiff ⟪U, V⟫ :=
  MDifferentiable.inner_bundle hU hV

omit [FiniteDimensional ℝ E] in
private lemma mdifferentiableAt_inner
    {U V : ∀ x : M, TangentSpace I x}
    (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) : MDiffAt ⟪U, V⟫ x :=
  MDifferentiableAt.inner_bundle hU hV

attribute [local fun_prop] mdifferentiable_inner mdifferentiableAt_inner

omit [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private lemma injective_eval_mdifferentiableAt_vectorField (x : M) {V : Type*}
    [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] :
    Function.Injective
      (fun A : TangentSpace I x →L[ℝ] V ↦
        fun (W : ∀ x, TangentSpace I x) (_ : MDiffAt (T% W) x) ↦ A (W x)) :=
  VectorBundle.injective_eval_mdifferentiableAt_sec I E (TangentSpace I) V x

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private lemma injective_inner_mdifferentiableAt_vectorField (x : M) :
    Function.Injective
      (fun X₀ : TangentSpace I x ↦
        fun (W : ∀ x, TangentSpace I x) (_ : MDiffAt (T% W) x) ↦ inner ℝ X₀ (W x)) := by
  intro X₀ Y₀ h
  suffices inner ℝ X₀ (X₀ - Y₀) = inner ℝ Y₀ (X₀ - Y₀) by
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, sub_eq_zero]
    exact this
  simpa using congr($h (extend E (X₀ - Y₀)) (mdifferentiableAt_extend I E (X₀ - Y₀)))

omit [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
private lemma tangent_completeSpace (x : M) : CompleteSpace (TangentSpace I x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let e := VectorBundle.continuousLinearEquivAt ℝ E (TangentSpace I) x
  rwa [completeSpace_congr (e := e.toEquiv) e.isUniformEmbedding]

private noncomputable def koszulAux
    (X Y Z : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  (d% ⟪Y, Z⟫ x (X x) + d% ⟪Z, X⟫ x (Y x) - d% ⟪X, Y⟫ x (Z x)
    - ⟪Y, mlieBracket I X Z⟫ x
    - ⟪Z, mlieBracket I Y X⟫ x
    + ⟪X, mlieBracket I Z Y⟫ x) / 2

private theorem tensorialAt_first_koszulAux
    (x : M) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (koszulAux (I := I) · Y Z x) x where
  smul hf hX := by
    simp (disch := fun_prop) [koszulAux, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  add hX₁ hX₂ := by
    simp (disch := fun_prop) [koszulAux, mlieBracket_add_right, mlieBracket_add_left,
      mvfderiv_fun_add, inner_add_left, inner_add_right]
    ring

private theorem tensorialAt_third_koszulAux
    (x : M) (hY : MDiffAt (T% Y) x) (hX : MDiffAt (T% X) x) :
    TensorialAt I E (koszulAux (I := I) X Y · x) x where
  smul hf hZ := by
    simp (disch := fun_prop) [koszulAux,
      mlieBracket_smul_right, mlieBracket_smul_left, mvfderiv_fun_mul,
      inner_smul_left, inner_smul_right, inner_add_right, real_inner_comm]
    ring
  add hZ₁ hZ₂ := by
    simp (disch := fun_prop) [koszulAux,
      mlieBracket_add_right, mlieBracket_add_left, mvfderiv_fun_add,
      inner_add_left, inner_add_right]
    ring

private noncomputable def koszulRiesz
    {Y : ∀ x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  letI : CompleteSpace (TangentSpace I x) := tangent_completeSpace (I := I) x
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    TensorialAt.mkHom₂ (koszulAux (I := I) · Y · x) x
      (fun _Z hZ ↦ tensorialAt_first_koszulAux (I := I) x hY hZ)
      (fun _X hX ↦ tensorialAt_third_koszulAux (I := I) x hY hX)

private theorem koszulRiesz_apply_inner
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (koszulRiesz (I := I) hY (X x)) (Z x) =
      koszulAux (I := I) X Y Z x := by
  letI : CompleteSpace (TangentSpace I x) := tangent_completeSpace (I := I) x
  unfold koszulRiesz
  simp [TensorialAt.mkHom₂_apply _ _ hX hZ]

open scoped Classical in
private noncomputable def covariantDerivativeAux
    (Y : ∀ x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  if hY : MDiffAt (T% Y) x then koszulRiesz (I := I) hY else 0

private theorem covariantDerivativeAux_apply_inner
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (covariantDerivativeAux (I := I) Y x (X x)) (Z x) =
      koszulAux (I := I) X Y Z x := by
  simpa [covariantDerivativeAux, dif_pos hY] using
    koszulRiesz_apply_inner (I := I) hX hY hZ

private lemma isCovariantDerivativeOn_covariantDerivativeAux :
    IsCovariantDerivativeOn E (covariantDerivativeAux (I := I) (M := M)) where
  add {Y Y'} x hY hY' _ := by
    apply injective_eval_mdifferentiableAt_vectorField (I := I) x
    ext X hX
    apply injective_inner_mdifferentiableAt_vectorField (I := I) x
    ext Z hZ
    change inner ℝ (covariantDerivativeAux (I := I) (Y + Y') x (X x)) (Z x) =
      inner ℝ ((covariantDerivativeAux (I := I) Y x
        + covariantDerivativeAux (I := I) Y' x) (X x)) (Z x)
    rw [covariantDerivativeAux_apply_inner (I := I) hX
      (mdifferentiableAt_add_section hY hY') hZ]
    simp only [add_apply, inner_add_left]
    rw [covariantDerivativeAux_apply_inner (I := I) hX hY hZ,
      covariantDerivativeAux_apply_inner (I := I) hX hY' hZ]
    simp (disch := fun_prop) [koszulAux, mvfderiv_fun_add,
      mlieBracket_add_left, mlieBracket_add_right, inner_add_left, inner_add_right]
    ring
  leibniz {Y f x} hY hf _ := by
    apply injective_eval_mdifferentiableAt_vectorField (I := I) x
    ext X hX
    apply injective_inner_mdifferentiableAt_vectorField (I := I) x
    ext Z hZ
    change inner ℝ (covariantDerivativeAux (I := I) (f • Y) x (X x)) (Z x) =
      inner ℝ ((f x • covariantDerivativeAux (I := I) Y x
        + (d% f x).smulRight (Y x)) (X x)) (Z x)
    rw [covariantDerivativeAux_apply_inner (I := I) hX (hf.smul_section hY) hZ]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, inner_add_left, inner_smul_left]
    rw [covariantDerivativeAux_apply_inner (I := I) hX hY hZ]
    simp (disch := fun_prop) [koszulAux, mvfderiv_fun_mul,
      mlieBracket_smul_left, mlieBracket_smul_right,
      inner_add_right, inner_smul_left, inner_smul_right, real_inner_comm]
    ring

private noncomputable def bundledCovariantDerivative :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := covariantDerivativeAux (I := I)
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_covariantDerivativeAux (I := I)

private theorem bundledCovariantDerivative_apply_inner
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (bundledCovariantDerivative (I := I) Y x (X x)) (Z x) =
      koszulAux (I := I) X Y Z x :=
  covariantDerivativeAux_apply_inner (I := I) hX hY hZ

private theorem bundledCovariantDerivative_apply_inner_right
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (X x) (bundledCovariantDerivative (I := I) Y x (Z x)) =
      koszulAux (I := I) Z Y X x := by
  rw [real_inner_comm]
  exact bundledCovariantDerivative_apply_inner (I := I) hZ hY hX

private theorem isMetricCompatible_bundledCovariantDerivative :
    (bundledCovariantDerivative (I := I) (M := M)).IsMetricCompatible
      (M := M) (V := TangentSpace I) := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X Y Z hX hY hZ
  change d% (fun p ↦ inner ℝ (Y p) (Z p)) x (X x) =
    inner ℝ (bundledCovariantDerivative (I := I) Y x (X x)) (Z x)
      + inner ℝ (Y x) (bundledCovariantDerivative (I := I) Z x (X x))
  rw [bundledCovariantDerivative_apply_inner (I := I) hX hY hZ,
    bundledCovariantDerivative_apply_inner_right (I := I) hY hZ hX]
  simp (disch := fun_prop) [koszulAux,
    fun x ↦ real_inner_comm (Z x), fun x ↦ real_inner_comm (Y x) (X x),
    mlieBracket_swap (V := Z), mlieBracket_swap (V := Y) (W := X)]
  ring

private theorem torsion_bundledCovariantDerivative :
    (bundledCovariantDerivative (I := I) (M := M)).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply injective_inner_mdifferentiableAt_vectorField (I := I) x
  ext Z hZ
  change inner ℝ
    (bundledCovariantDerivative (I := I) Y x (X x)
      - bundledCovariantDerivative (I := I) X x (Y x)) (Z x) =
    inner ℝ (mlieBracket I X Y x) (Z x)
  rw [inner_sub_left,
    bundledCovariantDerivative_apply_inner (I := I) hX hY hZ,
    bundledCovariantDerivative_apply_inner (I := I) hY hX hZ]
  simp (disch := fun_prop) [koszulAux,
    mlieBracket_swap (V := Y) (W := X), mlieBracket_swap (V := Z) (W := X),
    mlieBracket_swap (V := Z) (W := Y), real_inner_comm]
  ring

private theorem koszul_of_compatible_of_torsion
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htorsion : cov.torsion = 0)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (cov Y x (X x)) (Z x) = koszulAux (I := I) X Y Z x := by
  have eq1a := hmetric.mvfderiv_inner_eq X hY hZ
  have eq2a := hmetric.mvfderiv_inner_eq Y hZ hX
  have eq3a := hmetric.mvfderiv_inner_eq Z hX hY
  have eq1b := congr(inner ℝ (Y x) ($(htorsion) x (X x) (Z x)))
  have eq2b := congr(inner ℝ (Z x) ($(htorsion) x (Y x) (X x)))
  have eq3b := congr(inner ℝ (X x) ($(htorsion) x (Z x) (Y x)))
  simp (disch := fun_prop) [real_inner_comm, inner_sub_right,
    CovariantDerivative.torsion_apply, koszulAux] at *
  linear_combination - (eq1a + eq1b + eq2a + eq2b - eq3a - eq3b) / 2

private theorem koszul_of_compatible_of_torsion_extend
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hmetric : cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htorsion : cov.torsion = 0) {x : M} (X₀ : TangentSpace I x)
    (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    inner ℝ (cov Y x X₀) (Z x) = koszulAux (I := I) (extend E X₀) Y Z x := by
  nth_rw 1 [← FiberBundle.extend_apply_self E X₀]
  exact koszul_of_compatible_of_torsion (I := I) hmetric htorsion
    (mdifferentiableAt_extend I E X₀) hY hZ

end Construction

/-! ## Private smooth-regularity proof -/

section Regularity

variable [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E]
  {X Y Z W : ∀ x : M, TangentSpace I x} {x : M}

private theorem contMDiffAt_of_inner
    (hW : ∀ {Z : ∀ y : M, TangentSpace I y}, CMDiffAt ∞ (T% Z) x →
      CMDiffAt ∞ (fun y ↦ inner ℝ (Z y) (W y)) x) :
    CMDiffAt ∞ (T% W) x := by
  classical
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  let hs := isLocalFrameOn_orthonormalFrame (I := I) t b
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  apply hs.contMDiffAt_of_coeff _ (t.open_baseSet.mem_nhds hx)
  intro i
  have hframe : CMDiffAt ∞ (T% (orthonormalFrame t b i)) x :=
    (hs.contMDiffOn i).contMDiffAt (t.open_baseSet.mem_nhds hx)
  apply (hW hframe).congr_of_eventuallyEq
  exact Filter.eventually_of_mem (t.open_baseSet.mem_nhds hx) fun _ hy ↦
    orthonormalFrame_coeff_eq_inner (I := I) t b hy W i

set_option backward.isDefEq.respectTransparency false in
omit [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private theorem contMDiffAt_mvfderiv_section
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {x : M} (hf : CMDiffAt ∞ f x) :
    CMDiffAt ∞
      (fun y ↦ Bundle.TotalSpace.mk' (E →L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] F) y (d% f y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  convert hf.mfderiv_const (m := ∞) (by simp) using 1
  ext y v
  simp [mvfderiv, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
  rfl

omit [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private theorem contMDiffAt_mvfderiv_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {X : ∀ y : M, TangentSpace I y} {x : M}
    (hf : CMDiffAt ∞ f x) (hX : CMDiffAt ∞ (T% X) x) :
    CMDiffAt ∞ (fun y ↦ d% f y (X y)) x := by
  have h := (contMDiffAt_mvfderiv_section hf).clm_bundle_apply hX
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

omit [FiniteDimensional ℝ E] in
private theorem contMDiffAt_inner
    {U V : ∀ y : M, TangentSpace I y}
    (hU : CMDiffAt ∞ (T% U) x) (hV : CMDiffAt ∞ (T% V) x) :
    CMDiffAt ∞ (fun y ↦ inner ℝ (U y) (V y)) x :=
  ContMDiffAt.inner_bundle hU hV

private theorem contMDiffAt_koszulAux
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x)
    (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (koszulAux (I := I) X Y Z) x := by
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  letI : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  apply ContMDiffAt.div_const
  repeat apply ContMDiffAt.add
  all_goals try apply ContMDiffAt.neg
  all_goals try apply contMDiffAt_mvfderiv_apply
  all_goals try assumption
  · exact contMDiffAt_inner hY hZ
  · exact contMDiffAt_inner hZ hX
  · exact contMDiffAt_inner hX hY
  · exact contMDiffAt_inner hY (hX.mlieBracket_vectorField hZ (by simp))
  · exact contMDiffAt_inner hZ (hY.mlieBracket_vectorField hX (by simp))
  · exact contMDiffAt_inner hX (hZ.mlieBracket_vectorField hY (by simp))

omit [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private theorem eventually_mdifferentiableAt_of_contMDiffAt
    (hX : CMDiffAt ∞ (T% X) x) :
    ∀ᶠ y in nhds x, MDiffAt (T% X) y := by
  have hX' := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
  have hnhds := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hX'
  exact hnhds.mono fun _ hy ↦ hy.mdifferentiableAt one_ne_zero

private theorem contMDiffAt_bundledCovariantDerivative_apply_inner
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x)
    (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞
      (fun y ↦ inner ℝ (bundledCovariantDerivative (I := I) Y y (X y)) (Z y)) x := by
  apply (contMDiffAt_koszulAux hX hY hZ).congr_of_eventuallyEq
  filter_upwards [eventually_mdifferentiableAt_of_contMDiffAt hX,
    eventually_mdifferentiableAt_of_contMDiffAt hY,
    eventually_mdifferentiableAt_of_contMDiffAt hZ] with y hXy hYy hZy
  exact bundledCovariantDerivative_apply_inner (I := I) hXy hYy hZy

private theorem contMDiffAt_bundledCovariantDerivative_apply
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞
      (T% (fun y ↦ bundledCovariantDerivative (I := I) Y y (X y))) x := by
  apply contMDiffAt_of_inner
  intro Z hZ
  apply (contMDiffAt_bundledCovariantDerivative_apply_inner hX hY hZ).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y ↦
    real_inner_comm (bundledCovariantDerivative (I := I) Y y (X y)) (Z y)

omit [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [FiniteDimensional ℝ E] in
private lemma contMDiffAt_clm_apply_iff
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ F]
    {f : M → F →L[ℝ] G} {n : ℕ∞ω} {x : M} :
    CMDiffAt n f x ↔ ∀ y, CMDiffAt n (fun z ↦ f z y) x := by
  refine ⟨fun h y ↦ h.clm_apply contMDiffAt_const, fun h ↦ ?_⟩
  let d := finrank ℝ F
  have hd : d = finrank ℝ (Fin d → ℝ) := (finrank_fin_fun ℝ).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : G ≃L[ℝ] G)).trans
    (ContinuousLinearEquiv.piRing (Fin d))
  have hc : ContMDiffAt I 𝓘(ℝ, Fin d → G) n (fun z ↦ e₂ (f z)) x :=
    contMDiffAt_pi_space.mpr fun i ↦ h _
  have he : ContMDiffAt 𝓘(ℝ, Fin d → G) 𝓘(ℝ, F →L[ℝ] G) n
      e₂.symm (e₂ (f x)) :=
    contMDiffAt_iff_contDiffAt.mpr e₂.symm.contDiff.contDiffAt
  have hh := he.comp x hc
  apply hh.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y ↦ by simp

omit [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] in
private theorem contMDiffAt_endomorphism_of_apply
    {A : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : ∀ {X : ∀ y : M, TangentSpace I y},
      CMDiffAt ∞ (T% X) x →
      CMDiffAt ∞ (T% (fun y ↦ A y (X y))) x) :
    CMDiffAt ∞
      (fun y ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) y (A y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  apply contMDiffAt_clm_apply_iff.mpr
  intro v
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let X₀ : TangentSpace I x := t.symm x v
  have hAX := hA (contMDiffAt_extend (k := ∞) I E X₀)
  have hcoord := (t.contMDiffAt_section_iff hx).mp hAX
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [t.symmL_apply hy,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) t hy]
  simp [X₀, FiberBundle.extend, t]

private theorem contMDiffCovariantDerivative_bundled :
    CovariantDerivative.ContMDiffCovariantDerivative
      (bundledCovariantDerivative (I := I) (M := M)) ∞ where
  contMDiff := ⟨by
    intro σ hσ
    rw [contMDiffOn_univ] at hσ ⊢
    intro x
    apply contMDiffAt_endomorphism_of_apply
    intro X hX
    apply contMDiffAt_bundledCovariantDerivative_apply hX
    simpa using hσ x⟩

end Regularity

/-! ## Public explicit-metric API -/

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-- The Levi--Civita connection of the explicit smooth metric `g`, as
Mathlib's bundled covariant derivative on the tangent bundle. -/
noncomputable def leviCivitaConnection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    CovariantDerivative I E (TangentSpace I : M → Type _) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact bundledCovariantDerivative (I := I)

/-- The Levi--Civita connection is compatible with the explicit metric. -/
theorem isMetricCompatible_leviCivitaConnection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (leviCivitaConnection g).IsMetricCompatible (M := M) (V := TangentSpace I) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact isMetricCompatible_bundledCovariantDerivative (I := I)

/-- The torsion tensor of the Levi--Civita connection vanishes. -/
theorem torsion_leviCivitaConnection_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (leviCivitaConnection g).torsion = 0 := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact torsion_bundledCovariantDerivative (I := I)

/-- The Levi--Civita connection of a smooth metric has the smooth regularity
expected by Mathlib's curvature and geodesic consumers. -/
theorem contMDiff_leviCivitaConnection
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    CovariantDerivative.ContMDiffCovariantDerivative (leviCivitaConnection g) ∞ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact contMDiffCovariantDerivative_bundled (I := I)

/-- The source-ordered Koszul formula for the Levi--Civita connection.

The order is Morgan--Tian's: the final bracket terms are
`-⟨X,[Y,Z]⟩ + ⟨Y,[Z,X]⟩ + ⟨Z,[X,Y]⟩`. -/
theorem leviCivitaConnection_koszul
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {X Y Z : ∀ x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (leviCivitaConnection g Y x (X x)) (Z x) =
      (d% (fun p ↦ inner ℝ (Y p) (Z p)) x (X x)
        + d% (fun p ↦ inner ℝ (Z p) (X p)) x (Y x)
        - d% (fun p ↦ inner ℝ (X p) (Y p)) x (Z x)
        - inner ℝ (X x) (mlieBracket I Y Z x)
        + inner ℝ (Y x) (mlieBracket I Z X x)
        + inner ℝ (Z x) (mlieBracket I X Y x)) / 2 := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ (bundledCovariantDerivative (I := I) Y x (X x)) (Z x) = _
  rw [bundledCovariantDerivative_apply_inner (I := I) hX hY hZ]
  simp only [koszulAux]
  rw [mlieBracket_swap_apply (V := X) (W := Z),
    mlieBracket_swap_apply (V := Y) (W := X),
    mlieBracket_swap_apply (V := Z) (W := Y)]
  simp only [inner_neg_right]
  ring

/-- Any metric-compatible torsion-free Mathlib covariant derivative agrees
with `leviCivitaConnection g` when the differentiated vector field is
differentiable at the point.  The direction is an arbitrary tangent vector;
no differentiability hypothesis on an extending direction field is exposed. -/
theorem leviCivitaConnection_eq_at_of_isMetricCompatible_of_torsion_eq_zero
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    (hmetric :
      letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      cov.IsMetricCompatible (M := M) (V := TangentSpace I))
    (htorsion :
      letI : RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      cov.torsion = 0)
    {Y : ∀ x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x)
    (X₀ : TangentSpace I x) :
    leviCivitaConnection g Y x X₀ = cov Y x X₀ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply injective_inner_mdifferentiableAt_vectorField (I := I) x
  ext Z hZ
  exact (koszul_of_compatible_of_torsion_extend (I := I)
    isMetricCompatible_bundledCovariantDerivative torsion_bundledCovariantDerivative X₀ hY hZ).trans
      (koszul_of_compatible_of_torsion_extend (I := I) hmetric htorsion X₀ hY hZ).symm

end Connection
end Ch01
end MorganTianLib
