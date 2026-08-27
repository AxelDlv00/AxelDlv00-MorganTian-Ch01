import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Connection.Christoffel

/-!
# Provisional chart curvature computation

This module contains the private local-frame and chart calculation used while
the intrinsic section-level curvature producer is being completed.  It is
deliberately not imported by the Chapter 1 umbrella.  The definitions and
theorems below are private implementation checks, not a public coordinate
facade.  This file is distinct from the public-but-provisional
`Curvature.Provisional` namespace in `Curvature/Manifold.lean`, whose
arbitrary-extension replacement trigger is recorded in `ROADMAP.md`.

Source: Morgan--Tian `morganTian2007`, Definition 1.4 and Claim 1.5,
retained arXiv printed pp. 37--38.
-/

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

section ProvisionalChart

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-! The chart-frame proofs are duplicated here so the public Christoffel module
can keep its coordinate implementation private. -/

private noncomputable def provisionalChartFrame [IsManifold I ∞ M] (alpha : M)
    (i : Fin (Module.finrank ℝ EM)) (q : M) : TangentSpace I q :=
  (trivializationAt EM (TangentSpace I) alpha).localFrame (Module.finBasis ℝ EM) i q

private lemma provisionalMfderivChartFrame [IsManifold I ∞ M]
    (alpha : M) (i : Fin (Module.finrank ℝ EM)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    mfderiv I 𝓘(ℝ, EM) (extChartAt I alpha) p
        (provisionalChartFrame (I := I) alpha i p) =
      (Module.finBasis ℝ EM) i := by
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt hp]
  change t.continuousLinearMapAt ℝ p (t.localFrame b i p) = b i
  rw [t.localFrame_apply_of_mem_baseSet b hbase]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply, t.linearEquivAt_symm_apply]
  rw [← t.symmL_apply (R := ℝ) hbase]
  exact t.continuousLinearMapAt_symmL hbase (b i)

omit [FiniteDimensional ℝ EM] in
private lemma provisionalMlieBracketConstConst (c d : EM) :
    VectorField.mlieBracket 𝓘(ℝ, EM)
      (fun _ : EM => c) (fun _ : EM => d) = 0 := by
  rw [← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin_univ]
  funext x
  show fderiv ℝ (fun _ : EM => d) x ((fun _ : EM => c) x) -
      fderiv ℝ (fun _ : EM => c) x ((fun _ : EM => d) x) = 0
  rw [fderiv_fun_const, fderiv_fun_const]
  simp

private lemma provisionalChartFrameEventuallyEq [IsManifold I ∞ M]
    (alpha : M) (i : Fin (Module.finrank ℝ EM)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    provisionalChartFrame (I := I) alpha i =ᶠ[nhds p]
      VectorField.mpullback I 𝓘(ℝ, EM) (extChartAt I alpha)
        (fun _ => (Module.finBasis ℝ EM) i) := by
  have hopen : IsOpen (chartAt H alpha).source := (chartAt H alpha).open_source
  filter_upwards [hopen.mem_nhds hp] with q hq
  have hqsrc : q ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source]
  rw [VectorField.mpullback_apply]
  exact (((isInvertible_mfderiv_extChartAt hqsrc).inverse_apply_eq).mpr
    (provisionalMfderivChartFrame (I := I) alpha i hq).symm).symm

private lemma provisionalMlieBracketChartFrameEqZero [IsManifold I ∞ M]
    (alpha : M) (a b : Fin (Module.finrank ℝ EM)) {p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    VectorField.mlieBracket I (provisionalChartFrame (I := I) alpha a)
      (provisionalChartFrame (I := I) alpha b) p = 0 := by
  letI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [Filter.EventuallyEq.mlieBracket_vectorField_eq
      (provisionalChartFrameEventuallyEq (I := I) alpha a hp)
      (provisionalChartFrameEventuallyEq (I := I) alpha b hp)]
  have hsrc_nhds : (chartAt H alpha).source ∈ nhds p :=
    (chartAt H alpha).open_source.mem_nhds hp
  have hphi : ContMDiffAt I 𝓘(ℝ, EM) ∞
      (extChartAt I alpha) p :=
    (contMDiffOn_extChartAt (I := I) (x := alpha) (n := ∞)).contMDiffAt hsrc_nhds
  have hV : MDifferentiableAt 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, EM))
      (fun x => (TotalSpace.mk' EM x ((Module.finBasis ℝ EM) a) :
        TangentBundle 𝓘(ℝ, EM) EM))
      (extChartAt I alpha p) := by
    apply (show ContMDiffAt 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, EM)) ∞
      (fun x => (TotalSpace.mk' EM x ((Module.finBasis ℝ EM) a) :
        TangentBundle 𝓘(ℝ, EM) EM)) (extChartAt I alpha p) by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩).mdifferentiableAt
    simp
  have hW : MDifferentiableAt 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, EM))
      (fun x => (TotalSpace.mk' EM x ((Module.finBasis ℝ EM) b) :
        TangentBundle 𝓘(ℝ, EM) EM))
      (extChartAt I alpha p) := by
    apply (show ContMDiffAt 𝓘(ℝ, EM) (𝓘(ℝ, EM).prod 𝓘(ℝ, EM)) ∞
      (fun x => (TotalSpace.mk' EM x ((Module.finBasis ℝ EM) b) :
        TangentBundle 𝓘(ℝ, EM) EM)) (extChartAt I alpha p) by
      rw [contMDiffAt_totalSpace]
      exact ⟨contMDiffAt_id, by simpa using contMDiffAt_const⟩).mdifferentiableAt
    simp
  have hn : minSmoothness ℝ 2 ≤ ∞ := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  rw [← VectorField.mpullback_mlieBracket hV hW hphi hn]
  rw [provisionalMlieBracketConstConst, VectorField.mpullback_zero, Pi.zero_apply]

private lemma provisionalMlieBracketLocalFrameEqZero [IsManifold I ∞ M]
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (a b : Fin (Module.finrank ℝ EM)) :
    VectorField.mlieBracket I
      ((trivializationAt EM (TangentSpace I) alpha).localFrame
        (Module.finBasis ℝ EM) a)
      ((trivializationAt EM (TangentSpace I) alpha).localFrame
        (Module.finBasis ℝ EM) b) p = 0 := by
  change VectorField.mlieBracket I (provisionalChartFrame (I := I) alpha a)
      (provisionalChartFrame (I := I) alpha b) p = 0
  exact provisionalMlieBracketChartFrameEqZero (I := I) alpha a b hp

private lemma provisionalFderivChartScalarEqMvfderiv [IsManifold I ∞ M]
    (phi : M → ℝ) {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (hphi : MDifferentiableAt I 𝓘(ℝ, ℝ) phi p)
    (r : Fin (Module.finrank ℝ EM)) :
    fderiv ℝ (fun y : EM => phi ((extChartAt I alpha).symm y))
        (extChartAt I alpha p) (Module.finBasis ℝ EM r) =
      d% phi p ((trivializationAt EM (TangentSpace I) alpha).localFrame
        (Module.finBasis ℝ EM) r p) := by
  let phiChart := extChartAt I alpha
  have hsource : p ∈ phiChart.source := by
    simpa only [phiChart, extChartAt_source] using hp
  have hy : phiChart p ∈ phiChart.target := phiChart.map_source hsource
  have hyInterior : phiChart p ∈ interior phiChart.target := by
    exact (I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas H alpha) hp).mp hinterior
  have htarget : phiChart.target ∈ nhds (phiChart p) :=
    mem_interior_iff_mem_nhds.mp hyInterior
  have hinv : MDifferentiableAt 𝓘(ℝ, EM) I phiChart.symm (phiChart p) :=
    ((contMDiffWithinAt_extChartAt_symm_target (I := I) (n := ∞) alpha hy).contMDiffAt
      htarget).mdifferentiableAt (by simp)
  have hleft : phiChart.symm (phiChart p) = p := phiChart.left_inv hsource
  have hphiAtInv : MDifferentiableAt I 𝓘(ℝ, ℝ) phi
      (phiChart.symm (phiChart p)) := by
    simpa only [hleft] using hphi
  have hcoord : MDifferentiableAt 𝓘(ℝ, EM) 𝓘(ℝ, ℝ)
      (phi ∘ phiChart.symm) (phiChart p) :=
    hphiAtInv.comp (phiChart p) hinv
  have heq : phi =ᶠ[nhds p] (phi ∘ phiChart.symm) ∘ phiChart := by
    filter_upwards [(chartAt H alpha).open_source.mem_nhds hp] with q hq
    have hqsource : q ∈ phiChart.source := by
      simpa only [phiChart, extChartAt_source] using hq
    simp only [Function.comp_apply, phiChart]
    rw [(extChartAt I alpha).left_inv hqsource]
  change fderiv ℝ (phi ∘ phiChart.symm) (phiChart p)
      (Module.finBasis ℝ EM r) = _
  symm
  simp only [mvfderiv]
  rw [heq.mfderiv_eq, mfderiv_comp p hcoord (mdifferentiableAt_extChartAt hp)]
  change mfderiv 𝓘(ℝ, EM) 𝓘(ℝ, ℝ) (phi ∘ phiChart.symm) (phiChart p)
      (mfderiv I 𝓘(ℝ, EM) phiChart p
        ((trivializationAt EM (TangentSpace I) alpha).localFrame
          (Module.finBasis ℝ EM) r p)) = _
  rw [← provisionalMfderivChartFrame (I := I) alpha r hp, mfderiv_eq_fderiv]
  rfl

private lemma covariant_sum_apply {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    (f : ι → M → ℝ) (Y : ι → (x : M) → TangentSpace I x)
    {p : M} (hY : ∀ i, MDiffAt (T% (Y i)) p)
    (hf : ∀ i, MDiffAt (f i) p)
    (X : (x : M) → TangentSpace I x) :
    cov (∑ i, f i • Y i) p (X p) =
      ∑ i, (f i p • cov (Y i) p (X p) +
        (d% (f i) p (X p)) • Y i p) := by
  classical
  have hterm : ∀ i, MDiffAt (T% (f i • Y i)) p := fun i =>
    (hf i).smul_section (hY i)
  have hsum : ∀ s : Finset ι,
      cov (Finset.sum s (fun i => f i • Y i)) p =
        Finset.sum s (fun i => cov (f i • Y i) p) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using (cov.isCovariantDerivativeOn.zero (x := p))
    | @insert a s ha ih =>
      have hs : MDiffAt (T% (fun x => Finset.sum s (fun i => (f i • Y i) x))) p :=
        MDifferentiableAt.sum_section (fun i hi => hterm i)
      have hadd := cov.isCovariantDerivativeOn.add (hterm a) hs
      have hs_eq : (Finset.sum s (fun i => f i • Y i)) =
          (fun x => Finset.sum s (fun i => (f i • Y i) x)) := by
        funext x
        simp only [Finset.sum_apply]
      rw [← hs_eq, ih] at hadd
      have hsa : (Finset.sum (insert a s) (fun i => f i • Y i)) =
          f a • Y a + Finset.sum s (fun i => f i • Y i) := by
        funext x
        simp [Finset.sum_insert, ha]
      rw [hsa]
      simpa [Finset.sum_insert, ha] using hadd
  have h := hsum Finset.univ
  have h' := congrArg (fun A => A (X p)) h
  have heval : ∀ s : Finset ι,
      (Finset.sum s (fun i => cov (f i • Y i) p)) (X p) =
        Finset.sum s (fun i => cov (f i • Y i) p (X p)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, ih]
  rw [heval] at h'
  rw [h']
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := cov.isCovariantDerivativeOn.leibniz (hY i) (hf i)
  have hi'' := congrArg (fun A => A (X p)) hi'
  simpa [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply] using hi''

private lemma covariant_frame_expansion {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {p : M} {U : Set M}
    (A : (x : M) → TangentSpace I x)
    (f : ι → M → ℝ) (Y : ι → (x : M) → TangentSpace I x)
    (hA : MDiffAt (T% A) p) (hf : ∀ i, MDiffAt (f i) p)
    (hY : ∀ i, MDiffAt (T% (Y i)) p)
    (hU : U ∈ 𝓝 p)
    (hEq : ∀ q ∈ U, A q = ∑ i, f i q • Y i q) :
    cov A p = cov (∑ i, f i • Y i) p := by
  apply cov.isCovariantDerivativeOn.congr_of_eqOn hA
  · simpa only [Finset.sum_apply] using
      (MDifferentiableAt.sum_section (s := Finset.univ) (fun i hi =>
        (hf i).smul_section (hY i)))
  · exact hU
  · intro q hq
    rw [hEq q hq]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rfl

private lemma covariant_frame_second {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {p : M} {U : Set M}
    (X A : (x : M) → TangentSpace I x)
    (f : ι → M → ℝ) (Y : ι → (x : M) → TangentSpace I x)
    (hA : MDiffAt (T% A) p) (hf : ∀ i, MDiffAt (f i) p)
    (hY : ∀ i, MDiffAt (T% (Y i)) p)
    (hU : U ∈ 𝓝 p)
    (hEq : ∀ q ∈ U, A q = ∑ i, f i q • Y i q) :
    cov A p (X p) =
      ∑ i, (f i p • cov (Y i) p (X p) +
        (d% (f i) p (X p)) • Y i p) := by
  have hclm := covariant_frame_expansion cov A f Y hA hf hY hU hEq
  have hev := congrArg (fun B => B (X p)) hclm
  rw [hev]
  exact covariant_sum_apply cov f Y hY hf X

private lemma covariant_frame_gamma {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {p : M} {U : Set M}
    (e : ι → (x : M) → TangentSpace I x)
    (gamma : ι → ι → ι → M → ℝ)
    (i j k : ι)
    (he : ∀ s, MDiffAt (T% (e s)) p)
    (hgamma : ∀ s, MDiffAt (gamma j k s) p)
    (hA : MDiffAt (T% (fun q => cov (e k) q (e j q))) p)
    (hframe : ∀ q ∈ U,
      ∀ a b, cov (e b) q (e a q) = ∑ s, gamma a b s q • e s q)
    (hU : U ∈ 𝓝 p) :
    cov (fun q => cov (e k) q (e j q)) p (e i p) =
      (∑ s, (d% (gamma j k s) p (e i p)) • e s p) +
      ∑ s, gamma j k s p • (∑ l, gamma i s l p • e l p) := by
  have hsecond := covariant_frame_second cov (p := p) (U := U)
    (X := e i) (A := fun q => cov (e k) q (e j q))
    (f := fun s => gamma j k s) (Y := e)
    hA hgamma he hU (fun q hq => hframe q hq j k)
  rw [hsecond]
  rw [Finset.sum_add_distrib, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [hframe p (mem_of_mem_nhds hU) i s]

/-- The local-frame curvature component expansion.  With a frame `e` and
coefficients `gamma a b s` satisfying
`∇_(e_a) e_b = Σ_s gamma a b s e_s`, this is exactly
`∂_i Γ^l_jk - ∂_j Γ^l_ik + Γ^s_jk Γ^l_is - Γ^s_ik Γ^l_js`.
The theorem is independent of the particular chart and is the algebraic
chart-to-bundle bridge used by the chart specialization below. -/
private theorem curvature_frame_component {ι : Type*} [Fintype ι]
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {p : M} {U : Set M}
    (e : ι → (x : M) → TangentSpace I x)
    (gamma : ι → ι → ι → M → ℝ)
    (i j k : ι)
    (he : ∀ s, MDiffAt (T% (e s)) p)
    (hgamma_jk : ∀ s, MDiffAt (gamma j k s) p)
    (hgamma_ik : ∀ s, MDiffAt (gamma i k s) p)
    (hA_jk : MDiffAt (T% (fun q => cov (e k) q (e j q))) p)
    (hA_ik : MDiffAt (T% (fun q => cov (e k) q (e i q))) p)
    (hframe : ∀ q ∈ U,
      ∀ a b, cov (e b) q (e a q) = ∑ s, gamma a b s q • e s q)
    (hU : U ∈ 𝓝 p)
    (hbracket : mlieBracket I (e i) (e j) p = 0) :
    cov (fun q => cov (e k) q (e j q)) p (e i p) -
        cov (fun q => cov (e k) q (e i q)) p (e j p) -
        cov (e k) p (mlieBracket I (e i) (e j) p) =
      ∑ l, ((d% (gamma j k l) p (e i p)) -
          (d% (gamma i k l) p (e j p)) +
          ∑ s, (gamma j k s p * gamma i s l p -
            gamma i k s p * gamma j s l p)) • e l p := by
  classical
  have hprod (a : ι → ℝ) (b : ι → ι → ℝ) :
      (∑ s, a s • (∑ l, b s l • e l p)) =
        ∑ l, (∑ s, a s * b s l) • e l p := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [smul_smul]
  have hfirst := covariant_frame_gamma cov (p := p) (U := U)
    e gamma i j k he hgamma_jk hA_jk hframe hU
  have hsecond := covariant_frame_gamma cov (p := p) (U := U)
    e gamma j i k he hgamma_ik hA_ik hframe hU
  rw [hfirst, hsecond, hbracket, map_zero, sub_zero]
  rw [hprod (fun s => gamma j k s p) (fun s l => gamma i s l p)]
  rw [hprod (fun s => gamma i k s p) (fun s l => gamma j s l p)]
  calc
    (∑ s, (d% (gamma j k s) p (e i p)) • e s p) +
          (∑ l, (∑ s, gamma j k s p * gamma i s l p) • e l p) -
        ((∑ s, (d% (gamma i k s) p (e j p)) • e s p) +
          ∑ l, (∑ s, gamma i k s p * gamma j s l p) • e l p) =
      ((∑ l, (d% (gamma j k l) p (e i p)) • e l p) -
        ∑ l, (d% (gamma i k l) p (e j p)) • e l p) +
      ((∑ l, (∑ s, gamma j k s p * gamma i s l p) • e l p) -
        ∑ l, (∑ s, gamma i k s p * gamma j s l p) • e l p) := by
        abel
    _ = (∑ l, ((d% (gamma j k l) p (e i p)) -
          (d% (gamma i k l) p (e j p))) • e l p) +
        ∑ l, ((∑ s, gamma j k s p * gamma i s l p) -
          ∑ s, gamma i k s p * gamma j s l p) • e l p := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro l hl <;> rw [sub_smul]
    _ = ∑ l, (((d% (gamma j k l) p (e i p)) -
          (d% (gamma i k l) p (e j p))) +
        ((∑ s, gamma j k s p * gamma i s l p) -
          ∑ s, gamma i k s p * gamma j s l p)) • e l p := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      rw [add_smul]
    _ = ∑ l, ((d% (gamma j k l) p (e i p)) -
          (d% (gamma i k l) p (e j p)) +
          ∑ s, (gamma j k s p * gamma i s l p -
            gamma i k s p * gamma j s l p)) • e l p := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_sub_distrib]

/-! ### Provisional chart coefficients

The following definitions retain the source ordering: `a` is the direction,
`c` is the differentiated frame field, and `s` is the output coefficient.
The frame and metric-component plumbing is hidden behind these scalar
functions; the private checks below expose no coordinate facade. -/

/-- The private Levi--Civita Christoffel coefficient in the chart at `alpha`.

At points in the chart source this is the coefficient of
`∇_(e_a) e_c` in the private local frame. -/
private noncomputable def chartChristoffel
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (alpha : M) (a c s : Fin (Module.finrank ℝ EM)) (q : M) : ℝ :=
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  let e := t.localFrame b
  t.localFrame_coeff I b s q
    (Connection.leviCivitaConnection g (e c) q (e a q))

/-- The `l`-th local-frame component of the curvature commutator.

This is the chart-side computational quantity used by the coordinate formula.
It is intentionally stated in terms of `curvatureField` on the displayed local
frame; no theorem identifying it with the extension-based `curvature` value is
asserted here. -/
private noncomputable def chartCurvatureComponent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (alpha : M) (p : M) (i j k l : Fin (Module.finrank ℝ EM)) : ℝ :=
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  let e := t.localFrame b
  t.localFrame_coeff I b l p
    (curvatureField (Connection.leviCivitaConnection g)
      (e i) (e j) (e k) p)

/-- The private chart Christoffel coefficients are differentiable on the
chart source. -/
private theorem chartChristoffel_mdifferentiableAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (a c s : Fin (Module.finrank ℝ EM)) :
    MDiffAt (chartChristoffel (I := I) g alpha a c s) p := by
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  let e := t.localFrame b
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  have hA : MDiffAt (T% (fun q =>
      Connection.leviCivitaConnection g (e c) q (e a q))) p := by
    have hca : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% (e a)) p :=
      contMDiffAt_localFrame_of_mem (I := I) (n := ∞) (e := t) (b := b) a hbase
    have hcc : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% (e c)) p :=
      contMDiffAt_localFrame_of_mem (I := I) (n := ∞) (e := t) (b := b) c hbase
    exact (Connection.contMDiffAt_leviCivitaConnection_apply
      g hca hcc).mdifferentiableAt (by simp)
  exact mdifferentiableAt_localFrame_coeff b hbase hA s

/-- Pointwise, `chartChristoffel` is the inverse-Gram Christoffel formula from
`Connection.christoffel_formula`. -/
private theorem chartChristoffel_eq_christoffel_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j k : Fin (Module.finrank ℝ EM)) :
    let t := trivializationAt EM (TangentSpace I) alpha
    let b := Module.finBasis ℝ EM
    let e := t.localFrame b
    let G : Matrix (Fin (Module.finrank ℝ EM)) (Fin (Module.finrank ℝ EM)) ℝ :=
      fun a b => g.inner p (e a p) (e b p)
    let gij (a b : Fin (Module.finrank ℝ EM)) (y : EM) :=
      let q := (extChartAt I alpha).symm y
      g.inner q (e a q) (e b q)
    chartChristoffel (I := I) g alpha i j k p =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ EM),
        G⁻¹ k l *
          (fderiv ℝ (gij l j) (extChartAt I alpha p) (b i) +
            fderiv ℝ (gij i l) (extChartAt I alpha p) (b j) -
            fderiv ℝ (gij i j) (extChartAt I alpha p) (b l)) := by
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  let e := t.localFrame b
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  have hcoeff := t.localFrame_coeff_apply_of_mem_baseSet (I := I) b hbase
    (fun q => Connection.leviCivitaConnection g (e j) q (e i q)) k
  have hc := Connection.christoffel_formula (I := I) g hp hinterior i j k
  dsimp only [chartChristoffel]
  dsimp only [t, b, e] at hcoeff hc ⊢
  rw [hcoeff]
  exact hc

/-- The local-frame curvature commutator written with manifold directional
derivatives of the Christoffel coefficients.

The formula is the chart calculation for `chartCurvatureComponent`; the
local-frame/`FiberBundle.extend` identification for the public pointwise
`curvature` remains a separate bridge obligation. -/
private theorem chartCurvatureComponent_formula_d
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (i j k l : Fin (Module.finrank ℝ EM)) :
    chartCurvatureComponent (I := I) g alpha p i j k l =
      (d% (chartChristoffel (I := I) g alpha j k l) p
          ((trivializationAt EM (TangentSpace I) alpha).localFrame
            (Module.finBasis ℝ EM) i p)) -
      (d% (chartChristoffel (I := I) g alpha i k l) p
          ((trivializationAt EM (TangentSpace I) alpha).localFrame
            (Module.finBasis ℝ EM) j p)) +
      ∑ s, (chartChristoffel (I := I) g alpha j k s p *
          chartChristoffel (I := I) g alpha i s l p -
        chartChristoffel (I := I) g alpha i k s p *
          chartChristoffel (I := I) g alpha j s l p) := by
  let t := trivializationAt EM (TangentSpace I) alpha
  let b := Module.finBasis ℝ EM
  let e := t.localFrame b
  let gamma : Fin (Module.finrank ℝ EM) → Fin (Module.finrank ℝ EM) →
      Fin (Module.finrank ℝ EM) → M → ℝ := fun a c s q =>
    t.localFrame_coeff I b s q
      (Connection.leviCivitaConnection g (e c) q (e a q))
  have hbase : p ∈ t.baseSet := by
    simpa only [t, TangentBundle.trivializationAt_baseSet] using hp
  have he : ∀ s, MDiffAt (T% (e s)) p := by
    intro s
    exact (contMDiffAt_localFrame_of_mem (I := I) (n := ∞)
      (e := t) (b := b) s hbase).mdifferentiableAt (by simp)
  have hA : ∀ a c, MDiffAt (T% (fun q =>
      Connection.leviCivitaConnection g (e c) q (e a q))) p := by
    intro a c
    have hca : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% (e a)) p :=
      contMDiffAt_localFrame_of_mem (I := I) (n := ∞) (e := t) (b := b) a hbase
    have hcc : ContMDiffAt I (I.prod 𝓘(ℝ, EM)) ∞ (T% (e c)) p :=
      contMDiffAt_localFrame_of_mem (I := I) (n := ∞) (e := t) (b := b) c hbase
    exact (Connection.contMDiffAt_leviCivitaConnection_apply
      g hca hcc).mdifferentiableAt (by simp)
  have hgamma : ∀ a c s, MDiffAt (gamma a c s) p := by
    intro a c s
    dsimp [gamma]
    exact mdifferentiableAt_localFrame_coeff b hbase (hA a c) s
  have hframe : ∀ q ∈ t.baseSet, ∀ a c,
      Connection.leviCivitaConnection g (e c) q (e a q) =
        ∑ s, gamma a c s q • e s q := by
    intro q hq a c
    change _ = ∑ s, t.localFrame_coeff I b s q
      (Connection.leviCivitaConnection g (e c) q (e a q)) • e s q
    exact (t.isLocalFrameOn_localFrame_baseSet I 1 b).coeff_sum_eq
      (fun q => Connection.leviCivitaConnection g (e c) q (e a q)) hq
  have hU : t.baseSet ∈ 𝓝 p := t.open_baseSet.mem_nhds hbase
  have hbr : mlieBracket I (e i) (e j) p = 0 := by
    exact provisionalMlieBracketLocalFrameEqZero hp i j
  have hvec := curvature_frame_component
    (cov := Connection.leviCivitaConnection g)
    (p := p) (U := t.baseSet) e gamma i j k he (hgamma j k) (hgamma i k)
    (hA j k) (hA i k) hframe hU hbr
  have hcoef := congrArg (fun v => t.localFrame_coeff I b l p v) hvec
  have hcoef_frame (x l : Fin (Module.finrank ℝ EM)) :
      t.localFrame_coeff I b l p (e x p) = if x = l then 1 else 0 := by
    rw [t.localFrame_coeff_apply_of_mem_baseSet b hbase]
    change (t.basisAt b hbase).repr (t.localFrame b x p) l = if x = l then 1 else 0
    rw [t.localFrame_apply_of_mem_baseSet b hbase]
    simp [Bundle.Trivialization.basisAt, t.apply_mk_symm hbase (b x),
      Finsupp.single_apply]
  change t.localFrame_coeff I b l p
      ((Connection.leviCivitaConnection g)
          (fun q => (Connection.leviCivitaConnection g)
            (e k) q (e j q)) p (e i p) -
        (Connection.leviCivitaConnection g)
          (fun q => (Connection.leviCivitaConnection g)
            (e k) q (e i q)) p (e j p) -
        (Connection.leviCivitaConnection g)
          (e k) p (mlieBracket I (e i) (e j) p)) =
    (d% (gamma j k l) p (e i p)) -
      (d% (gamma i k l) p (e j p)) +
      ∑ s, (gamma j k s p * gamma i s l p -
        gamma i k s p * gamma j s l p)
  simpa [map_sub, map_add, map_smul, Finset.sum_apply, hcoef_frame] using hcoef

/-- The ordinary chart-coordinate curvature formula.  The order is exactly
`R_ij^l_k = ∂_i Γ^l_jk - ∂_j Γ^l_ik + Γ^s_jk Γ^l_is - Γ^s_ik Γ^l_js`.

This is the coordinate formula for the local-frame component; the
extension-based pointwise curvature bridge is intentionally not folded into
this declaration. -/
private theorem chartCurvatureComponent_formula
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    {alpha p : M} (hp : p ∈ (chartAt H alpha).source)
    (hinterior : I.IsInteriorPoint p)
    (i j k l : Fin (Module.finrank ℝ EM)) :
    chartCurvatureComponent (I := I) g alpha p i j k l =
      fderiv ℝ (fun y : EM =>
          chartChristoffel (I := I) g alpha j k l ((extChartAt I alpha).symm y))
        (extChartAt I alpha p) (Module.finBasis ℝ EM i) -
      fderiv ℝ (fun y : EM =>
          chartChristoffel (I := I) g alpha i k l ((extChartAt I alpha).symm y))
        (extChartAt I alpha p) (Module.finBasis ℝ EM j) +
      ∑ s, (chartChristoffel (I := I) g alpha j k s p *
          chartChristoffel (I := I) g alpha i s l p -
        chartChristoffel (I := I) g alpha i k s p *
          chartChristoffel (I := I) g alpha j s l p) := by
  rw [chartCurvatureComponent_formula_d (I := I) g hp i j k l]
  rw [provisionalFderivChartScalarEqMvfderiv
      (I := I) (phi := chartChristoffel (I := I) g alpha j k l)
      hp hinterior (chartChristoffel_mdifferentiableAt (I := I) g hp j k l) i]
  rw [provisionalFderivChartScalarEqMvfderiv
      (I := I) (phi := chartChristoffel (I := I) g alpha i k l)
      hp hinterior (chartChristoffel_mdifferentiableAt (I := I) g hp i k l) j]



end ProvisionalChart
end Curvature
end Ch01
end MorganTianLib
