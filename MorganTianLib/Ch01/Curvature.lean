import MorganTianLib.Ch01.Connection.Christoffel

/-!
# The canonical manifold curvature commutator

The connection-free algebraic sign/order kernel is owned by the adjacent
`MorganTianLib.Ch01.Curvature.Model` leaf.  This module owns only the dependent
manifold commutator built from the bundled Levi--Civita connection.  For vector fields the
operator is exactly Morgan--Tian Definition 1.4 (`morganTian2007`),

`R X Y W = ∇_X (∇_Y W) - ∇_Y (∇_X W) - ∇_[X,Y] W`,

and the public four-tensor keeps the source order
`curvature4 X Y Z W = g (R X Y W) Z`.  The field-level API is deliberately
kept visible: Mathlib's bundled covariant derivative axioms constrain values on
differentiable sections, so a fully pointwise tensor constructor needs a later
jet/locality layer.  The extension-based pointwise definition below records a
canonical value and the exported locality theorem states the exact
differentiability hypotheses under which a change of local extension is valid.

This is the Definition 1.4 construction.  The companion
`Curvature.Tensoriality` module proves the currently available pointwise
additivity and scalar laws in the three `(1,3)` slots and packages them as
`TensorialAt` witnesses, together with the first Bianchi identity in the
extension-based API.  These are the proved part of the route toward
Morgan--Tian Claim 1.5 (`morganTian2007`); the metric symmetries and differential Bianchi identity
are not claimed here.  The chart component below is a local-frame computational
quantity: until a later bridge theorem is supplied, it must not be read as an
identification with the `FiberBundle.extend`-based pointwise definition.

The first pair skew law and smooth-section regularity are proved in this file;
`Curvature.Tensoriality.curvature_bianchi` supplies the first Bianchi identity.
The metric last-pair and pair-interchange consequences remain reserved for the
metric tensor-covariant-derivative milestone; the differential/second Bianchi
identity is explicitly outside this module.
-/

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace Curvature

section ManifoldCurvature

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-- The covariant derivative of a vector field `Y` in the direction `X`.

Mathlib stores the direction as the final continuous-linear-map argument, so
this helper presents the conventional order used in Morgan--Tian formulas. -/
def covariantField
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    (X Y : (x : M) → TangentSpace I x) : (x : M) → TangentSpace I x :=
  fun x => cov Y x (X x)

/-- The Morgan--Tian curvature commutator on vector fields. -/
def curvatureField
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    (X Y W : (x : M) → TangentSpace I x) : (x : M) → TangentSpace I x :=
  fun x => covariantField cov X (covariantField cov Y W) x
    - covariantField cov Y (covariantField cov X W) x
    - covariantField cov (VectorField.mlieBracket I X Y) W x

/-- Proposition-level smoothness predicate for a tangent-bundle section.

This deliberately remains an unbundled predicate because the extension and
tensoriality lemmas consume dependent functions directly.  It interoperates
with Mathlib's bundled `ContMDiffSection`: package a proof as
`ContMDiffSection.mk X hX`, and recover this proposition with
`ContMDiffSection.contMDiff`. -/
abbrev SmoothSection (X : (x : M) → TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, EM)) ∞ (fun x =>
    Bundle.TotalSpace.mk' EM (E := fun x : M => TangentSpace I x) x (X x))

/-- A smooth covariant derivative sends two smooth fields to a smooth field. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_smooth
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y) :
    SmoothSection (covariantField cov X Y) := by
  have hout := (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
      (cov := cov) (k := ∞)).contMDiff (by simpa using hY.contMDiffOn)
  rw [contMDiffOn_univ] at hout
  have happly := hout.clm_bundle_apply hX
  simpa [SmoothSection, covariantField] using happly

/-- Smoothness of the curvature commutator. -/
lemma curvatureField_smooth
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y) (hW : SmoothSection W) :
    SmoothSection (curvatureField cov X Y W) := by
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  letI : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hYW := covariantField_smooth cov hY hW
  have hXW := covariantField_smooth cov hX hW
  have hXY : SmoothSection (VectorField.mlieBracket I X Y) := by
    exact ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      hX hY (by simp)
  have h1 := covariantField_smooth cov hX hYW
  have h2 := covariantField_smooth cov hY hXW
  have h3 := covariantField_smooth cov hXY hW
  intro q
  simpa [curvatureField] using
    (h1 q).sub_section (h2 q) |>.sub_section (h3 q)

/-- A smooth section is differentiable at every point. -/
omit [FiniteDimensional ℝ EM] in
lemma smoothSection_mdifferentiableAt {X : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (p : M) : MDiffAt (T% X) p :=
  (hX p).mdifferentiableAt (by simp)

/-- Additivity of the covariant derivative in its direction field. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_add_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Z : (x : M) → TangentSpace I x} {p : M}
    :
    covariantField cov (X + Y) Z p =
      covariantField cov X Z p + covariantField cov Y Z p := by
  unfold covariantField
  simp only [Pi.add_apply]
  rw [map_add]

/-- Additivity in the differentiated section, under pointwise regularity. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_add_argument
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Z : (x : M) → TangentSpace I x} {p : M}
    (hY : MDiffAt (T% Y) p) (hZ : MDiffAt (T% Z) p) :
    covariantField cov X (Y + Z) p =
      covariantField cov X Y p + covariantField cov X Z p := by
  unfold covariantField
  have h := (CovariantDerivative.isCovariantDerivativeOn cov).add hY hZ
  have h' := congrArg (fun A => A (X p)) h
  simpa [Pi.add_apply] using h'

/-- Homogeneity in the direction field. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_smul_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {c : ℝ} {X Y : (x : M) → TangentSpace I x} {p : M}
    :
    covariantField cov (c • X) Y p = c • covariantField cov X Y p := by
  unfold covariantField
  simp only [Pi.smul_apply]
  rw [map_smul]

/-- Leibniz rule for scalar multiplication in the differentiated section. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_smul_argument
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {f : M → ℝ} {X Y : (x : M) → TangentSpace I x} {p : M}
    (hf : MDiffAt f p) (hY : MDiffAt (T% Y) p) :
    covariantField cov X (f • Y) p =
      f p • covariantField cov X Y p + (d% f p).smulRight (Y p) (X p) := by
  unfold covariantField
  have h := (CovariantDerivative.isCovariantDerivativeOn cov).leibniz hY hf
  have h' := congrArg (fun A => A (X p)) h
  simpa using h'

/-- First-pair skew symmetry of the field curvature commutator. -/
omit [FiniteDimensional ℝ EM] in
lemma curvatureField_swap
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    (X Y W : (x : M) → TangentSpace I x) (p : M) :
    curvatureField cov Y X W p = -curvatureField cov X Y W p := by
  unfold curvatureField covariantField
  rw [mlieBracket_swap_apply]
  norm_num
  abel_nf

/-- Locality of the covariant derivative in its direction value. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_congr_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X X' Y : (x : M) → TangentSpace I x} {p : M}
    (h : X p = X' p) :
    covariantField cov X Y p = covariantField cov X' Y p := by
  unfold covariantField
  rw [h]

/-- Locality of the covariant derivative in its differentiated section. -/
omit [FiniteDimensional ℝ EM] in
lemma covariantField_congr_argument
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Y' : (x : M) → TangentSpace I x} {p : M}
    (hY : MDiffAt (T% Y) p) (hY' : MDiffAt (T% Y') p)
    (h : Y =ᶠ[nhds p] Y') :
    covariantField cov X Y p = covariantField cov X Y' p := by
  unfold covariantField
  have hc := (CovariantDerivative.isCovariantDerivativeOn cov).congr_of_eventuallyEq
    hY hY' (univ_mem : (Set.univ : Set M) ∈ nhds p) h
  exact congrArg (fun A => A (X p)) hc

/-- Extension locality of the curvature commutator in its first direction. -/
lemma curvatureField_congr_first
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X X' Y W : (x : M) → TangentSpace I x} {p : M}
    (hXW : MDiffAt (T% (covariantField cov X W)) p)
    (hXW' : MDiffAt (T% (covariantField cov X' W)) p)
    (hXW_eq : covariantField cov X W =ᶠ[nhds p]
      covariantField cov X' W)
    (h : X =ᶠ[nhds p] X') :
    curvatureField cov X Y W p = curvatureField cov X' Y W p := by
  letI : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by
    exact ENat.LEInfty.out)
  have hX : X p = X' p := h.eq_of_nhds
  have hb : VectorField.mlieBracket I X Y p =
      VectorField.mlieBracket I X' Y p :=
    h.mlieBracket_vectorField_eq (V := X') (V₁ := X)
      (W := Y) (W₁ := Y) Filter.EventuallyEq.rfl
  unfold curvatureField
  rw [covariantField_congr_direction cov hX,
    covariantField_congr_argument cov hXW hXW' hXW_eq,
    covariantField_congr_direction cov hb]

/-- Extension locality of the curvature commutator in its second direction. -/
lemma curvatureField_congr_second
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Y' W : (x : M) → TangentSpace I x} {p : M}
    (hYW : MDiffAt (T% (covariantField cov Y W)) p)
    (hYW' : MDiffAt (T% (covariantField cov Y' W)) p)
    (hYW_eq : covariantField cov Y W =ᶠ[nhds p]
      covariantField cov Y' W)
    (hY : Y =ᶠ[nhds p] Y') :
    curvatureField cov X Y W p = curvatureField cov X Y' W p := by
  letI : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by
    exact ENat.LEInfty.out)
  have hYp : Y p = Y' p := hY.eq_of_nhds
  have hb0 : VectorField.mlieBracket I Y X p =
      VectorField.mlieBracket I Y' X p :=
    hY.mlieBracket_vectorField_eq (V := Y') (V₁ := Y)
      (W := X) (W₁ := X) Filter.EventuallyEq.rfl
  have hb : VectorField.mlieBracket I X Y p =
      VectorField.mlieBracket I X Y' p := by
    calc
      VectorField.mlieBracket I X Y p =
          -VectorField.mlieBracket I Y X p := by
            rw [mlieBracket_swap_apply]
      _ = -VectorField.mlieBracket I Y' X p := by rw [hb0]
      _ = VectorField.mlieBracket I X Y' p := by
        rw [mlieBracket_swap_apply]
        simp only [neg_neg]
  have hinner : covariantField cov Y W p = covariantField cov Y' W p :=
    covariantField_congr_direction cov hYp
  unfold curvatureField
  rw [covariantField_congr_argument cov hYW hYW' hYW_eq,
    covariantField_congr_direction cov hYp,
    covariantField_congr_direction cov hb]

/-- Extension locality of the curvature commutator in its vector argument. -/
lemma curvatureField_congr_third
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y W W' : (x : M) → TangentSpace I x} {p : M}
    (hW : MDiffAt (T% W) p) (hW' : MDiffAt (T% W') p)
    (hYW : MDiffAt (T% (covariantField cov Y W)) p)
    (hYW' : MDiffAt (T% (covariantField cov Y W')) p)
    (hXW : MDiffAt (T% (covariantField cov X W)) p)
    (hXW' : MDiffAt (T% (covariantField cov X W')) p)
    (hYW_eq : covariantField cov Y W =ᶠ[nhds p]
      covariantField cov Y W')
    (hXW_eq : covariantField cov X W =ᶠ[nhds p]
      covariantField cov X W')
    (h : W =ᶠ[nhds p] W') :
    curvatureField cov X Y W p = curvatureField cov X Y W' p := by
  have hbr : covariantField cov (VectorField.mlieBracket I X Y) W p =
      covariantField cov (VectorField.mlieBracket I X Y) W' p :=
    covariantField_congr_argument cov hW hW' h
  unfold curvatureField
  rw [covariantField_congr_argument cov hYW hYW' hYW_eq,
    covariantField_congr_argument cov hXW hXW' hXW_eq, hbr]

/-- Extension-independence of the pointwise curvature value.

The hypotheses are exactly the local differentiability assumptions consumed by
Mathlib's covariant-derivative locality theorem.  This is the public bridge
from the field-level commutator to the extension-based tangent-space value. -/
theorem curvatureField_congr_of_eventuallyEq
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X X' Y Y' W W' : (x : M) → TangentSpace I x} {p : M}
    (hW : MDiffAt (T% W) p) (hW' : MDiffAt (T% W') p)
    (hYW : MDiffAt (T% (covariantField cov Y W)) p)
    (hYW' : MDiffAt (T% (covariantField cov Y W')) p)
    (hXW : MDiffAt (T% (covariantField cov X W)) p)
    (hXW' : MDiffAt (T% (covariantField cov X W')) p)
    (hYW_eq : covariantField cov Y W =ᶠ[nhds p]
      covariantField cov Y W')
    (hXW_eq : covariantField cov X W =ᶠ[nhds p]
      covariantField cov X W')
    (hY'W' : MDiffAt (T% (covariantField cov Y' W')) p)
    (hYW'_eq : covariantField cov Y W' =ᶠ[nhds p]
      covariantField cov Y' W')
    (hX'W' : MDiffAt (T% (covariantField cov X' W')) p)
    (hXW'_eq : covariantField cov X W' =ᶠ[nhds p]
      covariantField cov X' W')
    (hX : X =ᶠ[nhds p] X') (hYY' : Y =ᶠ[nhds p] Y')
    (hWW' : W =ᶠ[nhds p] W') :
    curvatureField cov X Y W p = curvatureField cov X' Y' W' p := by
  calc
    curvatureField cov X Y W p = curvatureField cov X Y W' p :=
      curvatureField_congr_third cov hW hW' hYW hYW' hXW hXW'
        hYW_eq hXW_eq hWW'
    _ = curvatureField cov X Y' W' p :=
      curvatureField_congr_second cov hYW' hY'W' hYW'_eq hYY'
    _ = curvatureField cov X' Y' W' p :=
      curvatureField_congr_first cov hXW' hX'W' hXW'_eq hX

omit [FiniteDimensional ℝ EM] in
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

omit [FiniteDimensional ℝ EM] in
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

/-! ### Canonical chart coefficients

The following definitions retain the source ordering: `a` is the direction,
`c` is the differentiated frame field, and `s` is the output coefficient.
The frame and metric-component plumbing is hidden behind these scalar
functions; the public theorems expose only chart-source and interior-point
hypotheses. -/

/-- The canonical Levi--Civita Christoffel coefficient in the chart at `alpha`.

At points in the chart source this is the coefficient of
`∇_(e_a) e_c` in the canonical local frame. -/
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

/-- The canonical chart Christoffel coefficients are differentiable on the
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
    exact Connection.Internal.mlieBracket_localFrame_eq_zero hp i j
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
  rw [Connection.Internal.fderiv_chartScalar_eq_mvfderiv
      (I := I) (phi := chartChristoffel (I := I) g alpha j k l)
      hp hinterior (chartChristoffel_mdifferentiableAt (I := I) g hp j k l) i]
  rw [Connection.Internal.fderiv_chartScalar_eq_mvfderiv
      (I := I) (phi := chartChristoffel (I := I) g alpha i k l)
      hp hinterior (chartChristoffel_mdifferentiableAt (I := I) g hp i k l) j]

/-- Additivity of the field curvature in its third vector slot. -/
lemma curvatureField_add_right
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y)
    (hZ : SmoothSection Z) (hW : SmoothSection W) (p : M) :
    curvatureField cov X Y (Z + W) p =
      curvatureField cov X Y Z p + curvatureField cov X Y W p := by
  have hZ' := smoothSection_mdifferentiableAt hZ p
  have hW' := smoothSection_mdifferentiableAt hW p
  have hYZ := smoothSection_mdifferentiableAt (covariantField_smooth cov hY hZ) p
  have hYW := smoothSection_mdifferentiableAt (covariantField_smooth cov hY hW) p
  have hXZ := smoothSection_mdifferentiableAt (covariantField_smooth cov hX hZ) p
  have hXW := smoothSection_mdifferentiableAt (covariantField_smooth cov hX hW) p
  letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out)
  letI : IsManifold I (∞ + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hXY : SmoothSection (VectorField.mlieBracket I X Y) := by
    exact ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      hX hY (by simp)
  have hsecY : covariantField cov Y (Z + W) =
      covariantField cov Y Z + covariantField cov Y W := by
    funext q
    exact covariantField_add_argument cov (smoothSection_mdifferentiableAt hZ q)
      (smoothSection_mdifferentiableAt hW q)
  have hsecX : covariantField cov X (Z + W) =
      covariantField cov X Z + covariantField cov X W := by
    funext q
    exact covariantField_add_argument cov (smoothSection_mdifferentiableAt hZ q)
      (smoothSection_mdifferentiableAt hW q)
  have hsecB : covariantField cov (VectorField.mlieBracket I X Y) (Z + W) =
      covariantField cov (VectorField.mlieBracket I X Y) Z +
        covariantField cov (VectorField.mlieBracket I X Y) W := by
    funext q
    exact covariantField_add_argument cov (smoothSection_mdifferentiableAt hZ q)
      (smoothSection_mdifferentiableAt hW q)
  unfold curvatureField
  rw [hsecY, hsecX, hsecB,
    covariantField_add_argument cov hYZ hYW,
    covariantField_add_argument cov hXZ hXW]
  simp only [Pi.add_apply]
  abel

/-- Additivity of the field curvature in its first vector slot. -/
lemma curvatureField_add_left
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y)
    (hZ : SmoothSection Z) (hW : SmoothSection W) (p : M) :
    curvatureField cov (X + Y) Z W p =
      curvatureField cov X Z W p + curvatureField cov Y Z W p := by
  have hX' := smoothSection_mdifferentiableAt hX p
  have hY' := smoothSection_mdifferentiableAt hY p
  have hXY' : SmoothSection (X + Y) := by
    intro q
    exact (hX q).add_section (hY q)
  have hbr : SmoothSection (VectorField.mlieBracket I (X + Y) Z) := by
    letI : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact ENat.LEInfty.out)
    letI : IsManifold I (∞ + 1) M := by
      simpa using (inferInstance : IsManifold I ∞ M)
    exact ContDiff.mlieBracket_vectorField hXY' hZ (by simp)
  have hbr_eq : VectorField.mlieBracket I (X + Y) Z =
      VectorField.mlieBracket I X Z + VectorField.mlieBracket I Y Z := by
    funext q
    exact VectorField.mlieBracket_add_left
      (smoothSection_mdifferentiableAt hX q)
      (smoothSection_mdifferentiableAt hY q)
  have hinner : covariantField cov (X + Y) W =
      covariantField cov X W + covariantField cov Y W := by
    funext q
    exact covariantField_add_direction cov
  unfold curvatureField
  rw [hbr_eq, hinner,
    covariantField_add_direction cov,
    covariantField_add_argument cov
      (smoothSection_mdifferentiableAt (covariantField_smooth cov hX hW) p)
      (smoothSection_mdifferentiableAt (covariantField_smooth cov hY hW) p),
    covariantField_add_direction cov]
  abel

/-- Additivity of the field curvature in its second vector slot. -/
lemma curvatureField_add_middle
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y)
    (hZ : SmoothSection Z) (hW : SmoothSection W) (p : M) :
    curvatureField cov X (Y + Z) W p =
      curvatureField cov X Y W p + curvatureField cov X Z W p := by
  calc
    curvatureField cov X (Y + Z) W p =
        -curvatureField cov (Y + Z) X W p := by
          have h := congrArg (fun v => -v)
            (curvatureField_swap cov X (Y + Z) W p)
          simpa only [neg_neg] using h.symm
    _ = -(curvatureField cov Y X W p + curvatureField cov Z X W p) := by
      rw [curvatureField_add_left cov hY hZ hX hW p]
    _ = curvatureField cov X Y W p + curvatureField cov X Z W p := by
      rw [curvatureField_swap cov Y X W p, curvatureField_swap cov Z X W p]
      abel

/-- The canonical pointwise `(1,3)` curvature, evaluated on tangent vectors
by the local smooth extensions supplied by `FiberBundle.extend`.  Its field
commutator has the Morgan--Tian order `R X Y W`. -/
noncomputable def curvature
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y W : TangentSpace I p) : TangentSpace I p :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  curvatureField (MorganTianLib.Ch01.Connection.leviCivitaConnection g)
    (FiberBundle.extend EM X) (FiberBundle.extend EM Y) (FiberBundle.extend EM W) p

/-- The source-ordered metric pairing of `curvature`: the third argument is
the pairing slot and the fourth is the curvature input. -/
noncomputable def curvature4
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) : ℝ :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  g.inner p (curvature g p X Y W) Z

/-- Unfolding equation for the extension-based pointwise curvature. -/
@[simp] theorem curvature_def
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y W : TangentSpace I p) :
    curvature g p X Y W =
      curvatureField (MorganTianLib.Ch01.Connection.leviCivitaConnection g)
        (FiberBundle.extend EM X) (FiberBundle.extend EM Y) (FiberBundle.extend EM W) p := rfl

/-- Unfolding equation preserving the source `(0,4)` argument order. -/
@[simp] theorem curvature4_def
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature4 g p X Y Z W = g.inner p (curvature g p X Y W) Z := rfl

/-- Skew symmetry in the first two curvature slots. -/
theorem curvature_swap
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y W : TangentSpace I p) :
    curvature g p Y X W = -curvature g p X Y W := by
  rw [curvature_def, curvature_def]
  exact curvatureField_swap _ _ _ _ _

/-- Skew symmetry in the first pair of the metric-paired curvature. -/
theorem curvature4_swap_first
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y Z W : TangentSpace I p) :
    curvature4 g p Y X Z W = -curvature4 g p X Y Z W := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [curvature4_def, curvature4_def, curvature_swap]
  change inner ℝ (-(curvature g p X Y W)) Z =
    -inner ℝ (curvature g p X Y W) Z
  exact inner_neg_left _ _

end ManifoldCurvature

end Curvature
end Ch01
end MorganTianLib
