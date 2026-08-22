import MorganTianLib.Ch01.Connection

/-!
# The manifold curvature commutator

This module connects the sign/order kernel in `Curvature.Model` to the
bundled Levi--Civita connection from `Ch01.Connection`.  For vector fields the
operator is exactly Morgan--Tian Definition 1.4,

`R X Y W = ∇_X (∇_Y W) - ∇_Y (∇_X W) - ∇_[X,Y] W`,

and the provisional four-tensor keeps the source order
`curvature4 X Y Z W = g (R X Y W) Z`.  The field-level API is deliberately
kept visible: Mathlib's bundled covariant derivative axioms constrain values on
differentiable sections, so a fully pointwise tensor constructor needs a later
jet/locality layer.  The extension-based pointwise definition below is a
provisional producer: its replacement trigger is the section-level
tensoriality/application theorem for arbitrary smooth local extensions.  The
exported locality theorem records the exact differentiability hypotheses under
which a germ-local change of extension is valid.

This is the `morganTian2007` Definition 1.4 construction.  The companion
`Curvature/Tensoriality.lean` module proves the currently available pointwise
additivity and scalar laws in the three `(1,3)` slots and packages them as
`TensorialAt` witnesses, together with the first Bianchi identity in the
extension-based API.  These are the proved part of the route toward
Morgan--Tian Claim 1.5; the metric symmetries and differential Bianchi identity
are not claimed here.  Chart computations are kept in the separate provisional
`Curvature/Provisional.lean` module and are not identified with this producer.

The first pair skew law and smooth-section regularity are proved in this file;
`MorganTianLib.Ch01.Curvature.Provisional.curvature_bianchi` supplies the first
Bianchi identity.  The source anchor is Morgan--Tian Claim 1.5, retained arXiv printed
pp. 37--38; the repository bibliography key is `morganTian2007`.
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

/-- Smoothness predicate for a tangent-bundle section. -/
abbrev SmoothSection (X : (x : M) → TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, EM)) ∞ (fun x =>
    Bundle.TotalSpace.mk' EM (E := fun x : M => TangentSpace I x) x (X x))

/-- A smooth covariant derivative sends two smooth fields to a smooth field. -/
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

/-- A smooth tangent-bundle section is differentiable at every point. -/
lemma smoothSection_mdifferentiableAt {X : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (p : M) : MDiffAt (T% X) p :=
  (hX p).mdifferentiableAt (by simp)

/-- Covariant differentiation is linear in the direction field at a point. -/
lemma covariantField_add_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X Y Z : (x : M) → TangentSpace I x} {p : M}
    :
    covariantField cov (X + Y) Z p =
      covariantField cov X Z p + covariantField cov Y Z p := by
  unfold covariantField
  simp only [Pi.add_apply]
  rw [map_add]

/-- Covariant differentiation is additive in a differentiable argument field. -/
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

/-- Covariant differentiation is homogeneous in the direction field. -/
lemma covariantField_smul_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {c : ℝ} {X Y : (x : M) → TangentSpace I x} {p : M}
    :
    covariantField cov (c • X) Y p = c • covariantField cov X Y p := by
  unfold covariantField
  simp only [Pi.smul_apply]
  rw [map_smul]

/-- Leibniz rule for a scalar multiple in the differentiated argument. -/
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

/-- The field commutator is skew in its first two fields. -/
lemma curvatureField_swap
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    (X Y W : (x : M) → TangentSpace I x) (p : M) :
    curvatureField cov Y X W p = -curvatureField cov X Y W p := by
  unfold curvatureField covariantField
  rw [mlieBracket_swap_apply]
  norm_num
  abel_nf

/-- The direction slot depends only on the value of the direction at `p`. -/
lemma covariantField_congr_direction
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    {X X' Y : (x : M) → TangentSpace I x} {p : M}
    (h : X p = X' p) :
    covariantField cov X Y p = covariantField cov X' Y p := by
  unfold covariantField
  rw [h]

/-- Germ-locality of the differentiated argument at a point. -/
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

/-- Germ-locality of the first field slot of the commutator. -/
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

/-- Germ-locality of the second field slot of the commutator. -/
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
  unfold curvatureField
  rw [covariantField_congr_argument cov hYW hYW' hYW_eq,
    covariantField_congr_direction cov hYp,
    covariantField_congr_direction cov hb]

/-- Germ-locality of the third field slot of the commutator. -/
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

/-- The field-level germ-locality contract for the commutator.

This is intentionally weaker than the still-pending arbitrary-extension
application theorem for the selected-extension pointwise producer. -/
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

private lemma curvatureField_add_right
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y)
    (hZ : SmoothSection Z) (hW : SmoothSection W) (p : M) :
    curvatureField cov X Y (Z + W) p =
      curvatureField cov X Y Z p + curvatureField cov X Y W p := by
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

private lemma curvatureField_add_left
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hX : SmoothSection X) (hY : SmoothSection Y)
    (hW : SmoothSection W) (p : M) :
    curvatureField cov (X + Y) Z W p =
      curvatureField cov X Z W p + curvatureField cov Y Z W p := by
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

private lemma curvatureField_add_middle
    (cov : CovariantDerivative I EM (TangentSpace I : M → Type _))
    [cov.ContMDiffCovariantDerivative ∞]
    {X Y Z W : (x : M) → TangentSpace I x}
    (hY : SmoothSection Y)
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
      rw [curvatureField_add_left cov hY hZ hW p]
    _ = curvatureField cov X Y W p + curvatureField cov X Z W p := by
      rw [curvatureField_swap cov Y X W p, curvatureField_swap cov Z X W p]
      abel

namespace Provisional

/-- The provisional selected-extension `(1,3)` curvature, evaluated on tangent
vectors by the local smooth extensions supplied by `FiberBundle.extend`.  Its
field commutator has the Morgan--Tian order `R X Y W`.  This producer is not
the canonical intrinsic API: replace it after section-level tensoriality and
the arbitrary smooth-extension application theorem are available. -/
noncomputable def curvature
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (X Y W : TangentSpace I p) : TangentSpace I p :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  curvatureField (MorganTianLib.Ch01.Connection.leviCivitaConnection g)
    (FiberBundle.extend EM X) (FiberBundle.extend EM Y) (FiberBundle.extend EM W) p

/-- The provisional source-ordered metric pairing of `curvature`: the third argument is
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

end Provisional

end ManifoldCurvature

end Curvature
end Ch01
end MorganTianLib
