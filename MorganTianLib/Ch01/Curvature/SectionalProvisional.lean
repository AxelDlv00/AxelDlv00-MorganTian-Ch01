import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Curvature.Plane

/-!
# Provisional tangent sectional curvature

This direct-only module connects the connection-free sectional-curvature API
to the selected-extension producer Curvature.Provisional.curvature4.
The connection-free definitions remain in Curvature.Sectional, while the
intrinsic quotient of independent generators is owned by `Curvature.Plane`;
this file owns only the bundled tangent metric adapters and their pointwise
results.

The producer is intentionally not promoted to a canonical Riemannian
curvature tensor.  Every theorem that uses plane or operator symmetries takes
an explicit IsAlgebraicCurvatureAt witness, leaving the pending metric
last-pair and pair-interchange proof visible at the API boundary.  The
selected-extension construction and its replacement trigger are documented in
Curvature.Manifold and the S06/S07 rows of ROADMAP.md.

The source convention is Morgan--Tian Definition 1.6
(`morganTian2007`), with the Gram normalization cross-checked against do
Carmo, Chapter 4, Section 3 (`doCarmo1992`).
-/

noncomputable section

open Bundle FiberBundle Filter Function Manifold Matrix Module VectorField
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace MorganTianLib
namespace Ch01
namespace Curvature

/-! ### Tangent-space facade -/

section TangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-- The metric at a point as a plain nested linear map.  The only bundle
instance used by this facade is the scoped Mathlib `RiemannianBundle` already
induced by `g.toRiemannianMetric`; no second metric representation is added. -/
noncomputable def metricBilinAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => g.inner p x y)
    (by intro x₁ x₂ y; simp)
    (by intro c x y; simp)
    (by intro x y₁ y₂; simp)
    (by intro c x y; simp)

omit [FiniteDimensional ℝ EM] in
/-- The canonical metric adapter is definitionally the bundled `g.inner`. -/
@[simp] theorem metricBilinAt_apply
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) :
    metricBilinAt g p x y = g.inner p x y := rfl

omit [FiniteDimensional ℝ EM] in
/-- The bundled Riemannian metric is symmetric as a nested linear map. -/
theorem metricBilinAt_symm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) :
    metricBilinAt g p x y = metricBilinAt g p y x := by
  exact g.symm p x y

/-- The Gram determinant of a tangent two-plane, using only the scoped
`Bundle.RiemannianBundle` induced by `g.toRiemannianMetric`. -/
noncomputable def metricWedgeSqAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) : ℝ :=
  wedgePairingDiag (metricBilinAt g p) x y

omit [FiniteDimensional ℝ EM] in
/-- Expansion of the pointwise metric Gram determinant in the bundled inner
product. -/
@[simp] theorem metricWedgeSqAt_def
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) :
    metricWedgeSqAt g p x y =
      g.inner p x x * g.inner p y y - g.inner p x y * g.inner p y x := rfl

omit [FiniteDimensional ℝ EM] in
/-- The pointwise tangent-space Gram determinant is nonnegative. -/
theorem metricWedgeSqAt_nonneg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) : 0 ≤ metricWedgeSqAt g p x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := wedgeSq_nonneg x y
  unfold wedgeSq at h
  change 0 ≤ inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ y x
  rw [show inner ℝ y x = inner ℝ x y from real_inner_comm x y]
  exact h

omit [FiniteDimensional ℝ EM] in
/-- Pointwise Gram positivity is equivalent to tangent-pair linear
independence. -/
theorem metricWedgeSqAt_pos_iff_linearIndependent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) :
    0 < metricWedgeSqAt g p x y ↔ LinearIndependent ℝ ![x, y] := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hinner : ∀ u v : TangentSpace I p, g.inner p u v = inner ℝ u v := by
    intro u v
    rfl
  rw [metricWedgeSqAt_def, hinner x x, hinner y y, hinner x y, hinner y x]
  rw [real_inner_comm x y]
  exact wedgeSq_pos_iff_linearIndependent x y

/-- Sectional curvature of the selected-extension producer, with the source
`(0,4)` order.  The quotient is zero on a degenerate pair by Lean's field
convention; symmetry and basis independence are stated below under an
algebraic-curvature witness. -/
noncomputable def sectionalCurvatureAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p) : ℝ :=
  Provisional.curvature4 g p x y x y / metricWedgeSqAt g p x y

/-- An explicit pointwise algebraic-curvature witness for the exact selected-
extension producer.  The generic Bianchi field here cycles the first three
slots; in source `(0,4)` order, `Provisional.curvature4_bianchi` cycles the
first, second, and fourth slots, with `IsAlgebraicCurvature.antisymm_last`
relating the two forms.  The witness is intentionally an input until S07
proves the metric last-pair symmetry of `Provisional.curvature4`. -/
def IsAlgebraicCurvatureAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) : Prop :=
  IsAlgebraicCurvature (fun x y z w => Provisional.curvature4 g p x y z w)

/-- Sectional curvature on an intrinsic tangent two-plane.  The quotient is
descended through `Curvature.SectionalPlane` using the existing plain
bilinear metric adapter; the selected-extension producer remains guarded by
the explicit pointwise algebraic-curvature witness. -/
noncomputable def sectionalCurvatureAtPlane
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) :
    SectionalPlane (TangentSpace I p) → ℝ :=
  sectionalCurvatureBilinPlane hR (metricBilinAt g p)

/-- The tangent plane evaluator reduces to the existing representative
sectional-curvature adapter. -/
@[simp] theorem sectionalCurvatureAtPlane_mk
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (q : SectionalPlaneBasis (TangentSpace I p)) :
    sectionalCurvatureAtPlane g p hR (sectionalPlaneMk q) =
      sectionalCurvatureAt g p q.x q.y := by
  rfl

/-- Generator-independence of the tangent-space plane evaluator. -/
theorem sectionalCurvatureAtPlane_basis_independent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    {q r : SectionalPlaneBasis (TangentSpace I p)}
    (hqr : sectionalPlaneChange q r) :
    sectionalCurvatureAt g p q.x q.y = sectionalCurvatureAt g p r.x r.y := by
  simpa [sectionalCurvatureAt, metricWedgeSqAt] using
    (sectionalCurvatureBilinPlane_basis_independent hR (metricBilinAt g p) hqr)

/-- Equality of quotient tangent planes gives equality of their sectional
curvature values. -/
theorem sectionalCurvatureAtPlane_eq_of_eq
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    {q r : SectionalPlaneBasis (TangentSpace I p)}
    (hqr : sectionalPlaneMk q = sectionalPlaneMk r) :
    sectionalCurvatureAtPlane g p hR (sectionalPlaneMk q) =
      sectionalCurvatureAtPlane g p hR (sectionalPlaneMk r) := by
  exact congrArg (sectionalCurvatureAtPlane g p hR) hqr

/-- The tangent plane evaluator is unchanged by reversing the generator
order. -/
theorem sectionalCurvatureAtPlane_swap
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (q : SectionalPlaneBasis (TangentSpace I p)) :
    sectionalCurvatureAtPlane g p hR (sectionalPlaneMk q.swap) =
      sectionalCurvatureAtPlane g p hR (sectionalPlaneMk q) := by
  rw [sectionalPlaneMk_swap]

/-- Pointwise diagonal constant sectional curvature for the exact producer.
The full tensor equivalence below additionally takes an explicit algebraic
curvature witness. -/
def HasConstantSectionalCurvatureAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (lam : ℝ) : Prop :=
  ∀ x y, Provisional.curvature4 g p x y x y = lam * metricWedgeSqAt g p x y

/-- The tangent quotient reduces to the source-ordered curvature component on
an orthonormal pair. -/
theorem sectionalCurvatureAt_orthonormal
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (x y : TangentSpace I p)
    (hxx : g.inner p x x = 1) (hyy : g.inner p y y = 1)
    (hxy : g.inner p x y = 0) :
    sectionalCurvatureAt g p x y = Provisional.curvature4 g p x y x y := by
  unfold sectionalCurvatureAt
  rw [metricWedgeSqAt_def, hxx, hyy, hxy, g.symm p y x]
  norm_num

/-- Pointwise constant curvature evaluates to its parameter on an orthonormal
tangent pair. -/
theorem hasConstantSectionalCurvatureAt_orthonormal
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (lam : ℝ) (hK : HasConstantSectionalCurvatureAt g p lam)
    (x y : TangentSpace I p)
    (hxx : g.inner p x x = 1) (hyy : g.inner p y y = 1)
    (hxy : g.inner p x y = 0) :
    Provisional.curvature4 g p x y x y = lam := by
  rw [hK x y, metricWedgeSqAt_def, hxx, hyy, hxy, g.symm p y x]
  norm_num

/-- The pointwise sectional quotient equals the constant parameter on an
orthonormal tangent pair. -/
theorem sectionalCurvatureAt_eq_constant_of_orthonormal
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (lam : ℝ) (hK : HasConstantSectionalCurvatureAt g p lam)
    (x y : TangentSpace I p)
    (hxx : g.inner p x x = 1) (hyy : g.inner p y y = 1)
    (hxy : g.inner p x y = 0) :
    sectionalCurvatureAt g p x y = lam := by
  rw [sectionalCurvatureAt_orthonormal g p x y hxx hyy hxy]
  exact hasConstantSectionalCurvatureAt_orthonormal g p lam hK x y hxx hyy hxy

/-- Pointwise sectional curvature is invariant under an invertible `GL₂`
change of tangent-plane generators. -/
theorem sectionalCurvatureAt_changeBasis
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (a b c d : ℝ) (x y : TangentSpace I p)
    (hdet : a * d - b * c ≠ 0) :
    sectionalCurvatureAt g p (a • x + b • y) (c • x + d • y) =
      sectionalCurvatureAt g p x y := by
  exact sectionalCurvatureBilin_changeBasis hR (metricBilinAt g p)
    a b c d x y hdet

/-- Swapping the two tangent-plane generators does not change the quotient. -/
theorem sectionalCurvatureAt_swap
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (x y : TangentSpace I p) :
    sectionalCurvatureAt g p y x = sectionalCurvatureAt g p x y := by
  simpa [sectionalCurvatureAt] using
    sectionalCurvatureAt_changeBasis g p hR 0 1 1 0 x y (by norm_num)

/-- The pointwise quotient vanishes for a zero first tangent generator. -/
theorem sectionalCurvatureAt_zero_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) (y : TangentSpace I p) :
    sectionalCurvatureAt g p 0 y = 0 := by
  have hR' : IsAlgebraicCurvature
      (fun x y z w => Provisional.curvature4 g p x y z w) := hR
  change Provisional.curvature4 g p 0 y 0 y /
      metricWedgeSqAt g p 0 y = 0
  rw [hR'.zero_first]
  simp [metricWedgeSqAt]

/-- The pointwise quotient vanishes for a zero second tangent generator. -/
theorem sectionalCurvatureAt_zero_right
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) (x : TangentSpace I p) :
    sectionalCurvatureAt g p x 0 = 0 := by
  have hR' : IsAlgebraicCurvature
      (fun x y z w => Provisional.curvature4 g p x y z w) := hR
  change Provisional.curvature4 g p x 0 x 0 /
      metricWedgeSqAt g p x 0 = 0
  rw [hR'.zero_second]
  simp [metricWedgeSqAt]

/-- The pointwise quotient vanishes on a linearly dependent tangent pair. -/
theorem sectionalCurvatureAt_eq_zero_of_not_linearIndependent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) {x y : TangentSpace I p}
    (hdep : ¬ LinearIndependent ℝ ![x, y]) :
    sectionalCurvatureAt g p x y = 0 := by
  have hR' : IsAlgebraicCurvature
      (fun x y z w => Provisional.curvature4 g p x y z w) := hR
  have hnum : Provisional.curvature4 g p x y x y = 0 := by
    rcases eq_or_ne x 0 with rfl | hx
    · exact hR'.zero_first y 0 y
    · have hnot : ¬ (∀ a : ℝ, a • x ≠ y) := by
        intro hall
        exact hdep ((LinearIndependent.pair_iff' hx).mpr hall)
      push Not at hnot
      rcases hnot with ⟨a, ha⟩
      rw [← ha, hR'.smul_second, hR'.smul_fourth, hR'.self_first]
      simp
  have hnpos : ¬ 0 < metricWedgeSqAt g p x y := by
    intro hpos
    exact hdep ((metricWedgeSqAt_pos_iff_linearIndependent g p x y).mp hpos)
  have hden : metricWedgeSqAt g p x y = 0 :=
    le_antisymm (not_lt.mp hnpos) (metricWedgeSqAt_nonneg g p x y)
  change Provisional.curvature4 g p x y x y /
      metricWedgeSqAt g p x y = 0
  rw [hnum, hden]
  simp

/-- Pointwise diagonal constant curvature is equivalent to the full
source-ordered tensor identity, assuming the explicit algebraic witness. -/
theorem hasConstantSectionalCurvatureAt_iff_tensor
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) (lam : ℝ) :
    HasConstantSectionalCurvatureAt g p lam ↔
      ∀ x y z w, Provisional.curvature4 g p x y z w =
        lam * (g.inner p x z * g.inner p y w -
          g.inner p x w * g.inner p y z) := by
  exact hasConstantCurvature_iff_tensor_bilin hR (metricBilinAt g p)
    (metricBilinAt_symm g p) lam

end TangentSpace

end Curvature
end Ch01
end MorganTianLib
