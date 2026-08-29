import MorganTianLib.Ch01.Curvature.Operator
import MorganTianLib.Ch01.Curvature.SectionalProvisional

/-!
# Provisional tangent curvature operator

This direct-only module connects the generic second-exterior-power operator
to the selected-extension tangent curvature producer.  The generic
construction remains in Curvature.Operator; the declarations here consume
the pointwise sectional adapter and retain an explicit
`IsAlgebraicCurvatureAt` witness for compatibility and dependency
transparency.  `Curvature.Provisional.curvature4_isAlgebraicCurvature`
discharges that witness for the selected producer, while the first-order
canonical producer replacement remains open.

The smooth-field metric symmetry boundary is proved in
`Curvature.Symmetries`; the operator statements remain direct-only and
conditional in this module until the first-order canonical producer replaces
the selected-extension facade.
-/

noncomputable section

open exteriorPower
open Bundle FiberBundle Manifold Matrix Module
open scoped Bundle ContDiff Manifold Matrix RealInnerProductSpace Topology

namespace MorganTianLib
namespace Ch01
namespace Curvature

/-! ### Tangent-space operator facade -/

section TangentSpace

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ EM]

/-- The curvature operator at a point, once the selected-extension curvature has
been supplied with its full algebraic-curvature witness.  The witness remains
explicit in this direct-only facade; `Curvature.Symmetries` supplies it for the
selected producer. -/
noncomputable def curvatureOperatorAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p) :
    (⋀[ℝ]^2 (TangentSpace I p)) →ₗ[ℝ]
      (⋀[ℝ]^2 (TangentSpace I p) →ₗ[ℝ] ℝ) :=
  curvatureOperator hR

/-- Pointwise decomposable evaluation recovers `Provisional.curvature4`. -/
theorem curvatureOperatorAt_ιMulti
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (x y z w : TangentSpace I p) :
    curvatureOperatorAt g p hR (ιMulti ℝ 2 ![x, y])
        (ιMulti ℝ 2 ![z, w]) =
      Provisional.curvature4 g p x y z w := by
  exact curvatureOperator_ιMulti hR x y z w

/-- Symmetry of the pointwise operator under its explicit witness. -/
theorem curvatureOperatorAt_symm
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (phi psi : ⋀[ℝ]^2 (TangentSpace I p)) :
    curvatureOperatorAt g p hR phi psi = curvatureOperatorAt g p hR psi phi := by
  exact curvatureOperator_symm hR phi psi

/-- Pointwise quadratic evaluation on a decomposable tangent wedge. -/
theorem curvatureOperatorAt_wedge_self
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (x y : TangentSpace I p) :
    curvatureOperatorAt g p hR (ιMulti ℝ 2 ![x, y])
        (ιMulti ℝ 2 ![x, y]) = Provisional.curvature4 g p x y x y := by
  exact curvatureOperator_ιMulti hR x y x y

/-- The pointwise sectional quotient is the operator quadratic form divided by
the bundled metric Gram determinant. -/
theorem sectionalCurvatureAt_eq_curvatureOperatorAt
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (x y : TangentSpace I p) :
    sectionalCurvatureAt g p x y =
      curvatureOperatorAt g p hR (ιMulti ℝ 2 ![x, y])
          (ιMulti ℝ 2 ![x, y]) / metricWedgeSqAt g p x y := by
  unfold sectionalCurvatureAt
  rw [curvatureOperatorAt_wedge_self]

/-- A pointwise nonnegative operator gives a nonnegative tangent sectional
quotient when the metric Gram determinant is supplied as nonnegative. -/
theorem curvatureOperatorAt_nonnegative_sectional
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (h : HasNonnegativeCurvatureOperator hR)
    (x y : TangentSpace I p)
    (hgram : 0 ≤ metricWedgeSqAt g p x y) :
    0 ≤ sectionalCurvatureAt g p x y := by
  rw [sectionalCurvatureAt_eq_curvatureOperatorAt g p hR x y]
  exact div_nonneg (h _) hgram

/-- Pointwise nonnegative curvature-operator positivity transfers to sectional
curvature. -/
theorem sectionalCurvatureAt_nonneg_of_hasNonnegativeCurvatureOperator
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (h : HasNonnegativeCurvatureOperator hR)
    (x y : TangentSpace I p) :
    0 ≤ sectionalCurvatureAt g p x y := by
  exact curvatureOperatorAt_nonnegative_sectional g p hR h x y
    (metricWedgeSqAt_nonneg g p x y)

/-- Pointwise positive curvature-operator positivity transfers to sectional
curvature under explicit nondegeneracy hypotheses. -/
theorem sectionalCurvatureAt_pos_of_hasPositiveCurvatureOperator
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (h : HasPositiveCurvatureOperator hR)
    {x y : TangentSpace I p}
    (hphi : ιMulti ℝ 2 ![x, y] ≠ 0)
    (hgram : metricWedgeSqAt g p x y ≠ 0) :
    0 < sectionalCurvatureAt g p x y := by
  rw [sectionalCurvatureAt_eq_curvatureOperatorAt g p hR x y]
  have hgram_pos : 0 < metricWedgeSqAt g p x y :=
    (metricWedgeSqAt_nonneg g p x y).lt_of_ne (Ne.symm hgram)
  exact div_pos (h _ hphi) hgram_pos

/-- A pointwise positive curvature operator is positive on every genuine
tangent two-plane.  Linear independence supplies both nondegeneracy
hypotheses required by
`sectionalCurvatureAt_pos_of_hasPositiveCurvatureOperator`; the exact bundled
metric is installed only locally to identify the exterior-square Gram form.

The algebraic-curvature witness remains explicit in this direct-only facade;
the smooth-field symmetry proof and selected-producer witness are in
`Curvature.Symmetries`. -/
theorem sectionalCurvatureAt_pos_of_hasPositiveCurvatureOperator_of_linearIndependent
    (g : Bundle.ContMDiffRiemannianMetric I ∞ EM (TangentSpace I : M → Type _))
    (p : M) (hR : IsAlgebraicCurvatureAt g p)
    (h : HasPositiveCurvatureOperator hR)
    {x y : TangentSpace I p} (hxy : LinearIndependent ℝ ![x, y]) :
    0 < sectionalCurvatureAt g p x y := by
  apply sectionalCurvatureAt_pos_of_hasPositiveCurvatureOperator g p hR h
  · letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact ιMulti_ne_zero_of_linearIndependent hxy
  · exact ((metricWedgeSqAt_pos_iff_linearIndependent g p x y).mpr hxy).ne'

end TangentSpace

end Curvature
end Ch01
end MorganTianLib
