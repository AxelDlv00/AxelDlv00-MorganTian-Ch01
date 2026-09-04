import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Shared manifold-calculus adapters

This module owns small regularity bridges shared by the Chapter 1 connection
and curvature developments.  They are stated only in terms of Mathlib's
manifold derivative and tangent-bundle APIs, so downstream geometric modules
do not need to depend on one another to reuse them.
-/

open Bundle FiberBundle Filter Manifold
open scoped Bundle ContDiff Manifold Topology

noncomputable section

namespace MorganTianLib
namespace Ch01
namespace ManifoldCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- Smoothness at a point for a tangent-bundle vector field. -/
abbrev SmoothAt (X : (x : M) → TangentSpace I x) (p : M) : Prop :=
  ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) p

/-- A tangent field smooth at the base point is differentiable throughout a
neighborhood of that point. -/
theorem smoothAt_eventually_mdifferentiableAt
    {X : (x : M) → TangentSpace I x} {p : M} (hX : SmoothAt X p) :
    ∀ᶠ q in 𝓝 p, MDiffAt (T% X) q := by
  have hX1 := hX.of_le (show (1 : ℕ∞ω) ≤ ∞ by exact ENat.LEInfty.out)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hX1
  exact hn.mono fun q hq => hq.mdifferentiableAt one_ne_zero

/-- Applying the manifold derivative of a smooth function to a smooth tangent
field preserves smoothness at the base point. -/
theorem contMDiffAt_mvfderiv_apply_along
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {X : (x : M) → TangentSpace I x} {p : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) ∞ f p) (hX : SmoothAt X p) :
    ContMDiffAt I 𝓘(ℝ, F) ∞ (fun y => d% f y (X y)) p := by
  have hsection : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun y => Bundle.TotalSpace.mk' (E →L[ℝ] F)
        (E := fun y : M => TangentSpace I y →L[ℝ] F) y (d% f y)) p := by
    letI : ChartedSpace (ModelProd H (E →L[ℝ] F))
        (Bundle.TotalSpace (E →L[ℝ] F)
          (fun y : M => TangentSpace I y →L[ℝ] F)) :=
      FiberBundle.chartedSpace
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    convert hf.mfderiv_const (m := ∞) (by simp) using 1
    ext y v
    simp [mvfderiv, inTangentCoordinates, ContinuousLinearMap.inCoordinates]
    rfl
  have h := hsection.clm_bundle_apply hX
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

end ManifoldCalculus
end Ch01
end MorganTianLib
