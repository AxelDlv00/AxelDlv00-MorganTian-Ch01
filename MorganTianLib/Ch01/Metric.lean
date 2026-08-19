import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Chapter 1 Riemannian metric coherence

This module installs an explicit smooth tangent metric through Mathlib's scoped
`Bundle.RiemannianBundle` interface and records the resulting coherence facts.
There is no project-owned metric type: public statements use
`Bundle.ContMDiffRiemannianMetric` and `Manifold.riemannianEDist` directly.

The extended Riemannian distance induces the original manifold topology.  On a
preconnected manifold it is finite: the finite-distance component is clopen,
and Mathlib's path-infimum API then supplies an actual `C^1` path of finite
length.  Only the separating extended-metric constructor needs `T3Space`; only
the finiteness and real-distance results need `PreconnectedSpace`.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
Definition 1.1 and the metric-ball discussion on p. 35.
-/

open Bundle Filter Manifold Set
open scoped Bundle ContDiff ENNReal Topology

namespace MorganTianLib
namespace Ch01

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Scoped bundle installation -/

/-- Installing `g.toRiemannianMetric` gives the intended smooth Riemannian
bundle predicate at the same regularity. -/
theorem contMDiffRiemannianBundle
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  infer_instance

/-- Installing `g.toRiemannianMetric` gives the continuous Riemannian bundle
predicate used by the path-length and distance constructions. -/
theorem continuousRiemannianBundle
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩

/-- The fibre inner product installed through `Bundle.RiemannianBundle` is
definitionally the bilinear form of the explicit metric. -/
theorem inner_eq_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (v w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ v w = g.inner x v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rfl

/-- The fibre norm is the norm induced by the explicit metric inner product. -/
theorem norm_eq_sqrt_metric
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (v : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ‖v‖ = Real.sqrt (g.inner x v v) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner]
  rfl

/-- The norm topology installed on a tangent fibre is the fibre's pre-existing
topology.  This is the topology-preserving branch of Mathlib's bundled metric
construction, stated explicitly to rule out a second tangent-fibre topology. -/
theorem tangent_topology_eq_norm_topology
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (inferInstance : TopologicalSpace (TangentSpace I x)) =
      (inferInstance :
        NormedAddCommGroup (TangentSpace I x)).toMetricSpace.toUniformSpace.toTopologicalSpace := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rfl

/-! ## Extended and finite Riemannian distance -/

/-- On a preconnected manifold, the Riemannian extended distance associated to
an explicit smooth metric is finite.  No separation, dimension, boundary, or
completeness hypothesis is needed.

The proof shows that the points at finite distance from `x` form a nonempty
clopen set.  Local chart segments make this set and its complement open; then
preconnectedness makes it all of `M`. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I x y < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  let s : Set M := {z | Manifold.riemannianEDist I x z < ⊤}
  have hs_open : IsOpen s := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    filter_upwards
      [eventually_riemannianEDist_lt I p (show (0 : ℝ≥0∞) < 1 by simp)] with q hpq
    change Manifold.riemannianEDist I x q < ⊤
    exact Manifold.riemannianEDist_triangle.trans_lt
      (ENNReal.add_lt_top.2 ⟨hp, hpq.trans (by simp)⟩)
  have hs_compl_open : IsOpen sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    change ¬Manifold.riemannianEDist I x p < ⊤ at hp
    have hxp : Manifold.riemannianEDist I x p = ⊤ := top_unique (not_lt.mp hp)
    filter_upwards
      [eventually_riemannianEDist_lt I p (show (0 : ℝ≥0∞) < 1 by simp)] with q hpq
    change ¬Manifold.riemannianEDist I x q < ⊤
    intro hxq
    have hsum :
        Manifold.riemannianEDist I x q + Manifold.riemannianEDist I q p < ⊤ :=
      ENNReal.add_lt_top.2
        ⟨hxq, (Manifold.riemannianEDist_comm.trans_lt hpq).trans (by simp)⟩
    have htri :
        Manifold.riemannianEDist I x p ≤
          Manifold.riemannianEDist I x q + Manifold.riemannianEDist I q p :=
      Manifold.riemannianEDist_triangle
    rw [hxp] at htri
    exact (not_le_of_gt hsum) htri
  have hs_clopen : IsClopen s := ⟨isOpen_compl_iff.mp hs_compl_open, hs_open⟩
  have hs_nonempty : s.Nonempty :=
    ⟨x, by simp [s, Manifold.riemannianEDist_self]⟩
  have hs_univ : s = Set.univ := hs_clopen.eq_univ hs_nonempty
  have hy : y ∈ s := by rw [hs_univ]; exact Set.mem_univ y
  exact hy

/-- Any two points of a preconnected manifold are joined by a `C^1` path of
finite Riemannian length.  This is the path witness underlying
`riemannianEDist_lt_top`, not a path-connectedness assumption. -/
theorem exists_contMDiff_path [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Set.Icc 0 1] 1 γ ∧
      Manifold.pathELength I γ 0 1 < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  exact Manifold.exists_lt_of_riemannianEDist_lt (riemannianEDist_lt_top g x y)

/-- Under Mathlib's topology-preserving extended-metric constructor, ambient
`edist` is exactly the Riemannian path-length infimum. -/
theorem edist_eq_riemannianEDist [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    edist x y = Manifold.riemannianEDist I x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  rfl

/-- The topology carried by the Riemannian extended metric is definitionally
the original manifold topology. -/
theorem topology_eq_riemannianEMetric [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    let h : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    (inferInstance : TopologicalSpace M) = h.toUniformSpace.toTopologicalSpace := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  rfl

/-- After the preconnectedness finiteness proof, ambient `dist` is the real
part of the Riemannian extended distance. -/
theorem dist_eq_riemannianEDist_toReal [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    dist x y = (Manifold.riemannianEDist I x y).toReal := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  rfl

/-- A `Metric.ball` for the finite Riemannian metric is exactly the real
Riemannian-distance sublevel set used in Chapter 1. -/
theorem metric_ball_eq_riemannianEDist [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (r : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    Metric.ball x r = {y | (Manifold.riemannianEDist I x y).toReal < r} := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  ext y
  simp only [Metric.mem_ball, Set.mem_setOf_eq]
  rw [dist_comm]
  rfl

end Ch01
end MorganTianLib
