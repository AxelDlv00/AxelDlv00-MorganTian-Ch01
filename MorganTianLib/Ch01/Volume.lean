import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import MorganTianLib.Ch01.Metric

/-!
# Chapter 1 Riemannian volume coherence

This module selects Mathlib's full-dimensional Euclidean-normalized Hausdorff
measure for the Riemannian distance installed by `Ch01.Metric`.  Its explicit
result type fixes the measurable space to the original manifold's Borel
structure, and its normalization reduces to Mathlib's `volume` on
finite-dimensional real inner-product spaces.

The module makes no polar, Jacobian, or cut-locus claim.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
the volume conventions used in the normal-coordinate and comparison discussion
on pp. 45--50.
-/

open Bundle Manifold MeasureTheory Measure Set
open scoped Bundle ContDiff ENNReal MeasureTheory Topology

namespace MorganTianLib
namespace Ch01

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The canonical Riemannian volume for `g`: Mathlib's full-dimensional,
Euclidean-normalized Hausdorff measure for the Riemannian extended metric.
The return type fixes the measurable space to the Borel structure of the
original manifold topology. -/
noncomputable def riemannianVolume
    [FiniteDimensional ℝ E] [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    @Measure M (borel M) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact μHE[Module.finrank ℝ E]

/-- The selected Riemannian volume is exactly Mathlib's Euclidean-normalized
Hausdorff measure for the installed Riemannian `edist`. -/
theorem riemannianVolume_eq_euclideanHausdorffMeasure
    [FiniteDimensional ℝ E] [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    riemannianVolume g = μHE[Module.finrank ℝ E] := by
  rfl

/-- For the installed Riemannian `edist`, the selected volume
`μHE[finrank ℝ E]` unfolds to Mathlib's dimension-dependent normalization
constant times raw Hausdorff measure. -/
theorem riemannianVolume_eq_smul_hausdorffMeasure
    [FiniteDimensional ℝ E] [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    riemannianVolume g =
      addHaarScalarFactor
          (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
          μH[Module.finrank ℝ E] • μH[Module.finrank ℝ E] := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  rw [riemannianVolume_eq_euclideanHausdorffMeasure]
  exact Measure.euclideanHausdorffMeasure_def _

/-- Every open set of the original manifold topology is measurable for the
Borel structure used by the selected Riemannian volume. -/
theorem isOpen_measurableSet_riemannianVolume [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {s : Set M} (hs : IsOpen s) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    MeasurableSet s := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact hs.measurableSet

/-- Every finite Riemannian metric ball is measurable for the Borel structure
used by the selected volume.  Preconnectedness appears only because
`Metric.ball` uses the finite distance installed after
`riemannianEDist_lt_top`. -/
theorem measurableSet_riemannianMetric_ball
    [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (r : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    MeasurableSet (Metric.ball x r) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  exact measurableSet_ball

/-- The scalar multiple selected by `μHE[finrank ℝ V]` is exactly `volume` on
every finite-dimensional real inner-product space.  This regression fixes the
Euclidean normalization and deliberately makes no such claim for raw `μH`. -/
theorem euclidean_volume_coherence
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] :
    letI : MeasurableSpace V := borel V
    letI : BorelSpace V := ⟨rfl⟩
    addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))))
        μH[Module.finrank ℝ V] • μH[Module.finrank ℝ V] =
      (volume : Measure V) := by
  letI : MeasurableSpace V := borel V
  letI : BorelSpace V := ⟨rfl⟩
  rw [← Measure.euclideanHausdorffMeasure_def,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]

end Ch01
end MorganTianLib
