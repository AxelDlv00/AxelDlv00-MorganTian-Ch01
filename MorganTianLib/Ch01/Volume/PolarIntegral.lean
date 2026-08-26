import MorganTianLib.Ch01.Volume
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Polar integration for the canonical Euclidean-normalized measure

This module proves the measure-theoretic polar decomposition used by the
volume part of Chapter 1.  It is deliberately independent of geodesics,
exponential maps, and polar coordinates on a manifold: the only geometric
input is an additive Haar measure on a finite-dimensional real normed model
space.  The canonical instance is Mathlib's Euclidean-normalized Hausdorff
measure `μHE[Module.finrank ℝ E]`, the same normalization selected by
`Ch01.riemannianVolume`.

For a nontrivial model space, `lintegral_eq_polar` writes a measurable
nonnegative integral as an iterated integral over the unit sphere and the
positive radial ray.  `setLIntegral_ball_eq_polar` gives the corresponding
ball formula, and `setLIntegral_ball_radial` records the radial specialization
used for model volumes.  The nontriviality hypothesis is explicit: in
dimension zero the origin is not null for `μH[0]`, while the unit sphere is
empty, so the all-space formula would be false.  The final zero-dimensional
regressions record that boundary rather than hiding it in an instance.

The proof uses Mathlib's
`Measure.measurePreserving_homeomorphUnitSphereProd`, `Measure.toSphere`,
`Measure.volumeIoiPow`, and Tonelli's `lintegral_prod`; no competing measure
or polar Jacobian is introduced.

Source: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 1,
the Gaussian polar-coordinate volume-form paragraph following Gauss's lemma,
p. 47 (bibliography key `morganTian2007`).  The present module formalizes its
measure-theoretic model-space part before any exponential-map or metric-density
producer is available.
-/

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology MeasureTheory

noncomputable section

namespace MorganTianLib
namespace Ch01

section PolarHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse radial map used by Mathlib's polar homeomorphism. -/
private def polarScale (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) : E :=
  (p.2 : ℝ) • (p.1 : E)

private theorem continuous_polarScale : Continuous (polarScale (E := E)) := by
  unfold polarScale
  fun_prop

private theorem polarScale_homeomorphUnitSphereProd (x : ({0}ᶜ : Set E)) :
    polarScale (homeomorphUnitSphereProd E x) = (x : E) := by
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simp [polarScale, smul_smul, mul_inv_cancel₀ hn]

variable [MeasurableSpace E] [BorelSpace E]

private theorem measurable_polarScale : Measurable (polarScale (E := E)) :=
  continuous_polarScale.measurable

end PolarHelpers

section GenericPolar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Polar decomposition for a Haar integral.**

The radial factor is `t ^ (finrank ℝ E - 1)` and the angular measure is
Mathlib's `μ.toSphere`.  The source space is required to be nontrivial because
the polar homeomorphism is defined on the complement of the origin.  This is
the model-space measure statement underlying the Gaussian polar volume-form
paragraph in Morgan--Tian Chapter 1, p. 47 (`morganTian2007`); its proof uses
`Measure.measurePreserving_homeomorphUnitSphereProd` followed by
`Measure.volumeIoiPow` and `lintegral_prod`. -/
theorem lintegral_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  have step1 : ∫⁻ x, f x ∂μ = ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap hms, restrict_compl_singleton]
  have step2 : ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))
      = ∫⁻ p, f (polarScale p) ∂(μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    exact lintegral_congr fun x => by rw [polarScale_homeomorphUnitSphereProd x]
  have hmeas : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p) :=
    hf.comp measurable_polarScale
  rw [step1, step2, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hinner : Measurable fun t : Ioi (0 : ℝ) => f ((t : ℝ) • (ω : E)) :=
    hf.comp ((continuous_id.smul continuous_const).comp continuous_subtype_val).measurable
  have hdens : Measurable fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1)) := by
    fun_prop
  simp only [polarScale]
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  exact lintegral_subtype_comap measurableSet_Ioi
    (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E)))

/-- **Polar decomposition over a metric ball.**

This is the non-radial ball form of the Gaussian polar-coordinate volume
formula in Morgan--Tian Chapter 1, p. 47 (`morganTian2007`).  The radius is
left unrestricted, so empty balls and empty radial intervals are included. -/
theorem setLIntegral_ball_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, f x ∂μ
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ t in Ioo (0 : ℝ) r,
            ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hind : Measurable ((ball (0 : E) r).indicator f) :=
    hf.indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball, lintegral_eq_polar μ hind]
  refine lintegral_congr fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  rw [← lintegral_indicator measurableSet_Ioo,
    ← lintegral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    by_cases htr : t < r
    · have hmem : t • (ω : E) ∈ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_mem, ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (ω : E) ∉ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_notMem, ht, htr, hmem, mem_Ioo]
  · have hnot : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem, ht, hnot]

/-- **Radial specialization of the ball formula.**

The angular factor is `μ.toSphere univ`, the model counterpart of the sphere
volume factor in the Gaussian polar-coordinate paragraph of Morgan--Tian
Chapter 1, p. 47 (`morganTian2007`). -/
theorem setLIntegral_ball_radial {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, φ ‖x‖ ∂μ
      = μ.toSphere univ
        * ∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ t := by
  rw [setLIntegral_ball_eq_polar μ (f := fun x : E => φ ‖x‖)
    (hφ.comp measurable_norm) r]
  have key : ∀ ω : sphere (0 : E) 1,
      (∫⁻ t in Ioo (0 : ℝ) r,
        ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ ‖t • (ω : E)‖)
        = ∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ t := by
    intro ω
    have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hnorm : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [hnorm]
  simp_rw [key]
  rw [lintegral_const, mul_comm]

end GenericPolar

section Canonical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- The polar formula for Mathlib's canonical Euclidean-normalized Hausdorff measure. -/
theorem euclideanHausdorffMeasure_lintegral_eq_polar
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μHE[Module.finrank ℝ E] : Measure E)
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E)))
        ∂(μHE[Module.finrank ℝ E] : Measure E).toSphere := by
  exact lintegral_eq_polar (μ := (μHE[Module.finrank ℝ E] : Measure E)) hf

end Canonical

section DimensionOne

variable {f : ℝ → ℝ≥0∞}

/-- One-dimensional regression: for `E = ℝ`, the radial power is `t ^ 0 = 1`. -/
theorem real_lintegral_eq_polar (hf : Measurable f) :
    ∫⁻ x, f x ∂(volume : Measure ℝ)
      = ∫⁻ ω : sphere (0 : ℝ) 1,
          (∫⁻ t in Ioi (0 : ℝ), f (t * (ω : ℝ)))
        ∂(volume : Measure ℝ).toSphere := by
  simpa [Module.finrank_self, smul_eq_mul] using
    (lintegral_eq_polar (μ := (volume : Measure ℝ)) hf)

end DimensionOne

section DimensionBoundary

variable {E₀ : Type*} [NormedAddCommGroup E₀]

/-- In dimension zero the unit sphere of a subsingleton model is empty. -/
@[simp] theorem unitSphere_one_eq_empty [Subsingleton E₀] :
    sphere (0 : E₀) 1 = (∅ : Set E₀) :=
  sphere_eq_empty_of_subsingleton one_ne_zero

variable [MeasurableSpace E₀]

/-- The zero-dimensional canonical Hausdorff measure still charges its unique point. -/
theorem euclideanHausdorffMeasure_zero_singleton [Subsingleton E₀] :
    (μHE[0] : Measure E₀) ({0} : Set E₀) = 1 := by
  rw [Measure.euclideanHausdorffMeasure_zero]
  exact hausdorffMeasure_zero_singleton _

end DimensionBoundary

end Ch01
end MorganTianLib
