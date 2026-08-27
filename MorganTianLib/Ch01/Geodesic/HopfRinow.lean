/-
Copyright (c) 2026 Axel Dlv. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
-/
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Geodesic
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Hopf--Rinow interfaces

This module is the S19 boundary between the intrinsic geodesic IVP and the
complete-manifold consequences used later in Chapter 1.  It deliberately
keeps three inputs separate:

* `RiemannianMetricComplete` installs the canonical extended Riemannian
  distance and asks for its `CompleteSpace` instance;
* `[CompleteSpace E]` remains the analytic premise of the local spray/ODE
  construction in `Geodesic`; and
* `[BoundarylessManifold I M]` is the all-initial-data contract for the local
  IVP.

The continuation and compactness producers below are the exact interfaces
still to be supplied by the maximal-domain and variation slices.  Continuation
domains and maximal lifetimes are explicitly open and order-connected, so a
disconnected island cannot masquerade as an extension through a finite
endpoint.  Public distance and length fields use Mathlib's
`Manifold.riemannianEDist` and `Manifold.pathELength` directly under a local
metric instance.  The proved theorems are the set-theoretic maximal-interval
argument and the reusable distance/length adapters.  Thus no theorem here
treats metric completeness as an ODE premise, and every existence claim names
its required producer.

The source-facing target is the paragraph preceding Morgan--Tian, Theorem
1.18, pp. 41--42 (`morganTian2007`); see also do Carmo (1992), Chapter 7,
Section 2 (`doCarmo1992`), and Lee (2018), Theorem 6.19 (`lee2018`).  The
minimizing-segment interface is intentionally
weaker than uniqueness or the no-conjugate-subsegment result, which belong to
later S24/V1 work.
-/

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Bundle ContDiff Manifold Topology ENNReal

namespace MorganTianLib
namespace Ch01
namespace Geodesic

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [FiniteDimensional ℝ E]

/-! ## Completeness of the selected distance -/

/-- Metric completeness for the *canonical selected Riemannian distance*.

`EMetricSpace.ofRiemannianMetric` is installed only in the body of this
predicate.  The proposition is therefore independent of any unrelated
`MetricSpace M` instance, while the local ODE premise `[CompleteSpace E]`
remains a separate typeclass argument. -/
def RiemannianMetricComplete
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  @CompleteSpace M inferInstance

/-- A lifetime is unbounded above, expressed without choosing an endpoint
convention for open intervals. -/
def LifetimeUnboundedAbove (s : Set ℝ) : Prop :=
  ∀ b : ℝ, ∃ t ∈ s, b < t

/-- A lifetime is unbounded below. -/
def LifetimeUnboundedBelow (s : Set ℝ) : Prop :=
  ∀ b : ℝ, ∃ t ∈ s, t < b

/-! ## Maximal geodesic and continuation contracts -/

/-- A maximal intrinsic geodesic supplied by the S18 maximal-domain layer.

The curve is total as a Lean function, but `lifetime` records the times at
which its geodesic and continuity certificates are valid.  Values outside the
lifetime are deliberately not used. -/
structure MaximalGeodesic
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) where
  /-- The total Lean representative of the maximal solution. -/
  curve : ℝ → M
  /-- The interval on which the representative is certified. -/
  lifetime : Set ℝ
  /-- The initial time belongs to the lifetime. -/
  zero_mem : (0 : ℝ) ∈ lifetime
  /-- Initial position. -/
  position_zero : curve 0 = p
  /-- Initial velocity in the chart at the initial point. -/
  initial_derivative :
    HasDerivAt (chartReading (I := I) p curve)
      (chartVelocityAt (I := I) p v) 0
  /-- The intrinsic equation on the lifetime. -/
  geodesic_on : isGeodesicOn (I := I) g curve lifetime
  /-- Continuity on the lifetime. -/
  continuous_on : ContinuousOn curve lifetime
  /-- The lifetime is interval-convex. -/
  interval :
    ∀ ⦃a b t : ℝ⦄, a ∈ lifetime → b ∈ lifetime → a ≤ t → t ≤ b → t ∈ lifetime
  /-- The maximal-domain producer supplies an open lifetime. -/
  lifetime_open : IsOpen lifetime
  /-- No certified geodesic extension exists on an open order-connected
  superdomain.  The explicit interval guards rule out disconnected islands
  outside a finite endpoint. -/
  maximal :
    ∀ (s : Set ℝ) (γ : ℝ → M), lifetime ⊆ s →
      (0 : ℝ) ∈ s → IsOpen s → s.OrdConnected →
      isGeodesicOn (I := I) g γ s → ContinuousOn γ s →
      (∀ t ∈ lifetime, γ t = curve t) → s ⊆ lifetime

/-- The constant zero-velocity maximal geodesic.  This is a concrete
unbounded-lifetime regression and does not use metric completeness. -/
def MaximalGeodesic.refl
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) : MaximalGeodesic (I := I) g p 0 where
  curve := fun _ : ℝ => p
  lifetime := Set.univ
  zero_mem := Set.mem_univ 0
  position_zero := rfl
  initial_derivative := by
    have hconst : HasDerivAt (chartReading (I := I) p (fun _ : ℝ => p)) 0 0 := by
      change HasDerivAt (fun _ : ℝ => extChartAt I p p) 0 0
      exact hasDerivAt_const (x := (0 : ℝ)) (c := extChartAt I p p)
    have hz := (trivializationAt E (TangentSpace I) p).zeroSection ℝ
      (mem_baseSet_trivializationAt E (TangentSpace I) p)
    have hs := congrArg Prod.snd hz
    have hv : chartVelocityAt (I := I) p (0 : TangentSpace I p) = 0 := by
      simpa [chartVelocityAt, Bundle.zeroSection] using hs
    simpa [hv] using hconst
  geodesic_on := by
    intro t ht
    exact isGeodesic_const (I := I) g p t
  continuous_on := continuousOn_const
  interval := by
    intro a b t ha hb hat htb
    exact Set.mem_univ t
  lifetime_open := isOpen_univ
  maximal := by
    intro s γ hs hzero hopen hinterval hgeo hcont heq
    exact fun t ht => Set.mem_univ t

/-- The constant maximal geodesic has the displayed lifetime. -/
@[simp]
theorem MaximalGeodesic.refl_lifetime
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) : (MaximalGeodesic.refl (I := I) g p).lifetime = Set.univ := rfl

/-- The certified lifetime is order-connected in the real-time order.

The explicit `interval` field is retained for compatibility with the S18
maximal-domain producer; this theorem exposes the corresponding Mathlib
`Set.OrdConnected` invariant required by the extension contract. -/
theorem MaximalGeodesic.lifetime_ordConnected
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p)
    (G : MaximalGeodesic (I := I) g p v) : G.lifetime.OrdConnected := by
  rw [Set.ordConnected_iff]
  intro a ha b hb _hab t ht
  exact G.interval ha hb ht.1 ht.2

/-- The constant regression has an unbounded forward lifetime without any
completeness premise. -/
theorem MaximalGeodesic.refl_unboundedAbove
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    LifetimeUnboundedAbove (MaximalGeodesic.refl (I := I) g p).lifetime := by
  intro b
  exact ⟨b + 1, Set.mem_univ _, by linarith⟩

/-- The constant regression has an unbounded backward lifetime without any
completeness premise. -/
theorem MaximalGeodesic.refl_unboundedBelow
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) :
    LifetimeUnboundedBelow (MaximalGeodesic.refl (I := I) g p).lifetime := by
  intro b
  exact ⟨b - 1, Set.mem_univ _, by linarith⟩

/-- The continuation output required from the completed S18 maximal solution.

The hypothesis is parameterized by `RiemannianMetricComplete`; this keeps the
metric-completeness route visible and prevents it from being silently reused
as the `[CompleteSpace E]` premise of the local ODE. -/
structure MaximalGeodesicContinuation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (G : MaximalGeodesic (I := I) g p v)
    [T3Space M] where
  /-- Forward continuation witness beyond every upper bound of the lifetime. -/
  right :
    RiemannianMetricComplete (I := I) g →
      ∀ b : ℝ, (∀ t ∈ G.lifetime, t ≤ b) →
        ∃ (s : Set ℝ) (γ : ℝ → M),
          G.lifetime ⊆ s ∧
          (0 : ℝ) ∈ s ∧
          IsOpen s ∧ s.OrdConnected ∧
          (∃ t ∈ s, b < t) ∧
          isGeodesicOn (I := I) g γ s ∧ ContinuousOn γ s ∧
          γ 0 = G.curve 0 ∧
          HasDerivAt (chartReading (I := I) p γ)
            (chartVelocityAt (I := I) p v) 0 ∧
          (∀ t ∈ G.lifetime, γ t = G.curve t)
  /-- Backward continuation witness beyond every lower bound of the lifetime. -/
  left :
    RiemannianMetricComplete (I := I) g →
      ∀ b : ℝ, (∀ t ∈ G.lifetime, b ≤ t) →
        ∃ (s : Set ℝ) (γ : ℝ → M),
          G.lifetime ⊆ s ∧
          (0 : ℝ) ∈ s ∧
          IsOpen s ∧ s.OrdConnected ∧
          (∃ t ∈ s, t < b) ∧
          isGeodesicOn (I := I) g γ s ∧ ContinuousOn γ s ∧
          γ 0 = G.curve 0 ∧
          HasDerivAt (chartReading (I := I) p γ)
            (chartVelocityAt (I := I) p v) 0 ∧
          (∀ t ∈ G.lifetime, γ t = G.curve t)

/-! ### The unbounded-lifetime argument -/

/-- Metric completeness plus the supplied forward continuation rules out a
finite upper lifetime.  The proof is the maximality contradiction, so it does
not identify metric completeness with the model-space ODE completion. -/
theorem maximalGeodesic_lifetime_unboundedAbove
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    {p : M} {v : TangentSpace I p}
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    LifetimeUnboundedAbove G.lifetime := by
  classical
  intro b
  by_contra hbound
  have hupper : ∀ t ∈ G.lifetime, t ≤ b := by
    intro t ht
    exact le_of_not_gt (fun htb => hbound ⟨t, ht, htb⟩)
  obtain ⟨s, γ, hs, hzero, hopen, hinterval, hmore, hgeo, hcont, _hγzero,
    _hγderiv, heq⟩ :=
    hcontinue.right hcomplete b hupper
  have hsubset : s ⊆ G.lifetime := G.maximal s γ hs hzero hopen hinterval hgeo hcont heq
  rcases hmore with ⟨t, ht, hbt⟩
  exact (not_lt_of_ge (hupper t (hsubset ht))) hbt

/-- The backward analogue of
`maximalGeodesic_lifetime_unboundedAbove`. -/
theorem maximalGeodesic_lifetime_unboundedBelow
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    {p : M} {v : TangentSpace I p}
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    LifetimeUnboundedBelow G.lifetime := by
  classical
  intro b
  by_contra hbound
  have hlower : ∀ t ∈ G.lifetime, b ≤ t := by
    intro t ht
    exact le_of_not_gt (fun htb => hbound ⟨t, ht, htb⟩)
  obtain ⟨s, γ, hs, hzero, hopen, hinterval, hmore, hgeo, hcont, _hγzero,
    _hγderiv, heq⟩ :=
    hcontinue.left hcomplete b hlower
  have hsubset : s ⊆ G.lifetime := G.maximal s γ hs hzero hopen hinterval hgeo hcont heq
  rcases hmore with ⟨t, ht, htb⟩
  exact (not_lt_of_ge (hlower t (hsubset ht))) htb

/-- A maximal interval with both continuation directions is all of `ℝ`. -/
theorem maximalGeodesic_lifetime_eq_univ_of_complete
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    {p : M} {v : TangentSpace I p}
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    G.lifetime = (Set.univ : Set ℝ) := by
  apply Set.eq_univ_of_forall
  intro t
  obtain ⟨a, ha, hat⟩ :=
    maximalGeodesic_lifetime_unboundedBelow g hcomplete G hcontinue t
  obtain ⟨b, hb, htb⟩ :=
    maximalGeodesic_lifetime_unboundedAbove g hcomplete G hcontinue t
  exact G.interval ha hb hat.le htb.le

/-- The source-facing global extension consequence for one initial datum.

The maximal-geodesic and continuation records already carry the producer
boundary conditions needed by this projection.  In particular, this wrapper
does not reintroduce `[CompleteSpace E]` or `[BoundarylessManifold I M]` merely
to project a supplied all-time continuation certificate. -/
theorem exists_globalGeodesic_of_complete
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    {p : M} {v : TangentSpace I p}
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ)
        (chartVelocityAt (I := I) p v) 0 ∧
      Continuous γ ∧ isGeodesic (I := I) g γ := by
  have hlife := maximalGeodesic_lifetime_eq_univ_of_complete g hcomplete G hcontinue
  have hcont : ContinuousOn G.curve (Set.univ : Set ℝ) := by
    rw [← hlife]
    exact G.continuous_on
  have hgeo : isGeodesicOn (I := I) g G.curve (Set.univ : Set ℝ) := by
    rw [← hlife]
    exact G.geodesic_on
  refine ⟨G.curve, G.position_zero, G.initial_derivative, ?_,
    (isGeodesicOn_univ_iff (I := I) g G.curve).mp hgeo⟩
  exact continuousOn_univ.mp hcont

/-- The all-initial-data maximal-domain producer expected by the global
extension theorem.  It records the boundaryless/model-space contract in its
type rather than hiding it in a finite-interval facade. -/
structure CompleteMaximalGeodesicData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M] where
  /-- Maximal geodesic supplied for each initial point and velocity. -/
  solution : ∀ (p : M) (v : TangentSpace I p),
    MaximalGeodesic (I := I) g p v
  /-- Continuation certificate associated with each supplied maximal solution. -/
  continuation : ∀ (p : M) (v : TangentSpace I p),
    MaximalGeodesicContinuation (I := I) g p v (solution p v)

/-- Every initial datum has a canonical all-real-time solution once the
completed S18 producer supplies maximality and continuation. -/
theorem exists_globalGeodesic_of_complete_all
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : CompleteMaximalGeodesicData (I := I) g) (p : M)
    (v : TangentSpace I p) :
    ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ)
        (chartVelocityAt (I := I) p v) 0 ∧
      Continuous γ ∧ isGeodesic (I := I) g γ := by
  exact exists_globalGeodesic_of_complete g hcomplete (data.solution p v)
    (data.continuation p v)

/-! ## Minimizing segments -/

/-- Affine reparameterization of a curve on a subinterval. -/
def affineReparam (γ : ℝ → M) (a b t : ℝ) : M :=
  γ (a + (b - a) * t)

omit [TopologicalSpace M] in
@[simp]
theorem affineReparam_zero (γ : ℝ → M) (a b : ℝ) :
    affineReparam γ a b 0 = γ a := by
  simp [affineReparam]

omit [TopologicalSpace M] in
@[simp]
theorem affineReparam_one (γ : ℝ → M) (a b : ℝ) :
    affineReparam γ a b 1 = γ b := by
  simp [affineReparam]

omit [TopologicalSpace M] in
/-- Constant-speed distance data is stable under translation of the parameter.
The hypotheses explicitly state that the translated times remain in the
original interval; no geodesic equation transfer is assumed here. -/
theorem constantSpeed_translate
    (D : M → M → ℝ≥0∞) (γ : ℝ → M) (L : ℝ≥0∞)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      D (γ s) (γ t) = ENNReal.ofReal |s - t| * L)
    (c s t : ℝ) (hs : s + c ∈ Set.Icc (0 : ℝ) 1)
    (ht : t + c ∈ Set.Icc (0 : ℝ) 1) :
    D (γ (s + c)) (γ (t + c)) =
      ENNReal.ofReal |s - t| * L := by
  rw [hγ _ hs _ ht]
  congr 2
  congr 1
  ring_nf

omit [TopologicalSpace M] in
/-- Constant-speed distance data is stable under restriction to a subinterval.
This is the arithmetic normalization consumed by later exponential and
variation modules. -/
theorem constantSpeed_restrict
    (D : M → M → ℝ≥0∞) (γ : ℝ → M) (L : ℝ≥0∞)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      D (γ s) (γ t) = ENNReal.ofReal |s - t| * L)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      D (affineReparam γ a b s)
          (affineReparam γ a b t) =
        ENNReal.ofReal |s - t| * D (γ a) (γ b) := by
  intro s hs t ht
  have hsa : a + (b - a) * s ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hs.1, hs.2, ha.1, hb.2]
  have hta : a + (b - a) * t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
  simp only [affineReparam]
  rw [hγ _ hsa _ hta, hγ a ha b hb]
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  rw [show (a + (b - a) * s) - (a + (b - a) * t) =
      (b - a) * (s - t) by ring, abs_mul, abs_of_nonneg hba,
    ENNReal.ofReal_mul hba]
  have habs : |a - b| = b - a := by
    rw [abs_sub_comm, abs_of_nonneg hba]
  rw [habs]
  ac_rfl

/-- A geodesic segment together with the source-facing minimizing and
constant-speed certificates.

The `restriction_geodesic` and `translation_geodesic` fields are explicit
equation-transfer outputs.  They prevent this S19 interface from silently
asserting affine invariance that has not yet been proved in the local S18
connection API. -/
structure MinimizingGeodesic
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) where
  /-- The smooth path whose endpoints are `x` and `y`. -/
  path : SmoothPath I x y
  /-- The intrinsic geodesic equation on the unit interval. -/
  geodesic_on : isGeodesicOn (I := I) g (path : ℝ → M) (Set.Icc 0 1)
  /-- Continuity on the parameter interval. -/
  continuous_on : ContinuousOn (path : ℝ → M) (Set.Icc 0 1)
  /-- Constant-speed normalization in the canonical extended distance. -/
  constant_speed :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (path s) (path t) =
        ENNReal.ofReal |s - t| * Manifold.riemannianEDist I x y
  /-- The path length is exactly the canonical Riemannian distance. -/
  length_eq_distance :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (path : ℝ → M) 0 1 =
      Manifold.riemannianEDist I x y
  /-- Affine restriction has a geodesic certificate. -/
  restriction_geodesic :
    ∀ {a b : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 → a ≤ b →
      isGeodesicOn (I := I) g
        (affineReparam (path : ℝ → M) a b) (Set.Icc 0 1)
  /-- Translation has a geodesic certificate on its pulled-back lifetime. -/
  translation_geodesic :
    ∀ c : ℝ,
      isGeodesicOn (I := I) g (fun t => path (t + c))
        ((fun t : ℝ => t + c) ⁻¹' Set.Icc (0 : ℝ) 1)

/-- The source endpoint of a minimizing segment. -/
@[simp]
theorem MinimizingGeodesic.source
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) :
    G.path 0 = x := G.path.source

/-- The target endpoint of a minimizing segment. -/
@[simp]
theorem MinimizingGeodesic.target
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) :
    G.path 1 = y := G.path.target

/-- The zero-length constant segment.  Besides being useful in later proofs,
this is the zero-dimensional/one-point regression for the interface. -/
def MinimizingGeodesic.refl
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) : MinimizingGeodesic (I := I) g x x where
  path := SmoothPath.refl x
  geodesic_on := by
    intro t ht
    change IsGeodesicAt (I := I) g (fun _ : ℝ => x) t
    exact isGeodesic_const (I := I) g x t
  continuous_on := continuousOn_const
  constant_speed := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    intro s hs t ht
    change Manifold.riemannianEDist I x x =
      ENNReal.ofReal |s - t| * Manifold.riemannianEDist I x x
    rw [Manifold.riemannianEDist_self, mul_zero]
  length_eq_distance := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.pathELength I (fun _ : ℝ => x) 0 1 =
      Manifold.riemannianEDist I x x
    rw [Manifold.riemannianEDist_self,
      Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    simp [mfderiv_const]
  restriction_geodesic := by
    intro a b ha hb hab t ht
    change IsGeodesicAt (I := I) g (fun _ : ℝ => x) t
    exact isGeodesic_const (I := I) g x t
  translation_geodesic := by
    intro c t ht
    change IsGeodesicAt (I := I) g (fun _ : ℝ => x) t
    exact isGeodesic_const (I := I) g x t

/-- Length/distance equality with the raw Mathlib declarations. -/
theorem MinimizingGeodesic.length_eq_riemannianEDist
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (G.path : ℝ → M) 0 1 =
      Manifold.riemannianEDist I x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact G.length_eq_distance

/-- In the finite canonical metric, the extended constant-speed identity reads
as the ordinary `dist` identity used by later variation arguments. -/
theorem MinimizingGeodesic.dist_eq_constSpeed
    [T3Space M] [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : MetricSpace M :=
      EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
    dist (G.path s) (G.path t) = |s - t| * dist x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M :=
    EMetricSpace.toMetricSpace (fun p q ↦ (riemannianEDist_lt_top g p q).ne)
  rw [dist_eq_riemannianEDist_toReal g (G.path s) (G.path t),
    dist_eq_riemannianEDist_toReal g x y]
  have hspeed := G.constant_speed s hs t ht
  change Manifold.riemannianEDist I (G.path s) (G.path t) =
      ENNReal.ofReal |s - t| * Manifold.riemannianEDist I x y at hspeed
  rw [hspeed]
  rw [ENNReal.toReal_ofReal_mul _ _ (abs_nonneg _)]

/-- The compactness/variation producer expected by the complete-manifold part
of S19.  Its finite-distance premise is explicit, so disconnected components
cannot accidentally be treated as joined by a finite minimizer. -/
structure MinimizingGeodesicData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    [T3Space M] [CompleteSpace E]
    [BoundarylessManifold I M] where
  /-- Minimizing segment existence whenever the selected distance is finite. -/
  exists_segment :
    RiemannianMetricComplete (I := I) g →
      ∀ x y : M,
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
        Manifold.riemannianEDist I x y < ⊤ →
        Nonempty (MinimizingGeodesic (I := I) g x y)

/-- A finite-distance component is enough for the compactness producer.  This
form intentionally has no global `[PreconnectedSpace M]` assumption. -/
theorem exists_minimizingGeodesic_of_finite
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : MinimizingGeodesicData (I := I) g) (x y : M)
    (hfinite :
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      Manifold.riemannianEDist I x y < ⊤) :
    Nonempty (MinimizingGeodesic (I := I) g x y) :=
  data.exists_segment hcomplete x y hfinite

/-- Segment-valued form of the source-facing minimizer theorem. -/
theorem exists_minimizingGeodesic_segment
    [T3Space M] [PreconnectedSpace M] [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : MinimizingGeodesicData (I := I) g) (x y : M) :
    Nonempty (MinimizingGeodesic (I := I) g x y) :=
  exists_minimizingGeodesic_of_finite g hcomplete data x y
    (riemannianEDist_lt_top g x y)

/-- Source-facing existence statement for a minimizing geodesic on a connected
component.  The length equality is stated against the canonical
`riemannianEDist`; the real `dist` form is provided by
`MinimizingGeodesic.dist_eq_constSpeed`. -/
theorem exists_minimizingGeodesic
    [T3Space M] [PreconnectedSpace M] [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : MinimizingGeodesicData (I := I) g) (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ γ : ℝ → M,
      γ 0 = x ∧ γ 1 = y ∧
      isGeodesicOn (I := I) g γ (Set.Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (γ s) (γ t) =
          ENNReal.ofReal |s - t| * Manifold.riemannianEDist I x y) ∧
      Manifold.pathELength I γ 0 1 = Manifold.riemannianEDist I x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rcases exists_minimizingGeodesic_segment g hcomplete data x y with ⟨G⟩
  refine ⟨G.path, G.path.source, G.path.target, G.geodesic_on,
    G.constant_speed, G.length_eq_distance⟩

/-! ## Combined source-facing boundary -/

/-- The reviewed S19 Hopf--Rinow boundary: once the S18 continuation producer
and the compactness/minimizer producer are supplied, metric completeness gives
the global geodesic and minimizing-segment consequences together.

This is intentionally an implication from those named producers, rather than
an opaque postulate asserting either existence result. -/
theorem hopfRinow
    [T3Space M] [PreconnectedSpace M] [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (geodesics : CompleteMaximalGeodesicData (I := I) g)
    (minimizers : MinimizingGeodesicData (I := I) g) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∀ (p : M) (v : TangentSpace I p),
      ∃ γ : ℝ → M,
        γ 0 = p ∧
        HasDerivAt (chartReading (I := I) p γ)
          (chartVelocityAt (I := I) p v) 0 ∧
        Continuous γ ∧ isGeodesic (I := I) g γ) ∧
    (∀ x y : M,
      ∃ γ : ℝ → M,
        γ 0 = x ∧ γ 1 = y ∧
        isGeodesicOn (I := I) g γ (Set.Icc (0 : ℝ) 1) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          Manifold.riemannianEDist I (γ s) (γ t) =
            ENNReal.ofReal |s - t| * Manifold.riemannianEDist I x y) ∧
        Manifold.pathELength I γ 0 1 = Manifold.riemannianEDist I x y) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  · intro p v
    exact exists_globalGeodesic_of_complete_all g hcomplete geodesics p v
  · intro x y
    exact exists_minimizingGeodesic g hcomplete minimizers x y

/-! ## Signature-level regressions -/

/-- The zero-dimensional/one-point regression is available without a
preconnectedness or completeness assumption. -/
theorem exists_refl_minimizingGeodesic
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) : Nonempty (MinimizingGeodesic (I := I) g x x) :=
  ⟨MinimizingGeodesic.refl g x⟩

/-! ### Euclidean regression -/

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The affine straight line in the standard Euclidean Riemannian manifold. -/
def euclideanStraightLine (x y : F) :
    SmoothPath (𝓘(ℝ, F)) x y where
  toFun := ContinuousAffineMap.lineMap x y
  source_eq := by simp [ContinuousAffineMap.coe_lineMap_eq]
  target_eq := by simp [ContinuousAffineMap.coe_lineMap_eq]
  smoothOn := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _

/-- The Euclidean straight line realizes the canonical path length. -/
theorem euclideanStraightLine_length (x y : F) :
    (euclideanStraightLine x y).eLength = edist x y := by
  change Manifold.pathELength 𝓘(ℝ, F) (ContinuousAffineMap.lineMap x y) 0 1 = edist x y
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
  exact lintegral_fderiv_lineMap_eq_edist

/-- The Euclidean straight line has the expected constant-speed extended
distance identity. -/
theorem euclideanStraightLine_speed (x y : F) (s t : ℝ) :
    edist ((euclideanStraightLine x y) s) ((euclideanStraightLine x y) t) =
      ‖s - t‖ₑ * edist x y := by
  change edist ((ContinuousAffineMap.lineMap x y) s)
      ((ContinuousAffineMap.lineMap x y) t) =
    ‖s - t‖ₑ * edist x y
  simp only [edist_eq_enorm_sub]
  simp only [ContinuousAffineMap.coe_lineMap_eq, AffineMap.lineMap_apply,
    vadd_eq_add, vsub_eq_sub]
  rw [show (s • (y - x) + x) - (t • (y - x) + x) =
      (s - t) • (y - x) by module, enorm_smul]
  rw [show ‖y - x‖ₑ = ‖x - y‖ₑ by rw [← neg_sub, enorm_neg]]

/-! The generic Euclidean witness specializes without additional manifold
assumptions to the one-dimensional and zero-dimensional model spaces. -/

/-- One-dimensional Euclidean straight lines retain the canonical length. -/
theorem euclideanStraightLine_one_dimensional (x y : ℝ) :
    (euclideanStraightLine x y).eLength = edist x y :=
  euclideanStraightLine_length x y

/-- The zero-dimensional Euclidean model has the same zero-length witness. -/
theorem euclideanStraightLine_zero_dimensional
    (x y : EuclideanSpace ℝ (Fin 0)) :
    (euclideanStraightLine x y).eLength = edist x y :=
  euclideanStraightLine_length x y

end Euclidean
