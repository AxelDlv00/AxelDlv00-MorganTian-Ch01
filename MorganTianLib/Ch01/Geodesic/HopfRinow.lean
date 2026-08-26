import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Geodesic

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
domains are required to be open and order-connected, hence interval-shaped;
this prevents a disconnected relative-continuity witness from counting as an
extension through a finite endpoint.  The proved theorems are the
set-theoretic maximal-interval argument and the reusable distance/length
adapters.  In particular, global witnesses can be packaged into the maximal
domain contract, affine restriction/translation preserves the checked path
length, and a supplied minimizing segment is proved no longer than every
smooth competitor with matching endpoints.  The selected-distance
completeness bridge reinstalls
the exact `EMetricSpace`/`CompleteSpace M` pair used by the predicate, while
the model-space completion remains a separate premise.  Thus no theorem here
treats metric completeness as an ODE premise, and every existence claim names
its required producer.  The maximal-lifetime contract also records openness,
and bounded-lifetime/model-completion probes guard the incomplete signatures.

The source-facing target is the paragraph preceding Morgan--Tian, Theorem
1.18, pp. 41--42 (`morganTian2007`); see also do Carmo (`doCarmo1992`),
Chapter 7, Section 2, and Lee (`lee2018`), Theorem 6.19.  The
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

/-! ## Canonical metric projections -/

/-- The extended distance selected by an explicit smooth Riemannian metric.

The bundle instance is local to this definition.  In particular, this does
not install a competing project-owned metric structure. -/
noncomputable def canonicalRiemannianEDist
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.riemannianEDist I x y

/-- The canonical path length selected by `g`, with no ambient metric instance
required from a caller. -/
noncomputable def canonicalPathELength
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Manifold.pathELength I γ a b

omit [FiniteDimensional ℝ E] in
/-- The selected extended distance vanishes on the diagonal. -/
@[simp]
theorem canonicalRiemannianEDist_self
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) : canonicalRiemannianEDist (I := I) g x x = 0 := by
  change (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I x x) = 0
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_self

omit [FiniteDimensional ℝ E] in
/-- A constant path has zero selected Riemannian length. -/
@[simp]
theorem canonicalPathELength_const
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x : M) (a b : ℝ) :
    canonicalPathELength (I := I) g (fun _ : ℝ => x) a b = 0 := by
  change (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (fun _ : ℝ => x) a b) = 0
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  simp [mfderiv_const]

/-! ### Completeness of the selected distance -/

/-- Metric completeness for the *canonical selected Riemannian distance*.

`EMetricSpace.ofRiemannianMetric` is installed only in the body of this
predicate.  The proposition is therefore independent of any unrelated
`MetricSpace M` instance, while the local ODE premise `[CompleteSpace E]`
remains a separate typeclass argument.  It is the metric-completeness input
for the complete-manifold paragraph preceding Morgan--Tian, Theorem 1.18
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19. -/
def RiemannianMetricComplete
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  @CompleteSpace M inferInstance

omit [FiniteDimensional ℝ E] in
/-- Reinstall the exact `EMetricSpace` used by `RiemannianMetricComplete`.

This bridge is intentionally explicit: `CompleteSpace M` depends on the
uniformity supplied by `EMetricSpace.ofRiemannianMetric`, so a bare hypothesis
about the selected Riemannian distance must not be mistaken for an arbitrary
ambient completeness instance.  It is the metric-completeness input used in
the complete-manifold paragraph before Morgan--Tian, Theorem 1.18; compare
do Carmo (`doCarmo1992`), Chapter 7, Section 2, and Lee (`lee2018`),
Theorem 6.19. -/
theorem completeSpace_of_RiemannianMetricComplete
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    @CompleteSpace M inferInstance := by
  exact hcomplete

omit [FiniteDimensional ℝ E] in
/-- On a preconnected manifold the selected extended distance is finite. -/
theorem canonicalRiemannianEDist_lt_top
    [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) : canonicalRiemannianEDist (I := I) g x y < ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact riemannianEDist_lt_top g x y

omit [FiniteDimensional ℝ E] in
/-- Under the selected Mathlib extended metric, ambient `edist` is exactly the
canonical Riemannian distance used by the completeness predicate. -/
theorem edist_eq_canonicalRiemannianEDist
    [T3Space M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      continuousRiemannianBundle g
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    edist x y = canonicalRiemannianEDist (I := I) g x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    continuousRiemannianBundle g
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  exact edist_eq_riemannianEDist g x y

/-! ## Intrinsic predicates on a lifetime -/

/-- The moving-foot geodesic predicate restricted to a set of times.

`IsGeodesicAt` is the S18 predicate built from the exact
`Connection.leviCivitaConnection g`; its coordinate contraction is exposed by
`chartChristoffelContraction_eq_leviCivita`.  This wrapper therefore introduces
no second connection vocabulary. -/
def isGeodesicOn
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, IsGeodesicAt (I := I) g γ t

/-- Restricting the lifetime to `Set.univ` is equivalent to the global
geodesic predicate. -/
@[simp]
theorem isGeodesicOn_univ_iff
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) :
    isGeodesicOn (I := I) g γ (Set.univ : Set ℝ) ↔ isGeodesic (I := I) g γ := by
  constructor
  · intro h t
    exact h t (Set.mem_univ t)
  · intro h t _
    exact h t

/-- Affine transport of a geodesic certificate on a time set.

The new lifetime is the literal preimage under `t ↦ a * t + c`; this keeps
restriction and translation compatible with the moving-foot equation without
assuming injectivity, endpoint conventions, or a larger ambient lifetime. -/
theorem isGeodesicOn_comp_affine
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : isGeodesicOn (I := I) g gamma s) (a c : ℝ) :
    isGeodesicOn (I := I) g (fun t ↦ gamma (a * t + c))
      ((fun t : ℝ ↦ a * t + c) ⁻¹' s) := by
  intro t ht
  exact IsGeodesicAt.comp_affine (I := I) g gamma a c t
    (h (a * t + c) ht)

/-- Set-relative time translation, with its exact pulled-back lifetime. -/
theorem isGeodesicOn_comp_add
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : isGeodesicOn (I := I) g gamma s) (c : ℝ) :
    isGeodesicOn (I := I) g (fun t ↦ gamma (t + c))
      ((fun t : ℝ ↦ t + c) ⁻¹' s) := by
  simpa only [one_mul] using isGeodesicOn_comp_affine (I := I) g gamma s h 1 c

/-- Set-relative time reversal, with its exact pulled-back lifetime. -/
theorem isGeodesicOn_comp_neg
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : isGeodesicOn (I := I) g gamma s) :
    isGeodesicOn (I := I) g (fun t ↦ gamma (-t))
      ((fun t : ℝ ↦ -t) ⁻¹' s) := by
  simpa only [neg_mul, one_mul, zero_add, add_zero, neg_one_mul] using
    isGeodesicOn_comp_affine (I := I) g gamma s h (-1) 0

/-- Set-relative velocity rescaling, with its exact pulled-back lifetime. -/
theorem isGeodesicOn_comp_mul_left
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M) (s : Set ℝ)
    (h : isGeodesicOn (I := I) g gamma s) (a : ℝ) :
    isGeodesicOn (I := I) g (fun t ↦ gamma (a * t))
      ((fun t : ℝ ↦ a * t) ⁻¹' s) := by
  simpa only [add_zero] using isGeodesicOn_comp_affine (I := I) g gamma s h a 0

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
lifetime are deliberately not used.  This is the maximal-geodesic side of the
complete-manifold paragraph preceding Morgan--Tian, Theorem 1.18
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19. -/
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
  superdomain.  Strict enlargement is supplied separately by the continuation
  contract; requiring interval-shaped superdomains prevents a relative
  continuity witness on a disconnected set from masquerading as continuation
  through a finite endpoint. -/
  maximal :
    ∀ (s : Set ℝ) (γ : ℝ → M), lifetime ⊆ s →
      IsOpen s → s.OrdConnected →
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
    intro s γ hs hopen hinterval hgeo hcont heq
    exact fun t ht => Set.mem_univ t

/-! A global witness can be viewed as a maximal witness with lifetime `univ`.
This adapter is deliberately one-way: it packages an already-proved global
solution, and does not manufacture one from metric completeness. -/

/-- Package an all-real-time geodesic as a maximal-domain witness.

The constructor is useful when an upstream S18 argument already returns a
global solution.  Its maximality proof is set-theoretic because `univ` has no
strict superdomain; no uniqueness of global solutions is asserted.  The
source-facing complete-manifold consequence is Morgan--Tian's preceding
complete-manifold paragraph and Theorem 1.18 (`morganTian2007`), compared with
do Carmo (`doCarmo1992`), Chapter 7, and Lee (`lee2018`), Theorem 6.19. -/
def MaximalGeodesic.of_global
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (γ : ℝ → M)
    (hzero : γ 0 = p)
    (hderiv : HasDerivAt (chartReading (I := I) p γ)
      (chartVelocityAt (I := I) p v) 0)
    (hcont : Continuous γ) (hgeo : isGeodesic (I := I) g γ) :
    MaximalGeodesic (I := I) g p v := by
  refine
    { curve := γ
      lifetime := Set.univ
      zero_mem := Set.mem_univ _
      position_zero := hzero
      initial_derivative := hderiv
      geodesic_on := ?_
      continuous_on := hcont.continuousOn
      interval := ?_
      lifetime_open := isOpen_univ
      maximal := ?_ }
  · intro t ht
    exact hgeo t
  · intro a b t ha hb hat htb
    exact Set.mem_univ t
  · intro s δ hs hopen hinterval hδ hcontδ heq t ht
    exact Set.mem_univ t

/-! The custom convexity field is retained for compatibility with the S18
maximal-domain producer, while the continuation boundary uses Mathlib's
order-connected interval predicate. -/

/-- The certified lifetime is order-connected in the real-time order. -/
theorem MaximalGeodesic.lifetime_ordConnected
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p)
    (G : MaximalGeodesic (I := I) g p v) : G.lifetime.OrdConnected := by
  rw [Set.ordConnected_iff]
  intro a ha b hb _hab t ht
  exact G.interval ha hb ht.1 ht.2

/-- The constant maximal geodesic has the displayed lifetime. -/
@[simp]
theorem MaximalGeodesic.refl_lifetime
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) : (MaximalGeodesic.refl (I := I) g p).lifetime = Set.univ := rfl

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

/-- A bounded lifetime is not forward complete.  This small negative control
keeps incomplete-domain behavior visible in the public API: no theorem may
turn a finite interval into an all-real-time solution without the named
continuation producer and metric-completeness input. -/
theorem incompleteLifetime_probe :
    ¬ LifetimeUnboundedAbove (Set.Ioo (-1 : ℝ) 1) := by
  intro h
  obtain ⟨t, ht, hmore⟩ := h 1
  exact (lt_irrefl (1 : ℝ)) (hmore.trans ht.2)

/-- A disconnected set cannot be used as an interval-shaped continuation
domain.  This negative regression protects the open/order-connected guard in
`MaximalGeodesic.maximal` from being weakened back to arbitrary supersets. -/
theorem disconnectedLifetime_not_ordConnected :
    ¬ ({0, 2} : Set ℝ).OrdConnected := by
  intro h
  have hm := h.out (show (0 : ℝ) ∈ ({0, 2} : Set ℝ) by simp)
    (show (2 : ℝ) ∈ ({0, 2} : Set ℝ) by simp)
  have hmid := hm (show (3 / 2 : ℝ) ∈ Set.Icc 0 2 by norm_num)
  norm_num at hmid

/-- The continuation output required from the completed S18 maximal solution.

The hypothesis is parameterized by `RiemannianMetricComplete`; this keeps the
metric-completeness route visible and prevents it from being silently reused
as the `[CompleteSpace E]` premise of the local ODE.  It is the continuation
input for the complete-manifold paragraph preceding Morgan--Tian, Theorem 1.18
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19. -/
structure MaximalGeodesicContinuation
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p) (G : MaximalGeodesic (I := I) g p v)
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M] where
  right :
    RiemannianMetricComplete (I := I) g →
      ∀ b : ℝ, (∀ t ∈ G.lifetime, t ≤ b) →
        ∃ (s : Set ℝ) (γ : ℝ → M),
          G.lifetime ⊆ s ∧
          IsOpen s ∧ s.OrdConnected ∧
          (∃ t ∈ s, b < t) ∧
          isGeodesicOn (I := I) g γ s ∧ ContinuousOn γ s ∧
          (∀ t ∈ G.lifetime, γ t = G.curve t)
  left :
    RiemannianMetricComplete (I := I) g →
      ∀ b : ℝ, (∀ t ∈ G.lifetime, b ≤ t) →
        ∃ (s : Set ℝ) (γ : ℝ → M),
          G.lifetime ⊆ s ∧
          IsOpen s ∧ s.OrdConnected ∧
          (∃ t ∈ s, t < b) ∧
          isGeodesicOn (I := I) g γ s ∧ ContinuousOn γ s ∧
          (∀ t ∈ G.lifetime, γ t = G.curve t)

/-- The continuation contract for a witness whose lifetime is already `univ`.

Both directions are witnessed by the same curve and domain.  This is a
proof-backed bridge from the source-facing all-time predicate to the maximal
domain record; the completeness argument remains in
`maximalGeodesic_lifetime_eq_univ_of_complete`. -/
theorem MaximalGeodesicContinuation.of_univ
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (p : M) (v : TangentSpace I p)
    (G : MaximalGeodesic (I := I) g p v)
    (hlife : G.lifetime = (Set.univ : Set ℝ)) :
    MaximalGeodesicContinuation (I := I) g p v G := by
  refine { right := ?_, left := ?_ }
  · intro _hcomplete b _hupper
    refine ⟨Set.univ, G.curve, ?_, isOpen_univ, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact Set.mem_univ t
    · exact Set.ordConnected_univ
    · exact ⟨b + 1, Set.mem_univ _, by linarith⟩
    · rw [← hlife]
      exact G.geodesic_on
    · rw [← hlife]
      exact G.continuous_on
    · intro t ht
      rfl
  · intro _hcomplete b _hlower
    refine ⟨Set.univ, G.curve, ?_, isOpen_univ, ?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact Set.mem_univ t
    · exact Set.ordConnected_univ
    · exact ⟨b - 1, Set.mem_univ _, by linarith⟩
    · rw [← hlife]
      exact G.geodesic_on
    · rw [← hlife]
      exact G.continuous_on
    · intro t ht
      rfl

/-! ### The unbounded-lifetime argument -/

/-- Metric completeness plus the supplied forward continuation rules out a
finite upper lifetime.  The proof is the maximality contradiction, so it does
not identify metric completeness with the model-space ODE completion. -/
theorem maximalGeodesic_lifetime_unboundedAbove
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    LifetimeUnboundedAbove G.lifetime := by
  classical
  intro b
  by_contra hbound
  have hupper : ∀ t ∈ G.lifetime, t ≤ b := by
    intro t ht
    exact le_of_not_gt (fun htb => hbound ⟨t, ht, htb⟩)
  obtain ⟨s, γ, hs, hopen, hinterval, hmore, hgeo, hcont, heq⟩ :=
    hcontinue.right hcomplete b hupper
  have hsubset : s ⊆ G.lifetime := G.maximal s γ hs hopen hinterval hgeo hcont heq
  rcases hmore with ⟨t, ht, hbt⟩
  exact (not_lt_of_ge (hupper t (hsubset ht))) hbt

/-- The backward analogue of
`maximalGeodesic_lifetime_unboundedAbove`. -/
theorem maximalGeodesic_lifetime_unboundedBelow
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (G : MaximalGeodesic (I := I) g p v)
    (hcontinue : MaximalGeodesicContinuation (I := I) g p v G) :
    LifetimeUnboundedBelow G.lifetime := by
  classical
  intro b
  by_contra hbound
  have hlower : ∀ t ∈ G.lifetime, b ≤ t := by
    intro t ht
    exact le_of_not_gt (fun htb => hbound ⟨t, ht, htb⟩)
  obtain ⟨s, γ, hs, hopen, hinterval, hmore, hgeo, hcont, heq⟩ :=
    hcontinue.left hcomplete b hlower
  have hsubset : s ⊆ G.lifetime := G.maximal s γ hs hopen hinterval hgeo hcont heq
  rcases hmore with ⟨t, ht, htb⟩
  exact (not_lt_of_ge (hlower t (hsubset ht))) htb

/-- A maximal interval with both continuation directions is all of `ℝ`. -/
theorem maximalGeodesic_lifetime_eq_univ_of_complete
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
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

The exact `[BoundarylessManifold I M]` and `[CompleteSpace E]` assumptions are
kept in the signature.  The former supplies all point-local interior facts to
the S18 producer; the latter is the checked local ODE premise. -/
theorem exists_globalGeodesic_of_complete
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
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
type rather than hiding it in a finite-interval facade.  This unresolved
producer input belongs to the complete-manifold paragraph preceding
Morgan--Tian, Theorem 1.18 (`morganTian2007`); compare do Carmo (`doCarmo1992`),
Chapter 7, Section 2, and Lee (`lee2018`), Theorem 6.19. -/
structure CompleteMaximalGeodesicData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M] where
  solution : ∀ (p : M) (v : TangentSpace I p),
    MaximalGeodesic (I := I) g p v
  continuation : ∀ (p : M) (v : TangentSpace I p),
    MaximalGeodesicContinuation (I := I) g p v (solution p v)

/-- A one-point/subsingleton manifold supplies the maximal-domain producer
without an analytic continuation argument: every tangent datum is zero, so
the constant geodesic has lifetime `univ`.  This is a proof-backed
zero-dimensional regression for the producer boundary, not a replacement for
the general S18 construction.  The complete-manifold source target is the
paragraph preceding Morgan--Tian, Theorem 1.18 (`morganTian2007`); compare do
Carmo (`doCarmo1992`), Chapter 7, and Lee (`lee2018`), Theorem 6.19. -/
noncomputable def CompleteMaximalGeodesicData.of_subsingleton
    [Subsingleton M] [∀ p : M, Subsingleton (TangentSpace I p)]
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    CompleteMaximalGeodesicData (I := I) g := by
  refine { solution := ?_, continuation := ?_ }
  · intro p v
    have hv : v = (0 : TangentSpace I p) := Subsingleton.elim _ _
    subst v
    exact MaximalGeodesic.refl g p
  · intro p v
    have hv : v = (0 : TangentSpace I p) := Subsingleton.elim _ _
    subst v
    exact MaximalGeodesicContinuation.of_univ g p 0
      (MaximalGeodesic.refl g p) rfl

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

/-- The source-facing geodesic-completeness predicate used by later exponential
and variation modules.  This is a producer-consuming wrapper: the actual S18
maximal-domain and continuation construction is supplied by `data`.  Its source
anchor is the complete-manifold paragraph preceding Morgan--Tian, Theorem 1.18
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19.  This is the existence form; the preceding
per-witness lifetime theorem is the contract for each supplied maximal
geodesic, and no uniqueness/equivalence claim is made here. -/
def IsGeodesicallyComplete
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) : Prop :=
  ∀ (p : M) (v : TangentSpace I p),
    ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ)
        (chartVelocityAt (I := I) p v) 0 ∧
      Continuous γ ∧ isGeodesic (I := I) g γ

/-- Turn the source-facing all-time existence predicate into the maximal-domain
producer expected by this module.

The chosen global curve is packaged with lifetime `univ`, and
`MaximalGeodesicContinuation.of_univ` supplies the two vacuous extension
certificates.  This direction is an adapter only: it does not prove
`IsGeodesicallyComplete` from metric completeness, and it deliberately makes
no uniqueness claim about the chosen witnesses. -/
noncomputable def CompleteMaximalGeodesicData.of_isGeodesicallyComplete
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (h : IsGeodesicallyComplete (I := I) g) :
    CompleteMaximalGeodesicData (I := I) g := by
  classical
  let γ : ∀ (p : M), TangentSpace I p → ℝ → M :=
    fun p v => Classical.choose (h p v)
  have hγzero : ∀ (p : M) (v : TangentSpace I p), γ p v 0 = p := by
    intro p v
    exact (Classical.choose_spec (h p v)).1
  have hγderiv : ∀ (p : M) (v : TangentSpace I p),
      HasDerivAt (chartReading (I := I) p (γ p v))
        (chartVelocityAt (I := I) p v) 0 := by
    intro p v
    exact (Classical.choose_spec (h p v)).2.1
  have hγcont : ∀ (p : M) (v : TangentSpace I p), Continuous (γ p v) := by
    intro p v
    exact (Classical.choose_spec (h p v)).2.2.1
  have hγgeo : ∀ (p : M) (v : TangentSpace I p),
      isGeodesic (I := I) g (γ p v) := by
    intro p v
    exact (Classical.choose_spec (h p v)).2.2.2
  let solution : ∀ (p : M) (v : TangentSpace I p),
      MaximalGeodesic (I := I) g p v :=
    fun p v => MaximalGeodesic.of_global g p v (γ p v)
      (hγzero p v) (hγderiv p v) (hγcont p v) (hγgeo p v)
  refine { solution := solution, continuation := ?_ }
  intro p v
  exact MaximalGeodesicContinuation.of_univ g p v (solution p v) rfl

/-- Metric completeness and a completed S18 producer imply the source-facing
geodesic-completeness predicate.  This is the forward producer implication at
Morgan--Tian, Theorem 1.18 (`morganTian2007`); compare do Carmo (`doCarmo1992`),
Chapter 7, Section 2, and Lee (`lee2018`), Theorem 6.19. -/
theorem isGeodesicallyComplete_of_complete
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : CompleteMaximalGeodesicData (I := I) g) :
    IsGeodesicallyComplete (I := I) g := by
  intro p v
  exact exists_globalGeodesic_of_complete_all g hcomplete data p v

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

/-- Restricting a geodesic certificate to a smaller time set is always valid.
The affine reparameterized equation itself is kept as a producer field below,
since its proof belongs to the S18 equation-transfer API. -/
theorem isGeodesicOn_mono
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) {s s' : Set ℝ} (hs : s' ⊆ s)
    (hγ : isGeodesicOn (I := I) g γ s) :
    isGeodesicOn (I := I) g γ s' := by
  intro t ht
  exact hγ t (hs ht)

/-- A geodesic on `[0,1]` stays geodesic after affine normalization of any
subinterval `[a,b]` contained in it.  The equation transfer is supplied by
the proved S18 affine lemma; the endpoint hypotheses are used only for the
interval-membership arithmetic. -/
theorem isGeodesicOn_affineReparam
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (gamma : ℝ → M)
    (hgamma : isGeodesicOn (I := I) g gamma (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    isGeodesicOn (I := I) g (affineReparam gamma a b) (Set.Icc (0 : ℝ) 1) := by
  have htransport := isGeodesicOn_comp_affine (I := I) g gamma
    (Set.Icc (0 : ℝ) 1) hgamma (b - a) a
  intro t ht
  have harg : a + (b - a) * t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
  change IsGeodesicAt (I := I) g (fun r ↦ gamma (a + (b - a) * r)) t
  simpa [add_comm] using htransport t (by
    change (b - a) * t + a ∈ Set.Icc (0 : ℝ) 1
    simpa only [add_comm] using harg)

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

omit [FiniteDimensional ℝ E] in
/-- Riemannian path length is unchanged by affine normalization of a contained
subinterval.

This is the length counterpart to `isGeodesicOn_affineReparam` and
`constantSpeed_restrict`.  The proof delegates the change of variables to
Mathlib's monotone reparameterization theorem and keeps the endpoint and
interval hypotheses explicit. -/
theorem canonicalPathELength_affineReparam
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : a ≤ b) (hγ : CMDiff[Set.Icc (0 : ℝ) 1] 1 γ) :
    canonicalPathELength (I := I) g (affineReparam γ a b) 0 1 =
      canonicalPathELength (I := I) g γ a b := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength I (fun t : ℝ => γ (a + (b - a) * t)) 0 1 =
    Manifold.pathELength I γ a b
  rw [show (fun t : ℝ => γ (a + (b - a) * t)) =
      γ ∘ (fun t : ℝ => a + (b - a) * t) by rfl]
  have hcomp :
      Manifold.pathELength I (γ ∘ (fun t : ℝ => a + (b - a) * t)) 0 1 =
        Manifold.pathELength I γ
          ((fun t : ℝ => a + (b - a) * t) 0)
          ((fun t : ℝ => a + (b - a) * t) 1) := by
    apply Manifold.pathELength_comp_of_monotoneOn zero_le_one
    · intro s hs t ht hst
      nlinarith [hab]
    · intro t ht
      fun_prop
    · have hsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1 := by
        intro t ht
        constructor <;> nlinarith [ha.1, hb.2, ht.1, ht.2]
      have hγab : MDiff[Set.Icc
          ((fun t : ℝ => a + (b - a) * t) 0)
          ((fun t : ℝ => a + (b - a) * t) 1)] γ := by
        simpa using (hγ.mono hsub).mdifferentiableOn (by norm_num)
      exact hγab
  have hf0 : (fun t : ℝ => a + (b - a) * t) 0 = a := by ring
  have hf1 : (fun t : ℝ => a + (b - a) * t) 1 = b := by ring
  simpa only [hf0, hf1] using hcomp

/-- The smooth-path wrapper for affine restriction to a contained subinterval.

The underlying function is totalized on `ℝ`, while the endpoint and smoothness
proofs are restricted to `[0,1]`.  This keeps the path representation aligned
with `SmoothPath` in `Ch01.Metric` and avoids introducing a second path type. -/
def _root_.MorganTianLib.Ch01.SmoothPath.affineReparam
    {x y : M} (p : MorganTianLib.Ch01.SmoothPath I x y)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    MorganTianLib.Ch01.SmoothPath I (p a) (p b) where
  toFun := MorganTianLib.Ch01.Geodesic.affineReparam (p : ℝ → M) a b
  source_eq := by simp [MorganTianLib.Ch01.Geodesic.affineReparam]
  target_eq := by simp [MorganTianLib.Ch01.Geodesic.affineReparam]
  smoothOn := by
    apply p.smoothOn.comp
    · rw [contMDiffOn_iff_contDiffOn]
      fun_prop
    · intro t ht
      constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]

omit [FiniteDimensional ℝ E] in
/-- Translation preserves path length on any unit interval whose translated
times lie in the certified domain. -/
theorem canonicalPathELength_translate
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (γ : ℝ → M) (c : ℝ)
    (hγ : CMDiff[Set.Icc c (c + 1)] 1 γ) :
    canonicalPathELength (I := I) g (fun t : ℝ => γ (t + c)) 0 1 =
      canonicalPathELength (I := I) g γ c (c + 1) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength I (fun t : ℝ => γ (t + c)) 0 1 =
    Manifold.pathELength I γ c (c + 1)
  rw [show (fun t : ℝ => γ (t + c)) =
      γ ∘ (fun t : ℝ => t + c) by rfl]
  have hcomp :
      Manifold.pathELength I (γ ∘ (fun t : ℝ => t + c)) 0 1 =
        Manifold.pathELength I γ
          ((fun t : ℝ => t + c) 0) ((fun t : ℝ => t + c) 1) := by
    apply Manifold.pathELength_comp_of_monotoneOn zero_le_one
    · intro s hs t ht hst
      linarith
    · intro t ht
      fun_prop
    · simpa [add_comm] using hγ.mdifferentiableOn (by norm_num)
  simpa [add_zero, add_comm] using hcomp

/-- A geodesic segment together with the source-facing minimizing and
constant-speed certificates.

The `restriction_geodesic` and `translation_geodesic` fields are retained as
producer-facing certificates for compatibility with the earlier S19 boundary.
The proof-backed `restriction_geodesic_proved` and
`translation_geodesic_proved` lemmas below derive the same compatibility from
`geodesic_on` using the affine equation-transfer API in `Geodesic`; producers
may therefore migrate away from duplicating these fields.  Its source boundary
is Morgan--Tian, Theorem 1.18
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19. -/
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
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      canonicalRiemannianEDist (I := I) g (path s) (path t) =
        ENNReal.ofReal |s - t| * canonicalRiemannianEDist (I := I) g x y
  /-- The path length is exactly the canonical Riemannian distance. -/
  length_eq_distance :
    canonicalPathELength (I := I) g (path : ℝ → M) 0 1 =
      canonicalRiemannianEDist (I := I) g x y
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

/-- The restriction certificate follows from the intrinsic equation itself.

This is the canonical proof-backed replacement for the producer field of the
same shape: affine reparameterization is handled by the S18 equation-transfer
lemma, and the interval hypotheses ensure that the pulled-back times remain
inside `[0,1]`. -/
theorem MinimizingGeodesic.restriction_geodesic_proved
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    isGeodesicOn (I := I) g
      (affineReparam (G.path : ℝ → M) a b) (Set.Icc (0 : ℝ) 1) :=
  isGeodesicOn_affineReparam (I := I) g (G.path : ℝ → M)
    G.geodesic_on ha hb hab

/-- The translated certificate follows from the intrinsic equation and has the
exact preimage lifetime. -/
theorem MinimizingGeodesic.translation_geodesic_proved
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) (c : ℝ) :
    isGeodesicOn (I := I) g (fun t ↦ (G.path : ℝ → M) (t + c))
      ((fun t : ℝ ↦ t + c) ⁻¹' Set.Icc (0 : ℝ) 1) :=
  isGeodesicOn_comp_add (I := I) g (G.path : ℝ → M)
    (Set.Icc (0 : ℝ) 1) G.geodesic_on c

/-- Constant-speed data for an affine subsegment, with the endpoint distance
made explicit.  This is the metric half of the restriction compatibility
consumed by later exponential and variation modules. -/
theorem MinimizingGeodesic.restriction_constantSpeed
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      canonicalRiemannianEDist (I := I) g
          (affineReparam (G.path : ℝ → M) a b s)
          (affineReparam (G.path : ℝ → M) a b t) =
        ENNReal.ofReal |s - t| *
          canonicalRiemannianEDist (I := I) g (G.path a) (G.path b) :=
  constantSpeed_restrict
    (D := canonicalRiemannianEDist (I := I) g)
    (γ := (G.path : ℝ → M))
    (L := canonicalRiemannianEDist (I := I) g x y)
    G.constant_speed ha hb hab

/-- Constant-speed data for a translated portion of a minimizing path. -/
theorem MinimizingGeodesic.translation_constantSpeed
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) (c s t : ℝ)
    (hs : s + c ∈ Set.Icc (0 : ℝ) 1)
    (ht : t + c ∈ Set.Icc (0 : ℝ) 1) :
    canonicalRiemannianEDist (I := I) g
        ((G.path : ℝ → M) (s + c)) ((G.path : ℝ → M) (t + c)) =
      ENNReal.ofReal |s - t| *
        canonicalRiemannianEDist (I := I) g x y :=
  constantSpeed_translate
    (D := canonicalRiemannianEDist (I := I) g)
    (γ := (G.path : ℝ → M))
    (L := canonicalRiemannianEDist (I := I) g x y)
    G.constant_speed c s t hs ht

/-- The affine subsegment has length at least its endpoint distance.

This lower bound is unconditional and deliberately does not pretend to prove
the compactness/minimizer step.  Equality is exposed as the explicit
`hsub` premise of `MinimizingGeodesic.restrict_of_length` below. -/
theorem MinimizingGeodesic.restriction_edist_le_length
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    canonicalRiemannianEDist (I := I) g (G.path a) (G.path b) ≤
      canonicalPathELength (I := I) g
        (affineReparam (G.path : ℝ → M) a b) 0 1 := by
  let q : MorganTianLib.Ch01.SmoothPath I (G.path a) (G.path b) :=
    MorganTianLib.Ch01.SmoothPath.affineReparam G.path ha hb hab
  change
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
      Manifold.riemannianEDist I (G.path a) (G.path b)) ≤
    (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I (q : ℝ → M) 0 1)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_le_pathELength
    (q.smoothOn.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))
    q.source q.target zero_le_one

/-- Translation preserves the certified length of a minimizing path whenever
the translated unit interval stays inside its smoothness interval. -/
theorem MinimizingGeodesic.translation_length
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y) (c : ℝ)
    (hc : Set.Icc c (c + 1) ⊆ Set.Icc (0 : ℝ) 1) :
    canonicalPathELength (I := I) g
        (fun t : ℝ => (G.path : ℝ → M) (t + c)) 0 1 =
      canonicalPathELength (I := I) g (G.path : ℝ → M) c (c + 1) := by
  apply canonicalPathELength_translate g (G.path : ℝ → M) c
  exact (G.path.smoothOn.of_le (by simp)).mono hc

/-- Construct a minimizing-segment certificate from its geometric core.

The two affine-compatibility fields are filled by the proved S18 transport
lemmas, so a compactness/variation producer only needs to provide the path,
its equation, constant speed, and length equality.  This is the producer
interface intended for the complete-manifold paragraph before Morgan--Tian,
Theorem 1.18 (`morganTian2007`), with do Carmo Chapter 7 and Lee Theorem 6.19
as comparison references. -/
def MinimizingGeodesic.of_core
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (path : SmoothPath I x y)
    (hgeo : isGeodesicOn (I := I) g (path : ℝ → M) (Set.Icc (0 : ℝ) 1))
    (hcont : ContinuousOn (path : ℝ → M) (Set.Icc (0 : ℝ) 1))
    (hspeed : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      canonicalRiemannianEDist (I := I) g (path s) (path t) =
        ENNReal.ofReal |s - t| * canonicalRiemannianEDist (I := I) g x y)
    (hlen : canonicalPathELength (I := I) g (path : ℝ → M) 0 1 =
      canonicalRiemannianEDist (I := I) g x y) :
    MinimizingGeodesic (I := I) g x y where
  path := path
  geodesic_on := hgeo
  continuous_on := hcont
  constant_speed := hspeed
  length_eq_distance := hlen
  restriction_geodesic := by
    intro a b ha hb hab
    exact isGeodesicOn_affineReparam (I := I) g (path : ℝ → M) hgeo ha hb hab
  translation_geodesic := by
    intro c
    exact isGeodesicOn_comp_add (I := I) g (path : ℝ → M)
      (Set.Icc (0 : ℝ) 1) hgeo c

/-- Package a finite subsegment once its path-length equality has been supplied
by the compactness/variation producer.

The geodesic equation, smooth-path endpoints, constant-speed identity, and
affine length change are all proved here.  The sole extra premise `hsub` is
the genuine segment-length equality that is not derivable from the current
unit-interval certificates alone; keeping it explicit prevents this adapter
from smuggling in the unresolved Hopf--Rinow compactness argument. -/
def MinimizingGeodesic.restrict_of_length
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b)
    (hsub : canonicalPathELength (I := I) g (G.path : ℝ → M) a b =
      canonicalRiemannianEDist (I := I) g (G.path a) (G.path b)) :
    MinimizingGeodesic (I := I) g (G.path a) (G.path b) := by
  let q : MorganTianLib.Ch01.SmoothPath I (G.path a) (G.path b) :=
    MorganTianLib.Ch01.SmoothPath.affineReparam G.path ha hb hab
  have hq : (q : ℝ → M) =
      MorganTianLib.Ch01.Geodesic.affineReparam (G.path : ℝ → M) a b := rfl
  refine MinimizingGeodesic.of_core g (G.path a) (G.path b) q ?_ ?_ ?_ ?_
  · rw [hq]
    exact G.restriction_geodesic_proved g x y ha hb hab
  · exact q.smoothOn.continuousOn
  · rw [hq]
    exact G.restriction_constantSpeed g x y ha hb hab
  · rw [hq]
    exact (canonicalPathELength_affineReparam g (G.path : ℝ → M)
      ha hb hab (G.path.smoothOn.of_le (by simp))).trans hsub

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
    intro s hs t ht
    change canonicalRiemannianEDist (I := I) g x x =
      ENNReal.ofReal |s - t| * canonicalRiemannianEDist (I := I) g x x
    simp
  length_eq_distance := by
    change canonicalPathELength (I := I) g (fun _ : ℝ => x) 0 1 =
      canonicalRiemannianEDist (I := I) g x x
    simp
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

/-- A minimizing segment is no longer than any smooth competitor with the same
endpoints.

`Manifold.riemannianEDist_le_pathELength` supplies the lower bound for the
competitor, while `G.length_eq_distance` identifies the candidate's length
with that infimum.  This explicit inequality is the variational interface
consumed by later first/second-variation modules; it does not assert
uniqueness.  The source statement is the complete-manifold paragraph before
Morgan--Tian, Theorem 1.18 (`morganTian2007`), compared with do Carmo
(`doCarmo1992`), Chapter 7, and Lee (`lee2018`), Theorem 6.19. -/
theorem MinimizingGeodesic.length_le_pathELength
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {γ : ℝ → M}
    (hγ : CMDiff[Set.Icc (0 : ℝ) 1] 1 γ)
    (hstart : γ 0 = x) (hend : γ 1 = y) :
    canonicalPathELength (I := I) g (G.path : ℝ → M) 0 1 ≤
      canonicalPathELength (I := I) g γ 0 1 := by
  calc
    canonicalPathELength (I := I) g (G.path : ℝ → M) 0 1 =
        canonicalRiemannianEDist (I := I) g x y := G.length_eq_distance
    _ ≤ canonicalPathELength (I := I) g γ 0 1 := by
      change
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          Manifold.riemannianEDist I x y) ≤
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          Manifold.pathELength I γ 0 1)
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγ hstart hend zero_le_one

/-- The competitor inequality on an arbitrary ordered parameter interval. -/
theorem MinimizingGeodesic.length_le_pathELength_interval
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    {a b : ℝ} {γ : ℝ → M}
    (hγ : CMDiff[Set.Icc a b] 1 γ)
    (hstart : γ a = x) (hend : γ b = y) (hab : a ≤ b) :
    canonicalPathELength (I := I) g (G.path : ℝ → M) 0 1 ≤
      canonicalPathELength (I := I) g γ a b := by
  calc
    canonicalPathELength (I := I) g (G.path : ℝ → M) 0 1 =
        canonicalRiemannianEDist (I := I) g x y := G.length_eq_distance
    _ ≤ canonicalPathELength (I := I) g γ a b := by
      change
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          Manifold.riemannianEDist I x y) ≤
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩;
          Manifold.pathELength I γ a b)
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hγ hstart hend hab

/-- The same competitor inequality specialized to the project's `SmoothPath`
representation. -/
theorem MinimizingGeodesic.length_le_smoothPath_eLength
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) (G : MinimizingGeodesic (I := I) g x y)
    (q : MorganTianLib.Ch01.SmoothPath I x y) :
    canonicalPathELength (I := I) g (G.path : ℝ → M) 0 1 ≤
      canonicalPathELength (I := I) g (q : ℝ → M) 0 1 := by
  exact MinimizingGeodesic.length_le_pathELength g x y G
    (q.smoothOn.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))
    q.source q.target

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
cannot accidentally be treated as joined by a finite minimizer.  This remains
an unresolved producer input for Morgan--Tian, Theorem 1.18 (`morganTian2007`);
compare do Carmo (`doCarmo1992`), Chapter 7, Section 2, and Lee (`lee2018`),
Theorem 6.19. -/
structure MinimizingGeodesicData
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    [T3Space M] [CompleteSpace E]
    [BoundarylessManifold I M] where
  exists_segment :
    RiemannianMetricComplete (I := I) g →
      ∀ x y : M, canonicalRiemannianEDist (I := I) g x y < ⊤ →
        Nonempty (MinimizingGeodesic (I := I) g x y)

/-- The minimizing-segment producer for a subsingleton manifold.  The only
pair of endpoints is the diagonal, where `MinimizingGeodesic.refl` supplies
the constant segment.  Finite distance is still consumed explicitly so this
adapter cannot blur the disconnected-component branch of S19.  The source
anchor is Morgan--Tian, Theorem 1.18 (`morganTian2007`), with do Carmo
(`doCarmo1992`), Chapter 7, and Lee (`lee2018`), Theorem 6.19 as cross-checks. -/
theorem MinimizingGeodesicData.of_subsingleton
    [Subsingleton M]
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)) :
    MinimizingGeodesicData (I := I) g := by
  refine { exists_segment := ?_ }
  intro _hcomplete x y _hfinite
  have hxy : y = x := Subsingleton.elim _ _
  subst y
  exact ⟨MinimizingGeodesic.refl g x⟩

/-- A finite-distance component is enough for the compactness producer.  This
form intentionally has no global `[PreconnectedSpace M]` assumption. -/
theorem exists_minimizingGeodesic_of_finite
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : MinimizingGeodesicData (I := I) g) (x y : M)
    (hfinite : canonicalRiemannianEDist (I := I) g x y < ⊤) :
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
    (canonicalRiemannianEDist_lt_top g x y)

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
    ∃ γ : ℝ → M,
      γ 0 = x ∧ γ 1 = y ∧
      isGeodesicOn (I := I) g γ (Set.Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        canonicalRiemannianEDist (I := I) g (γ s) (γ t) =
          ENNReal.ofReal |s - t| * canonicalRiemannianEDist (I := I) g x y) ∧
      canonicalPathELength (I := I) g γ 0 1 =
        canonicalRiemannianEDist (I := I) g x y := by
  rcases exists_minimizingGeodesic_segment g hcomplete data x y with ⟨G⟩
  refine ⟨G.path, G.path.source, G.path.target, G.geodesic_on,
    G.constant_speed, G.length_eq_distance⟩

/-! ## Combined source-facing boundary -/

/-- The reviewed S19 Hopf--Rinow boundary: once the S18 continuation producer
and the compactness/minimizer producer are supplied, metric completeness gives
the global geodesic and minimizing-segment consequences together.

This is intentionally an implication from those named producers, rather than
an opaque postulate asserting either existence result.  The source target is
Morgan--Tian, Theorem 1.18 and its preceding complete-manifold paragraph
(`morganTian2007`); compare do Carmo (`doCarmo1992`), Chapter 7, Section 2,
and Lee (`lee2018`), Theorem 6.19. -/
theorem hopfRinow
    [T3Space M] [PreconnectedSpace M] [CompleteSpace E]
    [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (geodesics : CompleteMaximalGeodesicData (I := I) g)
    (minimizers : MinimizingGeodesicData (I := I) g) :
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
          canonicalRiemannianEDist (I := I) g (γ s) (γ t) =
            ENNReal.ofReal |s - t| * canonicalRiemannianEDist (I := I) g x y) ∧
        canonicalPathELength (I := I) g γ 0 1 =
          canonicalRiemannianEDist (I := I) g x y) := by
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

omit [FiniteDimensional ℝ E] in
/-- Finiteness is deliberately a component hypothesis: this probe exposes the
`[PreconnectedSpace M]` premise used by the canonical distance bridge. -/
theorem finite_distance_component_probe
    [PreconnectedSpace M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (x y : M) : canonicalRiemannianEDist (I := I) g x y < ⊤ :=
  canonicalRiemannianEDist_lt_top g x y

/-- Disconnected manifolds use the finite-distance branch explicitly: a pair
in different extended-distance components is not silently fed to the
minimizer producer. -/
theorem disconnected_component_probe
    [T3Space M] [CompleteSpace E] [BoundarylessManifold I M]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (data : MinimizingGeodesicData (I := I) g) (x y : M) :
    canonicalRiemannianEDist (I := I) g x y < ⊤ →
      Nonempty (MinimizingGeodesic (I := I) g x y) :=
  exists_minimizingGeodesic_of_finite g hcomplete data x y

omit [FiniteDimensional ℝ E] in
/-- Points separated by a clopen subset have no path between them, hence their
canonical Riemannian extended distance is infinite.  This is the genuine
disconnected-component negative regression used to guard the finite-distance
minimizer branch. -/
theorem canonicalRiemannianEDist_top_of_clopen
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    {s : Set M} (hs : IsClopen s) {x y : M}
    (hx : x ∈ s) (hy : y ∉ s) :
    canonicalRiemannianEDist (I := I) g x y = ⊤ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hno : IsEmpty (Path x y) := by
    constructor
    intro γ
    have hrange : IsPreconnected (Set.range (γ : unitInterval → M)) :=
      isPreconnected_range γ.continuous
    have hxrange : x ∈ Set.range (γ : unitInterval → M) := by
      refine ⟨0, ?_⟩
      exact γ.source
    have hsub : Set.range (γ : unitInterval → M) ⊆ s :=
      hrange.subset_isClopen hs ⟨x, hxrange, hx⟩
    have hyrange : y ∈ Set.range (γ : unitInterval → M) := by
      refine ⟨1, ?_⟩
      exact γ.target
    exact hy (hsub hyrange)
  letI : IsEmpty (Path x y) := hno
  change Manifold.riemannianEDist I x y = ⊤
  rw [Manifold.riemannianEDist]
  simp

/-!
The global theorem above still requires `[CompleteSpace E]`, while its metric
argument is the proposition `RiemannianMetricComplete g`.  This declaration is
kept as a small signature regression: adding metric completeness cannot make
the local ODE's model-space instance implicit. -/
theorem metric_completeness_probe
    {E0 H0 M0 : Type*} [NormedAddCommGroup E0] [NormedSpace ℝ E0]
    [TopologicalSpace H0] [TopologicalSpace M0]
    {I0 : ModelWithCorners ℝ E0 H0} [ChartedSpace H0 M0]
    [IsManifold I0 ∞ M0] [T3Space M0]
    (g : Bundle.ContMDiffRiemannianMetric I0 ∞ E0
      (TangentSpace I0 : M0 → Type _))
    (hcomplete : RiemannianMetricComplete (I := I0) g) : True := by
  /- This assertion is expected to fail: metric completeness is on `M0`, not
     the model vector space `E0` used by the local ODE. -/
  fail_if_success exact (inferInstance : CompleteSpace E0)
  have _ := hcomplete
  trivial

/-- Local geodesic existence remains available for a selected metric that is
not complete.  This regression is deliberately signature-level: it uses the
actual S18 local-IVP theorem and therefore catches an accidental addition of
metric completeness to the model-space ODE premise. -/
theorem local_ivp_of_incomplete_riemannianMetric
    [T3Space M] [CompleteSpace E]
    (g : Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (_hincomplete : ¬ RiemannianMetricComplete (I := I) g)
    (p : M) (v : TangentSpace I p) (hp : I.IsInteriorPoint p) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M,
      γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ)
        (chartVelocityAt (I := I) p v) 0 ∧
      HasChartGeodesicEquationOn (I := I) g p γ (Set.Ioo (-ε) ε) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, ContinuousAt γ t) :=
  exists_localChartGeodesicAt g p v hp

/-! ### Euclidean regression -/

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The standard Euclidean metric, viewed at the `C^∞` regularity used by the
project (Mathlib's bundled construction is `C^ω` and is downgraded explicitly).
-/
noncomputable def euclideanSmoothMetric :
    Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, F) ∞ F
      (TangentSpace 𝓘(ℝ, F) : F → Type _) := by
  let g := riemannianMetricVectorSpace F
  exact { g with contMDiff := g.contMDiff.of_le (by simp) }

/-- The selected zero-dimensional Euclidean Riemannian distance is complete.
The `EMetricSpace` installed in this proof is exactly the one used by
`RiemannianMetricComplete`; completeness here is the subsingleton regression,
not an assumption about the model-space ODE.  This records the degenerate
complete-manifold case of the paragraph preceding Morgan--Tian, Theorem 1.18
(`morganTian2007`), with do Carmo (`doCarmo1992`), Chapter 7, and Lee
(`lee2018`), Theorem 6.19, as cross-checks. -/
theorem euclidean_zero_dimensional_metric_complete :
    RiemannianMetricComplete (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) := by
  unfold RiemannianMetricComplete
  letI : Bundle.RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) :
        EuclideanSpace ℝ (Fin 0) → Type _) :=
    ⟨(euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))).toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0))
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) :
        EuclideanSpace ℝ (Fin 0) → Type _) :=
    continuousRiemannianBundle (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
  letI : EMetricSpace (EuclideanSpace ℝ (Fin 0)) :=
    EMetricSpace.ofRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) _
  infer_instance

/-- The zero-dimensional Euclidean model supplies the all-initial-data
maximal-geodesic producer.  Tangent fibers are definitionally the zero model
space only after the explicit local conversion below, so the dependent
`Subsingleton` instance is kept visible in this regression. -/
noncomputable def euclidean_zero_dimensional_complete_maximal_data :
    CompleteMaximalGeodesicData (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) := by
  letI : ∀ p : EuclideanSpace ℝ (Fin 0),
      Subsingleton (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) p) := fun p => by
    change Subsingleton (EuclideanSpace ℝ (Fin 0))
    infer_instance
  exact CompleteMaximalGeodesicData.of_subsingleton
    (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))

/-- The corresponding zero-dimensional compactness/minimizer producer uses
the diagonal constant segment and keeps the finite-distance premise explicit. -/
theorem euclidean_zero_dimensional_minimizing_data :
    MinimizingGeodesicData (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) :=
  MinimizingGeodesicData.of_subsingleton
    (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))

/-- In the zero-dimensional complete model, every supplied maximal lifetime is
all of `ℝ`; the two unboundedness conjuncts make the lifetime contract
explicit for later exponential-map consumers. -/
theorem euclidean_zero_dimensional_maximal_lifetime
    (p : EuclideanSpace ℝ (Fin 0))
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) p) :
    let G :=
      (euclidean_zero_dimensional_complete_maximal_data).solution p v
    G.lifetime = (Set.univ : Set ℝ) ∧
      LifetimeUnboundedAbove G.lifetime ∧ LifetimeUnboundedBelow G.lifetime := by
  dsimp
  have hlife := maximalGeodesic_lifetime_eq_univ_of_complete
    (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
    euclidean_zero_dimensional_metric_complete
    (euclidean_zero_dimensional_complete_maximal_data.solution p v)
    (euclidean_zero_dimensional_complete_maximal_data.continuation p v)
  exact ⟨hlife,
    maximalGeodesic_lifetime_unboundedAbove
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
      euclidean_zero_dimensional_metric_complete
      (euclidean_zero_dimensional_complete_maximal_data.solution p v)
      (euclidean_zero_dimensional_complete_maximal_data.continuation p v),
    maximalGeodesic_lifetime_unboundedBelow
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
      euclidean_zero_dimensional_metric_complete
      (euclidean_zero_dimensional_complete_maximal_data.solution p v)
      (euclidean_zero_dimensional_complete_maximal_data.continuation p v)⟩

/-- The maximal-domain producer and selected-metric completeness combine to
give the source-facing all-real-time geodesic witness in the one-point model. -/
theorem euclidean_zero_dimensional_isGeodesicallyComplete :
    IsGeodesicallyComplete (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) := by
  exact isGeodesicallyComplete_of_complete
    (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
    euclidean_zero_dimensional_metric_complete
    euclidean_zero_dimensional_complete_maximal_data

/-- Every zero-dimensional endpoint pair is fed through the explicit finite
distance branch and receives the constant minimizing segment. -/
theorem euclidean_zero_dimensional_minimizing_segment
    (x y : EuclideanSpace ℝ (Fin 0)) :
    Nonempty (MinimizingGeodesic
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
      (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) x y) := by
  exact exists_minimizingGeodesic_of_finite
    (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
    euclidean_zero_dimensional_metric_complete
    euclidean_zero_dimensional_minimizing_data x y (by
      have hxy : y = x := Subsingleton.elim _ _
      subst y
      simp)

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

/-- The Euclidean straight line realizes the selected canonical Riemannian
length as well as the ambient extended distance. -/
theorem euclideanStraightLine_canonical_length (x y : F) :
    canonicalPathELength (I := 𝓘(ℝ, F)) (euclideanSmoothMetric (F := F))
      (euclideanStraightLine x y) 0 1 =
    canonicalRiemannianEDist (I := 𝓘(ℝ, F)) (euclideanSmoothMetric (F := F)) x y := by
  change Manifold.pathELength 𝓘(ℝ, F) (ContinuousAffineMap.lineMap x y) 0 1 =
    Manifold.riemannianEDist 𝓘(ℝ, F) x y
  have h := euclideanStraightLine_length x y
  change Manifold.pathELength 𝓘(ℝ, F) (ContinuousAffineMap.lineMap x y) 0 1 =
    edist x y at h
  rw [h]
  exact IsRiemannianManifold.out x y

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

/-- The canonical Euclidean distance has the same constant-speed identity as
the ambient extended distance. -/
theorem euclideanStraightLine_canonical_speed (x y : F) (s t : ℝ) :
    canonicalRiemannianEDist (I := 𝓘(ℝ, F)) (euclideanSmoothMetric (F := F))
      ((euclideanStraightLine x y) s) ((euclideanStraightLine x y) t) =
      ENNReal.ofReal |s - t| *
        canonicalRiemannianEDist (I := 𝓘(ℝ, F)) (euclideanSmoothMetric (F := F)) x y := by
  have hbundle :
      (⟨(euclideanSmoothMetric (F := F)).toRiemannianMetric⟩ :
        Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, F))) =
      (inferInstance : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, F))) := by
    rfl
  unfold canonicalRiemannianEDist
  rw [hbundle]
  rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)) _ _]
  rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)) x y]
  simpa only [Real.enorm_eq_ofReal_abs] using euclideanStraightLine_speed x y s t

/-! The generic Euclidean witness specializes without additional manifold
assumptions to the one-dimensional and zero-dimensional model spaces. -/

/-- One-dimensional Euclidean straight lines retain the canonical length. -/
theorem euclideanStraightLine_one_dimensional (x y : ℝ) :
    (euclideanStraightLine x y).eLength = edist x y :=
  euclideanStraightLine_length x y

/-- The one-dimensional specialization also uses the selected canonical metric.
-/
theorem euclideanStraightLine_one_dimensional_canonical (x y : ℝ) :
    canonicalPathELength (I := 𝓘(ℝ, ℝ)) (euclideanSmoothMetric (F := ℝ))
      (euclideanStraightLine x y) 0 1 =
    canonicalRiemannianEDist (I := 𝓘(ℝ, ℝ)) (euclideanSmoothMetric (F := ℝ)) x y :=
  euclideanStraightLine_canonical_length x y

/-- The zero-dimensional Euclidean model has the same zero-length witness. -/
theorem euclideanStraightLine_zero_dimensional
    (x y : EuclideanSpace ℝ (Fin 0)) :
    (euclideanStraightLine x y).eLength = edist x y :=
  euclideanStraightLine_length x y

/-- The zero-dimensional specialization retains the selected canonical length
identity, including the degenerate zero-distance case. -/
theorem euclideanStraightLine_zero_dimensional_canonical
    (x y : EuclideanSpace ℝ (Fin 0)) :
    canonicalPathELength (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
        (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0)))
        (euclideanStraightLine x y) 0 1 =
      canonicalRiemannianEDist (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)))
        (euclideanSmoothMetric (F := EuclideanSpace ℝ (Fin 0))) x y :=
  euclideanStraightLine_canonical_length x y

end Euclidean
