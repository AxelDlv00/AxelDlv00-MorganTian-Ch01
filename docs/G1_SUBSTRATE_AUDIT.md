# G1 Chapter 1 substrate and API audit

Inspection date: 2026-08-18 (Asia/Shanghai).

This is the repository-owned evidence artifact for roadmap node G1.  It
prepares, but does not make, the human substrate decision at G2.  In
particular, it does not accept a dependency, add a package, or change any
canonical representation in `ROADMAP.md`.

## Evidence boundary

The audit fixes four different kinds of evidence and does not substitute one
for another:

| Evidence | Immutable revision inspected | What it can establish |
| --- | --- | --- |
| Project baseline | `aa150877959ca78c1b1f382d0257e4c5e9c7753a` | Repository declarations and the accepted route before G1 |
| Mathlib source | `520045ab14e26149ee970e2e617ca04b09bde5d6` | Names, signatures, instances, imports, and implementation gaps at the pin |
| Candidate source | `palimpsest/Hopf-Rinow-DoCarmo` commit `60c3e1f6493646d667a0bb645f99110a34d26e00` | Prior-art declarations and packaging at that exact commit only |
| Primary publication | Morgan--Tian arXiv v2 (`math/0607607`, revised 2007-03-21), `prelim.tex` and retained PDF | Chapter 1 mathematics, statement numbering, and printed pp. 35--50 |

The project uses Lean `v4.32.1`.  Both inspected Lake manifests pin the same
Mathlib commit.  Candidate governance PR #40 has head
`6460d507cb578f408c8081e2b1398345ac3a2c43` and was still open at inspection;
none of its roadmap or governance claims are attributed to the audited main
commit.

The retained PDF recheck found two numbering errors in the bootstrap
inventory.  The Christoffel formula labelled `Gamma` is equation (1.1), and
the Gaussian metric expansion labelled `metricexp` is equation (1.5).  The
G1 roadmap update corrects both.  The mathematics and intended ownership are
unchanged.

## Pinned Mathlib surface

All paths in this section are relative to the pinned Mathlib `Mathlib/`
directory.  Names are shown fully qualified where they live in a namespace.
The displayed signatures are transcribed from the exact source; the context
tables state the implicit typeclass parameters that surround them.

### Direct public import edges

| Module | Direct public imports |
| --- | --- |
| `Topology/VectorBundle/Riemannian.lean` | `Analysis.InnerProductSpace.LinearMap`; `Topology.VectorBundle.Constructions`; `Topology.VectorBundle.Hom` |
| `Geometry/Manifold/VectorBundle/Riemannian.lean` | `Geometry.Manifold.VectorBundle.Hom`; `Geometry.Manifold.VectorBundle.MDifferentiable`; `Topology.VectorBundle.Riemannian` |
| `Geometry/Manifold/Riemannian/PathELength.lean` | `Analysis.Calculus.AddTorsor.AffineMap`; `Analysis.SpecialFunctions.SmoothTransition`; `Geometry.Manifold.ContMDiff.NormedSpace`; `Geometry.Manifold.Instances.Icc`; `MeasureTheory.Constructions.UnitInterval`; `MeasureTheory.Function.JacobianOneDim` |
| `Geometry/Manifold/Riemannian/Basic.lean` | `Geometry.Manifold.MFDeriv.Atlas`; `Geometry.Manifold.Riemannian.PathELength`; `Geometry.Manifold.VectorBundle.Riemannian`; `Geometry.Manifold.VectorBundle.Tangent`; `MeasureTheory.Integral.IntervalIntegral.ContDiff` |
| `Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean` | `Geometry.Manifold.VectorBundle.Hom`; `Geometry.Manifold.VectorBundle.ContMDiffSection`; `Geometry.Manifold.VectorBundle.Tangent`; `Geometry.Manifold.VectorBundle.Tensoriality` |
| `Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean` | `Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`; `Geometry.Manifold.VectorBundle.Riemannian`; `Geometry.Manifold.MFDeriv.NormedSpace` |
| `Geometry/Manifold/VectorBundle/CovariantDerivative/Torsion.lean` | `Topology.FiberBundle.Basic`; `Geometry.Manifold.VectorBundle.CovariantDerivative.Basic`; `Geometry.Manifold.VectorField.LieBracket` |

There are exactly six files under the pinned
`Geometry/Manifold/{Riemannian,VectorBundle}` subtrees whose names contain
`Riemannian` or `CovariantDerivative`: the two Riemannian manifold files, the
Riemannian vector-bundle file, and the three covariant-derivative files above.
Consequently, importing `Riemannian.Basic` does not import metric compatibility
or torsion; F1 would need those two modules explicitly unless a smaller
project-owned aggregator is selected.

### Metric data and instances

For `Bundle.RiemannianMetric`, `Bundle.RiemannianBundle`, and the continuous
variant, the ambient context is

```lean
{B : Type*} [TopologicalSpace B]
{F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
{E : B → Type*} [TopologicalSpace (TotalSpace F E)]
[∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)]
[∀ b, Module ℝ (E b)] [∀ b, IsTopologicalAddGroup (E b)]
[∀ b, ContinuousConstSMul ℝ (E b)]
[FiberBundle F E] [VectorBundle ℝ F E]
```

The public data class is:

```lean
namespace Bundle

structure RiemannianMetric (E : B → Type*) where
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  continuousAt (b : B) : ContinuousAt (fun v : E b => inner b v v) 0
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}

class RiemannianBundle (E : B → Type*) where
  g : RiemannianMetric E
```

`RiemannianBundle` is construction data, not the general theorem assumption.
Its two derived instances have these exact result types:

```lean
noncomputable scoped instance (priority := 80)
    [h : RiemannianBundle E] [∀ b, IsTopologicalAddGroup (E b)]
    [∀ b, ContinuousConstSMul ℝ (E b)] (b : B) :
    NormedAddCommGroup (E b)

noncomputable scoped instance (priority := 80)
    [h : RiemannianBundle E] [∀ b, IsTopologicalAddGroup (E b)]
    [∀ b, ContinuousConstSMul ℝ (E b)] (b : B) :
    InnerProductSpace ℝ (E b)
```

Both are scoped to `Bundle`; consumers must use `open scoped Bundle`.  This is
the mechanism that avoids a second, non-definitionally-equal norm on tangent
fibres.

For the smooth metric, add

```lean
{EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
{HB : Type*} [TopologicalSpace HB]
{IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
[ChartedSpace HB B]
```

to the preceding bundle context.  The exact data structure is:

```lean
namespace Bundle

structure ContMDiffRiemannianMetric
    (IB : ModelWithCorners ℝ EB HB) (n : ℕ∞ω) (F : Type*)
    (E : B → Type*) where
  inner (b : B) : E b →L[ℝ] E b →L[ℝ] ℝ
  symm (b : B) (v w : E b) : inner b v w = inner b w v
  pos (b : B) (v : E b) (hv : v ≠ 0) : 0 < inner b v v
  isVonNBounded (b : B) : IsVonNBounded ℝ {v : E b | inner b v v < 1}
  contMDiff : ContMDiff IB
    (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
    (fun b => TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) b (inner b))

def ContMDiffRiemannianMetric.toRiemannianMetric
    (g : ContMDiffRiemannianMetric IB n F E) : RiemannianMetric E
```

Given `g`, installing

```lean
letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
```

activates the pinned instance

```lean
instance (g : ContMDiffRiemannianMetric IB n F E) :
    letI : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle IB n F E
```

whose witness is definitionally `g.inner`.  The smooth metric also has a
`toContinuousRiemannianMetric` conversion, but the `Riemannian.Basic` module
documentation correctly warns that a general
`IsContMDiffRiemannianBundle IB n F E` assumption does not let typeclass
inference guess `n` to synthesize `IsContinuousRiemannianBundle F E`.
The G2 bridge must therefore install the continuous fact explicitly wherever
the distance constructor needs it.

### Path length, distance, and topology

The two core definitions are in namespace `Manifold`.  Their shared context is

```lean
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
{H : Type*} [TopologicalSpace H]
{I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[∀ x : M, ENorm (TangentSpace I x)]
```

with no Riemannian inner product required by either definition:

```lean
namespace Manifold

variable (I) in
irreducible_def pathELength (γ : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc a b, ‖mfderiv% γ t 1‖ₑ

variable (I) in
noncomputable irreducible_def riemannianEDist (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : CMDiff 1 γ), ∫⁻ t, ‖mfderiv% γ t 1‖ₑ
```

`pathELength` integrates against the one-dimensional interval measure.  That
measure is not a Riemannian volume measure on `M`.

For an already installed tangent `RiemannianBundle`, a `C^1` manifold, and
`IsContinuousRiemannianBundle`, `Riemannian.Basic` proves the path distance has
the original topology.  Its construction surface is:

```lean
@[reducible] def PseudoEMetricSpace.ofRiemannianMetric
    [RegularSpace M] : PseudoEMetricSpace M

@[reducible] def EMetricSpace.ofRiemannianMetric
    [T3Space M] : EMetricSpace M
```

The compatibility predicate for an existing extended metric has the context

```lean
[PseudoEMetricSpace M]
[RiemannianBundle (fun x : M => TangentSpace I x)]
```

and exact signature:

```lean
class IsRiemannianManifold
    (I : ModelWithCorners ℝ E H) (M : Type*) : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y
```

The constructed extended metric is registered by this exact anonymous
instance shape:

```lean
instance [RegularSpace M] :
    letI : PseudoEMetricSpace M :=
      PseudoEMetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M
```

Thus `IsRiemannianManifold` records distance equality only.  It does not carry
smoothness, a measure, a connection, completeness, connectedness, or finite
dimensionality.  `EMetricSpace.ofRiemannianMetric` requires `T3Space M`; the
finite-valued `MetricSpace` conversion additionally needs a proof that
`riemannianEDist I x y != top`, which the candidate derives from
`PreconnectedSpace M`.

### Covariant derivative, compatibility, and torsion

The bundled connection has ambient context

```lean
{𝕜 : Type*} [NontriviallyNormedField 𝕜]
{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
{H : Type*} [TopologicalSpace H]
{I : ModelWithCorners 𝕜 E H}
{M : Type*} [TopologicalSpace M] [ChartedSpace H M]
{F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
{V : M → Type*} [TopologicalSpace (TotalSpace F V)]
[∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
[∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
[∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V]
```

and exact public shape:

```lean
structure CovariantDerivative
    (I : ModelWithCorners 𝕜 E H) (F : Type*) (V : M → Type*) where
  toFun : (Π x : M, V x) →
    (Π x : M, TangentSpace I x →L[𝕜] V x)
  isCovariantDerivativeOnUniv :
    IsCovariantDerivativeOn F toFun Set.univ
```

It coerces to `toFun`.  The argument order is intentionally
`cov sigma x (X x)` for the paper expression `nabla_X sigma`.
`IsCovariantDerivativeOn` requires additivity and the Leibniz rule only for
sections differentiable at the point.  `CovariantDerivative` itself has no
regularity field; the separate class is

```lean
class ContMDiffCovariantDerivative
    [IsManifold I 1 M] [VectorBundle 𝕜 F V]
    (cov : CovariantDerivative I F V) (k : ℕ∞ω) where
  contMDiff : ContMDiffCovariantDerivativeOn F k cov.toFun Set.univ
```

For the real, finite-dimensional Riemannian bundle context

```lean
[VectorBundle ℝ F V]
[IsContMDiffRiemannianBundle I 1 F V]
[ContMDiffVectorBundle 1 F V I]
[FiniteDimensional ℝ F]
```

metric compatibility is exactly:

```lean
namespace CovariantDerivative

def IsMetricCompatible (cov : CovariantDerivative I F V) : Prop :=
  derivMetricTensor cov = 0
```

For torsion, specialize `V` to the tangent bundle and assume

```lean
[CompleteSpace 𝕜] [CompleteSpace E]
[FiniteDimensional 𝕜 E] [IsManifold I 2 M]
```

The exact bundled declarations are:

```lean
namespace CovariantDerivative

def torsion
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x : M) :
    TangentSpace I x →L[𝕜]
      TangentSpace I x →L[𝕜] TangentSpace I x

lemma torsion_eq_zero_iff
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) :
    cov.torsion = 0 ↔
      ∀ {X Y x}, MDiffAt (T% X) x → MDiffAt (T% Y) x →
        cov Y x (X x) - cov X x (Y x) =
          VectorField.mlieBracket I X Y x
```

The pinned tree contains no constructor or uniqueness theorem selecting a
connection that is both `IsMetricCompatible` and torsion-free.  In particular,
the fundamental theorem of Levi--Civita remains a producer gap, not an
instance search problem.

### Measure and absent producers

A case-insensitive search of the full pinned `Mathlib/` tree for a Riemannian
manifold measure or volume declaration returned no result.  The only nearby
measure API used by these modules is one-dimensional integration for path
length and ordinary Haar volume on inner-product spaces.  There is no checked
declaration tying a measure on `M` to the tangent metric, no polar Jacobian,
and no equality between metric-ball measure and Riemannian volume.  A2 must
produce those facts before C3 can state Bishop--Gromov.

Searches of the full pinned tree also found no differential-geometric producer
for Levi--Civita, Riemann curvature, sectional/Ricci/scalar curvature,
geodesics, a Riemannian exponential map, Jacobi fields, conjugate points, the
index form, cut locus, injectivity radius, or Bishop--Gromov.  Generic ODE,
manifold inverse-function, tensor, metric, measure, and integration APIs are
available, but they are infrastructure rather than any Chapter 1 theorem.
The complete claim-by-claim ownership is recorded below.

## Candidate dependency at `60c3e1f`

### Packaging, provenance, and reproducibility

| Check | Exact finding | Consequence for G2 |
| --- | --- | --- |
| Provenance | The history begins at Palimpsest commit `3ac7db9178d351984d95d6ceece2c2087e827053`; all later feature commits name `Palimpsest Contributor`, and merge commits name `Maintainer Adviser`.  README citations name do Carmo and Lee as mathematical sources. | Provenance is traceable to this forge, but mathematical citations do not grant a software license. |
| License | The Git tree has no `LICENSE`, `LICENSE.md`, `COPYING`, or `NOTICE`; a full tracked-tree scan found no copyright, SPDX, release, or license notice. | The candidate cannot be added or extracted from on the evidence available.  This blocks both Git-dependency and scoped-extraction routes until a human supplies reviewed licensing/provenance. |
| Lean/Mathlib | `lean-toolchain` is `leanprover/lean4:v4.32.1`; `lakefile.lean` and the manifest pin Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. | Syntactically compatible with this project at the audited pins. |
| Dependencies | Lake has one direct dependency, the Mathlib Git pin.  The manifest contains Mathlib's eight inherited Git packages and no `type: path` entry. | No sibling/path dependency or extra direct package would be introduced. |
| Standalone workflow | The repository owns `Lean CI` / `lake-build`, disables credential persistence, supports an absent Actions cache, and runs `lake exe cache get` then `lake build`. | The configuration is cold-run capable.  G1 did not run a forbidden local full build; an exact future dependency commit still needs its own terminal CI status. |
| Source/import size | 13 tracked Lean files, 4,743 lines; `HopfRinow.lean` directly imports all 12 subordinate modules. | Importing the umbrella takes the whole candidate.  A selected dependency should import narrow modules and document the resulting project import closure. |
| Holes and axioms | Source search found zero `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` commands. | No source-level mathematical hole or project axiom was found. |
| Resource exceptions | Source search found zero `set_option`; Lake sets only `autoImplicit := false` and `pp.unicode.fun := true`. | No heartbeat, recursion-depth, or transparency debt at this commit. |
| Proof axioms | The merged PR #38 review reports only `propext`, `Classical.choice`, and `Quot.sound` for its selected transfer declarations.  No exhaustive whole-library `#print axioms` report is retained at the merge commit. | G2 must rerun `#print axioms` for every declaration it proposes to export; the source scan is not a proof-term axiom audit. |
| Governance | Candidate PR #40 remained open at inspection and is not in `60c3e1f`. | The candidate has no accepted repository-owned roadmap at the audited commit. |

The direct project import graph is:

```text
Metric.ProperSpace
  -> Riemannian.Completeness <- Riemannian.Distance

Riemannian.Distance
  -> Riemannian.Geodesic
       -> Geodesic.Spray
            -> Geodesic.ChartChange -> Geodesic.EquationTransfer
            -> Geodesic.Existence -> Geodesic.Readback
  -> Riemannian.PathLength

Riemannian.Geodesic + Riemannian.PathLength
  -> Riemannian.Minimizing

Riemannian.Completeness + Riemannian.Minimizing
  -> Riemannian.HopfRinow
```

`Geodesic.ChartChange` is the largest file (1,196 lines), followed by
`Geodesic.Spray` (758) and `Geodesic` (537).  The distance-only route is much
smaller than the umbrella, while the current local-IVP route necessarily
brings in the coordinate spray and chart-change substrate.

### Relevant public signatures

Unless a declaration says otherwise, the candidate contexts below include

```lean
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
{H : Type*} [TopologicalSpace H]
{I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [ChartedSpace H M]
[IsManifold I ∞ M]
```

The coordinate geodesic and spray declarations additionally require
`[FiniteDimensional ℝ E] [I.Boundaryless]`; the finite-distance, minimizing,
and Hopf--Rinow declarations require `[T3Space M] [PreconnectedSpace M]`.

The candidate defines its explicit metric as a transparent alias, not new
data:

```lean
namespace HopfRinow

abbrev RiemannianMetric
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E
    (TangentSpace I : M → Type _)
```

Its distance bridge is therefore definitionally based on the pinned metric:

```lean
namespace HopfRinow.RiemannianMetric

def IsRiemannianDist (g : RiemannianMetric I M)
    [PseudoEMetricSpace M] : Prop :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  IsRiemannianManifold I M

@[reducible] noncomputable def toMetricSpace
    (g : RiemannianMetric I M)
    [T3Space M] [PreconnectedSpace M] : MetricSpace M

theorem toMetricSpace_edist (g : RiemannianMetric I M)
    [T3Space M] [PreconnectedSpace M] (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    letI : MetricSpace M := g.toMetricSpace
    edist x y = Manifold.riemannianEDist I x y

theorem toMetricSpace_topology (g : RiemannianMetric I M)
    [T3Space M] [PreconnectedSpace M] :
    g.toMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace M)
```

The intrinsic-looking geodesic predicate is a coordinate equation computed
directly from `g`; it is not expressed through Mathlib's bundled connection:

```lean
namespace HopfRinow.RiemannianMetric

def HasGeodesicEquationAt [I.Boundaryless]
    (g : RiemannianMetric I M) (gamma : ℝ → M) (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) gamma t) v t ∧
    (∀ᶠ s in nhds t, HasDerivAt
      (chartLocalCurve (I := I) gamma t)
      (deriv (chartLocalCurve (I := I) gamma t) s) s) ∧
    HasDerivAt
      (fun s => deriv (chartLocalCurve (I := I) gamma t) s) a t ∧
    a + chartChristoffelContraction (I := I) g (gamma t) v v
      (extChartAt I (gamma t) (gamma t)) = 0

def IsGeodesicOn [I.Boundaryless]
    (g : RiemannianMetric I M) (gamma : ℝ → M) (s : Set ℝ) : Prop :=
  ContinuousOn gamma s ∧
    ∀ t ∈ s, HasGeodesicEquationAt (I := I) g gamma t

def IsGeodesic [I.Boundaryless]
    (g : RiemannianMetric I M) (gamma : ℝ → M) : Prop :=
  Continuous gamma ∧
    ∀ t, HasGeodesicEquationAt (I := I) g gamma t
```

The current existence theorem is pointwise at the initial time:

```lean
theorem exists_geodesicEquationAt_initial
    [I.Boundaryless] [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (t0 : ℝ) :
    ∃ gamma : ℝ → M,
      gamma t0 = p ∧
      HasDerivAt (fun s => extChartAt I p (gamma s)) v t0 ∧
      HasGeodesicEquationAt (I := I) g gamma t0 ∧
      IsSprayGeodesicAt (I := I) g gamma t0
```

It does not assert `IsGeodesicOn` on any interval, a maximal interval, smooth
dependence on initial data, or a maximal exponential map.  Local integral
curve uniqueness is available only as eventual equality for two fixed-chart
tangent lifts with the same initial state.

The global and minimizing surfaces are conditional records:

```lean
structure CandidateGeodesicPredicate (g : RiemannianMetric I M) where
  isGeodesic : (ℝ → M) → Prop

structure GlobalGeodesicFor (g : RiemannianMetric I M)
    (G : CandidateGeodesicPredicate g)
    (p : M) (v : TangentSpace I p) where
  toFun : ℝ → M
  at_zero : toFun 0 = p
  deriv_at_zero :
    HasDerivAt (fun t => extChartAt I p (toFun t)) v 0
  continuous : Continuous toFun
  isGeodesic : G.isGeodesic toFun

def IsGeodesicallyCompleteFor (g : RiemannianMetric I M)
    (G : CandidateGeodesicPredicate g) : Prop :=
  ∀ p : M, ∀ v : TangentSpace I p,
    Nonempty (GlobalGeodesicFor g G p v)

def IsDistanceMinimizingOnUnitInterval
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric I M) (gamma : ℝ → M) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    dist (gamma s) (gamma t) =
      |s - t| * dist (gamma 0) (gamma 1)

structure MinimizingGeodesicFor
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric I M)
    (G : CandidateGeodesicPredicate g) (p q : M) where
  velocity : TangentSpace I p
  toGlobalGeodesic : GlobalGeodesicFor g G p velocity
  endpoint : toGlobalGeodesic 1 = q
  minimizes : g.IsDistanceMinimizingOnUnitInterval toGlobalGeodesic
```

Finally, every candidate Hopf--Rinow implication needs a value of:

```lean
structure HopfRinowBridge (g : RiemannianMetric I M)
    (G : CandidateGeodesicPredicate g) : Prop where
  properSpace_of_isGeodesicallyCompleteAtFor :
    ∀ p : M, IsGeodesicallyCompleteAtFor g G p →
      letI : MetricSpace M := g.toMetricSpace
      ProperSpace M
  isGeodesicallyCompleteFor_of_isMetricComplete :
    g.IsMetricComplete → g.IsGeodesicallyCompleteFor G
  hasMinimizingGeodesicsFromFor_of_isGeodesicallyCompleteAtFor :
    ∀ p : M, IsGeodesicallyCompleteAtFor g G p →
      g.HasMinimizingGeodesicsFromFor G p
```

These fields are assumptions to be constructed.  No declaration at the
audited commit produces `HopfRinowBridge`.  The facade therefore cannot
discharge Morgan--Tian Theorem 1.18.

### Coverage and collisions

| Roadmap consumer | Candidate evidence at the audited commit | Missing producer |
| --- | --- | --- |
| F1 connection/curvature | Chart Gram matrices, Christoffel contraction, and its chart-change law | No `CovariantDerivative`, Levi--Civita existence/uniqueness, metric-compatibility/torsion bridge, curvature, Hessian, or Laplacian |
| F2 geodesic IVP | Intrinsic coordinate predicate, chart-fixed spray, local integral lift, pointwise readback, affine reparametrization | No interval-valued local solution with `IsGeodesicOn`, maximal interval/gluing, smooth flow, exponential map, or unconditional Hopf--Rinow/minimizer theorem |
| J1 Jacobi/differential of exp | None | All intrinsic Jacobi, variation, conjugacy, linearized-flow, and `d exp` producers |
| Metric/distance | Transparent Mathlib metric alias; finite metric on `T3Space` and `PreconnectedSpace`; exact edistance/topology lemmas | No Riemannian measure/volume bridge |

There is no fully-qualified collision with Mathlib's
`Bundle.RiemannianMetric`, but `HopfRinow.RiemannianMetric` is both a type alias
and a namespace and is easily confused with the Mathlib name when namespaces
are opened.  The candidate also exports generic names `IsGeodesic`,
`IsGeodesicOn`, `IsMetricComplete`, and `HasGeodesicEquationAt` in that
namespace.  The project roadmap already reserves similar unqualified public
families.  G2 must either adopt the candidate names deliberately or wrap only
temporarily with a named deletion trigger; both vocabularies must not survive
as unrelated public APIs.

## Source-claim disposition

This table closes every row of the accepted source inventory.  Statement
numbers and pages were rechecked against the retained arXiv v2 PDF; raw labels
were rechecked in `prelim.tex`.  "Gap" means no declaration with the source
semantics exists in this repository, pinned Mathlib, or the audited candidate.
Candidate-relative or coordinate-local prior art is named but never counted as
a completed project declaration.

The two partially implemented A1 rows use the following exact project types:

```lean
namespace MorganTianLib.Ch01.Comparison

noncomputable def sn (k r : ℝ) : ℝ
noncomputable def ct (k r : ℝ) : ℝ
noncomputable def radialCoeff (k r : ℝ) : ℝ

theorem sn_ode (k : ℝ) (hk : 0 ≤ k) :
    (∀ r, deriv (deriv (sn k)) r = k * sn k r) ∧
      sn k 0 = 0 ∧ deriv (sn k) 0 = 1

theorem radialCoeff_sub_inv_mem_Icc
    (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    radialCoeff k r - 1 / r ∈ Set.Icc 0 (k * r / 2)

theorem tendsto_radialCoeff_sub_inv (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun r => radialCoeff k r - 1 / r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

theorem scalar_riccati_comparison
    {k r₀ : ℝ} (hk : 0 ≤ k) {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Set.Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Set.Ioo (0 : ℝ) r₀, φ' r + φ r ^ 2 ≤ k)
    (h0 : Tendsto (fun r => φ r - 1 / r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    ∀ r ∈ Set.Ioo (0 : ℝ) r₀, φ r ≤ radialCoeff k r

noncomputable def snPos (K r : ℝ) : ℝ
noncomputable def logDerivPos (K r : ℝ) : ℝ
noncomputable def firstPole (K : ℝ) : WithTop ℝ
def BeforeFirstPole (K r : ℝ) : Prop

theorem firstPole_eq (K : ℝ) (hK : 0 < K) :
    firstPole K = (Real.pi / Real.sqrt K : ℝ)

theorem snPos_firstPole (K : ℝ) (hK : 0 < K) :
    snPos K (Real.pi / Real.sqrt K) = 0

theorem snPos_ode (K : ℝ) (hK : 0 ≤ K) :
    (∀ r, deriv (deriv (snPos K)) r = -(K * snPos K r)) ∧
      snPos K 0 = 0 ∧ deriv (snPos K) 0 = 1

theorem snPos_pos (K r : ℝ) (hK : 0 ≤ K)
    (hpole : BeforeFirstPole K r) : 0 < snPos K r

theorem logDerivPos_eq (K r : ℝ) (hK : 0 < K) :
    logDerivPos K r = csPos K r / snPos K r
```

| ID | Morgan--Tian anchor | Existing exact declaration or explicit gap | Owner |
| --- | --- | --- | --- |
| S01 | Definition 1.1 and metric-ball paragraph, p. 35 | Mathlib substrate: `Bundle.ContMDiffRiemannianMetric`, `Bundle.RiemannianBundle`, `Manifold.riemannianEDist`, and `IsRiemannianManifold` with signatures above.  Gap: manifold metric existence, the chosen explicit/typeclass bridge, finite distance, and metric-ball coherence for the public Chapter 1 representation. | G2 |
| S02 | Theorem 1.2, pp. 35--36 | Gap: no Levi--Civita constructor or uniqueness theorem.  Mathlib only has `CovariantDerivative.IsMetricCompatible` and `CovariantDerivative.torsion = 0` as predicates. | G2, then F1 |
| S03 | Christoffel formula (1.1), p. 36, label `Gamma` | Gap in the project.  Candidate `chartChristoffel` and `chartChristoffelContraction` are coordinate prior art without a bundled-connection equivalence. | F1 |
| S04 | Hessian definition (1.2) and Lemma 1.3, pp. 36--37, labels `Hessian`/`Hessformula` | Gap: Hessian, symmetry, tensoriality, gradient identity, and coordinate formula. | F1 |
| S05 | Function Laplacian definition and (1.4), p. 37, label `laplacformula` | Gap: trace-of-Hessian Laplacian and sign convention bridge. | F1 |
| S06 | Definition 1.4, pp. 37--38 | Gap: `(1,3)` curvature, `(0,4)` lowering/order, and coordinate formula. | F1 |
| S07 | Claim 1.5, p. 38, label `Bianchi` | Gap: curvature symmetries and first/second Bianchi identities. | F1 |
| S08 | Definitions 1.6--1.7, pp. 38--39 | Gap: sectional curvature, constant-curvature characterization, and curvature operator. | F1 |
| S09 | Definition 1.8, p. 39 | Gap: Ricci tensor and scalar curvature. | F1 |
| S10 | Naturality paragraph after Definition 1.8, p. 39 | Gap: pullback naturality for Riemann, Ricci, and scalar curvature. | F1 |
| S11 | Lemma 1.9, p. 39, label `divRic` | Gap: divergence and contracted Bianchi identity `dR = 2 div Ric`. | F1 |
| S12 | Unnumbered tensor definitions before Lemma 1.10, pp. 39--40 | Gap: second covariant derivative and connection Laplacian for tensors of arbitrary rank. | F1 |
| S13 | Lemma 1.10, p. 40, label `lapformula` | Gap: the one-form Bochner/Laplacian identity.  Morgan--Tian is primary; its Gallot Proposition 4.36 cross-reference remains unverified because that edition is absent. | F1 |
| S14 | Theorem 1.11, p. 40 | Gap: space-form classification/export with the roadmap's local `2 <= n` correction. | F3 |
| S15 | Definition 1.12 and Example 1.13, p. 40 | Gap: Einstein predicate and the dimension 2/3 constant-curvature consequence. | F3 |
| S16 | Definition 1.14, p. 40, label `conedefn` | Gap: open-cone metric. | F3 |
| S17 | Proposition 1.15 and Corollary 1.16, pp. 40--41, label `conecurv` | Gap: cone curvature block decomposition and eigenvalues. | F3 |
| S18 | Definition 1.17 and coordinate IVP paragraph, p. 41 | Gap: unconditional interval IVP, uniqueness, and smooth dependence.  Candidate `HasGeodesicEquationAt`, `IsGeodesicOn`, and `exists_geodesicEquationAt_initial` have the exact signatures above, but the existence result proves the equation only at `t0`. | F2 |
| S19 | Theorem 1.18, pp. 41--42 | Gap: metric completeness implies all intrinsic geodesics extend for all time.  Candidate theorems require an unproduced `HopfRinowBridge`. | F2 after G2 |
| S20 | Length, energy, first variation, and criticality, pp. 41--43 | `Manifold.pathELength` exists.  Candidate path-length/minimizing lemmas are conditional prior art.  Gap: energy, Cauchy--Schwarz equality at source scope, first variation, geodesic criticality, and unconditional minimizer consequences. | F2 |
| S21 | Geodesic variations and Jacobi equation, pp. 43--44 | Gap: variation-to-Jacobi bridge, intrinsic Jacobi equation, and initial-data uniqueness. | J1 after F1/F2 |
| S22 | Definition 1.19, p. 44 | Gap: intrinsic conjugate-point predicate. | J1 |
| S23 | Second-variation formulas and boundary term, pp. 43--44 | Gap: arbitrary-family second variation, endpoint boundary terms, intrinsic index form, and symmetry. | V1 |
| S24 | Proposition 1.20, pp. 44--45, label `jacmin` | Gap: unique minimizing subsegments and absence of interior conjugate points. | V1 |
| S25 | Claim 1.21, p. 44 | Gap: index-form null space equals endpoint-vanishing Jacobi fields. | V1 |
| S26 | Definition 1.22, p. 45 | Gap: exponential map on the maximal star-shaped domain and the complete-domain equality. | F2 |
| S27 | Differential-of-exp paragraph and Corollary 1.23, pp. 45--46, label `star` | Gap: `d exp` as Jacobi endpoint evaluation and the minimizer local-diffeomorphism theorem. | J1/F2 |
| S28 | Definition 1.24 and Proposition 1.25, p. 46 | Gap: regular minimizing domain, closed/null cut locus, and exponential diffeomorphism onto its complement. | N1, with A2 for nullity |
| S29 | Definition 1.26 and following alternatives, p. 46 | Gap: extended injectivity radius, frontier/cut-distance equalities, and broken-geodesic/conjugate alternative. | N1 |
| S30 | Gaussian metric expansion (1.5), p. 46, label `metricexp` | Gap: term-by-term expansion through `O(r^5)` with the Sakai sign conversion. | F3/N1 |
| S31 | Gauss lemma, polar metric, and volume element, p. 47 | Gap: Gauss lemma, polar metric, polar Jacobian, and Riemannian volume identity. | N1/A2 |
| S32 | Lemma 1.27, p. 47 | Gap: Gaussian-coordinate Laplacian formula. | F1/N1 |
| S33 | Distance-Laplacian expansion before Exercise 1.28, p. 48 | Gap: `Delta r = (n-1)/r - (r/3) Ric(v,v) + O(r^2)`. | F3/N1 |
| S34 | Exercise 1.28 and Remark 1.29, p. 48, label `calabi` | Gap: global distributional/test-function inequality and integration-by-parts form, with the roadmap's local `2 <= n` correction. | C2 |
| S35 | Definition 1.30, pp. 48--49 | Project declarations: `sn`, `cs`, `ct`, `radialCoeff : ℝ → ℝ → ℝ`; `sn_ode (k) (hk : 0 <= k)` proves `sn'' = k*sn`, `sn 0 = 0`, `sn' 0 = 1`; `radialCoeff_sub_inv_mem_Icc` and `tendsto_radialCoeff_sub_inv` give origin control; `scalar_riccati_comparison` and `_Ioi` give the scalar comparison.  Remaining A1 gaps are vector/operator consumers. | A1, partial |
| S36 | Unnumbered positive-upper-curvature analogue before Lemma 1.32, p. 49 | Project declarations: `snPos`, `csPos`, `logDerivPos : ℝ → ℝ → ℝ`; `firstPole : ℝ → WithTop ℝ`; `BeforeFirstPole : ℝ → ℝ → Prop`; `snPos_ode`, `snPos_pos`, and `snPos_firstPole`.  Gap: the two normalized limits and Sturm/vector/operator consumers. | A1, partial |
| S37 | Theorem 1.31, p. 49, label `SCC` | Gap: intrinsic lower sectional-curvature comparison for Hessian/angular metric. | C1 |
| S38 | Unnumbered upper sectional-curvature analogue before Lemma 1.32, p. 49 | Gap: lower shape/angular-metric/normalized-Jacobian estimates on the regular first-pole interval. | C1 |
| S39 | Lemma 1.32, p. 49, label `localdiffeo` | Gap: curvature-norm local-diffeomorphism theorem with unbounded `K = 0` radius. | C1 |
| S40 | Theorem 1.33, p. 49, label `riccurvcomp` | Gap: radial Jacobian and trace comparison under the Ricci lower bound. | C2 |
| S41 | Theorem 1.34, p. 49, label `BishopGromov` | Gap: metric-ball/Riemannian-volume ratio monotonicity and limit one. | C3 |
| S42 | Proposition 1.35, p. 50, label `injvol` | Gap: lower volume from injectivity at the stated scale and dependence. | L1 |
| S43 | Theorem 1.36, p. 50, label `volinj` | Gap: injectivity lower bound from volume at the stated scale and dependence. | L1 |

For S35 and S36, the full exact theorem signatures are in
`MorganTianLib/Ch01/Comparison/Model.lean`; the table lists only declarations
whose mathematical role is part of the source row.  No candidate declaration
is imported or re-exported by the project.

## G2 decision matrix

The matrix records feasibility at the inspected revisions.  It deliberately
does not rank a winner, because licensing, ownership, and public API choices
require the human gate.

| Criterion | Reviewed Git dependency | Scoped extraction | Mathlib-native construction | Wait for upstream |
| --- | --- | --- | --- | --- |
| Exact input | Candidate at a newly reviewed immutable commit descended from `60c3e1f` | Minimum selected candidate modules, with retained commit/file provenance | Mathlib `520045ab` modules audited above plus project code | A future concrete Mathlib or accepted shared commit |
| Legal/provenance | **Blocked now:** no software license at `60c3e1f` | **Blocked now:** absence of a license also forbids copying/adaptation | Mathlib is Apache-2.0; project ownership is direct | Unknown until a concrete upstream revision exists |
| F1 value | Coordinate Gram/Christoffel prior art only | Could extract coordinate calculations after licensing | General connection, metric compatibility, and torsion substrate exists; Levi--Civita and curvature must be built | No current producer |
| F2 value | Useful distance coherence and local coordinate spray; no interval/maximal/exponential/Hopf--Rinow producer | Could limit scope to distance plus selected local-IVP modules | Largest implementation burden, but no facade debt | Blocks F2 indefinitely at this pin |
| J1 value | None | None at audited commit | Must be built | No current producer |
| Metric coherence | Explicit metric is a transparent Mathlib alias; candidate supplies finite-distance/topology lemmas | Same if distance module is included | Must reproduce a small explicit-metric adapter or choose typeclass-only public statements | Depends on future API |
| Measure coherence | Absent | Absent | Must be built in A2 | No current producer |
| Import/maintenance cost | External 13-file/4,743-line library; narrow imports possible, umbrella is broad | Smaller code surface but project owns adaptation and later deletion | No external repository, but project owns the full analytic/geometric proof surface | Lowest current maintenance, no progress |
| Namespace/API cost | `HopfRinow.RiemannianMetric` alias/namespace and generic geodesic names need an adoption decision | Names can be adapted once, with provenance and a removal trigger | Names can follow the accepted project ownership table directly | Migration risk deferred, not removed |
| Reproducibility | Compatible pins and cacheless workflow; recheck exact selected commit and terminal status | Project CI owns copied code after legal clearance | Existing project CI and pin | Cannot validate an API that does not yet exist |
| Earliest honest readiness | Only after license, governance, new-head audit, and unconditional producer review | Only after license and a bounded extraction design | Ready for a G2 implementation decision, not for claiming the missing mathematics | Not ready at the current pin |

### Mandatory coherence bridges

Whichever implementation route G2 selects must prove the following rather
than rely on naming similarity:

1. **Metric data:** install the chosen explicit smooth metric as exactly one
   scoped `Bundle.RiemannianBundle` and prove that its fibre inner product,
   norm, and topology are the intended ones.  Do not expose a second metric
   structure.
2. **Smooth/continuous bundle:** produce both
   `IsContMDiffRiemannianBundle` at the required regularity and the explicit
   `IsContinuousRiemannianBundle` instance needed by the distance constructor.
3. **Distance/topology:** relate `Manifold.riemannianEDist` to the ambient
   `edist`, its finite `dist`, the original topology, and the `Metric.ball`
   notation used in source statements.  State `T3Space` and
   `PreconnectedSpace` only where the checked constructors need them.
4. **Measure/volume:** select a Mathlib `Measure M`, prove Borel/topological
   compatibility, show it is the metric-induced Riemannian volume, and connect
   polar density and metric balls to that measure before C3.  No such producer
   is present in either audited substrate.
5. **Connection:** construct one
   `CovariantDerivative I E (TangentSpace I)` and prove
   `cov.IsMetricCompatible` and `cov.torsion = 0`, then prove uniqueness at the
   public regularity.  A coordinate Christoffel expression is a theorem about
   this object, not a second connection.
6. **Geodesic equation:** if candidate coordinate code is used, prove its
   `HasGeodesicEquationAt`/`IsGeodesicOn` is equivalent to vanishing covariant
   acceleration for the selected connection.  Then prove local interval IVP,
   maximal gluing, smooth initial-data dependence, and the maximal exponential
   domain without replacing them by global-candidate records.
7. **Curvature signs:** test the accepted curvature order/sign on a constant
   curvature model before using the connection in Jacobi, index, sectional,
   Ricci, or comparison statements.

### Questions reserved for the human gate

1. Can the candidate authors/maintainers supply a reviewed software license
   and provenance statement covering commit `60c3e1f` and descendants?
2. If candidate PR #40 or later analytic work merges, which new immutable
   commit should replace this audit, and has it obtained the required
   governance and CI statuses?
3. Should the project adopt the candidate's transparent explicit metric alias
   and finite-distance adapter, or keep public theorems typeclass-based and use
   a private adapter?
4. Is the candidate dependency acceptable while F2 still requires substantial
   project-owned maximal-geodesic and exponential work, or is a scoped,
   licensed extraction of only `Distance` and selected coordinate modules
   cheaper?
5. Which namespace owns the eventual public `IsGeodesic`, exponential, and
   minimizing APIs, and what exact deletion trigger applies to any candidate
   compatibility wrapper?
6. Is Mathlib-native Levi--Civita construction the selected F1 route, and what
   minimum differentiability is approved for existence, uniqueness, Hessian,
   curvature, and geodesic consumers?
7. Which concrete measure construction will A2 use, and which hypotheses are
   accepted for its metric-ball and polar-integration coherence theorems?
8. Is waiting for a named upstream proposal acceptable despite blocking F1,
   F2, A2, and all their descendants?  At the inspected pin there is no
   concrete upstream declaration to wait for.

Until those questions are answered, G2 is open.  F1, F2, and A2 must not begin
on the assumption that the candidate has been accepted.

## Reproduction notes

The API findings above were reproduced from the exact Git trees with direct
source inspection and full-tree `rg` searches.  The primary-source anchors
were checked both in `prelim.tex` and in `pdftotext -layout` output from the
retained arXiv PDF.  The candidate inventory used `git ls-tree`, its complete
Lake files, direct imports, and source scans for holes, axiom commands, unsafe
declarations, and resource options.

`palimpsest_lean_lsp` reported no diagnostics for the existing project file
`MorganTianLib/Ch01/Comparison/Model.lean`.  A diagnostic request for the
Chapter 1 root and a standalone `lean_run_code` probe for the additional
geometry imports reported that imports were out of date in the local editor
cache, so neither is used as signature evidence.  No local `lake build`, `lake
update`, or cache download was run.  The protected `Lean CI / lake-build
(pull_request)` status at the eventual PR head remains the deterministic build
authority and does not replace this semantic audit.
