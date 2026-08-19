# G2 substrate decision

Status: the Mathlib-native construction route was accepted at repository
commit `aa45255fc76b3de3870f6411dde9b1c733e39074`.  `Ch01.Metric` implements the
metric, smooth/continuous bundle, and Mathlib `C^1` distance/topology substrate;
`Ch01.Volume` implements the measure/volume bridge family, and the merged
`Ch01.Curvature` module implements the independent algebraic convention kernel
and all five sign/order regressions.  This revision adds the bundled
Levi--Civita producer with smooth consumer regularity in `Ch01.Connection`.
G2 is not complete: this connection slice still requires review at its exact
protected CI head, and the distance has not yet been identified with
Morgan--Tian's smooth-path infimum.  Those gates must close before F1, F2, or A2
starts.

Decision date: 2026-08-19 (Asia/Shanghai).

## Decision

Chapter 1 will use Mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6` as its only external geometric
substrate and will implement the missing coherence kernel in this repository.
There is no Hopf--Rinow-DoCarmo dependency, extracted candidate source, open-PR
dependency, sibling path, or reference-workspace import.

This is route 3 from `ROADMAP.md`: **Mathlib-native construction**.  It is
selected because it is the only route that is legally usable, reproducible at
the current immutable pin, and able to make progress without treating an open
proposal as released API.  The cost is explicit: this repository owns the
metric bridges, Riemannian volume definition, Levi--Civita construction,
connection regularity needed by F1, and all later geometric producers.

This record is a design decision, not a theorem.  No claim below becomes Lean
evidence until the named declaration and its proof have been independently
reviewed and the protected CI status is terminal at that exact head.

## Authority and re-audit

The evidence levels remain separate:

1. The project brief requires a standalone Chapter 1 library with no holes.
2. The accepted `ROADMAP.md` requires G2 before any geometric descendant.
3. Morgan--Tian Chapter 1 and the cited cross-checks determine the mathematics.
4. Pinned source determines which Lean declarations actually exist.
5. Open Mathlib pull requests and the reference workspace are prior art only.
6. Green CI will show elaboration, not that this selection or a theorem is
   mathematically faithful.

The selected inputs were rechecked as follows:

| Evidence | Exact revision or result | Re-audit result |
| --- | --- | --- |
| Project decision baseline | `2b48a6b6e6d4e115cb3d1c16e7ea7537c8bfd0f2` | G0, G1, and scalar A1 were present; G2 had no implementation when the route was audited |
| Accepted G2 route | `aa45255fc76b3de3870f6411dde9b1c733e39074` | Human-reviewed merge of the decision; no package, pin, workflow, or Lean declaration changed in that slice |
| Lean | `leanprover/lean4:v4.32.1` | Unchanged in `lean-toolchain` |
| Mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` | Checkout and manifest agree; the selected declarations contain no `sorry`, `admit`, mathematical `axiom`, `opaque`, or `unsafe` command.  The normalized-measure owner separately contains the disclosed unused `proof_wanted` described below |
| Mathlib license | Apache License 2.0, local file SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` | Permits use of the pinned library; any adapted prior-art code must retain its own attribution and modification notice |
| Candidate repository | `palimpsest/Hopf-Rinow-DoCarmo` main `60c3e1f6493646d667a0bb645f99110a34d26e00` | Main is unchanged and still has no tracked `LICENSE`, `COPYING`, or `NOTICE`; dependency and extraction remain blocked |
| Candidate governance | [PR #40](http://127.0.0.1:3001/palimpsest/Hopf-Rinow-DoCarmo/pulls/40) head `6460d507cb578f408c8081e2b1398345ac3a2c43` | Still open and not part of candidate main; it cannot change the audit of `60c3e1f` |
| Mathlib [PR #36845](https://github.com/leanprover-community/mathlib4/pull/36845) | head `41e2b25a520d7a24f37062855d2b091dab7a5d9d` | Still open and absent from the pin; concrete Apache-licensed Levi--Civita prior art only |
| Mathlib [PR #36036](https://github.com/leanprover-community/mathlib4/pull/36036) | head `31613e7e48c4559a8be4de48121c911d74586744` | Still open, WIP, merge-conflicted, and absent from the pin; its source holes rule out direct use |
| Mathlib [PR #33714](https://github.com/leanprover-community/mathlib4/pull/33714) | head `c4cbb8b896a4db75bf49cf1ab0a898232cede01e` | Still open and absent from the pin; metric-existence prior art only |

At the decision audit, the issue context abbreviated the project baseline as
`2b48a6b8`, while Git resolved the relevant protected-branch object to
`2b48a6b6e6d4e115cb3d1c16e7ea7537c8bfd0f2`; the former prefix did not
resolve.  That historical metadata/source conflict was resolved at evidence
level 4 in favor of the Git object.  The accepted decision is now the later
commit `aa45255fc76b3de3870f6411dde9b1c733e39074`.

The inspected selected Mathlib surface is
`Geometry.Manifold.Riemannian.Basic`,
`Geometry.Manifold.VectorBundle.Riemannian`, the three
`CovariantDerivative` modules `Basic`, `Metric`, and `Torsion`,
`Geometry.Euclidean.Volume.Measure` (and its imported raw Hausdorff measure), and
`Analysis.InnerProductSpace.Dual`.  Implementations use focused imports rather
than the `Mathlib` umbrella.  `Ch01.Metric` imports only
`Geometry.Manifold.Riemannian.Basic` and `Topology.Connected.Clopen`.
`Ch01.Volume` imports that focused metric module together with
`Geometry.Euclidean.Volume.Measure` and
`MeasureTheory.Constructions.BorelSpace.Metric`; neither adds a Lake
dependency or sibling path.

The selected `euclideanHausdorffMeasure` API was introduced by merged Mathlib
PR [#34697](https://github.com/leanprover-community/mathlib4/pull/34697) at
commit `9d092b118b6f9f777ba67c7a2d2c2bcdd1b52395`, which is an ancestor of the
project pin.  Its pinned owner file contains one `proof_wanted`,
`addHaarScalarFactor_hausdorffMeasure_eq`, asking for a closed formula for the
scaling constant.  Batteries elaborates this command to a private metadata
placeholder, not an exported theorem.  Neither
`euclideanHausdorffMeasure_def` nor
`InnerProductSpace.euclideanHausdorffMeasure_eq_volume` depends on it, and the
project does not consume or restate the wanted formula.  This is disclosed as
upstream source debt rather than counted as a proved API declaration.

The read-only OpenGA reference tree contains a different, later DoCarmo source
tree with an Apache license.  That does not license the forge candidate at
`60c3e1f`, does not make the reference tree a project dependency, and does not
override the G1 finding.  This apparent name-level conflict is resolved at
evidence level 4 by exact repository and revision identity.

## Route comparison

All four routes are compared against the same ten criteria.  "Bridge count"
counts the seven mandatory coherence families from G1, not individual helper
lemmas; splitting one family into more declarations does not make another
route semantically cheaper.

| Criterion | Reviewed Git dependency | Scoped licensed extraction | Mathlib-native construction | Wait for merged upstream |
| --- | --- | --- | --- | --- |
| Standalone CI reproducibility | Candidate pins match today, but the exact accepted dependency revision does not exist | Project CI would own copied files, but there is no legally selectable source revision | Existing workflow, toolchain, and manifest already reproduce the only dependency | No buildable project change until a merge and a new pin/toolchain audit |
| Immutable pins | Candidate `60c3e1f` is immutable but unusable; PR #40 is not main | A source commit could be named, but copying is blocked | Mathlib `520045ab` is already immutable in Lake and the manifest | Current PR heads are immutable evidence but not released library API |
| License and provenance | Blocked: no software license at candidate main | Blocked for the same reason | Mathlib is Apache-2.0; new project code has direct repository provenance | Mathlib PR code is Apache-2.0, but availability still requires merge and repinning |
| Transitive imports | Narrow distance imports are possible; the umbrella imports all 12 subordinate modules audited by G1 | Potentially smaller, but every copied import and later rebase becomes project-owned | Focused pinned imports only; no new Lake package or sibling path | Unknown at the future merge; #36036 currently has a broad 29-file change |
| Mathlib coherence | Candidate metric is an alias, but its coordinate connection vocabulary is not a Mathlib `CovariantDerivative` | Adapters would still be required and would become local debt | Direct use of Mathlib bundle metrics, distance, measure, and `CovariantDerivative` types | Potentially best after merge, but current heads do not provide the complete kernel |
| Axiom and `sorry` inventory | Candidate source scan is clean, but exported proof-term axioms are incomplete | Cannot legally perform the final extracted proof audit | Selected pinned declarations have no source holes; the measure owner's unused private `proof_wanted` is disclosed above, and every exported local theorem will receive an axiom check | #36036 contains holes; #36845 and #33714 do not cover all required producers |
| Semantic coverage | Partial distance and pointwise coordinate-geodesic work; no volume or bundled Levi--Civita producer | Same bounded source coverage | No hidden coverage claim: every missing producer is owned explicitly | No inspected proposal covers metric, distance, volume, connection regularity, curvature, and geodesics together |
| Namespace collisions | `HopfRinow.RiemannianMetric` and generic geodesic names overlap the roadmap vocabulary | Names could be changed, creating migration adapters | Project namespaces can follow the roadmap while public types remain Mathlib types | Future names are plausible migration targets but remain unstable before merge |
| Maintenance ownership | External repository plus local bridges and version coordination | Full ownership of adapted source plus provenance and deletion work | Full ownership of only the code Chapter 1 actually uses | Work is deferred, not removed; later pin migration and local bridges remain |
| Bridge count | All 7 families remain; candidate only partially supplies metric/distance and supplies none of measure/connection/sign contracts | All 7 remain, with partial reusable code only after licensing | All 7 are local and reviewable against one pin | All 7 remain at the current heads; a future merge may reduce connection work but not the other families |

The Git and extraction routes fail a legal hard gate before their engineering
benefits can be weighed.  Waiting fails the project-progress objective and has
no named merged revision.  Mathlib-native construction has the highest known
implementation cost, but it has no unresolved legal input, no extra package,
and no second public vocabulary.

## Answers to the eight G1 questions

1. **Candidate license.** No reviewed software license or provenance statement
   covers candidate main `60c3e1f` on the forge.  The separately licensed
   reference tree does not cure that defect.  Candidate dependency and
   extraction are rejected at this gate.
2. **Candidate successor.** No successor replaces the audit.  Candidate PR #40
   is still open and does not add a license to main.  A future candidate may be
   reconsidered only at a merged immutable commit with license, governance,
   source, proof, and CI re-audits.
3. **Metric representation.** Public statements use
   `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` directly.
   There is no candidate alias and no project alias.  Each theorem installs
   exactly one local `Bundle.RiemannianBundle` from `g.toRiemannianMetric`.
4. **Candidate F2 value.** It is not accepted.  The repository owns the later
   maximal-geodesic, exponential, minimizing, and Hopf--Rinow construction.
   No extraction is justified merely to obtain the candidate's incomplete
   pointwise coordinate IVP.
5. **Geodesic namespace.** `MorganTianLib.Ch01.Geodesic` owns the future public
   intrinsic geodesic, exponential, and minimizing API.  No candidate wrapper
   is introduced, so there is no compatibility alias to retain.  Private chart
   code must disappear from final theorem signatures when F2's intrinsic
   equivalence lands.
6. **Levi--Civita route and regularity.** Yes: construct a Mathlib
   `CovariantDerivative I E (TangentSpace I)` from the smooth metric.  Existence
   and pointwise uniqueness use a `C^2` manifold, a `C^1` metric (provided by
   the chosen smooth metric), and finite-dimensional real model space.  The
   object is unique on differentiable vector fields because Mathlib leaves its
   value on nondifferentiable fields unconstrained.  Smooth
   `ContMDiffCovariantDerivative` regularity is a separate obligation from
   existence and uniqueness; `Ch01.Connection` now proves it before F1 defines
   smooth curvature fields.
7. **Measure.** After installing the metric-induced `EMetricSpace` and its
   Borel measurable space, define Riemannian volume to be the pinned
   `MeasureTheory.Measure.euclideanHausdorffMeasure (Module.finrank Real E)`,
   not the unscaled raw Hausdorff measure.  With Mathlib's scoped notation this
   is `μHE[Module.finrank Real E]`.  It is a dimension-dependent scalar multiple
   of raw `μH[Module.finrank Real E]` constructed from the selected `edist`.  At
   the pin,
   `InnerProductSpace.euclideanHausdorffMeasure_eq_volume` proves that this
   scaled measure, unlike raw `μH`, is exactly `volume` on every
   finite-dimensional real inner-product space.  G2 must prove the Borel and
   metric coherence; A2 must prove chart and polar Jacobian formulas for this
   measure.  None of those later formulas is assumed here.
8. **Waiting.** Rejected.  There is no named merged revision to wait for.
   Migration is triggered only by a merged immutable Mathlib commit that is
   compatible with the selected toolchain or an approved repin and supplies a
   semantically equivalent producer with the needed regularity.  PR #36845 is
   the connection migration candidate; #33714 concerns metric existence only;
   a completed successor to #36036 may later inform F1/F2.

## Frozen coherence contracts

The contracts are implemented in reviewable dependency slices.  The metric,
volume, connection, and algebraic curvature-sign sections now have Lean owners
named in the bridge ledger; the source-distance correspondence remains
mandatory before G2 is complete.  Names are ownership descriptions; review may
improve a declaration name without changing its representation or semantics.

### Metric, norm, and topology

For an explicit smooth tangent metric `g`:

- install `letI : Bundle.RiemannianBundle (TangentSpace I) :=
  { g := g.toRiemannianMetric }` locally, never globally;
- synthesize and expose the intended
  `IsContMDiffRiemannianBundle I ∞ E (TangentSpace I)` and explicit
  `IsContinuousRiemannianBundle E (TangentSpace I)` witnesses;
- prove that the installed fibre `inner Real v w` is `g.inner x v w`;
- prove that its norm is the norm induced by that inner product; and
- prove that the norm topology is the pre-existing tangent-fibre topology used
  by the vector bundle.

No `RiemannianMetric` abbreviation, parallel metric class, or public
coordinate Gram matrix is permitted.

### Distance and balls

The extended metric is `EMetricSpace.ofRiemannianMetric I M`.  Under the exact
constructor hypotheses, prove:

- ambient `edist x y = Manifold.riemannianEDist I x y`;
- the constructed uniform and topological structures are the original ones;
- finiteness from preconnectedness by an actual piecewise smooth path, then
  install `EMetricSpace.toMetricSpace`;
- `dist x y = ENNReal.toReal (Manifold.riemannianEDist I x y)`; and
- `Metric.ball x r` is the corresponding Riemannian-distance sublevel set.

`T3Space M` occurs only for the separating `EMetricSpace` constructor.
`PreconnectedSpace M` occurs only in the finite-distance proof.  The extended
distance and topology theorems must not require connectedness.

This contract formalizes Morgan--Tian, Definition 1.1 and the metric-ball
paragraph on p. 35; it does not add a stronger global hypothesis to that local
definition.

The current `Ch01.Metric.exists_contMDiff_path` theorem proves only a
`CMDiff 1` (`C^1`) witness, exactly matching the regularity in Mathlib's
`riemannianEDist` infimum.  A `C^1` path need not be smooth.  The required
piecewise-smooth witness and equality between the Mathlib `C^1` infimum and
Morgan--Tian's smooth-path infimum therefore remain pending; no additional
completeness, boundarylessness, or finite-dimensionality assumption is needed
or added to the existing theorem.

### Riemannian volume

The sole volume measure is the full-dimensional Euclidean-normalized Hausdorff
measure `μHE[Module.finrank Real E]` of the metric just installed.  The
`Ch01.Volume` foundation module must record:

- its measurable space as the Borel space of the original topology in the
  explicit result type of `riemannianVolume`;
- every open set and every `Metric.ball` is measurable;
- the measure definition unfolds to Mathlib's pinned dimension-dependent
  scalar multiple of raw Hausdorff measure for the selected Riemannian `edist`;
  and
- every finite-dimensional real inner-product model reduces to Mathlib's
  `volume` by `InnerProductSpace.euclideanHausdorffMeasure_eq_volume`.

No Euclidean normalization is claimed for raw `μH[Module.finrank Real E]`.

G2 does not claim sphere integration, a polar change-of-variables theorem,
an exponential Jacobian, cut-locus measurability or nullity, or equality with
an arbitrary pre-existing `MeasureSpace M`.  Those belong to A2 and N1.

### Connection

The one public connection is a value of Mathlib's exact type
`CovariantDerivative I E (TangentSpace I)`.  The project may use the Koszul and
musical-isomorphism design from Mathlib PR #36845 as prior art, but it must not
import that head or describe its declarations as pinned API.  Any source-level
adaptation must retain the Apache attribution and say that it was modified.

The implementation must prove separately:

- construction from the selected explicit metric;
- `CovariantDerivative.IsMetricCompatible`;
- `cov.torsion = 0`;
- the Koszul formula; and
- uniqueness on differentiable vector fields at a point; and
- smooth `CovariantDerivative.ContMDiffCovariantDerivative` regularity for
  later curvature and geodesic consumers.

This is the G2 producer for Morgan--Tian, Theorem 1.2, pp. 35--36, cross-checked
against do Carmo (1992), Chapter 2, pp. 44--51, and Lee (2018), Theorem 5.10.

There is no second affine-connection structure.  Christoffel coefficients are
future coordinate theorems about this `CovariantDerivative`.  Since no
candidate coordinate geodesic code is selected, G2 has no coordinate-geodesic
adapter; F2 must state vanishing covariant acceleration directly and prove any
chart equivalence it later uses.

### Curvature convention

For vector fields `X`, `Y`, and `W`, the kernel is frozen as

```text
R X Y W = nabla_X (nabla_Y W)
          - nabla_Y (nabla_X W)
          - nabla_[X,Y] W.
```

The four-tensor uses Morgan--Tian's positional order: its third argument is the
metric-pairing slot and its fourth argument is the operator-input slot.

```text
curvature4 X Y Z W = g (R X Y W) Z.
```

The constant-curvature operator and four-tensor are therefore

```text
R_K X Y W = K * (g Y W * X - g X W * Y),
R4_K X Y Z W = K * (g X Z * g Y W - g X W * g Y Z).
```

`Ch01.Curvature` encodes these formulas without a connection or manifold
producer and establishes all of the following signs before F1 exports
geometric curvature:

| Consumer boundary | Required regression |
| --- | --- |
| Chart | `R_ijkl = K (g_ik g_jl - g_il g_jk)` in that exact argument order |
| Jacobi | for unit `V` and `J` perpendicular to `V`, `R_K J V V = K * J`, so `D^2 J + R(J,V)V = 0` has the spherical sign |
| Index form | the curvature contribution is `-g (R(J,V)V) J`, hence `-K * norm J ^ 2` on the same pair |
| Sectional | `R4_K X Y X Y = K` on an orthonormal pair |
| Ricci | for an orthonormal basis `e_i`, `sum_i R4_K X e_i Y e_i = (n - 1) * K * g X Y`, the source contraction of the second and fourth slots |

These are algebraic convention tests, not a claim that a geometric
constant-curvature manifold has already been constructed.  The later chart
curvature theorem must be tested against the same operator rather than
introducing a sign-changing adapter.

The finite-basis contraction theorem assumes only a finitely indexed
`OrthonormalBasis`.  It needs neither a nontriviality assumption nor a lower
dimension bound: in dimension zero the paired inner product vanishes, and in
dimension one the coefficient `finrank Real E - 1` vanishes.  The later
two-plane and comparison gates retain their separate `2 <= finrank Real E`
hypotheses.

The source anchor is Morgan--Tian, Definition 1.4 and the coordinate formula,
pp. 37--38; the Ricci contraction check also fixes the order used by Definition
1.8 on p. 39.

## Assumption and regularity table

| Assumption | First permitted use | Not permitted as a blanket hypothesis |
| --- | --- | --- |
| `FiniteDimensional Real E` | Levi--Civita musical isomorphism, volume dimension, and finite traces | Basic smooth metric, extended distance, or topology |
| `2 <= Module.finrank Real E` | Only source statements that need a two-plane or the accepted uniformization/weak-Calabi gates | Metric, connection existence, volume, geodesic IVP, or one-dimensional valid results |
| `I.Boundaryless` | A checked chart/ODE constructor that requires open model charts in F2 or later | G2 metric, measure, or Levi--Civita construction |
| `T3Space M` | `EMetricSpace.ofRiemannianMetric` | Bundle metric, connection, or extended path length |
| `PreconnectedSpace M` | Proof that all Riemannian extended distances are finite | Local metric/topology, connection, curvature, or volume definition |
| `SigmaCompactSpace M` | A later partition, integration, or global extension theorem whose checked constructor requires it | G2 metric, connection, or curvature convention |
| `ConnectedSpace M` | A source theorem genuinely stated for connected manifolds; otherwise prefer local or preconnected hypotheses | A synonym for completeness or a default Chapter 1 context |
| `CompleteSpace M` / metric completeness | Hopf--Rinow and its actual global consequences in F2 | Local geodesics, exponential domain, metric/measure coherence, or curvature |
| `CompleteSpace E` | Only if a checked analytic constructor cannot derive it from finite dimension | Public Levi--Civita statement when finite-dimensional completeness suffices |

Hausdorffness is expressed by the weakest checked class.  In this pin,
`T3Space M` supplies what the separating extended-metric constructor needs;
an additional `T2Space M` must not be repeated without a distinct consumer.

## Bridge ledger and ownership

The seven mandatory bridge families have these owners and completion tests:

| Family | Owner | G2 completion evidence | Status in this revision |
| --- | --- | --- | --- |
| Metric data | `Ch01.Metric` | one installation path plus fibre inner/norm/topology equalities | Implemented by `contMDiffRiemannianBundle`, `inner_eq_metric`, `norm_eq_sqrt_metric`, and `tangent_topology_eq_norm_topology` |
| Smooth/continuous bundle | `Ch01.Metric` | explicit successful instance synthesis at the selected regularity | Implemented by `contMDiffRiemannianBundle` and `continuousRiemannianBundle` |
| Distance/topology | `Ch01.Metric` | `edist`, finite `dist`, original topology, ball equalities, and the accepted smooth/piecewise-smooth source correspondence | Partially implemented: the clopen proof, `C^1` witness, and all Mathlib `edist`/`dist`/topology/ball equalities are proved; the smooth/piecewise-smooth witness and equality with the source path infimum remain pending |
| Measure/volume | `Ch01.Volume` | Euclidean Hausdorff definition, explicit Borel result type, metric dependence, Euclidean normalization | Implemented by `riemannianVolume`, its explicit Borel indexing, and its open-set, ball, raw-Hausdorff, and Euclidean normalization theorems |
| Connection | `Ch01.Connection` | construction, compatibility, torsion, Koszul, uniqueness, and smooth consumer regularity | Implemented by `covariantDerivative`, `covariantDerivative_isMetricCompatible`, `covariantDerivative_torsion_eq_zero`, `covariantDerivative_koszul`, `covariantDerivative_eq_at_of_isMetricCompatible_of_torsion_eq_zero`, and `covariantDerivative_contMDiff` |
| Geodesic equation | `Ch01.Geodesic` in F2 | intrinsic vanishing-acceleration definition; no G2 coordinate adapter is needed | Pending F2 after G2; no compatibility adapter exists |
| Curvature signs | `Ch01.Curvature` | algebraic model/operator pairing and all five constant-curvature regressions | Implemented by `modelCurvature`, `modelCurvature4`, their pairing and component theorems, the Jacobi/index/sectional regressions, and `sum_modelCurvature4_orthonormalBasis` |

The G2 implementation may split these into focused modules, but the Chapter 1
umbrella must import every completed public contract.  No module may import a
Chapter 2/3 file, the reference workspace, or an unmerged PR tree.

## Migration and deletion triggers

- If a successor of Mathlib PR #36845 merges, migrate only after an approved
  immutable Mathlib pin provides equivalent compatibility, torsion, uniqueness,
  and the regularity needed by Chapter 1.  Delete the project constructor in
  the migration PR; do not retain an alias vocabulary.
- If a successor of PR #33714 merges, it may supply an existence theorem for a
  smooth metric, but it does not replace the chosen explicit metric parameter
  or any distance/measure bridge without proved definitional compatibility.
- If a completed successor of PR #36036 merges, F1/F2 must audit curvature and
  geodesic signs, maximal domains, imports, and holes before reuse.
- A newly licensed candidate commit can reopen the route decision only through
  a separate reviewed roadmap revision.  It is not an automatic dependency
  migration trigger.
- Private helpers adapted from prior art are deleted once the corresponding
  pinned Mathlib declaration is used directly.  Public compatibility wrappers
  require a named downstream caller and a removal issue; G2 currently approves
  none.

## Implementation status

The accepted decision slice changed no Lean declaration, package pin,
workflow, or canonical theorem.  Focused implementation revisions now add
`Ch01.Metric`, `Ch01.Volume`, `Ch01.Connection`, and the algebraic
`Ch01.Curvature` kernel to the Chapter 1 umbrella.  Together they cover the
metric, smooth/continuous-bundle, measure/volume, connection, and
curvature-sign rows plus the Mathlib `C^1` side of the distance/topology row
without adding a compatibility adapter.  The curvature module defines only an
inner-product-space model; it does not define the connection-produced manifold
curvature API owned by F1.  These revisions deliberately add no
smooth-path-infimum equivalence, coordinate geodesic, polar integration,
exponential Jacobian, or cut-locus claim.

Local diagnostics and axiom/source scans support review of this revision; the
protected `Lean CI / lake-build (pull_request)` status remains the authoritative
build check.  After this connection slice merges, G2 remains open until the
smooth/piecewise-smooth source-distance correspondence is implemented and
reviewed.  F1, F2, and A2 therefore remain blocked.
