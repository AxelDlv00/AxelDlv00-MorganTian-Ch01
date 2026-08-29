# Morgan--Tian Chapter 1 roadmap

<!-- palimpsest-governance -->

Status: accepted bootstrap route at repository commit
`0a7e55543629438cacf6e25b698ba770274225d9`, with the A1 scalar, vector,
operator, trace, and determinant/density comparison increments and completed
G1 evidence audit recorded below.  The Mathlib-native G2 route in
[`docs/G2_SUBSTRATE_DECISION.md`](docs/G2_SUBSTRATE_DECISION.md) was accepted
at `aa45255fc76b3de3870f6411dde9b1c733e39074`.  Every G2-owned coherence family
was implemented by accepted head
`07d2a0be1a7aa3e38d827756b6585edb5a2ade60`: `Ch01.Metric` supplies the metric,
smooth/continuous-bundle, Mathlib `C^1` distance/topology, and source-distance
bridges; `Ch01.Volume` supplies normalized volume; `Ch01.Connection` supplies
the bundled Levi--Civita connection with smooth consumer regularity; and
`Ch01.Curvature` supplies the algebraic sign/order kernel and five regressions.
The geodesic-equation handoff is owned by F2 after G2 and is not a G2
prerequisite.  Consequently G2 is complete at `07d2a0b`, and F1, F2, and A2 are
unlocked there.

The later focused F1 `Ch01.Connection.Christoffel` increment proves the
canonical connection's chart-coordinate formula and completes S03 while
leaving S04--S05 open; open issue #13 continues from that frontier.  The merged
E1 revision separately proves the generic smooth-vector-bundle metric theorem
and its arbitrary finite-dimensional tangent-bundle corollary, closing E1 and,
together with G2, S01.  The G2 completion decision was re-audited at protected
branch head `8f43241e6f754e6958266d15537fdef10e73175c`.  It makes no new S04--S43
completion claim.  This file is the repository-owned route for the Chapter 1
library.  It is not a transcription of the project brief, and each
implementation claim is limited to the exact audited revision named below.

The issue-35 F1 increment advances the curvature frontier without closing the
whole source claim: the exact bundled Levi--Civita field commutator, its
source-ordered four-tensor facade, local-frame calculation, and pointwise slot
laws are recorded as partial S06/S07 progress below.  The selected-extension
facade is explicitly provisional: it has no arbitrary smooth-extension
application theorem and must not be treated as the canonical intrinsic
producer or consumed by downstream geometry.  The extension/local-frame chart
identification, metric symmetries, the differential Bianchi identity, and
model-coordinate regressions remain explicit debt until their own producers
are reviewed; the first Bianchi identity is included in the proved S07 subset.

## Authority and evidence

Decisions use the following authority order:

1. The project objective and its constraints fix scope and the required
   strength of the end artifact.
2. Once this bootstrap PR is accepted, this roadmap fixes the reviewed route.
3. Checked publications support mathematical statements and source anchors.
4. The pinned Lean, Mathlib, and shared-dependency sources support API claims.
5. Existing formalizations are prior art and feasibility evidence only.
6. Blueprints, generated sites, and informal notes are planning aids.
7. CI proves elaboration and tests at a commit; it does not prove intent or
   correspondence with the book.

Conflicts are recorded at the authority level where they occur.  The direct
source audit confirms the issue snapshot's connection claim: the pinned
Mathlib tree contains `Geometry/Manifold/VectorBundle/CovariantDerivative`
(`Basic`, `Metric`, and `Torsion`) alongside the bundle metric and induced
path-length APIs.  The candidate DoCarmo connection files remain prior art.
The G2 decision rejects that repository as a dependency at the audited
unlicensed commit; a future route revision would have to recheck its intrinsic
geodesic conventions as well as its legal and producer status.

The primary source is Morgan and Tian's arXiv v2 source (`math/0607607`,
revised 21 March 2007), whose retained PDF is the checked Chapter 1 source.
Its printed Chapter 1 pages are 35--50.  The publication edition is the 2007
Clay Mathematics Monograph 3; the arXiv source and the book have the same
Chapter 1 text, but their compiled pagination differs.  Roadmap page numbers
below refer to the retained arXiv PDF's printed pages and are paired with
section/statement anchors so that the edition distinction is visible.

The source/API audit for this bootstrap used:

- Morgan--Tian `prelim.tex` and the retained arXiv PDF for every Chapter 1
  claim in the inventory below.
- Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`, especially
  `Geometry/Manifold/VectorBundle/Riemannian.lean`,
  `Geometry/Manifold/VectorBundle/CovariantDerivative/{Basic,Metric,Torsion}.lean`,
  `Geometry/Manifold/Riemannian/Basic.lean`, and
  `Geometry/Manifold/Riemannian/PathELength.lean`.
- The concrete but unmerged Mathlib proposals at PR #36845 head
  `41e2b25a520d7a24f37062855d2b091dab7a5d9d`, PR #36036 head
  `31613e7e48c4559a8be4de48121c911d74586744`, and PR #33714 head
  `c4cbb8b896a4db75bf49cf1ab0a898232cede01e`, as current prior art only;
  none is available at the pinned commit.
- The candidate `palimpsest/Hopf-Rinow-DoCarmo` main commit
  `60c3e1f6493646d667a0bb645f99110a34d26e00`, which is not yet an accepted
  dependency and is not used by this bootstrap package.
- The reference Morgan--Tian development as prior art only.  Its 168-file,
  approximately 50,700-line Chapter 1 split and its Chapter 1 to Chapter 2
  import are specifically not adopted.
- The publication records and stable URLs in `docs/references.bib`.

The completed declaration-level G1 audit is
[`docs/G1_SUBSTRATE_AUDIT.md`](docs/G1_SUBSTRATE_AUDIT.md).  It records the
exact pinned signatures and imports, the candidate's license and producer
gaps, a disposition for every source row, and the bounded alternatives and
questions for G2.  The G2 decision record resolves those questions, records
the exact re-audit, freezes the implementation contract, and identifies the six
G2-owned bridge families and their Lean evidence.  The final source-distance
implementation at `07d2a0be1a7aa3e38d827756b6585edb5a2ade60` completed the last
of those six families.  The ledger's seventh row is an explicit post-gate F2
geodesic handoff, not an unnamed G2 check.

## End state and boundaries

The end artifact is a standalone, reusable Lean library rooted at
`MorganTianLib/Ch01.lean`.  It will contain faithful declarations and proofs,
or a named milestone and gated proof target, for every source claim in the
inventory.  It will have no `sorry`, no project-owned axioms carrying
mathematical content, no sibling filesystem dependency, and a green
repository-owned CI workflow at the exact reviewed head.

The final public API must cover:

1. Bundle Riemannian metrics, the Levi--Civita connection, Hessian, and
   Laplacian.
2. Curvature tensors/operators, sectional/Ricci/scalar curvature, both Bianchi
   identities, divergence and Bochner identities, naturality, and rescaling.
3. Constant-curvature and Einstein consequences, the Chapter 1 examples, and
   the cone curvature calculation at the source strength.
4. Geodesic initial-value problems, energy and first variation, Hopf--Rinow
   interfaces, the maximal exponential map, and its differential.
5. Intrinsic Jacobi fields, conjugate points, the index form, second variation,
   and the no-interior-conjugate/unique-subsegment theorem for minimizers.
6. Normal coordinates, cut locus, cut time, injectivity radius, polar metric
   and volume descriptions, and Gaussian normal-coordinate claims.
7. Sectional and Ricci comparison, the stated local-diffeomorphism radius, and
   Bishop--Gromov relative volume comparison.
8. The `injvol` and `volinj` estimates with the source hypotheses and
   constants/dependence intact.

Out of scope are Chapters 2 and 3, Ricci flow, later-book geometry, generated
blueprints/sites/dashboards, and wholesale ports of prior-art trees.  A later
chapter may consume a deliberately exported Chapter 1 interface, but it may
not be imported by the final Chapter 1 DAG.  Upstreaming to Mathlib is
human-owned and is not a completion condition.

## Bootstrap build contract

G0 supplies the package and CI contract only; it intentionally exposes an
empty Chapter 1 umbrella.  The package uses:

- Lean `leanprover/lean4:v4.32.1` in `lean-toolchain`.
- Mathlib git commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6` in `lakefile.lean` and
  `lake-manifest.json`.
- No DoCarmo, Hopf--Rinow, sibling path, or reference-workspace dependency.
- `autoImplicit := false`; any heartbeat or transparency exception must be
  added only at a named failing boundary and audited when that boundary is
  repaired.

The default target is the `MorganTianLib` library, with the root importing
only `MorganTianLib.Ch01`.  Every new module will carry module documentation;
public definitions and major theorems will carry docstrings and precise
literature anchors.  Imports stay at the smallest stable API boundary.

`.gitea/workflows/lean.yml` is repository-owned and has workflow name `Lean CI`
and job id `lake-build`, which yields the protected status
`Lean CI / lake-build (pull_request)`.  It checks out the candidate commit,
derives keys from `lean-toolchain` and `lake-manifest.json`, tolerates an
absent `ACTIONS_CACHE_URL`, restores dependency packages and weekly project
outputs when the cache service exists, runs `lake exe cache get`, and runs
`lake build`.  Cache saves are restricted to pushes to `main`; pull requests
only restore.  Action revisions are immutable commit SHAs.  The separate
`.github/workflows/lean.yml` implements the same G0 workflow contract for
GitHub with immutable `actions/checkout` and `leanprover/lean-action` pins;
it retains only the action's Mathlib artifact restoration and explicitly
disables its whole-`.lake` GitHub cache, so the build has no project-cache
dependency on the Actions cache service.  The separate
`palimpsest/review-panel` status remains a forge governance status and is not
faked by this workflow.

## Canonical representations and public API

The reviewed G2 decision freezes representations before F1--J1.  The selected
choices are:

- **Metric and distance.** Public statements use Mathlib's
  `Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I)` directly, with one
  local `Bundle.RiemannianBundle` installation.  There is no project or
  candidate metric alias.  `pathELength` and `riemannianEDist` are the induced
  length/distance infrastructure.  `Ch01.Metric` proves fibre inner, norm,
  topology, ambient `edist`/`dist`, finite `C^1`-path, and `Metric.ball`
  coherence for this Mathlib substrate.  Endpoint-preserving quantitative chart
  replacement and endpoint-flat concatenation prove that the smooth and finite
  piecewise-smooth length infima both equal `Manifold.riemannianEDist`.  Two
  unrelated public metric or distance structures are forbidden.
- **Connection.** The public connection is exactly Mathlib's
  `CovariantDerivative I E (TangentSpace I)`, constructed from the selected
  metric, with proved metric compatibility, zero torsion, the Koszul formula,
  and uniqueness on differentiable vector fields.  A chart Christoffel
  formula is an implementation theorem, not a second connection.
- **Curvature.** The public `(1,3)` tensor is `R X Y Z` with
  `R X Y Z = nabla_X(nabla_Y Z) - nabla_Y(nabla_X Z) -
  nabla_[X,Y] Z`.  In Morgan--Tian's positional order the `(0,4)` form is
  `curvature4 X Y Z W = g (R X Y W) Z`.  Sectional curvature is
  `curvature4 X Y X Y` on an orthonormal pair, while the Jacobi and index-form
  curvature term uses `R J V V`.  A constant-curvature model must produce
  `R_K X Y W = lambda * (g Y W * X - g X W * Y)` and
  `R_{ijkl} = lambda (g_{ik} g_{jl} - g_{il} g_{jk})`; this is the kernel test
  before J1.
- **Geodesics and exponential.** G2 selects no candidate geodesic API.
  `MorganTianLib.Ch01.Geodesic` owns the project-built intrinsic API in F2.
  The maximal exponential domain preserves an unbounded/complete case rather
  than using a finite-radius facade.
- **Jacobi fields.** `JacobiField gamma` is an intrinsic tangent-bundle field
  along `gamma` satisfying the source-ordered covariant Jacobi equation
  `D^2 J + R J V V = 0`.  Chart `(J,DJ)` pairs and parallel-frame matrices are
  private proof representations, with explicit equivalence theorems.
  Conjugacy means a nonzero endpoint-vanishing intrinsic Jacobi field; the
  kernel of `d exp` equivalence is proved before local-diffeomorphism arguments.
- **Index form.** The public index form is the intrinsic symmetric bilinear
  integral on fields along a geodesic, with endpoint conditions stated
  explicitly.  A frame/inner-product-space form is an adapter proved equal to
  it, never a replacement definition.
- **Cut and injectivity.** Cut time, cut locus, and injectivity radius use
  codomains that retain `infty`.  Book-definition equivalences (frontier of
  the maximal minimizing domain, distance to the cut locus, and the conjugate
  or broken-geodesic alternatives) are required before comparison APIs use
  them.
- **Measure and volume.** The one Riemannian volume is Mathlib's
  `MeasureTheory.Measure.euclideanHausdorffMeasure (Module.finrank ℝ E)`, or
  `μHE[Module.finrank ℝ E]`, for the selected metric-induced distance.  This is
  the pinned Euclidean-normalized scalar multiple of raw Hausdorff measure, not
  raw `μH` itself.  `Ch01.Volume.riemannianVolume` selects that measure over
  the original Borel structure, and the volume module proves its metric,
  measurable-ball, raw-Hausdorff, and finite-dimensional inner-product-space
  normalization facts.  A2 owns the measure-theoretic primitives needed before
  cut-locus nullity: chart Jacobians, Sard/change-of-variables lemmas,
  measurability, sphere/radial integration, and ratio-of-integrals lemmas that
  do not mention normal geometry.  N2 owns the post-N1 polar Jacobian and its
  equality with this measure.  A ratio for an arbitrary density is an A1/A2
  analytic lemma only; it is not Bishop--Gromov until N2/C3 prove the density
  and metric-ball equalities.

### Hypotheses and proof architecture

Morgan--Tian's standing manifold convention is smooth, finite-dimensional
(`n`-dimensional), paracompact, and Hausdorff.  Lean statements spell out the
Mathlib chart, topology, and bundle instances they actually consume.  They do
not impose connectedness, completeness, finite dimension, or no-boundary
assumptions globally on supplied-metric results that remain valid without
them.  In particular:

- the public metric is smooth (`∞`), while the source-distance bridge compares
  smooth and accepted piecewise-smooth paths with Mathlib's `C^1` paths;
- the Levi--Civita construction may use the audited `C^2` atlas/`C^1` metric
  minimum internally.  `Ch01.Connection` separately proves the smooth bundled
  connection regularity needed by F1; uniqueness is stated on the differentiable
  vector fields on which Mathlib's connection axioms determine a value;
- E1 retains the source's finite-dimensional metric-existence contract.
  `MetricExistence.nonempty_contMDiffRiemannianMetric` proves the
  partition-of-unity bundle theorem from a topology-compatible model-fiber
  inner product (`InnerProductSpace ℝ F`), a finite-dimensional base model
  (`FiniteDimensional ℝ EB`), and `SigmaCompactSpace B` and `T2Space B`, in
  addition to the topology, chart, `FiberBundle`, `VectorBundle`,
  smooth-manifold, and `ContMDiffVectorBundle` instances.  It proves the
  existing-fiber topology compatibility required by
  `Bundle.ContMDiffRiemannianMetric`; no extra fiber topological-group or scalar
  continuity hypothesis appears in the exported signature.
  `MetricExistence.nonempty_contMDiffRiemannianMetric_tangentSpace` transports
  the Euclidean inner product along a finite-dimensional continuous linear
  equivalence inside the proof, so its arbitrary finite-dimensional manifold
  model has no public `InnerProductSpace` assumption and is not claimed to be
  Hilbertizable.  These E1 hypotheses do not constrain G2 or later theorems
  stated for a supplied metric;
- elsewhere, finite-dimensional hypotheses occur at traces, determinants,
  Riemannian volume, curvature contractions, and finite-dimensional
  ODE/linear-algebra consumers.  The special `2 <= n` hypotheses occur only in
  S14 and S34, while S15 records its exact dimension 2/3 alternatives;
- F2's source-facing geodesic IVP for every initial point and the resulting
  global exponential contracts assume the weakest checked manifold-level class
  `[BoundarylessManifold I M]`.  Point-local variants instead expose
  `I.IsInteriorPoint p`; the pinned
  `exists_isMIntegralCurveAt_of_contMDiffAt` and local-uniqueness APIs expose
  this alternative, while the all-points wrappers use the class.  The existence
  theorem also requires the model-space premise `[CompleteSpace E]`.
  The stronger model-level `[I.Boundaryless]` recorded in the G2 substrate
  decision is sufficient to synthesize this class, but is not the public F2
  requirement.  Metric completeness does not imply either condition, so these
  hypotheses remain separate from Hopf--Rinow;
- preconnectedness is used only to make the induced extended distance finite;
  connectedness, completeness, compact closure, sigma compactness, and absence
  of boundary are introduced row by row where the source theorem or a checked
  integration/ODE API needs them; and
- V1 records the exact curve/family regularity supporting both boundary terms
  and integration by parts.  Review rejects any convenient regularity choice
  that weakens the source's arbitrary-family second variation.

Proofs proceed from intrinsic public objects to private adapters: connection
and curvature first; geodesic and Jacobi chart ODEs with equivalence theorems;
frame-level index/Riccati arguments; and measure/Sard/change-of-variables
primitives independently of normal geometry.  Cut geometry then feeds the N2
polar/Gaussian producers and measure identities.  A1's analytic comparison
theorems intentionally accept abstract functions or operators.  They become
Morgan--Tian comparison results only when J1/N2/C1/C2 supply and identify the
geometric producer.  This direction prevents an assumed density or chart
matrix from being mistaken for a manifold theorem.

### Proposed module and declaration ownership

The names below are families and ownership boundaries, not a promise that all
files are created by G0:

| Module | Public families | Internal/provisional material |
| --- | --- | --- |
| `Metric` | canonical bundle metric predicates, distance/topology bridges, rescaling | chart components |
| `Volume` | normalized Riemannian volume, Borel and metric-measure coherence | chart, tangent-Jacobian, and polar Jacobians |
| `Connection` | `CovariantDerivative`, metric compatibility, torsion-free, `hessian`, function and tensor connection Laplacians | Christoffel computations |
| `Curvature.Model` | connection-free curvature sign/order model and regressions | none |
| `Curvature.Manifold` | field commutator and provisional selected-extension `(1,3)`/`(0,4)` subset | arbitrary-extension application, chart calculations, coordinate contractions |
| `Curvature.Tensoriality` | selected-extension pointwise tensorial and first-Bianchi subset | unreconciled metric pair symmetries and arbitrary-extension application |
| `Curvature.Sectional` | connection-free `IsAlgebraicCurvature`, Gram-normalized sectional curvature, and constant-curvature identities | geometric witness discharge; intrinsic quotient-of-planes API owned by `Curvature.Plane`; tangent facade owned by `Curvature.SectionalProvisional` |
| `Curvature.Plane` | intrinsic unoriented two-plane quotient, span characterization, and generator-independent sectional evaluators | geometric witness discharge and canonical orthonormal-basis choices |
| `Curvature.Operator` | connection-free second-exterior-power curvature operator and positivity interface | geometric witness discharge and canonical exterior-square metric choice; tangent facade owned by `Curvature.OperatorProvisional` |
| `Curvature.SectionalProvisional` | witness-gated tangent sectional quotient and plane results over `Provisional.curvature4` | selected-extension producer remains provisional |
| `Curvature.OperatorProvisional` | witness-gated tangent curvature operator and sectional positivity transfer | selected-extension producer remains provisional |
| `Models` | `constantCurvature`, Einstein consequences, `coneMetric`, cone curvature | model-specific coordinates |
| `Geodesic` | IVP/maximal domain, speed/energy, first variation, Hopf--Rinow adapters, `exp` | complete-only helpers |
| `Jacobi` | intrinsic fields, equation, existence/uniqueness, conjugacy, `dExp` bridge | chart pairs and frames |
| `IndexForm` | intrinsic index form, second variation, minimizer criterion | frame quadratic form |
| `Normal` | normal neighborhoods, Gauss lemma, cut time/locus, injectivity radius, polar volume | cut-time/frontier scaffolds |
| `Comparison` | model functions, SCC, Ricci comparison, `localDiffeo`, BG, `injvol`, `volinj` | density/radial hypotheses |
| `Ch01.lean` | stable umbrella imports and documented downstream API | no plumbing wildcard exports |

Compatibility aliases require a named downstream user and a removal trigger.
Names from Mathlib or an accepted shared dependency are used directly when
semantically equal; wrappers are deleted after migration rather than retained
as a second public vocabulary.

## Source-claim inventory

This is the normative completeness ledger.  An implementation PR closes a row
only when its public owner proves the source-strength claim and the named risk
gate.  A theorem in a private adapter, an analytic consumer with assumed
geometric inputs, or a green build does not close the row.  Pages are the
printed Chapter 1 pages in the checked arXiv v2 PDF; labels in parentheses are
the source's TeX labels.  `Open` means no repository declaration presently
claims the result.

| ID | Source claim and precise evidence | Public owner/API | Node | Hard prerequisites | Proof-risk gate | Status in this revision |
| --- | --- | --- | --- | --- | --- | --- |
| S01 | Metric, finite-dimensional existence under the source's standing manifold convention, smooth-path distance, and metric balls: Definition 1.1 and following paragraphs, p. 35; `morganTian2007` | `MetricExistence`: generic bundle existence and its tangent-bundle corollary; `Metric`: direct Mathlib metric and distance/topology/ball bridges | E1 + G2 | E1: topology-compatible `InnerProductSpace ℝ F`, `FiniteDimensional ℝ EB`, `SigmaCompactSpace B`, `T2Space B`, and the smooth bundle/manifold instances used by partition of unity; G2: pinned bundle metric and path-length APIs | derive the arbitrary finite-dimensional tangent-bundle corollary without a second metric representation or an arbitrary-Banach existence claim, and prove smooth and accepted piecewise-smooth path infima equal Mathlib's `C^1` infimum | **Complete.** `Ch01.MetricExistence.nonempty_contMDiffRiemannianMetric` proves generic smooth-vector-bundle existence from the exact E1 hypotheses, including positive definiteness, symmetry, existing-fiber topology compatibility, and smooth dependence; `nonempty_contMDiffRiemannianMetric_tangentSpace` separately derives the arbitrary finite-dimensional tangent result by transporting a Euclidean model form internally, with no public model `InnerProductSpace`. `Ch01.Metric` proves supplied-metric coherence; defines smooth and finite piecewise-smooth paths with canonical length; gives endpoint-preserving, length-controlled replacements of `C^1` paths; proves `smoothPathEDist = piecewiseSmoothPathEDist = riemannianEDist`; and constructs finite piecewise-smooth witnesses on preconnected manifolds without extra dimension, completeness, boundary, or separation assumptions. No other G2, F1, F2, or A2 status changes as a consequence of E1 |
| S02 | Levi--Civita existence and uniqueness: Theorem 1.2, pp. 35--36; `morganTian2007`; `doCarmo1992`, Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; `lee2018`, Thm. 5.10 and Cor. 5.11(b), equation (5.10), printed pp. 123--124 | `Connection.leviCivitaConnection` | G2 -> F1 | S01 and bundled `CovariantDerivative` producer | construct the connection from the metric and prove compatibility, torsion zero, Koszul, regularity, and uniqueness on the same field class | **Complete.** `Ch01.Connection` constructs Mathlib's exact bundled type and proves metric compatibility, zero torsion, the source-ordered Koszul formula, uniqueness for a differentiable field at a point and arbitrary tangent direction, and smooth `ContMDiffCovariantDerivative` regularity |
| S03 | Christoffel equation (1.1) (`Gamma`), p. 36; `morganTian2007` | `Connection.christoffel_formula` | F1 | S02 and chart differentiation | chart formula must be proved equivalent to the bundled connection; chart data stays private | **Complete.** `Ch01.Connection.Christoffel` identifies the chart coefficients of the exact canonical `leviCivitaConnection g` with the inverse-Gram contraction in equation (1.1) at an interior chart point; the local frame and metric components remain proof data |
| S04 | Hessian equation (1.2) and Lemma 1.3 (`Hessian`, `Hessformula`), pp. 36--37; `morganTian2007` | `Connection.hessian` and symmetry/tensor/coordinate lemmas | F1 | S02--S03 | align covector versus gradient conventions and prove tensoriality at the advertised regularity | Open |
| S05 | Function Laplacian and equation (1.4) (`laplacformula`), p. 37; `morganTian2007` | `Connection.laplacian` | F1 | S04 and finite-dimensional trace | preserve the source sign: nonnegative at a local minimum and nonpositive spectrum | Open |
| S06 | `(1,3)`/`(0,4)` curvature and coordinate formula: Definition 1.4, pp. 37--38; `morganTian2007` | `Curvature.Provisional.curvature`, `Curvature.Provisional.curvature4`; field commutator `Curvature.curvatureField` | F1 | S02--S03 | constant-curvature regression must verify argument order and the frozen sign convention; the selected-extension facade must be replaced at the intrinsic producer boundary | **Partial/provisional.** `Ch01.Curvature.Manifold` defines the field commutator from the exact bundled `leviCivitaConnection` and the source-ordered selected-extension `curvature4`, with first-pair skew and smooth-section regularity. `Curvature/Tensoriality.lean` adds pointwise additivity, scalar laws, and `TensorialAt` witnesses in all three `(1,3)` slots. The arbitrary smooth-extension application theorem, raw local-frame identification, Euclidean/nonconstant-metric coordinate regressions, and remaining geometric model checks are still open; no downstream consumer may treat `Curvature.Provisional` as canonical |
| S07 | Curvature symmetries and both Bianchi identities: Claim 1.5 (`Bianchi`), p. 38; `morganTian2007` | Current subset: `Curvature.Provisional.curvature_swap`, `Curvature.Provisional.curvature4_swap_first`, `Curvature.Provisional.curvature_tensorial_*`, `Curvature.Provisional.curvature_bianchi`, and `Curvature.Provisional.curvature4_bianchi`; target families `Curvature.symm`, `bianchi1`, `bianchi2` | F1 | S06 and tensor covariant derivative | permutations and second-derivative regularity must match the chosen `(0,4)` order | **Partial/provisional.** The first-pair skew law, the three-slot fiberwise tensorial additivity/scalar subset, and the selected-extension first Bianchi identity in both `(1,3)` and source-ordered `(0,4)` forms are exported (including `TensorialAt` witnesses). Metric last-pair skew, pair interchange, the arbitrary-extension application theorem, and the differential/second Bianchi identity remain open; no full symmetry or second-Bianchi completion is claimed |
| S08 | Sectional curvature, constant-curvature tensor identity, spherical/Euclidean/hyperbolic examples, and curvature operator: Definitions 1.6--1.7 and intervening model paragraph, pp. 38--39; `morganTian2007` | `Curvature.Sectional` (`sectionalCurvature`, `HasConstantCurvature`), `Curvature.Plane` (`SectionalPlane`, `sectionalCurvaturePlane`), and `Curvature.Operator` (`curvatureOperator`); direct-only `Curvature.SectionalProvisional` (`sectionalCurvatureAt`, `sectionalCurvatureAtPlane`, `IsAlgebraicCurvatureAt`) and `Curvature.OperatorProvisional` (`curvatureOperatorAt`); `Models.standardSpaceCurvature` | F1 -> F3 | S06--S07 and exterior-square API; F1 curvature API for F3 models | fix orthonormal-pair independence and wedge normalization before positivity claims; standard models are sign regressions, not assumed examples | **Partial intrinsic-plane/algebraic/operator boundary.** `Curvature.Sectional` proves the determinant-square change-of-generators law, the diagonal-to-full constant-curvature tensor equivalence in the frozen slot order, Gram normalization, symmetry, and degenerate behavior. `Curvature.Plane` now presents genuine unoriented two-planes as a quotient of independent ordered generators, proves quotient equality iff span equality, descends the span, and supplies inner-product and plain-bilinear sectional evaluators with representative and swap independence. `Curvature.Operator` constructs the symmetric bilinear form on Mathlib's `⋀[ℝ]^2`, proves decomposable-wedge evaluation, and transports nonnegative/positive operator bounds to sectional bounds. The direct-only tangent adapters in `Curvature.SectionalProvisional` and `Curvature.OperatorProvisional` consume the exact `Provisional.curvature4`; every plane or operator theorem retains an explicit `IsAlgebraicCurvatureAt` input until S07 proves metric last-pair skew/pair interchange, so these adapters are not a canonical producer replacement. Zero-, one-, and two-dimensional algebraic model regressions include full four-tensor and full operator zero results where applicable, plus a scaled component/slot-sign convention probe; an independent nonconstant-metric Levi--Civita regression remains open. Standard spherical/hyperbolic manifolds and the unconditional geometric producer witness remain open F3/F1 work. |
| S09 | Ricci and scalar curvature: Definition 1.8, p. 39; `morganTian2007` | `Curvature.ricci`, `scalarCurvature` | F1 | S06--S07, the F1 curvature API in S08, and finite-dimensional trace | contractions must reproduce the constant-curvature values with the frozen slot order | **Open geometric API.** The required second/fourth-slot algebraic contraction regression is proved in `Ch01.Curvature`, including dimensions zero and one; manifold Ricci and scalar curvature remain open |
| S10 | Pullback naturality of Riemann, Ricci, and scalar curvature: paragraph after Definition 1.8, p. 39; `morganTian2007` | `Curvature.curvature_naturality`, `ricci_naturality`, `scalarCurvature_naturality` | F1 | S02, S06, S09 and metric pullback | transport the canonical connection; no chart-isometry surrogate in the public theorem | Open |
| S11 | Contracted Bianchi identity: Lemma 1.9 (`divRic`), p. 39; `morganTian2007` | `Curvature.divRic` | F1 | S07, S09 and divergence | verify contraction order and `dR = 2 div Ric` with the source Laplacian/divergence signs | Open |
| S12 | Second covariant derivative and connection Laplacian for arbitrary-rank tensors: definitions before Lemma 1.10, pp. 39--40; `morganTian2007` | `Connection.secondCovariantDerivative`, `connectionLaplacian` | F1 | S02 and tensor-bundle contractions | theorem must be rank-generic; a one-form-only wrapper is insufficient | **Partial.** `Connection.TensorLaplacian` adds the raw rank-generic evaluation layer, scalar/one-form adapters, conditional finite-dimensional trace and frame theorems, a conditional outer-direction `TensorialAt` bridge, inner-direction add/smul laws with a `TensorialAt` packaging adapter, unconditional constant-scalar linearity in the tensor argument through the mixed derivative, source-ordered second derivative, and raw metric trace (with zero/neg normalization regressions), an identity-section cancellation regression, covariant Christoffel plus metric-dual compatibility bridges, and explicit tensor-slot locality lemmas. The latest slices also prove first-direction extension independence at a point and guarded trace sums for arbitrary differentiable frame extensions, including equality of two extension families with the same point values; `e04bd625f374f29aad6ec52cadb6afe86d343d01` adds the local-`MDiffAt` Leibniz/additivity contract for the inner direction, its conditional `TensorialAt` packaging, and a pointwise equality adapter. The provisional leaf is direct-only and absent from the stable `Ch01.lean` umbrella pending the S13 replacement trigger below. Smooth bundled tensor-section producer proofs, an unconditional second-direction contract, the full dual-frame component formula, canonical Hessian/trace compatibility, and flat/nonconstant model regressions remain open |
| S13 | One-form Bochner identity: Lemma 1.10 (`lapformula`), p. 40; `morganTian2007`; `gallotHulinLafontaine2004`, Prop. 4.36, p. 168, **unverified cross-check reported by Morgan--Tian** | `Curvature.bochnerFormula` | F1 | S05, S09, S12 | reconcile `df`, metric dual, Ricci contraction, and connection-Laplacian signs | Open |
| S14 | Space-form uniformization and quotient consequence: Theorem 1.11 and following paragraph, p. 40; `morganTian2007` | `Models.spaceFormClassification`, `spaceForm_quotient` or an explicit external theorem interface | F3 | S08, S19/F2 Hopf--Rinow interface, universal-cover/covering/isometry theory | retain completeness and simple connectivity in the classification, freeness/discreteness in the quotient, and add only the reviewed `2 <= n` non-vacuity gate | Open; human decision required if the classification proof exceeds Chapter 1 infrastructure |
| S15 | Einstein definition and dimension 2/3 consequence: Definition 1.12 and Example 1.13, p. 40; `morganTian2007` | `Models.einstein`, `einstein_constantCurvature_of_dim_le_three` | F3 | S08--S09 | state exact dimension alternatives and factor `lambda / (n - 1)` | Open |
| S16 | Open cone metric: Definition 1.14 (`conedefn`), p. 40; `morganTian2007` | `Models.coneMetric` | F3 | S01 and product-manifold metric | enforce positive radial coordinate and avoid a public coordinate-dependent metric | **Partial substrate.** `Models.Cone` defines the intrinsic positive radial subtype `Cone`, its smooth radius, and the pointwise form `coneForm` with positivity and symmetry. The bundled `ContMDiffRiemannianMetric` assembly and hom-bundle smoothness proof remain open: the pinned Mathlib API has no product/pullback bilinear-section constructor, so this slice does not claim `Models.coneMetric` or install a competing coordinate facade |
| S17 | Cone curvature block and eigenvalues: Proposition 1.15 (`conecurv`) and Corollary 1.16, pp. 40--41; `morganTian2007` | `Models.coneCurvature` (future geometric owner), `Models.coneCurvatureModel` (partial fixed-model consumer), `coneCurvatureEigenvalue` | F3 | S08, S16, S03 | verify exterior-square block order, zero multiplicity, and `s^-2 (lambda_i - 1)` scaling | **Partial algebraic block.** `Models.Cone` provides the abstract `Λ²(V × ℝ) ≃ₗ Λ²V × V` split, the zero mixed sector (the pure radial-radial wedge is vacuous), and the horizontal `s² (Rm_N - wedge² g_N)` consumer through the accepted S08 `Curvature.curvatureOperator`. The renamed `Models.coneCurvatureModel` is explicitly fixed-inner-product-space model data; `Models.coneCurvature` remains reserved for the source-strength geometric producer. The geometric cone Levi--Civita/curvature producer remains gated by S06/S07, and the requested eigenvalue/multiplicity scaling remains gated by a canonical exterior-square Riesz endomorphism. `coneCurvatureBlock` is a named wrapper with this model consumer as its sole current caller and is to be migrated to `coneWedgeBlockForm` when that producer lands; no competing operator or provisional geometric witness is introduced |
| S18 | Geodesic equation, coordinate ODE, IVP uniqueness/smoothness: Definition 1.17 and following paragraph, p. 41; `morganTian2007`; `doCarmo1992`, Ch. 3, pp. 61--75 | `Geodesic.isGeodesic`, intrinsic IVP/maximal solution | F2 | S02; `[CompleteSpace E]` for the checked ODE API; `[BoundarylessManifold I M]` for the all-initial-data contract, or `I.IsInteriorPoint p` for a point-local IVP | prove chart ODE/intrinsic equivalence, interval maximality, and smooth dependence; export the weakest manifold-level/interior-point hypothesis rather than `[I.Boundaryless]`; a pointwise equation is insufficient | **Partial.** The local chart spray and fixed-chart spray/equation equivalence, private chart-local tangent-bundle lift under `[BoundarylessManifold I M]`, canonical-connection bridge, point-local and boundaryless IVP, local state uniqueness, restriction lemma, witness/choice maximal-domain substrate, conditional overlap-agreement API, explicit global-witness unbounded-lifetime corollary, initial-time intrinsic bridge, zero-velocity uniqueness plus canonical Euclidean zero-velocity regressions, and the chart-overlap kinematic bridge (source membership, smooth/full and second Frechet transition derivatives, chart-reading chain rule, tangent-velocity transport, and the applied second-order chain rule for `D²τ(u')u' + Dτ(u'')`) are present. The compatible-family slice now also proves eventual-equality congruence for the local equation, continuity and chart smoothness of the canonical union representative, and a conditional bundled maximal-solution constructor. `HasChristoffelTransitionAt` now records the exact remaining metric transition identity, while conditional acceleration/equation transfer and a boundaryless local `GeodesicSolution` constructor consume that contract with explicit eventual regularity hypotheses. The constant zero-velocity curve supplies a genuine global `GeodesicSolution` witness and an all-time maximal-domain/unbounded-lifetime regression. The canonical Euclidean model now also has a proved zero-coefficient theorem, arbitrary-velocity zero contraction, affine straight-line coordinate-acceleration regression for the flat branch, and a source-facing affine geodesic predicate plus global bundled affine witness for arbitrary Euclidean initial velocity. The private nonconstant one-dimensional fixture now includes an equation-level sign probe: at `u(0)=1`, `u'(0)=1`, and `u''(0)=1/2`, the reversed residual vanishes while the canonical residual is nonzero. The metric Christoffel transformation law, unconditional canonical gluing/maximal solution and arbitrary-initial-data nonempty witness theorem, smooth manifold-valued maximal curve, and joint smooth initial-data dependence remain open; this slice is `Part of #34`. |
| S19 | On a complete boundaryless manifold, minimizing geodesics and the Hopf--Rinow implication: paragraph before and Theorem 1.18, pp. 41--42; `morganTian2007`; `doCarmo1992`, Ch. 7, pp. 157--166; `lee2018`, Thm. 6.19 | `Geodesic.exists_minimizingGeodesic`, `hopfRinow` | F2 | S01, metric completeness, and the all-initial-data `[BoundarylessManifold I M]` branch of S18 | keep metric completeness and boundarylessness as independent public assumptions, and connect them to the canonical maximal geodesic and minimizer existence, with connected-component assumptions explicit | Open; the rejected dependency's facade is not evidence |
| S20 | Energy, first variation, criticality, constant speed, and energy/length inequalities: pp. 41--43; `morganTian2007`; `doCarmo1992`, Ch. 9, pp. 185--201 | `Geodesic.energy`, `Geodesic.Variation.firstEnergyVariation` | F2 | S01--S02 and S18 | exact path/variation regularity, endpoint terms, and equality conditions must remain visible | **Partial.** `Ch01.Geodesic.Variation` exports the canonical bundle-metric energy and contains a concrete affine-line Euclidean velocity/squared-speed/energy regression, the real speed integral and its direct `Manifold.pathELength` bridge, interval Cauchy--Schwarz with both a.e. and continuous pointwise constant-speed equality forms, interval additivity, positive affine reparameterization density/composition contracts, constant-speed/zero-velocity/sign regressions, a smooth two-parameter variation structure, the full endpoint first-variation formula with closed-interval continuity and interior-derivative witnesses, and genuine `HasDerivAt` fixed-endpoint criticality together with a one-way zero-acceleration implication under explicit `FirstVariationData`. The converse from universal fixed-endpoint criticality is intentionally deferred: the current variation-local acceleration field is not identified with the single curve-level S18 acceleration, and no per-variation test-field witness or criticality equivalence is exported. The S18 producer still discharges the covariant-acceleration and intrinsic-geodesic bridge; minimizer notions remain with S19. |
| S21 | Geodesic variations, Jacobi equation, and initial-data uniqueness: pp. 43--44; `morganTian2007`; `doCarmo1992`, Ch. 5, pp. 101--121 | `Jacobi.JacobiField`, variation bridge, existence/uniqueness | J1 | F1 and F2 | intrinsic equation `D^2 J + R J V V = 0` must agree with chart/frame adapters and frozen curvature order | Open |
| S22 | Conjugate point: Definition 1.19, p. 44; `morganTian2007` | `Jacobi.IsConjugate` | J1 | S21 | quantify a nonzero intrinsic field vanishing at the initial and target endpoints | Open |
| S23 | Full second variation, boundary term, bilinear form, and endpoint-fixed index form: pp. 43--45; `morganTian2007`; `doCarmo1992`, Ch. 9, pp. 185--201; `lee2018`, Thm. 10.22 and Prop. 10.24 | `IndexForm.indexForm`, `secondVariation` | V1 | S20--S21 | select and prove sufficient regularity for arbitrary families; do not silently drop the free-end boundary term | Open |
| S24 | Unique minimizing subsegments and no interior conjugate point: Proposition 1.20 (`jacmin`), pp. 44--45; `morganTian2007`; `petersen2006`, Ch. 5, Prop. 19 and Lemma 14, pp. 139--140 | `IndexForm.minimizer_no_conjugate` | V1 | S22--S23 | justify corner shortening and piecewise-field smoothing rather than formalizing the source sketch as an axiom | Open |
| S25 | Index-form null space equals endpoint-vanishing Jacobi fields: Claim 1.21, p. 44; `morganTian2007` | `IndexForm.nullspace_iff_jacobi` | V1 | S21 and S23 | supply the fundamental-lemma/density argument at the selected field regularity | Open |
| S26 | Exponential map on the maximal star domain and complete case: Definition 1.22, p. 45; `morganTian2007`; `doCarmo1992`, Ch. 3, pp. 61--75 | `Geodesic.exp`, `expDomain` | F2 | S18; S19 only for the complete case; `I.IsInteriorPoint p` at a fixed base point, or `[BoundarylessManifold I M]` for the source-facing all-base-points family | codomain/domain must retain the incomplete and unbounded cases; state the base-point interior hypothesis on local maps and the weakest manifold-level class on the global family; complete-only helpers are private | Open |
| S27 | Normal-neighborhood/Gaussian coordinates, surjectivity when complete, differential of `exp` via Jacobi fields, and local diffeomorphism: paragraphs after Definition 1.22 and Corollary 1.23 (`star`), pp. 45--46; `morganTian2007` | `Normal.normalNeighborhood`, `Jacobi.dExp_eq_endpoint`, `Geodesic.exp_localDiffeomorph` | J1 -> N1 | S19, S21--S22, and S24--S26; `I.IsInteriorPoint p` for point-local conclusions, or `[BoundarylessManifold I M]` for the all-points/complete conclusions | prove the J1 kernel/conjugacy bridge before N1 invokes the inverse function theorem; propagate the exact interior/boundaryless contract and distinguish the local normal ball from the maximal/complete domain | Open |
| S28 | On a complete boundaryless manifold, regular minimizing domain, closed/null cut locus, and exponential diffeomorphism: the complete-manifold scope sentence before Definition 1.24 and Definition 1.24/Proposition 1.25, p. 46; `morganTian2007`; `petersen2006`, Ch. 5, Lemma 12, p. 133 and Prop. 19, p. 139 | `Normal.cutLocus`, `exp_on_regularDomain` | N1 | S19 completeness/Hopf--Rinow and `[BoundarylessManifold I M]`, F2, J1, V1, and A2's pre-N1 Sard/change-of-variables and measurability primitives | state completeness and the weakest manifold-level no-boundary class on the global theorem while keeping local exp-domain/cut-time definitions point-local under the required interior hypotheses; prove measurability/nullity using checked Sard/change-of-variables APIs, with no assumed-null facade | Open |
| S29 | On a complete boundaryless manifold, injectivity radius, frontier/cut-distance equalities, and broken-geodesic/conjugate alternative: Definition 1.26 and following paragraph under the complete-manifold scope, p. 46; `morganTian2007` | `Normal.injectivityRadius`, equivalence theorems | N1 | S19 and S28, including `[BoundarylessManifold I M]` for the global equivalences | retain infinity, keep completeness separate from boundarylessness, and prove all three characterizations plus the alternative; local injectivity-radius/exp-domain definitions are point-local under their exact interior hypotheses | Open |
| S30 | Gaussian metric expansion through `O(r^5)`: equation (1.5) (`metricexp`), p. 46; `morganTian2007`; `sakai1996`, Prop. 3.1, p. 41, **cross-check unavailable locally** | `Normal.metricExpansion` | N2 | S03, S06--S09, and S27; hence the completed F1 curvature and N1 normal-neighborhood APIs | audit every coefficient, derivative order, remainder, and Sakai-to-Morgan--Tian sign conversion | Open |
| S31 | Gauss lemma, polar metric, and polar volume element: p. 47; `morganTian2007`; `petersen2006`, Ch. 5, Lemma 12, p. 133 | `Normal.gaussLemma`, `Normal.polarMetric`, `Volume.polarJacobian` | N2 | S26--S28, A2's measure/change-of-variables primitives, and canonical measure | prove the post-N1 Jacobian/change-of-variables equality with `riemannianVolume`; coordinate density is private | **Partial substrate only.** `Ch01.Volume` fixes normalized measure; no polar producer is present |
| S32 | Coordinate Laplacian formula: Lemma 1.27, p. 47; `morganTian2007` | `Normal.laplacianGaussian` | N2 | S05 and S30 | determinant-density formula must agree with the Hessian-trace sign | Open |
| S33 | Local distance-Laplacian expansion and following mean-curvature/shape-operator identification, p. 48; `morganTian2007`; `petersen2006`, pp. 265--268 | `Normal.laplacianDistance_asymptotic`, `radialShape_eq_hessian`, `trace_radialShape` | N2 | S30--S32 | prove `Delta r = (n-1)/r - (r/3) Ric(v,v) + O(r^2)` with exact coefficient/remainder and identify the Hessian and mean-curvature traces | Open |
| S34 | Calabi distributional inequality and test-function formulation: Exercise 1.28 and Remark 1.29 (`calabi`), p. 48; `morganTian2007`; `petersen2006`, Lemma 42, p. 284 | `Comparison.laplacianDistance_weak` | C2 | F1, N2 including S31, and distribution/test-function integration | add `2 <= n` only here; prove Lipschitz/Sobolev and integration-by-parts semantics | Open |
| S35 | Flat/hyperbolic `sn_k`, `ct_k`, ODE, and radial coefficient: Definition 1.30 and following formulas, pp. 48--49; `morganTian2007`; `petersen2006`, Ch. 9, Sec. 1 | `Comparison.Model` plus Riccati/trace/determinant consumers | A1 | G0 and scalar/linear analysis | totalize `k = 0` without division by `sqrt 0`; analytic theorems may not claim a manifold producer | **Analytic layer implemented.** Model, scalar/vector Sturm, operator/trace Riccati, determinant, `normDet`, and abstract density results exist; geometric producers remain open |
| S36 | Positive-curvature model needed by the upper analogue: unnumbered paragraph before Lemma 1.32, p. 49; `morganTian2007`; `petersen2016`, Sec. 6.4, Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257 | `Comparison.snPos`, `logDerivPos`, positive Riccati/Sturm/density consumers | A1 | scalar and finite-dimensional operator analysis | restrict to `K > 0` and the first-pole interval; separate analytic inputs from C1 geometry | **Analytic layer implemented.** Origin limits, first pole, scalar/vector Sturm and no-zero comparison, operator comparison, and abstract density results exist; no Jacobi, conjugacy, or geometric lower-Jacobian producer exists |
| S37 | Lower sectional-curvature comparison (`SCC`): Theorem 1.31, p. 49; `morganTian2007`; `petersen2006`, Ch. 9, Sec. 1; `lee2018`, Thm. 11.7(b) | `Comparison.sectional` | C1 | A1, J1, and N2 | translate sectional bounds to the Jacobi/Riccati order and prove shape and angular-metric inequalities on the regular segment | Open |
| S38 | Upper sectional analogue: paragraph before Lemma 1.32, p. 49; `morganTian2007`; `petersen2006`, Ch. 9, Sec. 1; `petersen2016`, Thms. 6.4.3/6.4.6, pp. 255--257; `lee2018`, Thm. 11.7(a) | `Comparison.sectional_upper` | C1 | A1 positive model, J1, and N2 | on `0 < r < min (r0, pi/sqrt K)`, prove lower Hessian, angular metric, and normalized Jacobian with the accepted inequality directions | Open; required by S42 |
| S39 | On a complete boundaryless manifold, curvature-norm local diffeomorphism: Lemma 1.32 (`localdiffeo`) under the complete-manifold scope, p. 49; `morganTian2007` | `Comparison.exp_localDiffeomorph_of_curvatureBound` | C1 | S19, S27, and S36--S38, including `[BoundarylessManifold I M]` | use boundarylessness together with completeness to put the full tangent ball in the exponential domain, including the infinite radius at `K = 0`; check norm-to-sectional conversion and exact source domain/codomain while leaving point-local comparison results on their actual exp domains | Open |
| S40 | Ricci comparison (`riccurvcomp`): Theorem 1.33, p. 49; `morganTian2007`; `petersen2006`, Ch. 9, Sec. 1 | `Comparison.ricci` | C2 | A1, F1, J1, and N2 | connect trace Riccati to the actual radial shape and normalized polar Jacobian | Open; only assumed-producer analytic consumers exist |
| S41 | Relative Bishop--Gromov comparison: Theorem 1.34 (`BishopGromov`), p. 49; `morganTian2007`; `cheegerGromovTaylor1982`, Prop. 4.1; `lee2018`, Thm. 11.19 | `Comparison.bishopGromov` | C3 | A2, C2, N1 | preserve compact-closure/local Ricci hypotheses, cut-locus nullity, metric-ball identity, and limit-one normalization | Open; canonical volume exists but no geometric ratio theorem does |
| S42 | Injectivity-to-volume estimate (`injvol`): Proposition 1.35, p. 50; `morganTian2007` | `Comparison.volume_lower_of_inj` | L1 | C1 including S38, C3, N1 | retain completeness, curvature norm, and dependence `delta(n, epsilon)`; normalize with `r^-2 g`, correcting the source proof's `r^2 g` typo without changing the theorem | Open |
| S43 | Volume-to-injectivity estimate (`volinj`): Theorem 1.36, p. 50; `morganTian2007`; `cheegerGromovTaylor1982`, Thm. 4.3 and (4.22), p. 46; `cheegerEbin1975`, Thm. 5.8, p. 96, **alternative unavailable locally** | `Comparison.inj_lower_of_volume` | L1 | C3, N1, local covering/compactness package | retain source hypotheses, scale, and `delta(n, epsilon)`; human decides whether the proof package is in-project or a separately reviewed dependency | Open; human depth gate remains |

The ledger ends at Morgan--Tian Theorem 1.36, immediately before Chapter 2 in
`prelim.tex`.  No row may import Chapter 2 or 3.  Source prose that supports a
row, such as constant-speed consequences in S20 or cut-locus nullity in S28,
is part of that row's contract rather than an optional remark.

## Source corrections and degenerate cases

The source formulas at the comparison boundary need explicit total definitions
before they become Lean APIs:

- For `k >= 0`, retain `sn_k(0) = 0` and `sn_k(r) = r` in the flat branch, and
  retain the positive-`k` hyperbolic formula and signs.  The radial comparison
  coefficient, for `r > 0`, is defined piecewise as
  `sn'_k(r) / sn_k(r) = 1 / r` when `k = 0` and
  `sqrt k * ct_k(r)` when `k > 0`.  Thus `ct_k` is not implemented by a total
  Lean division at `k = 0`; the displayed source expression is recorded as a
  `k > 0` formula with its flat branch supplied separately.
- For the distinct positive-curvature branch with `K > 0`, A1 defines
  `snPos K r = sin (sqrt K * r) / sqrt K` and
  `logDerivPos K r = (snPos K)' r / snPos K r =
  sqrt K * cot (sqrt K * r)`.  It proves the normalized ODE
  `phi'' + K * phi = 0`, `phi 0 = 0`, `phi' 0 = 1`, the small-radius facts
  `snPos K r / r -> 1` and `r * logDerivPos K r -> 1`, positivity on the first
  interval `0 < r < pi / sqrt K`, and the first positive zero at
  `pi / sqrt K`.  On each regular polar segment, C1 must consume these A1
  facts in `Comparison.sectional_upper` only for
  `0 < r < min (r_0, pi / sqrt K)` and state the lower bounds
  `(snPos' K r / snPos K r) * g_r <= Hess r`,
  `snPos K r ^ 2 * g_S <= g_r`, and
  `snPos K r ^ (n - 1) <= J(r, theta)` for the normalized polar Jacobian.
  The hyperbolic lower-curvature family above remains unchanged.
- Under S39's complete-and-`[BoundarylessManifold I M]` hypotheses, the radius
  in `localdiffeo` is an extended radius: it is unbounded when `K = 0` and is
  `pi / sqrt K` when `K > 0`.  Boundarylessness supplies the all-initial-data
  IVP contract and completeness supplies its global extension, together giving
  the full exponential domain needed for that conclusion.  Point-local
  comparison statements remain restricted to their actual exp domains and
  exact interior hypotheses.  The formal statement must not obtain a spurious
  zero radius from total division by `sqrt 0`.
- The printed Theorem 1.11 has no dimension hypothesis.  The formal
  classification contract adds `2 <= n` (or an equivalent non-vacuity
  assumption), because the constant-curvature tensor identity is vacuous in
  dimension one and the line would otherwise satisfy the premise while
  contradicting the positive-curvature conclusion.  This correction is local
  to the classification theorem and is not propagated to unrelated claims.
- The all-manifold distributional form of the weak Calabi inequality also
  requires `2 <= n`, locally in `Comparison.laplacianDistance_weak`.  In
  dimension one, `f(x) = |x|` on `Real` has distributional Laplacian
  `2 * delta_0`, while `(n - 1) / f` vanishes almost everywhere.  This gate is
  not imposed on `Normal.laplacianDistance_asymptotic` or any unrelated claim.
- In the proof of Proposition 1.35, the printed instruction to replace `g` by
  `r^2 g` cannot make a radius-`r` ball into a radius-one ball.  The normalized
  metric is `r^-2 g`: distances scale by `r^-1`, curvature norms by `r^2`, and
  volume by `r^-n`.  L1 must prove and use those scaling identities.  This is
  an evidence-level-3 correction to the proof text only; the stated `injvol`
  theorem and its `delta(n, epsilon)` dependence are unchanged.

## Milestone DAG

Each node is a focused, reviewable PR.  A node is complete only when its public
statements, proofs, documentation, imports, and source anchors pass review.

```text
G0 --> G1 --> G2
 |              |--> F1
 |              |--> F2
 |              `--> A2
 |--> A1
 `--> E1

F1 + F2                       --> F3
F1 + F2                       --> J1 --> V1
F2 + A2 + J1 + V1            --> N1
F1 + A2 + N1                 --> N2
A1 + J1 + N2                 --> C1
A1 + F1 + J1 + N2            --> C2
A2 + C2 + N1                 --> C3
C1 + C3 + N1                 --> L1
G0 + G1 + G2 + E1 + F1 + F2 + F3 + A1 + A2 + J1 + V1 + N1 + N2 + C1 + C2 + C3 + L1
                               --> Z1
```

The frontiers are intentional: A1 and E1 start directly after G0 and run in
parallel with G1 and the human-gated substrate route.  E1 proves only
finite-dimensional existence of a smooth metric; it does not block work
carried out with a supplied metric and is not an additional G2 coherence gate.
At G2 completion head `07d2a0be1a7aa3e38d827756b6585edb5a2ade60`, F1, F2,
and the normal-geometry-independent A2 measure primitives became unlocked to
run in parallel while A1 may continue.  F3 waits for both F1 and F2 because S14
consumes Hopf--Rinow, then joins Z1 independently of the normal/comparison
branch.  J1 waits only for F1/F2 and V1 waits for J1.  N1 waits for
F2/A2/J1/V1 so S28 can prove cut-locus nullity from completed measure primitives.
N2 then waits for F1/A2/N1 and closes the post-cut polar and Gaussian rows
S30--S33.  C1 and C2 run in parallel only after N2, with their listed analytic,
foundation, and Jacobi inputs.  C3 waits for A2/C2/N1, not C1.  L1 waits for
C1/C3/N1, and Z1 waits for every prior node and therefore every inventory row,
including E1, F3, and N2.

Node contracts:

- **G0**: this roadmap, bibliography, package, toolchain, manifest, root
  module, and workflow. No mathematical implementation.
- **E1** (`G0`, complete): `Ch01.MetricExistence` proves the
  partition-of-unity bundle theorem for a
  topology-compatible model-fiber `InnerProductSpace ℝ F`, a
  `FiniteDimensional ℝ EB` base model, and `SigmaCompactSpace B` and
  `T2Space B`, with the required chart, smooth-manifold, and smooth-vector-bundle
  instances.  Its distinct tangent-bundle theorem derives the source-strength
  corollary for an arbitrary finite-dimensional manifold by transporting a
  Euclidean inner product through a continuous linear equivalence internal to
  the proof.  This discharges the source's
  finite-dimensional existence paragraph without changing the explicit metric
  parameter or generality of the supplied-metric geometric theorems.
- **G1** (`G0`): close the table above with current Mathlib and candidate dependency
  signatures, import graph, and exact source anchors.
- **G2** (`G1`, human gate; complete at
  `07d2a0be1a7aa3e38d827756b6585edb5a2ade60`): first merge the repository-owned
  substrate selection in `docs/G2_SUBSTRATE_DECISION.md`; then implement and
  prove its metric/distance/measure and connection bridges, audit assumptions,
  and freeze curvature signs.  The exhaustive G2-owned checklist is metric
  data, smooth/continuous bundle coherence, distance/topology including the
  source-facing infimum equalities, normalized measure/volume, the bundled
  Levi--Civita producer and regularity, and the algebraic curvature sign/order
  kernel.  `Ch01.Metric`, `Ch01.Volume`, `Ch01.Connection`, and
  `Ch01.Curvature.Model` implement those six families and are imported by the
  Chapter 1 umbrella.  The later `Curvature.Manifold` layer is an explicitly
  provisional F1 consumer and does not alter the completed G2 kernel.  The
  ledger's geodesic-equation row is a post-gate F2 handoff:
  making it a G2 prerequisite would create the cycle `G2 -> F2 -> G2`.
  Therefore F1, F2, and A2 are unlocked.  The algebraic kernel still makes no
  manifold-curvature claim.
- **F1** (`G2`): connection, Hessian/function and tensor connection
  Laplacians, curvature, Bianchi, Ricci/scalar, divergence/Bochner,
  naturality, and rescaling.
- **F2** (`G2`): intrinsic geodesic IVP, speed/energy/first variation, Hopf--Rinow,
  maximal exponential domain, zero differential, and minimizing neighborhoods.
  Its point-local IVP and exponential theorems take `I.IsInteriorPoint p`; its
  source-facing all-initial-data and all-base-points contracts take the weaker
  `[BoundarylessManifold I M]`, not the stronger `[I.Boundaryless]` from the G2
  assumption table.  Completeness is added separately only for Hopf--Rinow and
  global extension; none of these hypotheses is added to G2 supplied-metric,
  measure, or connection contracts.
- **F3** (`F1`, `F2`): space-form classification and quotient consequences,
  Einstein consequences, and cone metric/curvature.  Its F2 edge is required by
  S14's Hopf--Rinow input; it owns no post-N1 normal-coordinate claim.
- **A1** (`G0`): hyperbolic/flat `sn`/`ct`, the positive-curvature `snPos` and
  logarithmic derivative with validity/first-zero facts, scalar/vector/operator
  Sturm and Riccati comparison, determinant/trace inequalities, and
  small-radius asymptotics independently of unproduced manifold data.  The
  scalar positive-curvature interface is implemented at
  `e874c4c7b6126984488c487cbb78077828233457`; the operator Riccati upper/lower
  interface is implemented at `cc1ad4e3d445dee8878b760182b07375a15571b9`.
  The finite-dimensional trace
  Cauchy--Schwarz/Riccati layer, basis-free logarithmic absolute-determinant
  formula, canonical inner-product `normDet` consequences, and
  direction-generic normalized positive-density adapters are implemented by
  issue #10.  Issue #11 adds the basis-free vector Sturm comparison and its
  positive-slope no-zero analytic corollary.  The
  positive-curvature geometric lower-Jacobian conclusion remains gated on the
  C1/J1/N2 producers and is not claimed by A1.
- **A2** (`G2`): the pre-N1 measure toolkit: chart Jacobians, checked
  Sard/change-of-variables and measurability primitives, sphere/radial
  integration, and ratio-of-integrals lemmas independent of cut, exponential,
  or polar geometry.  The focused `Ch01.Volume.ChangeOfVariables` slice proves
  smooth positive chart Gram densities in an inner-product model, while its
  chart-set, transition, null-transport, and normalized-Euclidean Jacobian
  layer is stated over the accepted arbitrary finite-dimensional real normed
  model, with only a C¹ manifold assumption where tangent derivatives are
  used.  It uses Mathlib's `LinearMap.normDet` and determinant APIs directly.
  The same direct leaf contains a provisional tangent-space
  `riemannianJacobian`/`chartCoordinateJacobian` adapter: its intrinsic value is
  a source-dimensional tangent-fibre area factor, not a path-metric volume
  density or a competing global Jacobian.  This leaf is intentionally not
  exported by the stable `Ch01.lean` umbrella.  Its first named downstream
  consumer is the N1 `Normal.cutLocus`/`exp_on_regularDomain` nullity proof;
  when that consumer lands, retain the adapter only if that proof needs the
  intrinsic tangent factor, and otherwise migrate to Mathlib's `normDet` and
  delete the compatibility wrappers.  The slice does not yet identify
  `riemannianVolume` with the chart-density integral: the pinned Mathlib API
  has no Hausdorff-volume/chart-density bridge, and no assumption-backed
  replacement or second global measure is introduced.  That bridge and the
  sphere/radial and ratio-of-integrals toolkit remain open A2 work.  A2
  supplies S28 nullity but owns no post-N1 polar-density equality; that work is
  N2.
- **J1** (`F1`, `F2`): intrinsic Jacobi equation, existence/uniqueness/linearity, chart and
  frame reductions, geodesic variations, and `d exp`.
- **V1** (`J1`): exact regularity for arbitrary-family first/second variation,
  intrinsic/frame index equality, fundamental lemma, negative directions, and
  the minimizer/no-conjugate theorem.
- **N1** (`F2`, `A2`, `J1`, `V1`): close S27--S29: point-local normal
  neighborhoods, segment/exp-domain and cut-time definitions under their exact
  interior hypotheses; then, under completeness and
  `[BoundarylessManifold I M]`, cut-locus nullity, injectivity-radius
  equivalences, and exponential diffeomorphism.  N1 consumes A2's completed
  measure primitives but does not produce polar integration or Gaussian
  expansions.
- **N2** (`F1`, `A2`, `N1`): close S30--S33 after their curvature,
  normal-neighborhood, cut, and measure inputs exist: Gaussian metric expansion,
  Gauss lemma, polar metric and volume/Jacobian equality, coordinate Laplacian,
  local distance-Laplacian expansion, and radial shape/trace identifications.
- **C1** (`A1`, `J1`, `N2`): the lower-bound SCC statement, its unnumbered
  upper-sectional-bound analogue, and the complete-and-boundaryless
  `localdiffeo` consequence without an extra curvature hypothesis.  On a
  regular polar segment, the upper comparison consumes A1's positive-curvature
  model only for
  `0 < r < min (r_0, pi / sqrt K)` and gives the lower shape, angular-metric,
  and normalized-Jacobian directions stated in `Comparison.sectional_upper`.
  It is required by the lower sphere-volume estimate in `injvol`.
- **C2** (`A1`, `F1`, `J1`, `N2`): radial Jacobi matrix and trace/determinant
  comparison producing the manifold `riccurvcomp` theorem, plus the resulting
  weak/distributional Calabi inequality rather than merely a producer-shaped
  inequality.  The `2 <= n` gate applies only to the global all-manifold weak
  theorem, not to the local distance-Laplacian asymptotic.
- **C3** (`A2`, `C2`, `N1`): identify polar density and metric-ball volume, handle cut locus and
  compact-closure hypotheses, prove monotonicity and the limit-one statement.
- **L1** (`C1`, `C3`, `N1`): exact `injvol` and the deeper `volinj`; it explicitly waits for C1's
  upper sectional comparison as well as C3/N1.  Split `volinj` if its
  compactness/covering layer is a separate reviewable boundary.
- **Z1** (all prior nodes): stable root API,
  source-fidelity/axiom/`sorry`/import/doc/citation audits, and downstream
  Chapter 1 interface checks.  In particular, F3- and N2-owned rows cannot
  bypass Z1.

## Dependency alternatives and hard gates

The exact ten-criterion comparison and answers to the eight reserved G1
questions are in `docs/G2_SUBSTRATE_DECISION.md`.  The four route dispositions
are:

1. **Reviewed Git dependency: rejected at this gate.** Candidate main
   `60c3e1f` remains unlicensed, and its partial producers would not remove the
   connection, measure, or maximal-geodesic work.
2. **Scoped extraction: rejected at this gate.** The same missing software
   license blocks copying or adaptation from the forge candidate.  A
   differently licensed reference tree is not the audited candidate revision.
3. **Mathlib-native construction: selected.** Keep Mathlib
   `520045ab14e26149ee970e2e617ca04b09bde5d6` as the only external geometric
   substrate, use its bundle metric, induced distance, Euclidean-normalized
   Hausdorff measure, and bundled `CovariantDerivative` types directly, and own
   the missing producers in focused Chapter 1 modules.
4. **Wait for upstream: rejected at this gate.** PR #36845, PR #36036, and PR
   #33714 remain unmerged, use later toolchains, and do not jointly supply the
   complete kernel.  A named merged immutable revision can trigger migration,
   but an open head is prior art rather than pinned API.

The route decision is reproducible from this matrix; a future proposal must
update every row, not merely show a compiling import.

| Criterion | Reviewed Git dependency | Licensed/scoped extraction | Mathlib-native construction | Wait for upstream |
| --- | --- | --- | --- | --- |
| Legal provenance | **Fails:** candidate main `60c3e1f` has no reviewed software license | **Fails:** copying/adaptation has the same license defect | **Passes:** pinned Mathlib is Apache-2.0 and repository code has direct provenance | License is plausible for Mathlib PRs, but unmerged code is not an available dependency |
| Immutable pin and reproducibility | Commit exists, but is legally unusable and adds another package | An immutable source could be recorded only after a licensed revision exists | Existing Lake manifest pins `520045ab`; no new package or toolchain is needed | No merged revision exists to pin; current heads are evidence only |
| Public API coherence | Candidate metric alias and coordinate connection vocabulary require adapters | Renaming copied APIs creates project-owned duplicate vocabulary | Direct bundle metric, induced distance/measure, and `CovariantDerivative` types satisfy the one-representation rule | Could improve after merge, but current proposals do not supply one coherent kernel |
| Transitive imports | Focused imports may be possible; candidate umbrella brings all audited subordinate modules | Each copied import and later rebase becomes local maintenance | Focused imports only, with no sibling/reference path | Future import graph is unknown; inspected WIP changes are broad |
| Proof-hole/axiom inventory | Candidate source scan is clean, but required producer proofs are absent | Final audit cannot begin before legal extraction is possible | Selected exported APIs have no consumed holes; local exports receive axiom/`sorry` audits, and the unused upstream `proof_wanted` is disclosed in the G2 record | One inspected WIP contains holes; the others do not cover the required producers |
| Maintenance ownership | External repository, local bridges, and coordinated version updates | Full ownership of copied code, attribution, adapters, and deletion | Full ownership only of Chapter 1's missing producers against one pin | Defers work; later repinning and migration remain project work |
| Source coverage | Partial metric/distance and pointwise geodesic prior art; no normalized volume, bundled connection producer, or complete geometric kernel | Same bounded coverage after any legal gate | Coverage gaps are explicit as S01--S43 and assigned to focused nodes | No inspected proposal jointly covers metric, distance, measure, connection regularity, curvature, geodesics, and comparison |

The Git and extraction routes fail the legal gate.  Waiting fails the progress
and reproducibility gates.  The selected route has the largest known local
proof burden, but it is the only route whose legal input, immutable pin, public
representations, imports, and remaining coverage can all be reviewed now.

A human route decision is reopened only by one of two evidence packages: (a) a
merged candidate commit with a reviewed software license/provenance record,
focused import graph, exported-proof inventory, and source/API coverage audit;
or (b) a merged immutable Mathlib revision, compatible with the current
toolchain or an approved repin, that supplies a semantically equivalent metric,
connection, geodesic, or comparison producer with the required regularity.  The
decision PR must rerun the matrix, name migration/deletion work, and identify
the exact S-rows improved.  An open PR, draft license, or successful experiment
does not meet this threshold.  Separately, S14 and S43 retain their explicit
human depth decisions because an external classification or covering package
could exceed a reviewable Chapter 1 node even under the selected route.

Hard gates are recorded in the decision:

- one canonical metric/distance/measure representation and proved coherence;
- curvature sign/order checked by a constant-curvature example at chart,
  Jacobi, index, sectional, and Ricci boundaries;
- finite dimension, dimension lower bounds (including local `2 <= n` gates for
  the uniformization classification and the all-manifold weak Calabi theorem),
  the pointwise `I.IsInteriorPoint p` or manifold-level
  `[BoundarylessManifold I M]` contract, Hausdorffness, sigma compactness,
  connectedness, and completeness introduced only where source proofs require
  them; the stronger `[I.Boundaryless]` is not substituted at a public boundary,
  and any other stronger public hypothesis needs approval;
- arbitrary variation regularity chosen against a chart-local adapter without
  weakening second variation;
- cut-locus measurability/nullity proved using checked measure/Sard/change of
  variables APIs, never an assumed-null predicate;
- `metricexp` checked term by term against Sakai and its sign warning resolved;
- `volinj` retained at source strength, with a human scope decision if its
  covering/compactness theory is project-scale;
- every Lean/Mathlib/shared revision gets a compatibility, namespace,
  signature, instance, axiom, and source-fidelity audit.

The selected route was accepted through human review and merge at
`aa45255fc76b3de3870f6411dde9b1c733e39074`.  The curvature sign/order kernel
and bundled connection producer/regularity were merged before the final
supplied-metric smooth/piecewise-smooth distance correspondence.  Accepted head
`07d2a0be1a7aa3e38d827756b6585edb5a2ade60` is the first head containing every
G2-owned family, so it completes G2 and unlocks F1, F2, and A2.  The intrinsic
geodesic equation remains pending in F2; it is downstream work, not completion
debt on its own prerequisite.

## Provisional debt and replacement triggers

| Provisional construction | Permitted use and cost | Replacement trigger |
| --- | --- | --- |
| Chart-coordinate `(J,DJ)` pairs, state-transition flows, chart partitions, parallel frames | Private proof reductions for J1/V1/C1/C2; duplicate coordinates and increase bridge obligations | Intrinsic Jacobi existence plus chart/frame equivalence theorem lands; final theorem signatures contain no chart artifact |
| Complete-space `globalGeodesic`/`expMapGlobal` helpers | F2 exploration only; they hide maximal-domain and local-domain cases | F2 proves the canonical maximal exponential API and a complete-case equivalence |
| `IsRadialJacobi`, polar-density, cut-time, cut-locus, local-isometry, and injectivity-radius facades | A1/A2/N1/N2 integration scaffolding only; producer semantics are otherwise absent | Retire or make private when N1/N2/C2 proves the named geometric producer/equivalence; no final source theorem quantifies over the facade |
| Provisional tangent/chart Jacobian leaf (`riemannianJacobian`, `chartCoordinateJacobian`) | Direct leaf import only; source-dimensional tangent area factor for the future N1 nullity consumer, with no path-metric volume claim or stable umbrella export | When `Normal.cutLocus`/`exp_on_regularDomain` consumes it, either retain the intrinsic factor with that named proof as its caller or migrate to Mathlib `LinearMap.normDet` and delete the wrappers |
| Raw tensor-derivative/Laplacian evaluation leaf (`secondCovariantDerivative`, `connectionLaplacian`) | Direct leaf import only; arbitrary `MixedTensorSection` inputs may retain extension/frame-choice dependence, so this is not yet a stable tensor API | Before S13's `Curvature.bochnerFormula` consumer is accepted, prove a smooth bundled, extension-independent producer and migrate that consumer; otherwise retain only the raw direct leaf and do not umbrella-export the canonical Laplacian API |
| Abstract `expBallVolume` density ratios | Analytic ratio lemmas only; not a manifold volume theorem | C3 proves polar density = Riemannian measure and exp preimage = metric ball off the null cut locus |
| `Option`-valued exceptional cut time, radius, or exponential-domain helpers | Private construction aid only; `none` is easy to misread and duplicates the canonical extended value | Replace at the public boundary by the proved `WithTop`/maximal-domain representation; delete after N1 equivalences land |
| Selected-extension `Curvature.Provisional.curvature`/`curvature4` facade | S06/S07 exploration only; fiberwise laws and first Bianchi are useful checks, but the `FiberBundle.extend` producer has no arbitrary smooth-section application theorem and carries a maintenance/import cost | Replace or retire it when section-level tensoriality in all field slots and the arbitrary-extension application theorem are proved; downstream curvature consumers remain gated until that trigger |
| Wrappers duplicating Mathlib/shared declarations | Temporary compatibility only with a named caller | Delete after migration to the canonical declaration |
| Temporary Git or path dependency | None is currently permitted.  A route-change PR may use an immutable, licensed Git dependency only after the human matrix decision; sibling/reference paths remain forbidden | Remove or promote to the reviewed manifest pin at the exact migration node; Z1 rejects every undeclared or path dependency |
| Any Chapter 1 to Chapter 2 import | Forbidden in Z1; temporary only if a missing general theorem is being relocated | Move the general theorem to shared or Chapter 1 before Z1 |
| Transparency/heartbeat exceptions | Named failing boundary only; maintenance and reproducibility cost | Re-audit on dependency changes and remove when the boundary is repaired |
| Reference tree's 168-file split | Prior-art navigation only; import and review cost | Consolidate helpers to one owner/proof purpose; split only at stable API boundaries |

## Bibliography and source policy

`docs/references.bib` contains exactly the publications used by this roadmap.
Every key has a claim-level connection here and in the inventory; a general
reading recommendation is not sufficient reason to retain an entry.

| Bibliography key | Inventory claims and exact anchors | Evidence status |
| --- | --- | --- |
| `morganTian2007` | S01--S43, Definition 1.1 through Theorem 1.36, printed pp. 35--50 | **Checked primary:** retained arXiv v2 PDF and original `prelim.tex`; the Clay book has the same Chapter 1 text but different compiled pagination |
| `doCarmo1992` | S02/S03, Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; S18/S26, Ch. 3, pp. 61--75; S21, Ch. 5, pp. 101--121; S19, Ch. 7, pp. 157--166; S20/S23, Ch. 9, pp. 185--201 | **Checked cross-check:** retained English scan at these result/page anchors; Morgan--Tian's bibliography says 1993, while the retained/catalogued English edition is 1992 |
| `petersen2006` | S24, Ch. 5, Prop. 19/Lem. 14, pp. 139--140; S28/S31, Ch. 5, Lem. 12, p. 133; S33, pp. 265--268; S34, Lem. 42, p. 284; S35/S37/S38/S40, Ch. 9, Sec. 1 | **Edition unavailable:** these are Morgan--Tian's explicit second-edition cross-references and are not treated as independently reverified in this workspace |
| `petersen2016` | S36, Sec. 6.4, Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257; S38, Thms. 6.4.3/6.4.6, pp. 255--257 | **Checked cross-check:** retained third-edition PDF; its reorganized numbering never substitutes for the unavailable 2006 anchors |
| `lee2018` | S02/S03, Thm. 5.10 and Cor. 5.11(b), equation (5.10), printed pp. 123--124; S19, Thm. 6.19; S23, Thm. 10.22 and Prop. 10.24; S37/S38, Thm. 11.7; S41, Thm. 11.19 | **Checked cross-check:** retained second-edition PDF and extracted theorem/corollary text |
| `gallotHulinLafontaine2004` | S13, Prop. 4.36, p. 168, as cited immediately before Morgan--Tian Lemma 1.10 | **Unavailable/unverified:** retained workspace has no 2004 edition; Morgan--Tian remains the proof authority |
| `sakai1996` | S30, Prop. 3.1, p. 41, including the sign-convention warning stated after equation (1.5) | **Unavailable/unverified:** retained workspace has no Sakai volume; Morgan--Tian's displayed coefficients are the implementation target until independently checked |
| `cheegerGromovTaylor1982` | S41, Prop. 4.1; S43, Thm. 4.3 and inequality (4.22), p. 46 | **Checked proof authority:** retained article PDF and extracted Section 4 source |
| `cheegerEbin1975` | S43, Thm. 5.8, p. 96 | **Unavailable/unverified alternative:** retained workspace has no copy; it cannot override the checked Morgan--Tian/CGT contract |

Unavailable cross-checks are kept only because the primary source points to
their exact result and the row records the unresolved verification debt.  A
future source audit either verifies that exact edition/result or removes the
cross-check; it may not silently promote bibliographic metadata into
mathematical evidence.

## Audit triggers and records

An audit entry is updated in the same PR whenever any of these changes:

- Lean, Mathlib, or shared Riemannian dependency revision/API/instance graph;
- metric, connection, geodesic, exponential, Jacobi, conjugacy, cut locus,
  injectivity, measure, or comparison representation;
- curvature, index-form, or Laplacian sign convention;
- publication edition, bibliography key, source anchor, theorem hypothesis,
  constant, normalization, or claimed correspondence;
- milestone dependency, public module/import boundary, downstream interface,
  scope, or non-goal;
- provisional facade, path dependency, package option, axiom, or `sorry`;
- a plausible Mathlib replacement API or a usable immutable Hopf--Rinow
  revision becomes available;
- workflow/status naming, protected-branch requirement, or build root.

Each record names the changed node/declaration, sources and APIs rechecked,
migration decision, remaining debt and its replacement trigger, and the exact
reviewed commit.  Each row is a historical statement scoped to its named
revision; a later gate decision does not rewrite what an earlier focused
revision established.  The audit history is:

| Revision | Change | Rechecked evidence | Decision |
| --- | --- | --- | --- |
| `bootstrap` / `e317497422c4e869ca2072f63f19b211a197bedf` | Initial package, Mathlib pin, source inventory, bibliography, and CI contract | Morgan--Tian arXiv v2 Chapter 1 PDF/source; Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`; Hopf--Rinow main `60c3e1f6493646d667a0bb645f99110a34d26e00`; publication records in `docs/references.bib` | Keep G2 open; no mathematical dependency selected; no provisional facade exposed |
| `review-response` / `32bf9a3179d54c8301ba2c8e48072f474d774978` | Applied the source-correction gates for `k = 0`, `K = 0`, the upper sectional comparison needed by `injvol`, and the `2 <= n` uniformization non-vacuity condition; removed the unused Petersen 2016 key; downgraded the Gallot cross-check to unverified | Morgan--Tian `prelim.tex` Definitions 1.30, Theorem 1.11, SCC, `localdiffeo`, and `injvol`; retained-source inventory confirms no Gallot 2004 text; bibliography/roadmap consistency audit | Keep G2 open; all five requested corrections are documented, and no mathematical implementation is claimed |
| `architecture-response` / `9f1b32d194a904ada7b614d0c12d13314aef4296` | Corrected every DAG edge; added curvature naturality, arbitrary-tensor connection Laplacian, and separate local/weak Calabi rows; reanchored Petersen editions; added A1 ownership of the positive-curvature model used by C1 | Morgan--Tian `prelim.tex` naturality paragraph, tensor-Laplacian definitions, local/weak Calabi passages, Definition 1.30, comparison-section pointer, and upper-bound paragraph; Petersen 2016 Section 6.4 retained printed pages 254--257 | Keep G2 as the human substrate gate and G0 implementation-free; restore `petersen2016` only as a precise, used cross-check |
| `mathematical-correctness-response` / `a202631d534786fba23bad4c15d434cbb759988f` | Bound `Comparison.sectional_upper` to the regular first-pole interval with explicit lower shape, angular-metric, and Jacobian directions; added `2 <= n` only to the all-manifold weak Calabi theorem | Morgan--Tian `prelim.tex` local/weak Calabi passages and upper-bound paragraph; Petersen 2016 Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257; the one-dimensional `abs` distributional counterexample | Keep the repaired Petersen edition split, A1 producer, hyperbolic SCC branch, C1-to-L1 edge, and local asymptotic unchanged |
| `A1-model-scalar` / `70cc263f77dc9ee70b6246a94edd00f3f7f6a13d` | Added the standalone `Comparison.Model` API for flat/hyperbolic and spherical profiles, their normalized ODEs, positivity and first-pole facts, totalized radial coefficients, the quantitative origin estimate, and scalar Riccati comparison | Morgan--Tian Definition 1.30 and comparison discussion, pp. 48--49; Petersen 2016 Section 6.4, pp. 254--257; pinned Mathlib trigonometric derivative/bound, square-root, and one-variable derivative-monotonicity APIs; focused public-mathlib-PR search found no close packaged comparison-profile analogue | Keep the functions in A1 with no manifold facade; expose the scalar theorem through the Chapter 1 root; leave the spherical limits `snPos K r / r -> 1` and `r * logDerivPos K r -> 1`, scalar/vector Sturm, vector/operator/trace Riccati, determinant inequalities, and manifold bridges pending |
| `G1-substrate-audit` / `96f226c580bf12ff7db80bf2bcc8c61da44f17f2` | Added the declaration-level Mathlib and candidate audit, corrected the Christoffel and Gaussian-expansion equation anchors, and assigned every source-inventory row to an exact declaration or explicit milestone gap | Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`; `palimpsest/Hopf-Rinow-DoCarmo` `60c3e1f6493646d667a0bb645f99110a34d26e00`; Morgan--Tian arXiv v2 Chapter 1 PDF and `prelim.tex`; current project declarations at baseline `aa150877959ca78c1b1f382d0257e4c5e9c7753a` | Mark G1 complete and present four bounded routes at G2; keep G2 open, add no dependency or facade, and preserve all accepted canonical representations |
| `G1-review-response` / `67e2bff29b6c048a0f340808e3d2e44050f98212` | Replaced broad metric source-section assumptions with exact exported contexts, made the candidate source count reproducible, audited three concrete unmerged Mathlib proposals, and corrected the unsupported claim that both spherical normalized limits were already proved | Pinned Mathlib `@Bundle.RiemannianMetric`, `@Bundle.RiemannianBundle`, continuous, and smooth metric signatures; candidate `60c3e1f6493646d667a0bb645f99110a34d26e00` tree and line totals; Mathlib PR #36845 head `41e2b25a520d7a24f37062855d2b091dab7a5d9d`, PR #36036 head `31613e7e48c4559a8be4de48121c911d74586744`, and PR #33714 head `c4cbb8b896a4db75bf49cf1ab0a898232cede01e`; current `Comparison.Model` declarations | Keep Mathlib pinned at `520045ab`, keep G2 open, count no PR declaration as available source, and retain both positive-curvature normalized limits as pending A1 work |
| `G2-selection` / `docs/G2_SUBSTRATE_DECISION.md` | Selected Mathlib-native construction, resolved all eight G1 questions, froze the explicit metric, Euclidean-normalized Hausdorff-volume, bundled-connection, assumption, and source-aligned curvature-sign contracts, and named migration triggers | Project baseline `2b48a6b6e6d4e115cb3d1c16e7ea7537c8bfd0f2`; Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` and Apache license; merged Mathlib PR #34697 and its pinned `μHE` source; unchanged candidate main `60c3e1f6493646d667a0bb645f99110a34d26e00`; open candidate PR #40 and unchanged Mathlib PR heads #36845, #36036, and #33714 on 2026-08-19 | Select route 3 only when this revision is merged; add no dependency or facade; keep G2 and all geometric descendants blocked until the coherence kernel lands |
| `G2-metric-volume` / `MorganTianLib/Ch01/{Metric,Volume}.lean` | Installed one scoped Mathlib bundle metric; proved its smooth/continuous, fibre inner/norm/topology, finite `C^1`-path, Mathlib `edist`/`dist`/ball, Borel, and normalized-volume bridges; exported both focused modules through the Chapter 1 umbrella | Accepted route commit `aa45255fc76b3de3870f6411dde9b1c733e39074`; Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` Riemannian bundle/`C^1` path-distance and Euclidean Hausdorff measure APIs; Morgan--Tian Definition 1.1 as the distinct smooth-path target and volume usage on pp. 35, 45--50; merged Mathlib PRs #27250, #27462, and #34697 as API provenance | Keep these direct Mathlib representations and introduce no compatibility adapter; retain S01 as partial until the smooth/piecewise-smooth path correspondence and equality of infima are proved; keep G2, F1, F2, and A2 blocked on that bridge, the connection producer, and all curvature-sign regressions |
| `G2-smooth-path-foundation` / `MorganTianLib/Ch01/Metric.lean` | Added source-facing smooth paths on `[0, 1]`, endpoint-typed finite piecewise-smooth paths, summed canonical lengths, both canonical-to-source infimum inequalities, local smooth chart segments, and finite piecewise-smooth witnesses on preconnected manifolds; retained the existing weak assumption boundary and added no ambient metric structure | Morgan--Tian Definition 1.1 and following paragraph, p. 35; Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` `Riemannian.PathELength` and `Riemannian.Basic`; [Mathlib PR #26778](https://github.com/leanprover-community/mathlib4/pull/26778) as provenance for the deliberate canonical `C^1` infimum | Keep the auxiliary infima only as correspondence statements. Retain S01 and G2 as partial until an endpoint-preserving, length-controlled approximation of near-minimizing `C^1` paths proves the reverse inequalities and equality; retain the separate E1 and bundled-connection gates |
| `A1-positive-scalar` / `e874c4c7b6126984488c487cbb78077828233457` | Completed the positive-curvature scalar boundary in `Comparison.Model`: both requested origin limits, strong logarithmic-derivative normalization, the regular Riccati ODE, the lower Riccati comparison used by the upper-sectional branch, scalar Sturm comparison and positivity, public flat corollaries, and public exact-model regressions | Morgan--Tian Definition 1.30 and upper-comparison discussion, pp. 48--49; Petersen 2016 Section 6.4, where Cor. 6.4.2 directly supports the scalar Riccati theorem while Thms. 6.4.3/6.4.6 are geometric targets and cross-checks, not statements of the scalar Wronskian theorem; pinned Mathlib derivative-slope, logarithmic derivative, interval-integral fundamental theorem, trigonometric bound, and derivative-monotonicity APIs; pinned Mathlib source search found no packaged geometric Riccati/Sturm analogue | Keep the complete scalar implementation, including its interval-integral proof, in standalone analytic `Comparison.Model`; export the exact-model regressions with the public comparison theorems and flat corollaries; leave vector/operator Riccati, trace, determinant, and all manifold/Jacobi/polar bridges to dependent issues |
| `A1-positive-scalar-review-response` / `24afcb8519006e44b680f6bf749aa64925d8f31e` | Replaced the unrelated real-log import with the canonical logarithmic-derivative owner; moved the interval-FTC-dependent Riccati proof to `Comparison.PositiveRiccati`; made both exact-model regressions private; qualified the Sturm/Jacobi producer and Petersen attribution without changing the public comparison theorems or flat corollaries | Pinned Mathlib `Mathlib/Analysis/Calculus/LogDeriv.lean` at `520045ab14e26149ee970e2e617ca04b09bde5d6` and the exact import-set LSP probe; Petersen 2016 Section 6.4, Cor. 6.4.2 and geometric Thms. 6.4.3/6.4.6, pp. 254--257; exact diffs from `e874c4c7b6126984488c487cbb78077828233457` and review artifacts for the import, visibility, source, and module-boundary findings | Keep model profiles, origin estimates, and ODE facts independent of measure integration; import focused `Comparison.PositiveRiccati` through the Chapter 1 umbrella; retain exact-model instantiations only as private compile-time checks; in the later Jacobi bridge apply scalar Sturm on the nonvanishing interval before a hypothetical first zero and extend to the endpoint by continuity |
| `A1-operator-riccati` / `cc1ad4e3d445dee8878b760182b07375a15571b9` | Added quadratic-form operator Riccati comparison in both curvature directions, operator-norm singular normalization, flat corollaries, reusable minimum-Rayleigh facts, and private exact-model regressions; generalized the upper theorem beyond finite dimension and confined finite-dimensional nontriviality to the lower extremal-eigenvalue proof | Morgan--Tian Chapter 1 comparison discussion and Theorem 1.31, pp. 48--49; Petersen 2016 Section 6.4, Cor. 6.4.2 and geometric Thms. 6.4.3/6.4.6, pp. 254--257; pinned Mathlib `Analysis.InnerProductSpace.Rayleigh`, continuous-linear-map calculus, and left-slope fencing APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; [Mathlib PR #4920](https://github.com/leanprover-community/mathlib4/pull/4920) for `hasEigenvector_of_isMinOn`, [PR #35173](https://github.com/leanprover-community/mathlib4/pull/35173) ("Rayleigh quotients are bounded above by the operator norm"), and [PR #35464](https://github.com/leanprover-community/mathlib4/pull/35464) for sharp symmetric-operator norm bounds | Keep `Comparison.OperatorRiccati` manifold-free and expose it through the Chapter 1 umbrella; unlike the reference prior art, keep support-function and barrier machinery private and import no Jacobi records or geometric facades; leave vector Sturm, trace Riccati, determinant/volume-density consequences, and every manifold/Jacobi/polar producer pending |
| `A1-trace-determinant` / `6e7b502a79debd00299b1c3bf7751a0889a9df7f` | Added trace Cauchy--Schwarz including dimension zero, flat/hyperbolic traced Riccati comparison, the basis-free logarithmic derivative of `abs (det J)`, upper/lower normalized-density monotonicity for `sn`/`snPos`, explicit flat reductions, origin-normalized consequences, and equality-model regressions | Morgan--Tian `prelim.tex` Definition 1.30 and `riccurvcomp`, pp. 48--49; Petersen (2006), Chapter 9, Section 1; Petersen (2016), Section 6.4, Cor. 6.4.2; pinned Mathlib trace/determinant/to-matrix/continuous-multilinear derivative APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; reference `TraceRiccati.lean`, `MatrixCalculus.lean`, and `VolumeElement.lean` as prior art only | Keep the analytic API in A1, use private matrices only to prove Jacobi's formula, and leave vector/operator Riccati and every geometric producer/coherence theorem to C1/C2/C3/N1 |
| `A1-trace-determinant-review-response` / `d3d049b0467d3f1bff9edcf254f7d0a592c553d7` | Weakened determinant-only assumptions to finite-dimensional real normed spaces, made `hasDerivAt_div_pow` pointwise, added nonconstant flat upper/lower direction regressions while retaining the equality models, and corrected the Petersen 2016 printed-page offsets | Pinned Mathlib pointwise quotient/power derivative and determinant APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; Petersen (2016), Section 6.4, Cor. 6.4.2 on pp. 254--255 and Thms. 6.4.3/6.4.6 on pp. 255--257; focused elaboration and public-signature checks | Require an inner product only for symmetric trace/Riccati consequences, keep the public comparison conclusions and private matrix boundary unchanged, and retain all geometric debt at C1/C2/C3/N1 |
| `A1-trace-determinant-architecture-response` / `345f10db3c1fb4d9d595ddf8a82c6de26933c8d7` | Replaced written inner-product equalities with `LinearMap.IsSymmetric`, transported the inner-product traced consequences from the normed-space absolute determinant to `LinearMap.normDet`, and restored `Comparison.PositiveRiccati` as an independent direct Chapter 1 umbrella import | Pinned Mathlib `Trace.lean` and `NormDet.lean` at `520045ab14e26149ee970e2e617ca04b09bde5d6`, including `normDet_eq_abs_det` and `hausdorffMeasure_image`; focused dependency-chain elaboration, root export probes, public-signature checks, and representative axiom checks | Keep `endomorphismAbsDet` only as the more general normed-space calculus; use `normDet` directly for inner-product volume-factor consumers.  Accept the canonical facade's exact public import cost (`Adjoint`, `GramMatrix`, `SingularValues`, and `Geometry.Euclidean.Volume.Measure`) because C2/N1/C3 need the measure-facing API; add no compatibility wrapper or deferred replacement debt.  Keep `PositiveRiccati` independent of `DeterminantDensity` and export both public leaves directly from `Ch01.lean` |
| `A1-vector-sturm` / `MorganTianLib/Ch01/Comparison/VectorSturm.lean` | Added basis-free first- and second-norm derivative identities, vector Sturm comparison on the strict first-pole interval for `K ≥ 0` including the totalized flat branch, the positive-slope no-zero corollary, and the one-sided initial-derivative slope bridge | Morgan--Tian Chapter 1 comparison discussion, printed pp. 48--49; the existing `Comparison.scalar_sturm_comparison_pos`; pinned Mathlib real inner-product calculus, one-sided derivative/slope, closed-zero-set infimum, and Cauchy--Schwarz APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Keep the theorem over an arbitrary real inner-product space without finite-dimensionality, completeness, or nontriviality assumptions.  Require `V 0 = 0`, closed-interval continuity, twice differentiable interior data, the right-origin derivative bound and norm-slope limit, and extend through a hypothetical first zero by continuity.  Export no Jacobi, geodesic, exponential, polar-density, cut-locus, or geometric comparison facade; those producers remain in J1/C1/N2 |
| `issue-15-governance` / audited baseline `599f5241fee042dd50e9e60a3a343a1cbac7aa39` | Recast S01--S43 as a field-complete source-to-API ledger; added independent finite-dimensional E1 for the previously hidden metric-existence claim; made the complete-and-boundaryless scope explicit for the geodesic IVP descendants S19 and S26--S29 and for S39; reconciled every ledger prerequisite with an acyclic node schedule by adding `F2 -> F3`, placing pre-cut measure primitives in A2, and adding post-cut polar/Gaussian node N2 for S30--S33; connected every bibliography entry to exact rows; distinguished checked, unavailable, and unverified evidence; recorded the `r^-2 g` normalization correcting the S42 proof typo | Original Morgan--Tian arXiv v2 `prelim.tex` and PDF through Theorem 1.36, including its ordinary smooth-manifold convention, the `n`-dimensional opening, the complete-manifold scope before Definition 1.24, and the S14/S27--S34 producer order; the ledger's hard prerequisites checked against the milestone graph, frontier prose, and node contracts; pinned Mathlib `IntegralCurve.ExistUnique` and `IsManifold.InteriorBoundary`, which distinguish `I.IsInteriorPoint p`, `[BoundarylessManifold I M]`, and the stronger `[I.Boundaryless]`; [Mathlib PR #33714](https://github.com/leanprover-community/mathlib4/pull/33714), with `InnerProductSpace ℝ F`, `FiniteDimensional ℝ EB`, `SigmaCompactSpace B`, and `T2Space B` as prior-art existence assumptions; pinned Mathlib `ContMDiffRiemannianMetric` source for the existing-fiber-topology requirement; retained do Carmo, Petersen 2016, Lee 2018, and CGT copies; absence audit for Petersen 2006, Gallot--Hulin--Lafontaine 2004, Sakai 1996, and Cheeger--Ebin 1975; metric/curvature/volume scaling; project modules/imports and workflow at exact baseline `599f5241fee042dd50e9e60a3a343a1cbac7aa39` | Keep the accepted Mathlib-native route, canonical representations, and CI contract.  Add E1 as a G0-parallel finite-dimensional final-completeness obligation, with a topology-compatible model inner product and the actual partition-of-unity hypotheses, without changing G2 descendants or supplied-metric generality.  Require `I.IsInteriorPoint p` for point-local geodesic/exponential statements and the weakest `[BoundarylessManifold I M]` class for source-facing all-points contracts; add completeness separately to S28--S29's global cut conclusions and S39's full-ball conclusion.  Schedule F3 after F2, N1 after A2, and N2 after F1/A2/N1 so every row has an ordered closer and C1/C2 consume completed polar/Gaussian producers.  Preserve S42's statement while using the corrected proof normalization.  G2 debt remains the smooth/piecewise-smooth distance bridge, bundled connection producer/regularity, and curvature regressions; unavailable cross-checks are verification debt with removal-or-verification triggers |
| `G2-curvature-kernel` / `MorganTianLib/Ch01/Curvature.lean` | Added the basis-free constant-curvature model operator and four-tensor, proved their Morgan--Tian third/fourth-slot pairing, and proved the component, Jacobi, index-form, orthonormal-sectional, and finite-orthonormal-basis contraction regressions | Accepted roadmap baseline `80bdb7f7eb6bd1efb3b52b91cbb1293b52dd928d`; Morgan--Tian Definition 1.4 and coordinate formula, pp. 37--38, Definition 1.8, p. 39, and Jacobi/index formulas, pp. 43--44; pinned Mathlib real inner-product and orthonormal-basis APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Keep the algebraic API independent of the manifold connection and impose no unnecessary dimension bound; dimensions zero and one remain covered by the contraction theorem.  Make no constant-curvature-manifold, sectional-curvature, or Ricci-curvature claim; keep G2 blocked on the source-distance gate and leave the manifold curvature API to F1 |
| `issue-18-connection` / `MorganTianLib/Ch01/Connection.lean` | Added the explicit-metric Mathlib-native Levi--Civita producer, compatibility, torsion, source-ordered Koszul, differentiable-field pointwise uniqueness, and smooth consumer regularity; exported the module through the Chapter 1 umbrella | Morgan--Tian Theorem 1.2, printed pp. 35--36; do Carmo (1992), Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; Lee (2018), Theorem 5.10 and Corollary 5.11(b), equation (5.10), printed pp. 123--124; pinned Mathlib `CovariantDerivative`, metric, torsion, local-frame, manifold-derivative, and finite-dimensional dual APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; Apache-licensed Mathlib PR #36845 head `41e2b25a520d7a24f37062855d2b091dab7a5d9d` and PR #36036 head `31613e7e48c4559a8be4de48121c911d74586744` as modified prior art only | Mark S02 and the connection bridge complete with no project connection alias or public chart facade; retain G2 as open on the independent smooth/piecewise-smooth distance correspondence |
| `G2-smooth-distance-correspondence` / `MorganTianLib/Ch01/Metric.lean` | Added endpoint-preserving quantitative chart replacement for `C^1` paths, compact monotone subdivision into accepted smooth segments, the limiting reverse infimum inequality, endpoint-flat smooth concatenation with exact length additivity, and equality of both source-facing infima with `Manifold.riemannianEDist` | Accepted main baseline `9f735b3d1ff28252afed506ba74db28d0d74412a`; Morgan--Tian Definition 1.1 and following paragraph, p. 35; pinned Mathlib `Riemannian.Basic`, `Riemannian.PathELength`, smooth-transition, manifold-chart, and compact-cover APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Mark the supplied-metric G2 distance component complete and S01 partial only on E1 metric existence.  Keep the auxiliary infima as correspondence statements, add no ambient metric or stronger global assumption, and leave all other G2 gate and descendant statuses unchanged in this focused revision |
| `issue-26-christoffel` / `MorganTianLib/Ch01/Connection/Christoffel.lean` | Added the chart-coordinate coefficient theorem for the explicit-metric canonical Levi--Civita connection, including the local coordinate-frame bracket calculation, chart/manifold derivative bridge, Koszul first-kind identity, and inverse-Gram contraction | Accepted roadmap baseline `07d2a0be1a7aa3e38d827756b6585edb5a2ade60`; Morgan--Tian equation (1.1), printed p. 36; do Carmo (1992), Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; Lee (2018), Corollary 5.11(b), equation (5.10), printed pp. 123--124; pinned Mathlib chart, tangent local-frame, manifold derivative, Gram matrix, and nonsingular inverse APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Mark S03 complete without defining another connection or public coordinate facade.  Require an explicit smooth metric and an interior chart point, keep coordinate data private, and leave Hessian S04, function Laplacian S05, and all curvature/tensor-Laplacian rows open |
| `issue-26-review-response` / `b57eb2ee13bfce92709df681f199ff1888c568eb` | Corrected the do Carmo and Lee source anchors for the connection producer and Christoffel bridge across the Lean module docstrings, G2 decision, bibliography, S02/S03 ledger rows, and audit history; no declaration or representation changed | Retained do Carmo scan: Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; retained Lee second-edition PDF: Theorem 5.10 and Corollary 5.11(b), equation (5.10), printed pp. 123--124; Morgan--Tian equation (1.1), p. 36 | Keep `Connection.leviCivitaConnection`, `Connection.christoffel_formula`, private chart plumbing, and S03 completion unchanged; this is documentation/source-mapping correction only |
| `issue-34-geodesic-local` / `45d2774b1dfe2394dd0df7be8e1bee965f137075` | Added the focused `Ch01.Geodesic` chart spray and Morgan--Tian coordinate equation, an explicit `Connection.leviCivitaConnection` coefficient/contraction bridge, point-local and `[BoundarylessManifold I M]` local IVP theorems with continuity witnesses, state- and curve-level local uniqueness, intrinsic-coordinate transport guarded by chart source/continuity, and restriction compatibility; exported the module through `Ch01.lean` and added point-local connection regularity | Morgan--Tian Definition 1.17 and the coordinate/initial-value paragraph, printed p. 41; pinned Mathlib integral-curve/ODE APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; repository `Connection.leviCivitaConnection` and `Connection.Christoffel` declarations; focused direct Lean elaboration and root-import probes | Keep this as a partial F2 handoff (`Part of #34`). The canonical maximal solution/domain, moving-chart gluing, unbounded-lifetime compatibility, smooth curve and smooth initial-data dependence, and Euclidean/nonconstant-metric regression suite remain provisional debt; do not mark S18 complete or introduce Hopf--Rinow/exp-map claims |
| `issue-34-geodesic-witness-spray` / `25d455fac648c1beb23ac24a4efd4c46f8cef9f5` | Added the private chart-local tangent-bundle spray lift, explicit solution-witness/selected-curve and overlap-compatibility interfaces for the maximal-domain substrate, the global-witness-to-unbounded-lifetime corollary, the initial-time fixed-chart/intrinsic bridge, and the zero-tangent/constant-solution uniqueness regression; retained the canonical bundled metric and the weakest `[BoundarylessManifold I M]` wrapper | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib `IntegralCurve.ExistUnique`, tangent-bundle trivializations, `ContMDiffOn` chart composition, and boundary/interior APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; repository `Connection.leviCivitaConnection`/`Connection.Christoffel`; direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep this as a partial F2 handoff (`Part of #34`). The private lift is chart-local proof infrastructure, not a global spray; the compatibility premise is not discharged. Do not mark S18 complete: the Christoffel transition law, canonical gluing/maximality/nonempty witness, smooth maximal curve and joint flow dependence, and concrete nonconstant-metric regression remain open. |
| `issue-34-geodesic-fixed-chart-regressions` / `43f33eb` | Completed the private fixed-chart converse and iff between the second-order chart equation and the first-order spray state ODE, removed dead frame plumbing, added source anchors, and added a concrete canonical Euclidean zero-velocity regression using Mathlib's `riemannianMetricVectorSpace` | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib `Riemannian.Basic` and ODE/chart APIs; direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep this as a partial F2 handoff (`Part of #34`). The fixed-chart equivalence is not a moving-chart transition theorem; retain the open Christoffel transformation law, canonical gluing/maximality/nonempty witness, smooth maximal curve and joint flow dependence, and concrete nonconstant-metric/straight-line probes. |
| `issue-34-geodesic-tangent-ivp` / `pending` | Consumed the private chart-local spray lift with a point-local tangent-bundle smoothness and integral-curve witness. The witness exposes only the prescribed base interior point and `[CompleteSpace E]`; it does not install a global tangent-bundle boundaryless instance or claim a global spray. | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib tangent-bundle trivialization, `ContMDiffAt`, interior-boundary, and `IntegralCurve.ExistUnique` APIs; direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep this as a partial F2 handoff (`Part of #34`). The fixed-to-moving Christoffel law, canonical gluing/maximality, smooth parameter flow, and concrete nonconstant-metric/straight-line probes remain open. |
| `issue-34-geodesic-transition-kinematics` / `pending` | Added the chart-overlap kinematic bridge: explicit transition source and interior overlap membership, smooth/full and second Frechet transition derivatives, eventual chart-reading equality and first-derivative transport, and tangent-velocity transport through Mathlib's `tangentCoordChange`; no metric-dependent Christoffel identity is asserted | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib chart-transition, `ContDiffAt.fderiv_right`, `HasFDerivAt.comp_hasDerivAt`, tangent-trivialization, and `tangentCoordChange` APIs; direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep this as a partial F2 handoff (`Part of #34`). Use the transition derivatives as proof infrastructure for the still-open fixed-to-moving Christoffel law; canonical gluing/maximality/nonempty witnesses, smooth maximal curve and joint initial-data dependence, and concrete nonconstant-metric/straight-line probes remain open. |
| `issue-34-geodesic-second-order-zero-regression` / `pending` | Added the applied second-order transition chain rule `D²τ(u')u' + Dτ(u'')`, together with a canonical global `GeodesicSolution` for zero initial velocity and the resulting all-time maximal-domain/unbounded-lifetime regression; the general moving-chart Christoffel law and arbitrary-data gluing remain intentionally unclaimed | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib `HasFDerivAt.comp_hasDerivAt` and `HasDerivAt.clm_apply`, chart-transition APIs, and the existing intrinsic constant-curve regression; direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep this as a partial F2 handoff (`Part of #34`). Consume the applied chain rule in the future Christoffel transformation proof; retain the zero-velocity global witness as a boundary regression, not evidence for arbitrary initial data, smooth maximal curves, joint flow dependence, or concrete nonconstant-metric probes. |
| `issue-34-geodesic-conditional-union` / `pending` | Added eventual-equality congruence for the chart geodesic contract, open-domain equation transfer, continuity and chart smoothness of the canonical union representative under pairwise compatibility, a conditional bundled maximal-solution constructor and bundled-domain extension theorem, and a restriction-data regression; no metric transition identity is hidden in these lemmas | Morgan--Tian Definition 1.17 and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib `Topology.Neighborhoods`, derivative congruence, `ContDiffAt`, and existing geodesic witness/union APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; focused isolated derivative proof and static API audit (repository LSP unavailable because required Mathlib artifacts are read-only/missing) | Keep this as a partial F2 handoff (`Part of #34`). The conditional constructor requires the still-open fixed-to-moving Christoffel law and arbitrary-data nonempty/compatibility theorem; its smoothness is in the initial chart and is not yet a manifold-valued smoothness contract. The raw extension maximality predicate, joint initial-data dependence, and concrete nonconstant-metric/straight-line probes remain open. |
| `issue-34-geodesic-euclidean-regression` / `pending` | Added a concrete canonical-Euclidean coefficient calculation through `Connection.christoffel_formula`, proving zero chart coefficients, zero contraction for arbitrary velocity pairs, and zero coordinate acceleration for affine straight-line paths; the bundled `riemannianMetricVectorSpace` and existing connection remain the only geometric data | Morgan--Tian equation (1.1), Definition 1.17, and the coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib `Riemannian.Basic`, tangent trivialization, and `Connection.christoffel_formula`; focused direct elaboration of `Geodesic.lean` and the Chapter 1 umbrella | Keep S18 partial (`Part of #34`). This is a concrete flat-branch Euclidean regression; because all coefficients vanish, it does not distinguish Christoffel sign or lower-slot order and does not discharge the moving-chart metric transformation law, unconditional gluing or arbitrary-data maximality, smooth manifold-valued/joint flow dependence, or the required nonconstant-metric sign/slot probe. |
| `issue-34-geodesic-affine-transport` / `pending` | Added the quadratic Christoffel-contraction law and fixed-chart affine reparameterization of the regularity and geodesic-equation contracts, together with global and set-relative translation, time-reversal, and velocity-rescaling adapters; the pulled-back time set is retained literally | Morgan--Tian Definition 1.17 and the coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib derivative composition/shift APIs and the canonical `Connection.leviCivitaConnection`; focused direct pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep S18 partial (`Part of #34`). This is a local algebraic/time-calculus slice and does not prove the moving-chart Christoffel transformation law, unconditional gluing or arbitrary-data maximality, smooth manifold-valued maximal curves, joint initial-data dependence, or the concrete nonconstant-metric sign/slot probe. |
| `issue-34-geodesic-nonconstant-metric-probe` / `pending` | Added a private smooth one-dimensional metric fixture with inner product `(1 + x^2) • inner`, proved its bundled Christoffel formula through `Connection.christoffel_formula`, and checked the coordinate contraction at `x = 1` and unit velocity is `1 / 2`; arbitrary Mathlib basis scaling is canceled explicitly, so the probe detects the nonzero derivative/sign branch rather than relying on a flat zero.  The nested smooth-metric construction has scoped 400000/1000000 heartbeat caps as a private elaboration-performance boundary | Morgan--Tian equation (1.1) and Definition 1.17 (`morganTian2007`); pinned Mathlib `Riemannian.Basic`, `Matrix.inv_subsingleton`, tangent trivialization, derivative, and bundled Levi--Civita APIs; direct pinned-artifact elaboration of `Geodesic.lean` | Keep S18 partial (`Part of #34`). The private fixture is a regression only and adds no competing metric or connection API. Re-audit or remove the scoped caps when the pinned dependency changes. The moving-chart Christoffel transformation law, unconditional gluing or arbitrary-data maximality, smooth manifold-valued maximal curves, and joint initial-data dependence remain open. |
| `issue-34-geodesic-affine-global-sign` / `pending` | Extended the Euclidean model from fixed-chart acceleration to the complete source-facing affine geodesic predicate, bundled a global `GeodesicSolution` for arbitrary position and velocity, and proved its maximal-domain substrate is all of time with unbounded lifetime.  Upgraded the private `(1 + x^2) • inner` fixture to an equation-level quadratic-path regression where the reversed-sign residual vanishes but the canonical `u'' + Gamma(u',u')` residual equals `1` | Morgan--Tian equation (1.1), Definition 1.17, and the coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib model-chart, tangent-trivialization, derivative, and bundled Levi--Civita APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; focused pinned-artifact elaboration of the connection, Christoffel, geodesic, variation, and Chapter 1 umbrella modules | Keep S18 partial (`Part of #34`). The affine witness is a Euclidean regression, not arbitrary-metric nonemptiness or maximality. The nonconstant fixture is private proof data and introduces no second public metric or connection. The moving-chart Christoffel transformation law, unconditional overlap gluing, manifold-valued maximal smoothness, and joint initial-data dependence remain open. |
| `issue-34-geodesic-transition-transfer` / `pending` | Added the explicit `HasChristoffelTransitionAt` producer contract in the alpha-to-beta orientation, a totalized-derivative chart-reading regularity bridge, second-order chart-acceleration transport, fixed-to-moving solved-equation transfer, a boundaryless conditional local `GeodesicSolution` constructor, and a named affine initial-velocity regression | Morgan--Tian equation (1.1), Definition 1.17, and coordinate/initial-value paragraph, printed p. 41 (`morganTian2007`); pinned Mathlib chart-transition, `HasDerivAt.congr_of_eventuallyEq`, tangent-coordinate, boundary/interior, and bundled Levi--Civita APIs; focused pinned-artifact elaboration of `Geodesic.lean` and `Ch01.lean` | Keep S18 partial (`Part of #34`). The transition contract is a premise until its metric proof lands; the conditional constructor does not establish unconditional arbitrary-data nonemptiness, canonical overlap gluing/maximality, manifold-valued maximal smoothness, or joint initial-data dependence. |
| `E1-metric-existence` / `MorganTianLib/Ch01/MetricExistence.lean` | Added `nonempty_contMDiffRiemannianMetric`, the generic smooth-vector-bundle theorem built from an actual smooth partition of unity, and the distinct `nonempty_contMDiffRiemannianMetric_tangentSpace` corollary, whose auxiliary Euclidean form is transported internally through Mathlib's finite-dimensional continuous linear equivalence; exported the focused module through the Chapter 1 umbrella.  Nested hom-bundle synthesis has a 400000-heartbeat cap, and five private finite-sum or coordinate-transport proofs have scoped 800000-heartbeat caps | Accepted roadmap revision `a6684bb6eef31dbdc75c76e541b4f4475bc1e303`; Morgan--Tian Definition 1.1 and following existence paragraph, printed p. 35; pinned Mathlib `ContMDiffRiemannianMetric`, `ContMDiffVectorBundle`, hom-bundle, bounded-unit-ball, smooth partition-of-unity, and `toEuclidean` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; Apache-licensed Mathlib PR #33714 exact head `c4cbb8b896a4db75bf49cf1ab0a898232cede01e` as modified prior art absent from the pinned dependency and as provenance for the 800000-heartbeat proof boundaries | Mark E1 and S01 complete.  Keep `Bundle.ContMDiffRiemannianMetric` as the only public metric representation, add no global competing instance, and keep the generic model-fiber `InnerProductSpace` separate from the tangent theorem's weaker arbitrary finite-dimensional normed model.  Treat the private heartbeat caps as a named elaboration-performance exception: re-audit or remove them when the pinned dependency changes.  Do not change the completion state of other G2 gates, F1, F2, A2, or their descendants |
| `G2-gate-reconciliation` / completion head `07d2a0be1a7aa3e38d827756b6585edb5a2ade60`, audited baseline `8f43241e6f754e6958266d15537fdef10e73175c` | Reconciled the current G2 status with its exhaustive bridge ledger: metric data, smooth/continuous bundle coherence, distance/topology and source correspondence, normalized volume, the bundled Levi--Civita producer/regularity, and curvature sign/order are the six G2-owned families; the geodesic-equation row is an F2 handoff after the gate.  Preserved all earlier focused audit rows as historical statements | Accepted producer heads `599f5241fee042dd50e9e60a3a343a1cbac7aa39` (metric/volume), `c65121f0410f368b75dd8d57fe7df09620f9fe12` (curvature signs), `ae92775c2e3bff2278da8cfb38e12b560d2ba213` (connection), and `07d2a0be1a7aa3e38d827756b6585edb5a2ade60` (final distance correspondence), all imported by `MorganTianLib/Ch01.lean`; exact exported hypotheses and declaration checks in `docs/G2_SUBSTRATE_DECISION.md`; proof-hole, `unsafe`, forbidden-dependency, root-import, DAG, and workflow-shape scans at `8f43241e6f754e6958266d15537fdef10e73175c` | Mark G2 complete at `07d2a0b` and unlock F1, F2, and A2.  Keep the intrinsic geodesic equation pending in F2.  Preserve S03 completion at `a6684bb6eef31dbdc75c76e541b4f4475bc1e303` and open issue #13's S04--S05 frontier; make no new S04--S43 claim and change no canonical representation or Lean API |
| `issue-35-curvature` / `8bacffab227158d3bd0d8528b3ae8c2708b50b1c` | Original reviewed owner set: `MorganTianLib/Ch01.lean`, `MorganTianLib/Ch01/Connection.lean`, `MorganTianLib/Ch01/Connection/Christoffel.lean`, `MorganTianLib/Ch01/Curvature.lean`, `MorganTianLib/Ch01/Curvature/Tensoriality.lean`, and `ROADMAP.md`. Connected the exact bundled Levi--Civita connection to the source-ordered extension-based curvature commutator and `(0,4)` pairing; added smooth-section regularity, first-pair skew, the local-frame chart derivative/quadratic formula, pointwise additivity/scalar laws with `TensorialAt` witnesses in all three `(1,3)` slots, and the extension-based first Bianchi identity in both `(1,3)` and `(0,4)` orders | Accepted roadmap baseline `598b3f4337666d633c3686e1e561f739f71a0e98`; exact reviewed head `8bacffab227158d3bd0d8528b3ae8c2708b50b1c`; Morgan--Tian `morganTian2007`, Definition 1.4 and Claim 1.5, retained arXiv printed pp. 37--38; pinned Mathlib `CovariantDerivative`, `FiberBundle.extend`, local-frame, chart-derivative, torsion, and Jacobi APIs; declarations across the six owners listed in the change column | Keep S06 partial until the raw local-frame/chart component is identified with the extension-based pointwise value and Euclidean/nonconstant-metric regressions are added. Record the first-pair, tensorial, and first-Bianchi subset of S07; leave metric last-pair/pair interchange, differential/second Bianchi, arbitrary-extension application, and downstream geometric contractions to their dependency milestones |
| `issue-35-curvature-review-response` / `14d5dadc08169f393d2ab23fd04970de24a1440b` | Response revision across `MorganTianLib/Ch01.lean`, `MorganTianLib/Ch01/Connection/Christoffel.lean`, `MorganTianLib/Ch01/Curvature.lean`, `MorganTianLib/Ch01/Curvature/Model.lean`, `MorganTianLib/Ch01/Curvature/Manifold.lean`, `MorganTianLib/Ch01/Curvature/Provisional.lean`, `MorganTianLib/Ch01/Curvature/Tensoriality.lean`, and `ROADMAP.md`: restored the connection-free model boundary, moved the manifold producer to its own module, placed all selected-extension pointwise laws under `Curvature.Provisional`, and moved chart/frame checks to a private unimported leaf while retaining only `Connection.christoffel_formula` publicly. Removed dead helper obligations, corrected source-qualified documentation, and recorded the provisional facade's maintenance cost and arbitrary-extension replacement trigger | Exact implementation response commit `14d5dadc08169f393d2ab23fd04970de24a1440b`; rechecked against the original review head `8bacffab227158d3bd0d8528b3ae8c2708b50b1c`; Morgan--Tian `morganTian2007`, Definition 1.4 and Claim 1.5, retained arXiv printed pp. 37--38; pinned Mathlib `CovariantDerivative`, `TensorialAt`, `FiberBundle.extend`, local-frame, and chart-derivative APIs; completed direct Lean elaboration of all changed leaves and the Chapter 1 root import | Keep the selected-extension namespace explicitly provisional and gate downstream curvature consumers until section-level tensoriality plus the arbitrary smooth-extension application theorem exists; keep chart equivalence, metric symmetries, regressions, and second Bianchi as separate debt |
| `A2-chart-jacobian-first-slice` / `MorganTianLib/Ch01/Volume/ChangeOfVariables.lean` | Added smooth positive chart Gram densities and exact overlap laws, a `LinearMap.normDet` Jacobian adapter with zero/one-dimensional regressions, normalized-Euclidean injective area/change-of-variables, separate image measurability and null transport, equidimensional critical-value nullity, and chart-independent coordinate nullity | Accepted roadmap baseline `598b3f4337666d633c3686e1e561f739f71a0e98`; Morgan--Tian volume and cut-locus discussion, pp. 45--50; pinned Mathlib `NormDet.lean`, `MeasureTheory.Function.Jacobian`, tangent coordinate-change, and `μHE` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; local source audit found no theorem identifying the Riemannian path-metric Hausdorff measure with chart density | Mark only this pre-N1 A2 subset implemented.  Keep the canonical `riemannianVolume` chart formula, sphere/radial integration, and ratio-of-integrals open; add no competing global measure, metric instance, cut-locus claim, exponential-map facade, or post-N1 polar equality |
| `A2-chart-jacobian-review-response` / `d0c3aa977df35ee68a2bf7f011490f9b0769193a` | Split the inner-product Gram/smooth-density proofs from the C1 arbitrary-normed chart-transition layer and the finite-dimensional `muHE` Jacobian/null layer; made `LinearMap.normDet` primary with absolute-determinant corollaries; removed the project facade and duplicate Mathlib aliases, weakened tangent/nullity consumers to the upstream C1 contract, renamed predicate-first declarations, removed the provisional leaf from the stable Chapter 1 umbrella, and corrected the Hausdorff-normalization wording with the `morganTian2007` citation | Morgan--Tian Chapter 1 volume and cut-locus discussion, pp. 45--50 (`morganTian2007`); pinned Mathlib `NormDet`, `MeasureTheory.Function.Jacobian`, and tangent-coordinate APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; ROADMAP ownership/G2 migration rules; focused leaf/root compiler and exported-signature probes plus source and import scans | Keep `ChangeOfVariables` as a direct leaf import pending a named stable consumer; retain the canonical chart-density/`riemannianVolume` bridge, sphere/radial and ratio-of-integrals work, and N1/N2 debt; introduce no competing measure or Jacobian facade |
| `A2-normdet-change-of-variables` / `6a73f13bfc390a1a234c015b507a89a33040d4a9` | Added the continuous-linear-map `LinearMap.normDet` adapter for coordinate determinants, same-dimensional composition and inverse positivity laws, named identity/scaling/zero- and one-dimensional regressions, a separate image-measurability wrapper, canonical-normDet critical-value nullity, injective `μHE` change-of-variables and area formulas, and the normDet chart-transition corollary; exported the focused leaf through `MorganTianLib/Ch01.lean` | Morgan--Tian Chapter 1 volume and cut-locus discussion, pp. 45--50 (`morganTian2007`); pinned Mathlib `Analysis.InnerProductSpace.NormDet` and `MeasureTheory.Function.Jacobian` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; `Volume.lean`'s canonical `riemannianVolume`/`euclidean_volume_coherence` declarations; focused pinned-artifact elaboration, root-import compilation, and source/import scans | Mark this additional pre-N1 A2 subset implemented.  Keep Mathlib's `LinearMap.normDet` and `μHE[finrank ℝ E]` as the only canonical Jacobian/measure choices; the chart-density identification with `riemannianVolume`, sphere/radial and ratio-of-integrals results, and N1/N2 claims remain open, with no competing measure, metric instance, or Jacobian facade |
| `A2-normdet-alias-cleanup` / `ff30eaaf2d4cc1a50d0d2d1e76ae8b83eb096ca4` | Removed the exact project alias of `MeasureTheory.measurable_image_of_fderivWithin`, retained the upstream theorem as the separately documented image-measurability result, and kept the specialized canonical-normDet Sard and change-of-variables API unchanged | Pinned Mathlib `MeasureTheory.Function.Jacobian` source at `520045ab14e26149ee970e2e617ca04b09bde5d6`; accepted A2 no-duplicate-alias route; focused leaf and Chapter 1 umbrella elaboration, exported-signature probes, and representative axiom checks | Keep Mathlib's declaration as the canonical image-measurability result and avoid a second vocabulary.  Preserve the implemented pre-N1 A2 subset and all open chart-density, sphere/radial, ratio-of-integrals, N1, and N2 debt |
| `A2-tangent-riemannian-jacobian` / `669380f85b241e8a028b90666b9143d1b7586fa7` | Added the basis-independent tangent-space `riemannianJacobian`, a model-coordinate `chartCoordinateJacobian` adapter, the exact-source density-weighted coordinate agreement law, and identity/composition laws with explicit source/middle dimension transport through `VectorBundle.finiteDimensional` and `VectorBundle.finrank_eq` | Morgan--Tian Chapter 1 volume and cut-locus discussion, pp. 45--50 (`morganTian2007`); pinned Mathlib `Topology.VectorBundle.FiniteDimensional`, `Geometry.Manifold.MFDeriv.Tangent`, `Topology.VectorBundle.Basic`, and `Analysis.InnerProductSpace.NormDet` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; canonical `riemannianVolume` declarations in `Volume.lean`; fresh leaf elaboration, exported signatures, and axiom probes | Mark this tangent-Jacobian/chart-compatibility subset implemented as a provisional direct leaf, not as a stable umbrella API.  The intrinsic definition/id/composition contexts use arbitrary finite-dimensional normed model spaces; coordinate/density adapters retain inner-product assumptions.  The first named consumer is N1 `Normal.cutLocus`/`exp_on_regularDomain`; until it lands, keep the leaf direct-only and retain no path-metric volume or competing Jacobian claim.  Keep `riemannianVolume`/chart-density identification, sphere/radial and ratio-of-integrals results, nullity consumers in N1, and all N1/N2 claims open; retain Mathlib `normDet` and `μHE[finrank ℝ E]` as the only global Jacobian/measure choices |
| `A2-tangent-riemannian-jacobian-instance-correction` / `8a848d1ad1ad91248e15f45c18c6e13dfc5190a1` | Corrected the tangent `tangentNormDet`, `tangentNormDet_comp`, and chart-agreement instance graph by snapshotting source, middle, and target metric data before installing each target metric; added the same-bundle, two-distinct-inner-product regression `tangentNormDet_two_metrics_regression` | Pinned Mathlib `Topology.VectorBundle.Riemannian` (`RiemannianBundle`-derived fibre instances) and `Analysis.InnerProductSpace.NormDet` (`LinearMap.normDet`, `normDet_comp_of_finrank_eq`) APIs at `520045ab14e26149ee970e2e617ca04b09de5d6`; rechecked the tangent/chart declarations, exported signatures, and the private two-metric regression | Retain the explicit metric snapshots: the current `RiemannianBundle` instance API needs source/middle/target structures made explicit when fibre types coincide, and no competing metric or Jacobian representation is introduced.  Keep `ChangeOfVariables` a provisional direct-only leaf until the named N1 `Normal.cutLocus`/`exp_on_regularDomain` consumer lands; then reassess the adapter for stable export.  Preserve the open chart-density/`riemannianVolume`, sphere/radial, ratio-of-integrals, nullity, N1, and N2 work and retain Mathlib `normDet`/`μHE[finrank ℝ E]` as the canonical choices |
| `issue-44-sectional-operator` / `aff33a14e02833c9cd4c0d33903721732cf5608c` | Added the intrinsic algebraic-curvature predicate, determinant/`GL₂` change-of-generators plane API, diagonal-to-full constant-curvature tensor equivalence, and a symmetric bilinear curvature operator on Mathlib's second exterior power; connected these consumers to the exact explicit-metric `Provisional.curvature4` through an honest pointwise witness boundary and added dimensions zero/one/two plus algebraic slot-sign convention probes | Morgan--Tian Definitions 1.6--1.7 and the constant-curvature paragraph, printed pp. 38--39 (`morganTian2007`); do Carmo (1992), Chapter 4; Petersen (2016), Chapter 3; pinned Mathlib `LinearAlgebra.ExteriorPower.Basic`, `AlternatingMap`, real inner-product, and orthonormal-basis APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; current `Curvature.Provisional` producer and S07 ledger boundary | Mark the generic plane/exterior-square and explicit-witness tangent consumer subset implemented. Keep S08 partial: the current pinned Mathlib has no Riemann-curvature symmetry theorem, and the selected-extension producer still needs the S07 metric last-pair proof before `IsAlgebraicCurvatureAt` can be discharged. The algebraic component probes do not replace the independent nonconstant-metric Levi--Civita regression. Do not treat the explicit witness as a geometric completion. Leave standard sphere/hyperbolic manifolds, space forms, cones, Ricci/scalar contractions, naturality, and second Bianchi to their existing milestones. |
| `issue-50-adapter-response` / `009a200a5e779507b3e189d5855fdd4526338` | Restored the witness-gated tangent facade as the direct-only `Curvature.SectionalProvisional` and `Curvature.OperatorProvisional` modules, exported their pointwise sectional/operator declarations through the Chapter 1 umbrella, removed stale leaf imports, and synchronized ownership/S08 documentation with the public surface | Exact parent `c36c80a8bfacc48da2905b3933309af97f267a07`; the formerly elaborated tangent bodies at `aff33a14...`; pinned Mathlib `Bundle.ContMDiffRiemannianMetric`, `LinearAlgebra.ExteriorPower.Basic`, and the existing `Curvature.Provisional.curvature4`; local documentation rules in `contribute.md`, `pr-review.md`, and `mathlib-reviewing.md` | Keep the selected-extension producer provisional and require explicit `IsAlgebraicCurvatureAt` witnesses for plane/operator symmetry and positivity. The intrinsic leaves remain connection-free; metric last-pair/pair-interchange, unconditional witness discharge, quotient-of-planes/basis existence, and geometric model regressions remain open at S07/S08. |

| `review-response` / `7f730076fd42ca5dabdb9996661a11a71fd576f9` | Added the `Ch01.Geodesic.Variation` energy, length, and first-variation contracts and their Chapter 1 umbrella export; corrected the integral density to unrestricted `mfderiv` with a `velocityWithin` endpoint adapter, kept acceleration and fixed-endpoint witness contracts interior-aware, and retained S20 **Partial** | Morgan--Tian `prelim.tex`, pp. 41--43 (`morganTian2007`); do Carmo Ch. 9, pp. 185--201 (`doCarmo1992`); pinned `PathELength` and interval FTC/integration-by-parts APIs at Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`; rechecked the variation leaf, Chapter 1 umbrellas, and public declarations | Keep S20 **Partial** and the Mathlib-native density. Defer the intrinsic S18 covariant-derivative/geodesic producer and S19 minimizer/path-length canonicalization; replace the provisional `VelocityExtension`, endpoint adapter, and `pathELength` wrapper when those S18/S19 consumers land. Exact audited code head: `7f730076fd42ca5dabdb9996661a11a71fd576f9` |
| `workflow-review-response` / `11b2efdc7f80329db384644b3769152ac87a183c` | Added the GitHub-only retry/preserve behavior in `.github/workflows/lean.yml`: the pinned Lean-action step retains its first outcome, retries only when `build-status` is empty, and preserves a reported build failure; `.gitea/workflows/lean.yml` is unchanged | Rechecked the pinned [`leanprover/lean-action` `action.yml`](https://github.com/leanprover/lean-action/blob/38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9/action.yml) output contract (`SUCCESS`, `FAILURE`, or empty, with empty meaning the build step did not run); rechecked workflow name `Lean CI`, protected job `lake-build`, `pull_request` candidate-ref checkout, `build: true`, immutable checkout/action pins, and required status `Lean CI / lake-build (pull_request)` | Retain the GitHub-only retry for pre-Lake Mathlib-artifact setup failures; source/build failures remain blocking, and the protected status, job, ref, pins, and Gitea workflow stay unchanged. Remove the workaround after a pinned `lean-action` revision documents a nonempty terminal status for setup failures and that behavior is confirmed by a CI run. Exact audited workflow head: `11b2efdc7f80329db384644b3769152ac87a183c` |
| `issue-41-tensor-laplacian` / `a7b88d2da029456db6d1dbe21c77d54f13517e26` | Added the raw rank-generic `secondCovariantDerivative`/`connectionLaplacian` evaluators, scalar and one-form adapters, Riesz/finite-dimensional trace and orthonormal-frame bridges, constant-scalar, identity-section, and dimension regressions, a conditional outer-direction `TensorialAt` bridge, inner-direction add/smul laws with a `TensorialAt` packaging adapter, and covariant Christoffel plus metric-dual compatibility bridges | Morgan--Tian discussion preceding `lapformula`, pp. 39--40, `morganTian2007`; pinned Mathlib `CovariantDerivative.Basic`, `CovariantDerivative.Metric`, `Tensoriality`, and `Analysis.InnerProductSpace.Trace` APIs; existing `Connection.christoffel_formula` | Keep S12 partial: the evaluator representation is not a bundled tensor section, and unconditional producer instantiation, full dual-frame component signs, canonical Hessian/trace compatibility, and flat/nonconstant model probes remain follow-up work |
| `issue-41-public-boundary-review-response` / `c4f6fb8191c82bcdaa7872a699ab205b9550e803` | Removed the provisional tensor-derivative/Laplacian leaf from the stable `Ch01.lean` umbrella, documented the direct-import boundary beside the raw evaluator, and added an S12 provisional-debt row with an objective S13 consumer trigger | Accepted canonical-representation and provisional-debt policy in this roadmap; current Chapter 1 import graph; Morgan--Tian pp. 39--40 (`morganTian2007`); pinned Mathlib connection, tensoriality, and trace APIs; focused direct-leaf and stable-root elaboration against the pinned artifacts, plus source/import scans | Keep the raw evaluation layer direct-only. Before S13's `Curvature.bochnerFormula` is accepted, prove a smooth bundled, extension-independent producer and migrate that consumer; otherwise do not umbrella-export a canonical connection Laplacian. Preserve the exact `leviCivitaConnection` and conditional trace bridge |
| `issue-41-tensor-argument-linearity` / `71f61fa` | Added the unconditional constant-scalar tensor-argument laws for the raw mixed derivative, source-ordered second derivative, rank-preserving second-derivative section, and raw metric-trace evaluator, together with zero/neg normalization for the second evaluator and Laplacian wrappers. The directional calculus bridge explicitly handles Mathlib's totalized `mvfderiv` off differentiability; no producer, direction-slot tensoriality, or new connection is introduced | Morgan--Tian discussion preceding `lapformula`, pp. 39--40, `morganTian2007`; pinned Mathlib `Geometry.Manifold.MFDeriv.NormedSpace`/`Basic` (`mvfderiv_smul`, `mfderiv_zero_of_not_mdifferentiableAt`) and `Analysis.InnerProductSpace.Trace`; focused direct-leaf elaboration, typed exported-API probes, and `#print axioms` checks | Keep S12 partial and direct-only. The smooth bundled tensor producer, unconditional second-direction extension independence, full dual-frame component signs, canonical Hessian/trace compatibility, and flat/nonconstant model probes remain open; migrate only after the S13 replacement trigger is met |
| `issue-41-tensor-extension-locality` / `ee2c002` | Added pointwise locality for covector and tangent tensor-slot updates from the existing multilinearity/tensoriality predicates; proved unconditional first-direction extension independence for the raw mixed derivative and the outer slot of the source-ordered second derivative under explicit tensor-slot hypotheses; added guarded arbitrary differentiable-extension and two-family trace-sum certificates, preserving the exact `leviCivitaConnection` and the raw direct-only boundary | Morgan--Tian discussion preceding `lapformula`, pp. 39--40, `morganTian2007`; pinned Mathlib `Tensoriality` (`TensorialAt.pointwise₂`), `VectorBundle.MDifferentiable` (`mdifferentiableAt_extend`), `CovariantDerivative.Basic`, and `Analysis.InnerProductSpace.Trace`; direct pinned-artifact compilation of the changed leaf and source/import/hole scans | Keep S12 partial and direct-only. The smooth bundled tensor producer, inner-direction extension-independence producer (with the existing differentiability-guarded laws retained), full dual-frame component signs, canonical Hessian/trace compatibility, and flat/nonconstant model probes remain open; the new trace certificates are the permitted bridge until the S13 producer replacement trigger is met |
| `issue-41-inner-direction-locality` / `e04bd625f374f29aad6ec52cadb6afe86d343d01` | Added local-`MDiffAt` Leibniz and additivity laws for the source-ordered second derivative's inner direction, using the exact bundled `leviCivitaConnection` correction term; packaged those laws as a conditional Mathlib `TensorialAt` witness and added a pointwise equality adapter for locally differentiable direction extensions. The existing smooth-extension laws remain as compatibility wrappers, and no tensor-bundle producer or new connection is introduced | Morgan--Tian discussion preceding `lapformula`, pp. 39--40, `morganTian2007`; pinned Mathlib `CovariantDerivative.Basic` (`IsCovariantDerivativeOn.leibniz`, `.add`) and `Tensoriality` (`TensorialAt.pointwise`); direct pinned-artifact elaboration of the changed leaf, four exported `#print axioms` checks, and source/import/hole scans | Keep S12 partial and direct-only. The regularity premise that the first covariant derivative of every differentiable direction extension is `MDiffAt` remains explicit; a smooth bundled producer, unconditional inner-direction extension-independence theorem, full dual-frame component signs, canonical Hessian/trace compatibility, and flat/nonconstant model probes remain open |


| `A2-chart-density-null-transport` / `e960f338ac43b3d79f76f8aac8db8aafa91b9174` | Added the exact-source density-weighted chart-overlap `lintegral` transport law, using the pinned injective Jacobian API and the Gram-density transition identity; added countable-Lipschitz transport of `μHE[finrank ℝ E]`-null images and a scoped canonical `riemannianVolume` wrapper with explicit metric/Borel instances | Morgan--Tian Chapter 1 volume and cut-locus discussion, pp. 45--50 (`morganTian2007`); pinned Mathlib `MeasureTheory.Function.Jacobian`, Hausdorff-measure, Lipschitz-image, and `Geometry.Euclidean.Volume.Measure` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; canonical normalization declarations in `MorganTianLib/Ch01/Volume.lean`; fresh direct leaf elaboration, exported signatures, and `#print axioms` probes | Mark this focused pre-N1 A2 subset implemented.  Keep the Riemannian path-metric/chart-density identification, sphere/radial integration, ratio-of-integrals estimates, and N1/N2 consumers open; retain `ChangeOfVariables` as a direct provisional leaf under the existing umbrella boundary, and add no competing global measure, metric instance, or Jacobian vocabulary |
| `variation-criticality-deferral` / `5a65e9529de8de7ec736e41aa6b933034567d71c` | Removed the variation-indexed `FixedEndpointCriticalityWitness`, `AllVariationCriticalityWitness`, and criticality/acceleration equivalences; retained the first-variation formula, the one-way fixed-endpoint zero-acceleration implication, and the universal criticality premise; clarified that `CovariantAccelerationData` is curve-level and corrected the density-only reparameterization documentation | Morgan--Tian `prelim.tex`, pp. 41--43 (`morganTian2007`); do Carmo Ch. 9, pp. 185--201 (`doCarmo1992`); pinned interval FTC and `HasDerivAt` APIs; exact review findings on the universal test-field quantifier and variation-local acceleration | Keep S20 **Partial**. Reintroduce a criticality converse only after S18 supplies one curve-level acceleration field shared by every variation, a link from each first-variation package to that field, and a universal fixed-endpoint test-field realization; until then keep the converse/equivalence declarations deleted and the universal criticality predicate premise-only |
| `issue-44-plane-quotient` / `229bf12` | Added `Curvature.Plane`: the intrinsic unoriented quotient of independent ordered generators, the span characterization of quotient equality, the descended span, and inner-product/plain-bilinear sectional evaluators with representative and swap independence; integrated the witness-gated tangent-plane adapter and umbrella export | Morgan--Tian Definitions 1.6--1.7 and the constant-curvature paragraph, printed pp. 38--39 (`morganTian2007`); do Carmo Chapter 4, Section 3 (`doCarmo1992`); Petersen Chapter 3 (`petersen2016`); pinned `sectionalCurvature_changeBasis`, `Submodule.mem_span_pair`, and Lean quotient APIs; focused source elaboration, `#print axioms`, and import/hole/hygiene scans | Mark only this intrinsic-plane subset implemented. Keep S08 partial: the selected-extension producer still requires the S07 metric-symmetry witness, canonical orthonormal-basis choices and independent nonconstant-metric regression remain open, and standard sphere/hyperbolic manifolds plus all Ricci/naturality/Bianchi descendants remain at their named milestones |
| `issue-44-plane-consumers` / `8ffeb41113cb0c58d5abb2b6657be5db4b35dbe9` | Added the constant-curvature equivalence for linearly independent pairs and intrinsic quotient planes, together with its exact-metric, witness-gated tangent counterpart; proved that linear independence gives a nonzero decomposable exterior-square generator and used it to transfer positive curvature-operator bounds to genuine planes in both the algebraic and tangent APIs | Morgan--Tian Definitions 1.6--1.7, printed pp. 38--39 (`morganTian2007`); do Carmo Chapter 4, Section 3 (`doCarmo1992`); Petersen Chapter 3 (`petersen2016`); pinned Mathlib `ExteriorPower.Basic` universal-property API and the existing strict Gram criterion; completed Lean LSP diagnostics on all five changed files, focused pinned-artifact elaboration, consumer signature probes, exported `#print axioms` checks, and import/hole/hygiene scans | Mark this genuine-plane consumer subset implemented. Keep S08 partial: `IsAlgebraicCurvatureAt` remains explicit until S07 supplies metric last-pair skew and pair interchange; the independent nonconstant-metric Levi--Civita regression, canonical orthonormal-plane choices, and standard sphere/hyperbolic manifold examples remain open, with no Ricci, naturality, or Bianchi status change |
| `issue-57-architecture-response` / reviewed head `c7e264b9b3db5bcdc168280d8623a8663481de89` | Renamed the fixed-inner-product-space `Models.coneCurvature` declaration and its dependent theorem family to `Models.coneCurvatureModel`/`coneCurvatureModel_*`; retained the generic `coneWedgeBlockForm`, documented `coneCurvatureBlock`'s sole model caller and migration trigger, preserved the `Models.Cone` public import through `MorganTianLib/Ch01.lean`, and recorded the S16/S17 partial boundaries with `Models.coneCurvature` reserved for the later geometric owner | Morgan--Tian Definition 1.14, Proposition 1.15, and Corollary 1.16, printed pp. 40--41 (`morganTian2007`); pinned Mathlib `ExteriorPower.Basic`, `MFDeriv.SpecificFunctions`, `FiniteDimensionBilinear`, and `Curvature.Operator` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; rechecked the Chapter 1 umbrella import, public declaration names, and the existing S06/S07 producer boundary | Keep `Models.Cone`, `positiveReal`, `coneRadius`, `coneTangentProjection`, `coneForm`, `coneWedgeEquiv`, `coneWedgeBlockForm`, and `coneCurvatureDifferenceOperator` as partial reusable substrate. Keep `Models.coneCurvatureModel` as a noncanonical fixed-model consumer only and leave `Models.coneCurvature` unoccupied for the source-strength geometric producer. Migrate/delete `coneCurvatureBlock` after that producer consumes `coneWedgeBlockForm`; the replacement requires bundled cone metric/hom-bundle smoothness, the selected-extension-to-intrinsic Levi--Civita/curvature producer, and the exterior-square metric/Riesz eigenvalue/multiplicity bridge. No deferred producer is claimed at this revision; the audit scope is the exact reviewed head named above |
## Review and completion checklist

Before Z1, reviewers require:

- a complete source table with no unanchored claim or weakened hypothesis;
- exact declaration/docstring/module/import audits following the Mathlib style
  guides, while recognizing that upstreaming is separate;
- a public API search for duplicates and a compatibility decision for every
  shared name;
- `#print axioms`/`sorry`/transparency/heartbeat and forbidden-import audits;
- source citation and edition checks for every bibliography key;
- metric, curvature-sign, regularity, measure, and cut-locus gates recorded;
- final root import and downstream Chapter 1 consumer checks;
- the protected `Lean CI / lake-build (pull_request)` status at the exact head.

Green CI is required validation, but it is never used as evidence that the
formal statements faithfully implement Morgan--Tian without the source audit.
