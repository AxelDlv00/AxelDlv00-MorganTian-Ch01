# Morgan--Tian Chapter 1 roadmap

<!-- palimpsest-governance -->

Status: accepted bootstrap route at repository commit
`0a7e55543629438cacf6e25b698ba770274225d9`, with the A1 scalar, operator,
trace, and determinant/density comparison increments and completed G1 evidence
audit recorded below.  The Mathlib-native G2 route in
[`docs/G2_SUBSTRATE_DECISION.md`](docs/G2_SUBSTRATE_DECISION.md) was accepted
at `aa45255fc76b3de3870f6411dde9b1c733e39074`.  At accepted roadmap baseline
`80bdb7f7eb6bd1efb3b52b91cbb1293b52dd928d`, `Ch01.Metric` implements the
metric and Mathlib `C^1` distance/topology substrate, and `Ch01.Volume`
implements the normalized-volume family.  `Ch01.Curvature` implements the
independent inner-product-space curvature sign/order kernel and its five
regressions, and the merged `Ch01.Connection` module implements the bundled
Levi--Civita producer with smooth consumer regularity.  The focused F1
`Ch01.Connection.Christoffel` increment proves the canonical connection's
chart-coordinate formula and completes S03 while leaving S04--S05 open.  The
preceding G2 revision completes the supplied-metric source-distance
correspondence: it gives endpoint-preserving,
length-controlled piecewise-smooth replacements of `C^1` paths, flattens finite
chains to smooth paths without changing length, and identifies both auxiliary
infima with `Manifold.riemannianEDist`.  This revision separately completes E1:
`Ch01.MetricExistence` proves the generic smooth-vector-bundle metric theorem
and derives the arbitrary finite-dimensional tangent-bundle corollary without
assuming an inner product on the manifold model.  Together these results close
S01.  This focused revision does not mark the other G2 gates complete or unlock
G2 descendants.  This file is the repository-owned
route for the Chapter 1 library.  It is not a
transcription of the project brief, and each implementation claim is limited
to the exact audited revision named below.

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
the exact re-audit, freezes the implementation contract, and now records which
metric, volume, connection, and algebraic curvature-sign contracts have Lean
evidence.  The supplied-metric source-distance correspondence is now proved;
the status of other G2 completion checks is unchanged.

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
| `Volume` | normalized Riemannian volume, Borel and metric-measure coherence | chart and polar Jacobians |
| `Connection` | `CovariantDerivative`, metric compatibility, torsion-free, `hessian`, function and tensor connection Laplacians | Christoffel computations |
| `Curvature` | `curvature`, `(0,4)` form, `sectionalCurvature`, `ricci`, scalar, Bianchi, pullback naturality | coordinate contractions |
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
| S06 | `(1,3)`/`(0,4)` curvature and coordinate formula: Definition 1.4, pp. 37--38; `morganTian2007` | `Curvature.curvature`, `Curvature.curvature4` | F1 | S02--S03 | constant-curvature regression must verify argument order and the frozen sign convention | **Partial.** `Ch01.Curvature` proves the algebraic model operator/four-tensor pairing and exact component regression; the connection-produced manifold curvature and coordinate theorem remain open in F1 |
| S07 | Curvature symmetries and both Bianchi identities: Claim 1.5 (`Bianchi`), p. 38; `morganTian2007` | `Curvature.symm`, `bianchi1`, `bianchi2` | F1 | S06 and tensor covariant derivative | permutations and second-derivative regularity must match the chosen `(0,4)` order | Open |
| S08 | Sectional curvature, constant-curvature tensor identity, spherical/Euclidean/hyperbolic examples, and curvature operator: Definitions 1.6--1.7 and intervening model paragraph, pp. 38--39; `morganTian2007` | `Curvature.sectionalCurvature`, `constantCurvature`, `curvatureOperator`; `Models.standardSpaceCurvature` | F1 -> F3 | S06--S07 and exterior-square API; F1 curvature API for F3 models | fix orthonormal-pair independence and wedge normalization before positivity claims; standard models are sign regressions, not assumed examples | **Partial.** `Ch01.Curvature` supplies only the algebraic constant-curvature model and its orthonormal-pair sign regression; geometric sectional curvature, curvature operators, and standard-space examples remain open |
| S09 | Ricci and scalar curvature: Definition 1.8, p. 39; `morganTian2007` | `Curvature.ricci`, `scalarCurvature` | F1 | S06--S07, the F1 curvature API in S08, and finite-dimensional trace | contractions must reproduce the constant-curvature values with the frozen slot order | **Open geometric API.** The required second/fourth-slot algebraic contraction regression is proved in `Ch01.Curvature`, including dimensions zero and one; manifold Ricci and scalar curvature remain open |
| S10 | Pullback naturality of Riemann, Ricci, and scalar curvature: paragraph after Definition 1.8, p. 39; `morganTian2007` | `Curvature.curvature_naturality`, `ricci_naturality`, `scalarCurvature_naturality` | F1 | S02, S06, S09 and metric pullback | transport the canonical connection; no chart-isometry surrogate in the public theorem | Open |
| S11 | Contracted Bianchi identity: Lemma 1.9 (`divRic`), p. 39; `morganTian2007` | `Curvature.divRic` | F1 | S07, S09 and divergence | verify contraction order and `dR = 2 div Ric` with the source Laplacian/divergence signs | Open |
| S12 | Second covariant derivative and connection Laplacian for arbitrary-rank tensors: definitions before Lemma 1.10, pp. 39--40; `morganTian2007` | `Connection.secondCovariantDerivative`, `connectionLaplacian` | F1 | S02 and tensor-bundle contractions | theorem must be rank-generic; a one-form-only wrapper is insufficient | Open |
| S13 | One-form Bochner identity: Lemma 1.10 (`lapformula`), p. 40; `morganTian2007`; `gallotHulinLafontaine2004`, Prop. 4.36, p. 168, **unverified cross-check reported by Morgan--Tian** | `Curvature.bochnerFormula` | F1 | S05, S09, S12 | reconcile `df`, metric dual, Ricci contraction, and connection-Laplacian signs | Open |
| S14 | Space-form uniformization and quotient consequence: Theorem 1.11 and following paragraph, p. 40; `morganTian2007` | `Models.spaceFormClassification`, `spaceForm_quotient` or an explicit external theorem interface | F3 | S08, S19/F2 Hopf--Rinow interface, universal-cover/covering/isometry theory | retain completeness and simple connectivity in the classification, freeness/discreteness in the quotient, and add only the reviewed `2 <= n` non-vacuity gate | Open; human decision required if the classification proof exceeds Chapter 1 infrastructure |
| S15 | Einstein definition and dimension 2/3 consequence: Definition 1.12 and Example 1.13, p. 40; `morganTian2007` | `Models.einstein`, `einstein_constantCurvature_of_dim_le_three` | F3 | S08--S09 | state exact dimension alternatives and factor `lambda / (n - 1)` | Open |
| S16 | Open cone metric: Definition 1.14 (`conedefn`), p. 40; `morganTian2007` | `Models.coneMetric` | F3 | S01 and product-manifold metric | enforce positive radial coordinate and avoid a public coordinate-dependent metric | Open |
| S17 | Cone curvature block and eigenvalues: Proposition 1.15 (`conecurv`) and Corollary 1.16, pp. 40--41; `morganTian2007` | `Models.coneCurvature`, `coneCurvatureEigenvalue` | F3 | S08, S16, S03 | verify exterior-square block order, zero multiplicity, and `s^-2 (lambda_i - 1)` scaling | Open |
| S18 | Geodesic equation, coordinate ODE, IVP uniqueness/smoothness: Definition 1.17 and following paragraph, p. 41; `morganTian2007`; `doCarmo1992`, Ch. 3, pp. 61--75 | `Geodesic.isGeodesic`, intrinsic IVP/maximal solution | F2 | S02; `[CompleteSpace E]` for the checked ODE API; `[BoundarylessManifold I M]` for the all-initial-data contract, or `I.IsInteriorPoint p` for a point-local IVP | prove chart ODE/intrinsic equivalence, interval maximality, and smooth dependence; export the weakest manifold-level/interior-point hypothesis rather than `[I.Boundaryless]`; a pointwise equation is insufficient | Open; candidate code is prior art only |
| S19 | On a complete boundaryless manifold, minimizing geodesics and the Hopf--Rinow implication: paragraph before and Theorem 1.18, pp. 41--42; `morganTian2007`; `doCarmo1992`, Ch. 7, pp. 157--166; `lee2018`, Thm. 6.19 | `Geodesic.exists_minimizingGeodesic`, `hopfRinow` | F2 | S01, metric completeness, and the all-initial-data `[BoundarylessManifold I M]` branch of S18 | keep metric completeness and boundarylessness as independent public assumptions, and connect them to the canonical maximal geodesic and minimizer existence, with connected-component assumptions explicit | Open; the rejected dependency's facade is not evidence |
| S20 | Energy, first variation, criticality, constant speed, and energy/length inequalities: pp. 41--43; `morganTian2007`; `doCarmo1992`, Ch. 9, pp. 185--201 | `Geodesic.energy`, `Variation.firstEnergyVariation` | F2 | S01--S02 and S18 | exact path/variation regularity, endpoint terms, and equality conditions must remain visible | Open; Mathlib supplies length only |
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
| S35 | Flat/hyperbolic `sn_k`, `ct_k`, ODE, and radial coefficient: Definition 1.30 and following formulas, pp. 48--49; `morganTian2007`; `petersen2006`, Ch. 9, Sec. 1 | `Comparison.Model` plus Riccati/trace/determinant consumers | A1 | G0 and scalar/linear analysis | totalize `k = 0` without division by `sqrt 0`; analytic theorems may not claim a manifold producer | **Analytic layer implemented.** Model, scalar/operator/trace Riccati, determinant, `normDet`, and abstract density results exist; vector Sturm and geometric producers remain open |
| S36 | Positive-curvature model needed by the upper analogue: unnumbered paragraph before Lemma 1.32, p. 49; `morganTian2007`; `petersen2016`, Sec. 6.4, Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257 | `Comparison.snPos`, `logDerivPos`, positive Riccati/Sturm/density consumers | A1 | scalar and finite-dimensional operator analysis | restrict to `K > 0` and the first-pole interval; separate analytic inputs from C1 geometry | **Analytic layer implemented.** Origin limits, first pole, scalar/operator comparison, and abstract density results exist; no geometric lower-Jacobian producer exists |
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
After G2, F1, F2, and the normal-geometry-independent A2 measure primitives run
in parallel while A1 may continue.  F3 waits for both F1 and F2 because S14
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
- **G2** (`G1`, human gate): first merge the repository-owned substrate
  selection in `docs/G2_SUBSTRATE_DECISION.md`; then implement and prove its
  metric/distance/measure and connection bridges, audit assumptions, and
  freeze curvature signs.  The metric, Mathlib `C^1` distance/topology, smooth
  and finite piecewise-smooth path types, both infimum comparisons and
  equalities, and finite preconnected witness are present in `Ch01.Metric`;
  the measure/volume family is present in `Ch01.Volume`; the bundled connection
  producer and regularity are present in `Ch01.Connection`; and the algebraic
  sign/order model and all five regressions are present in `Ch01.Curvature`.
  The supplied-metric source-distance bridge is complete.  This focused
  revision does not mark the other G2 completion checks complete or unlock a
  descendant; the algebraic kernel does not claim a manifold curvature API.
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
  issue #10.  Vector Sturm remains open.  The
  positive-curvature geometric lower-Jacobian conclusion remains gated on the
  C1/J1/N2 producers and is not claimed by A1.
- **A2** (`G2`): the pre-N1 measure toolkit: chart Jacobians, checked
  Sard/change-of-variables and measurability primitives, sphere/radial
  integration, and ratio-of-integrals lemmas independent of cut, exponential,
  or polar geometry.  It supplies S28 nullity but owns no post-N1 polar-density
  equality; that work is N2.
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
and bundled connection producer/regularity are merged, and the supplied-metric
smooth/piecewise-smooth distance correspondence now has a Lean implementation.
This focused revision does not change the status of other G2 completion checks.

## Provisional debt and replacement triggers

| Provisional construction | Permitted use and cost | Replacement trigger |
| --- | --- | --- |
| Chart-coordinate `(J,DJ)` pairs, state-transition flows, chart partitions, parallel frames | Private proof reductions for J1/V1/C1/C2; duplicate coordinates and increase bridge obligations | Intrinsic Jacobi existence plus chart/frame equivalence theorem lands; final theorem signatures contain no chart artifact |
| Complete-space `globalGeodesic`/`expMapGlobal` helpers | F2 exploration only; they hide maximal-domain and local-domain cases | F2 proves the canonical maximal exponential API and a complete-case equivalence |
| `IsRadialJacobi`, polar-density, cut-time, cut-locus, local-isometry, and injectivity-radius facades | A1/A2/N1/N2 integration scaffolding only; producer semantics are otherwise absent | Retire or make private when N1/N2/C2 proves the named geometric producer/equivalence; no final source theorem quantifies over the facade |
| Abstract `expBallVolume` density ratios | Analytic ratio lemmas only; not a manifold volume theorem | C3 proves polar density = Riemannian measure and exp preimage = metric ball off the null cut locus |
| `Option`-valued exceptional cut time, radius, or exponential-domain helpers | Private construction aid only; `none` is easy to misread and duplicates the canonical extended value | Replace at the public boundary by the proved `WithTop`/maximal-domain representation; delete after N1 equivalences land |
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
reviewed commit.  The audit history is:

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
| `issue-15-governance` / audited baseline `599f5241fee042dd50e9e60a3a343a1cbac7aa39` | Recast S01--S43 as a field-complete source-to-API ledger; added independent finite-dimensional E1 for the previously hidden metric-existence claim; made the complete-and-boundaryless scope explicit for the geodesic IVP descendants S19 and S26--S29 and for S39; reconciled every ledger prerequisite with an acyclic node schedule by adding `F2 -> F3`, placing pre-cut measure primitives in A2, and adding post-cut polar/Gaussian node N2 for S30--S33; connected every bibliography entry to exact rows; distinguished checked, unavailable, and unverified evidence; recorded the `r^-2 g` normalization correcting the S42 proof typo | Original Morgan--Tian arXiv v2 `prelim.tex` and PDF through Theorem 1.36, including its ordinary smooth-manifold convention, the `n`-dimensional opening, the complete-manifold scope before Definition 1.24, and the S14/S27--S34 producer order; the ledger's hard prerequisites checked against the milestone graph, frontier prose, and node contracts; pinned Mathlib `IntegralCurve.ExistUnique` and `IsManifold.InteriorBoundary`, which distinguish `I.IsInteriorPoint p`, `[BoundarylessManifold I M]`, and the stronger `[I.Boundaryless]`; [Mathlib PR #33714](https://github.com/leanprover-community/mathlib4/pull/33714), with `InnerProductSpace ℝ F`, `FiniteDimensional ℝ EB`, `SigmaCompactSpace B`, and `T2Space B` as prior-art existence assumptions; pinned Mathlib `ContMDiffRiemannianMetric` source for the existing-fiber-topology requirement; retained do Carmo, Petersen 2016, Lee 2018, and CGT copies; absence audit for Petersen 2006, Gallot--Hulin--Lafontaine 2004, Sakai 1996, and Cheeger--Ebin 1975; metric/curvature/volume scaling; project modules/imports and workflow at exact baseline `599f5241fee042dd50e9e60a3a343a1cbac7aa39` | Keep the accepted Mathlib-native route, canonical representations, and CI contract.  Add E1 as a G0-parallel finite-dimensional final-completeness obligation, with a topology-compatible model inner product and the actual partition-of-unity hypotheses, without changing G2 descendants or supplied-metric generality.  Require `I.IsInteriorPoint p` for point-local geodesic/exponential statements and the weakest `[BoundarylessManifold I M]` class for source-facing all-points contracts; add completeness separately to S28--S29's global cut conclusions and S39's full-ball conclusion.  Schedule F3 after F2, N1 after A2, and N2 after F1/A2/N1 so every row has an ordered closer and C1/C2 consume completed polar/Gaussian producers.  Preserve S42's statement while using the corrected proof normalization.  G2 debt remains the smooth/piecewise-smooth distance bridge, bundled connection producer/regularity, and curvature regressions; unavailable cross-checks are verification debt with removal-or-verification triggers |
| `G2-curvature-kernel` / `MorganTianLib/Ch01/Curvature.lean` | Added the basis-free constant-curvature model operator and four-tensor, proved their Morgan--Tian third/fourth-slot pairing, and proved the component, Jacobi, index-form, orthonormal-sectional, and finite-orthonormal-basis contraction regressions | Accepted roadmap baseline `80bdb7f7eb6bd1efb3b52b91cbb1293b52dd928d`; Morgan--Tian Definition 1.4 and coordinate formula, pp. 37--38, Definition 1.8, p. 39, and Jacobi/index formulas, pp. 43--44; pinned Mathlib real inner-product and orthonormal-basis APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Keep the algebraic API independent of the manifold connection and impose no unnecessary dimension bound; dimensions zero and one remain covered by the contraction theorem.  Make no constant-curvature-manifold, sectional-curvature, or Ricci-curvature claim; keep G2 blocked on the source-distance gate and leave the manifold curvature API to F1 |
| `issue-18-connection` / `MorganTianLib/Ch01/Connection.lean` | Added the explicit-metric Mathlib-native Levi--Civita producer, compatibility, torsion, source-ordered Koszul, differentiable-field pointwise uniqueness, and smooth consumer regularity; exported the module through the Chapter 1 umbrella | Morgan--Tian Theorem 1.2, printed pp. 35--36; do Carmo (1992), Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; Lee (2018), Theorem 5.10 and Corollary 5.11(b), equation (5.10), printed pp. 123--124; pinned Mathlib `CovariantDerivative`, metric, torsion, local-frame, manifold-derivative, and finite-dimensional dual APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; Apache-licensed Mathlib PR #36845 head `41e2b25a520d7a24f37062855d2b091dab7a5d9d` and PR #36036 head `31613e7e48c4559a8be4de48121c911d74586744` as modified prior art only | Mark S02 and the connection bridge complete with no project connection alias or public chart facade; retain G2 as open on the independent smooth/piecewise-smooth distance correspondence |
| `G2-smooth-distance-correspondence` / `MorganTianLib/Ch01/Metric.lean` | Added endpoint-preserving quantitative chart replacement for `C^1` paths, compact monotone subdivision into accepted smooth segments, the limiting reverse infimum inequality, endpoint-flat smooth concatenation with exact length additivity, and equality of both source-facing infima with `Manifold.riemannianEDist` | Accepted main baseline `9f735b3d1ff28252afed506ba74db28d0d74412a`; Morgan--Tian Definition 1.1 and following paragraph, p. 35; pinned Mathlib `Riemannian.Basic`, `Riemannian.PathELength`, smooth-transition, manifold-chart, and compact-cover APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Mark the supplied-metric G2 distance component complete and S01 partial only on E1 metric existence.  Keep the auxiliary infima as correspondence statements, add no ambient metric or stronger global assumption, and leave all other G2 gate and descendant statuses unchanged in this focused revision |
| `issue-26-christoffel` / `MorganTianLib/Ch01/Connection/Christoffel.lean` | Added the chart-coordinate coefficient theorem for the explicit-metric canonical Levi--Civita connection, including the local coordinate-frame bracket calculation, chart/manifold derivative bridge, Koszul first-kind identity, and inverse-Gram contraction | Accepted roadmap baseline `07d2a0be1a7aa3e38d827756b6585edb5a2ade60`; Morgan--Tian equation (1.1), printed p. 36; do Carmo (1992), Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; Lee (2018), Corollary 5.11(b), equation (5.10), printed pp. 123--124; pinned Mathlib chart, tangent local-frame, manifold derivative, Gram matrix, and nonsingular inverse APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6` | Mark S03 complete without defining another connection or public coordinate facade.  Require an explicit smooth metric and an interior chart point, keep coordinate data private, and leave Hessian S04, function Laplacian S05, and all curvature/tensor-Laplacian rows open |
| `issue-26-review-response` / `b57eb2ee13bfce92709df681f199ff1888c568eb` | Corrected the do Carmo and Lee source anchors for the connection producer and Christoffel bridge across the Lean module docstrings, G2 decision, bibliography, S02/S03 ledger rows, and audit history; no declaration or representation changed | Retained do Carmo scan: Theorem 3.6 and Remark 3.7/formula (10), printed pp. 55--56; retained Lee second-edition PDF: Theorem 5.10 and Corollary 5.11(b), equation (5.10), printed pp. 123--124; Morgan--Tian equation (1.1), p. 36 | Keep `Connection.leviCivitaConnection`, `Connection.christoffel_formula`, private chart plumbing, and S03 completion unchanged; this is documentation/source-mapping correction only |
| `E1-metric-existence` / `MorganTianLib/Ch01/MetricExistence.lean` | Added `nonempty_contMDiffRiemannianMetric`, the generic smooth-vector-bundle theorem built from an actual smooth partition of unity, and the distinct `nonempty_contMDiffRiemannianMetric_tangentSpace` corollary, whose auxiliary Euclidean form is transported internally through Mathlib's finite-dimensional continuous linear equivalence; exported the focused module through the Chapter 1 umbrella.  Nested hom-bundle synthesis has a 400000-heartbeat cap, and five private finite-sum or coordinate-transport proofs have scoped 800000-heartbeat caps | Accepted roadmap revision `a6684bb6eef31dbdc75c76e541b4f4475bc1e303`; Morgan--Tian Definition 1.1 and following existence paragraph, printed p. 35; pinned Mathlib `ContMDiffRiemannianMetric`, `ContMDiffVectorBundle`, hom-bundle, bounded-unit-ball, smooth partition-of-unity, and `toEuclidean` APIs at `520045ab14e26149ee970e2e617ca04b09bde5d6`; Apache-licensed Mathlib PR #33714 exact head `c4cbb8b896a4db75bf49cf1ab0a898232cede01e` as modified prior art absent from the pinned dependency and as provenance for the 800000-heartbeat proof boundaries | Mark E1 and S01 complete.  Keep `Bundle.ContMDiffRiemannianMetric` as the only public metric representation, add no global competing instance, and keep the generic model-fiber `InnerProductSpace` separate from the tangent theorem's weaker arbitrary finite-dimensional normed model.  Treat the private heartbeat caps as a named elaboration-performance exception: re-audit or remove them when the pinned dependency changes.  Do not change the completion state of other G2 gates, F1, F2, A2, or their descendants |

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
