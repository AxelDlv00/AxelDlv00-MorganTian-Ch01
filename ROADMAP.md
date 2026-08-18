# Morgan--Tian Chapter 1 roadmap

Status: accepted bootstrap route at repository commit
`0a7e55543629438cacf6e25b698ba770274225d9`, with the A1 scalar comparison
increment recorded below.  This file is the repository-owned route for the
Chapter 1 library.  It is not a transcription of the project brief, and each
implementation claim is limited to the exact audited commit named below.

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
path-length APIs.  The candidate DoCarmo connection files remain prior art;
G2 must still check that their intrinsic geodesic conventions are compatible
before selecting that repository as a dependency.

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
- The candidate `palimpsest/Hopf-Rinow-DoCarmo` main commit
  `60c3e1f6493646d667a0bb645f99110a34d26e00`, which is not yet an accepted
  dependency and is not used by this bootstrap package.
- The reference Morgan--Tian development as prior art only.  Its 168-file,
  approximately 50,700-line Chapter 1 split and its Chapter 1 to Chapter 2
  import are specifically not adopted.
- The publication records and stable URLs in `docs/references.bib`.

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

G2 freezes representations before F1--J1.  The intended choices are:

- **Metric and distance.** Use Mathlib's
  `ContMDiffRiemannianMetric`/`RiemannianBundle` and
  `IsRiemannianManifold`, with `pathELength` and `riemannianEDist` as the
  induced length/distance infrastructure.  If the dependency gate selects an
  explicit metric object for differential geometry, it must have proved
  conversion, topology, distance, norm, and measure coherence lemmas.  Two
  unrelated public metric or distance structures are forbidden.
- **Connection.** The public connection is the pinned bundled
  `CovariantDerivative`-style object selected by G2, with metric compatibility
  and zero torsion.  If that name is supplied by a reviewed shared dependency
  rather than Mathlib, the bridge to Mathlib's bundle metric is public and
  proved.  A chart Christoffel formula is an implementation theorem, not a
  second connection.
- **Curvature.** The public `(1,3)` tensor is `R X Y Z` with
  `R X Y Z = nabla_X(nabla_Y Z) - nabla_Y(nabla_X Z) -
  nabla_[X,Y] Z`.  The `(0,4)` form is `g (R X Y W) Z`, so its argument order
  agrees with the Chapter 1 `R_{ijkl}` convention.  Sectional curvature is
  `R X Y X Y` on an orthonormal pair.  A constant-curvature model must produce
  `R_{ijkl} = lambda (g_{ik} g_{jl} - g_{il} g_{jk})`; this is the kernel test
  before J1.
- **Geodesics and exponential.** Reuse an accepted intrinsic geodesic,
  maximal-domain, minimizing, and exponential API if G2 accepts
  Hopf--Rinow-DoCarmo.  Otherwise build the minimum local intrinsic API in
  `MorganTianLib.Ch01.Geodesic` and record the migration trigger.  The maximal
  exponential domain preserves an unbounded/complete case rather than using a
  finite-radius facade.
- **Jacobi fields.** `JacobiField gamma` is an intrinsic tangent-bundle field
  along `gamma` satisfying the covariant Jacobi equation.  Chart `(J,DJ)`
  pairs and parallel-frame matrices are private proof representations, with
  explicit equivalence theorems.  Conjugacy means a nonzero endpoint-vanishing
  intrinsic Jacobi field; the kernel of `d exp` equivalence is proved before
  local-diffeomorphism arguments.
- **Index form.** The public index form is the intrinsic symmetric bilinear
  integral on fields along a geodesic, with endpoint conditions stated
  explicitly.  A frame/inner-product-space form is an adapter proved equal to
  it, never a replacement definition.
- **Cut and injectivity.** Cut time, cut locus, and injectivity radius use
  codomains that retain `infty`.  Book-definition equivalences (frontier of
  the maximal minimizing domain, distance to the cut locus, and the conjugate
  or broken-geodesic alternatives) are required before comparison APIs use
  them.
- **Measure and volume.** Use Mathlib measures, metric balls, tangent-space
  polar integration, and the model-space denominator coherently.  A ratio for
  an arbitrary density is an A1/A2 analytic lemma only; it is not
  Bishop--Gromov until N1/C3 prove the density and metric-ball equalities.

### Proposed module and declaration ownership

The names below are families and ownership boundaries, not a promise that all
files are created by G0:

| Module | Public families | Internal/provisional material |
| --- | --- | --- |
| `Metric` | canonical bundle metric predicates, coherence bridges, rescaling | chart components |
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

This table is the completeness ledger.  Every row gets a declaration/proof or
an explicit gated milestone; unnumbered source prose is included rather than
silently dropped.  Pages are printed Chapter 1 pages in arXiv v2.

| Source claim and anchor | Intended API/module | Milestone and prerequisite | Current status |
| --- | --- | --- | --- |
| Riemannian metric and metric ball, Definition 1.1, pp. 35--36; `morganTian2007` | Mathlib metric bridge, `Metric` | G2; Mathlib metric audit | inventory |
| Fundamental theorem of Levi--Civita, Theorem 1.2, p. 35; `morganTian2007`, `doCarmo1992` Ch. 2, pp. 44--51 | `Connection.covariantDerivative` | G2 then F1 | inventory |
| Christoffel formula (1.2), p. 36; `morganTian2007` | `Connection.christoffel_formula` | F1, chart bridge | inventory |
| Hessian definition and `Hessformula`, Definition/Lemma 1.3, pp. 36--37; `morganTian2007` | `Connection.hessian`, symmetry/formula lemmas | F1 | inventory |
| Function Laplacian as Hessian trace, p. 37; `morganTian2007` | `Connection.laplacian` | F1 | inventory |
| Curvature `(1,3)` and `(0,4)` definitions and coordinate formula, Definition 1.4, pp. 37--38; `morganTian2007` | `Curvature.curvature`, `curvature₄` | F1; sign gate | inventory |
| Symmetries and first/second Bianchi, Claim 1.5, p. 38; `morganTian2007` | `Curvature.bianchi₁`, `bianchi₂` | F1 | inventory |
| Sectional curvature and curvature operator, Definitions 1.6--1.7, pp. 38--39; `morganTian2007` | `sectionalCurvature`, `curvatureOperator` | F1 | inventory |
| Ricci and scalar curvature, Definition 1.8, p. 39; `morganTian2007` | `ricci`, `scalarCurvature` | F1 | inventory |
| Naturality of Riemann, Ricci, and scalar curvature under diffeomorphism pullback, unnumbered paragraph after Definition 1.8, p. 39; `morganTian2007` | `Curvature.curvature_naturality`, `ricci_naturality`, `scalarCurvature_naturality` | F1; metric/connection pullback bridge | inventory |
| Contracted Bianchi/divergence of Ricci, Lemma 1.9 (`divRic`), p. 39; `morganTian2007` | `divRic` | F1 | inventory |
| Second covariant derivative and connection Laplacian on tensors of arbitrary rank, unnumbered definitions before `lapformula`, pp. 39--40; `morganTian2007` | `Connection.secondCovariantDerivative`, `Connection.connectionLaplacian` | F1; tensor-bundle trace bridge | inventory |
| Bochner/Laplacian identity, Lemma 1.10 (`lapformula`), p. 40; `morganTian2007`, `gallotHulinLafontaine2004` (claimed cross-check: Proposition 4.36, p. 168, per Morgan--Tian; 2004 edition text unavailable, so unverified) | `bochnerFormula`, `laplacianDistance` | F1; Morgan--Tian primary, Gallot cross-check unverified | inventory |
| Uniformization statement, Theorem 1.11, p. 40; `morganTian2007` | Chapter 1 exported interface or gated external theorem | F3; preserve strength with a `2 <= n` non-vacuity gate | inventory |
| Einstein definition/consequences, Definition 1.12 and Example 1.13, p. 40; `morganTian2007` | `Models.einstein`, constant-curvature contractions | F3 | inventory |
| Cone metric definition, Definition 1.14 (`conedefn`), p. 40; `morganTian2007` | `Models.coneMetric` | F3 | inventory |
| Cone curvature proposition, Proposition 1.15 (`conecurv`) and eigenvalue corollary 1.16, pp. 40--41; `morganTian2007` | `Models.coneCurvature`, `coneCurvatureEigenvalue` | F3 | inventory |
| Geodesic definition/coordinate IVP, Definition 1.17, p. 41; `morganTian2007`, `doCarmo1992` Ch. 3, pp. 61--75 | `Geodesic.isGeodesic`, IVP | F2 | inventory |
| Hopf--Rinow, Theorem 1.18, pp. 41--42; `morganTian2007`, `doCarmo1992` Ch. 7, pp. 157--166 | `Geodesic.hopfRinow` adapter | F2/G2 | inventory |
| Length, energy, Cauchy--Schwarz, first variation, and geodesic criticality, pp. 41--43; `morganTian2007`, `doCarmo1992` Ch. 9, pp. 185--201 | `Geodesic.energy`, `Variation.firstEnergyVariation` | F2 | inventory |
| Geodesic variations and Jacobi equation, pp. 43--44; `morganTian2007`, `doCarmo1992` Ch. 5, pp. 101--121 | `Jacobi.jacobiEquation`, variation bridge | J1; F1/F2 | inventory |
| Conjugate point definition, Definition 1.19, p. 44; `morganTian2007` | `Jacobi.IsConjugate` | J1 | inventory |
| Index-form second variation and arbitrary-family boundary term, pp. 43--45; `morganTian2007`, `doCarmo1992` Ch. 9, pp. 185--201 | `IndexForm.secondVariation` | V1; exact regularity gate | inventory |
| Minimal subsegments/no conjugate points, Proposition 1.20 (`jacmin`), pp. 44--45; `morganTian2007`, `petersen2006` Ch. 5, Prop. 19/Lem. 14, pp. 139--140 | `IndexForm.minimizer_no_conjugate` | V1 | inventory |
| Jacobi null-space claim 1.21, p. 44; `morganTian2007` | `IndexForm.nullspace_iff_jacobi` | V1 | inventory |
| Exponential map/maximal star domain, Definition 1.22, p. 45; `morganTian2007`, `doCarmo1992` Ch. 3, pp. 61--75 | `Geodesic.exp`, maximal domain | F2 | inventory |
| Differential of exponential via Jacobi fields and local diffeomorphism `star`, Corollary 1.23, pp. 45--46; `morganTian2007` | `Jacobi.dExp_eq_endpoint`, `Geodesic.exp_local_diffeomorph` | J1/F2 | inventory |
| Cut locus and exponential diffeomorphism, Definition 1.24/Proposition 1.25, p. 46; `morganTian2007`, `petersen2006` Ch. 5, Lem. 12, p. 133 and Prop. 19, p. 139 | `Normal.cutLocus`, `Normal.exp_on_regular_domain` | N1 | inventory |
| Injectivity radius and frontier/conjugate alternatives, Definition 1.26, p. 46; `morganTian2007`, `petersen2006` Ch. 5 | `Normal.injectivityRadius`, equivalences | N1 | inventory |
| Gaussian normal metric expansion `metricexp`, equation (1.8), pp. 46--47; `morganTian2007`, `sakai1996` Prop. 3.1, p. 41, with sign conversion | `Normal.metricExpansion` | F3/N1; term audit | inventory |
| Gauss lemma, polar metric and volume element, p. 47; `morganTian2007`, `petersen2006` Ch. 5, Lem. 12, p. 133 | `Normal.gaussLemma`, polar Jacobian | N1/A2 | inventory |
| Gaussian-coordinate Laplacian, Lemma 1.27, p. 47; `morganTian2007` | `Normal.laplacianGaussian` | F1/N1 | inventory |
| Distance-Laplacian local expansion `Delta r = (n-1)/r - (r/3) Ric(v,v) + O(r^2)`, unnumbered computation before Exercise 1.28, p. 48; `morganTian2007`, `petersen2006` pp. 265--268 | `Normal.laplacianDistance_asymptotic` | F3/N1; `metricexp` and Gaussian-Laplacian consumers | inventory |
| Calabi weak/distributional distance-Laplacian inequality and test-function formulation, Exercise 1.28 and Remark 1.29, p. 48; `morganTian2007`, `petersen2006` Lemma 42, p. 284 | `Comparison.laplacianDistance_weak` | C2; require `2 <= n` locally for the all-manifold distributional theorem; F1/N1 plus checked distribution/test-function integration API | inventory |
| Hyperbolic/flat model functions `sn_k` and `ct_k`, Definition 1.30, p. 48; `morganTian2007`, `petersen2006` Ch. 9, Section 1 | `Comparison.sn`, `Comparison.ct` | A1; define the radial coefficient piecewise at `k = 0` | model ODE, positivity, first integral, radial coefficient, small-radius bound, and scalar Riccati comparison implemented at `70cc263f77dc9ee70b6246a94edd00f3f7f6a13d`; vector/operator consumers pending |
| Positive-curvature spherical model for the upper comparison, implicit in the unnumbered analogue before `localdiffeo`, p. 49; `morganTian2007`, `petersen2016` Section 6.4, Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257 | `Comparison.snPos`, `Comparison.logDerivPos`, positivity and first-zero facts | A1; for `K > 0`, valid on `0 < r < pi / sqrt K`; explicit C1 input | total flat/spherical profile, ODE, first-pole radius/zero, positivity interval, and logarithmic derivative implemented at `70cc263f77dc9ee70b6246a94edd00f3f7f6a13d`; Sturm comparison pending |
| Sectional curvature comparison `SCC`, Theorem 1.31, p. 49; `morganTian2007`, `petersen2006` Ch. 9, Section 1 | `Comparison.sectional` | C1; A1/J1/N1 | inventory |
| Upper sectional-curvature comparison on a regular polar segment: if `K > 0`, `sec <= K`, and `0 < r < min (r_0, pi / sqrt K)`, then `(snPos' K r / snPos K r) * g_r <= Hess r`, `snPos K r ^ 2 * g_S <= g_r`, and `snPos K r ^ (n - 1) <= J(r, theta)` for the normalized polar Jacobian; unnumbered analogue immediately before `localdiffeo`, p. 49; `morganTian2007`, `petersen2006` Ch. 9, Section 1; `petersen2016` Thms. 6.4.3/6.4.6, pp. 255--257 | `Comparison.sectional_upper` | C1; A1 positive model/J1/N1, and an explicit prerequisite for L1 `injvol` | inventory |
| Curvature-norm local diffeomorphism `localdiffeo`, Lemma 1.32, p. 49; `morganTian2007` | `Comparison.exp_local_diffeomorph_of_curvature_bound` | C1; A1 positive model/J1/N1; use an unbounded radius when `K = 0`, and `pi / sqrt K` when `K > 0` | inventory |
| Ricci comparison `riccurvcomp`, Theorem 1.33, p. 49; `morganTian2007`, `petersen2006` Ch. 9, Section 1 | `Comparison.ricci` | C2; A1/F1/J1/N1 | inventory |
| Bishop--Gromov relative comparison `BishopGromov`, Theorem 1.34, p. 49; `morganTian2007`, `cheegerGromovTaylor1982` Prop. 4.1 | `Comparison.bishopGromov` | C3; A2/C2/N1 | inventory |
| Lower volume from injectivity `injvol`, Proposition 1.35, p. 50; `morganTian2007` | `Comparison.volume_lower_of_inj` | L1; C1 (including the upper sectional comparison)/C3/N1 | inventory |
| Volume-to-injectivity `volinj`, Theorem 1.36, p. 50; `morganTian2007`, `cheegerGromovTaylor1982` Thm. 4.3 and (4.22), p. 46; `cheegerEbin1975` Thm. 5.8, p. 96 | `Comparison.inj_lower_of_volume` | L1; human depth gate | inventory |

The unlabelled rows are anchored by section, numbered statement where the PDF
has one, and printed page.  The source's later Chapters 2 and 3 are not
included in this ledger.

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
- The radius in `localdiffeo` is an extended radius: it is unbounded when
  `K = 0` and is `pi / sqrt K` when `K > 0`.  The formal statement must not
  obtain a spurious zero radius from total division by `sqrt 0`.
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

## Milestone DAG

Each node is a focused, reviewable PR.  A node is complete only when its public
statements, proofs, documentation, imports, and source anchors pass review.

```text
G0 --> G1 --> G2
 |              |--> F1 --> F3
 |              |--> F2
 |              `--> A2
 `--> A1

F1 + F2                  --> J1 --> V1
F2 + J1 + V1             --> N1
A1 + J1 + N1             --> C1
A1 + F1 + J1 + N1        --> C2
A2 + C2 + N1             --> C3
C1 + C3 + N1             --> L1
G0 + G1 + G2 + F1 + F2 + F3 + A1 + A2 + J1 + V1 + N1 + C1 + C2 + C3 + L1
                           --> Z1
```

The frontiers are intentional: A1 starts directly after G0 and runs in
parallel with G1 and the human-gated substrate route.  After G2, F1, F2, and
A2 run in parallel while A1 may continue; F3 starts after F1 and joins Z1
independently.  J1 waits only for F1/F2, V1 waits for J1, and N1 waits for
F2/J1/V1.  C1 and C2 then run in parallel with their listed A1, foundation,
Jacobi, and normal prerequisites.  C3 waits for A2/C2/N1, not C1.  L1 waits
for C1/C3/N1, and Z1 waits for every prior node and therefore every inventory
row, including F3.

Node contracts:

- **G0**: this roadmap, bibliography, package, toolchain, manifest, root
  module, and workflow. No mathematical implementation.
- **G1** (`G0`): close the table above with current Mathlib and candidate dependency
  signatures, import graph, and exact source anchors.
- **G2** (`G1`, human gate): human-select the substrate; prove metric/distance/measure and
  connection bridges, audit assumptions, and freeze curvature signs.
- **F1** (`G2`): connection, Hessian/function and tensor connection
  Laplacians, curvature, Bianchi, Ricci/scalar, divergence/Bochner,
  naturality, and rescaling.
- **F2** (`G2`): intrinsic geodesic IVP, speed/energy/first variation, Hopf--Rinow,
  maximal exponential domain, zero differential, and minimizing neighborhoods.
- **F3** (`F1`): space forms, Einstein consequences, cones, coordinate curvature, and
  normal-coordinate prerequisites.
- **A1** (`G0`): hyperbolic/flat `sn`/`ct`, the positive-curvature `snPos` and
  logarithmic derivative with validity/first-zero facts, scalar/vector/operator
  Sturm and Riccati comparison, determinant/trace inequalities, and
  small-radius asymptotics independently of unproduced manifold data.
- **A2** (`G2`): Riemannian measure/Jacobian, sphere/radial integration,
  measurability, and ratio-of-integrals lemmas.
- **J1** (`F1`, `F2`): intrinsic Jacobi equation, existence/uniqueness/linearity, chart and
  frame reductions, geodesic variations, and `d exp`.
- **V1** (`J1`): exact regularity for arbitrary-family first/second variation,
  intrinsic/frame index equality, fundamental lemma, negative directions, and
  the minimizer/no-conjugate theorem.
- **N1** (`F2`, `J1`, `V1`): segment domain, uniqueness, cut time/locus, nullity, injectivity
  radius, exponential diffeomorphism, Gauss lemma, polar metric/shape/volume,
  and Gaussian claims.
- **C1** (`A1`, `J1`, `N1`): the lower-bound SCC statement, its unnumbered
  upper-sectional-bound analogue, and the `localdiffeo` consequence without
  an extra curvature hypothesis.  On a regular polar segment, the upper
  comparison consumes A1's positive-curvature model only for
  `0 < r < min (r_0, pi / sqrt K)` and gives the lower shape, angular-metric,
  and normalized-Jacobian directions stated in `Comparison.sectional_upper`.
  It is required by the lower sphere-volume estimate in `injvol`.
- **C2** (`A1`, `F1`, `J1`, `N1`): radial Jacobi matrix and trace/determinant
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
  Chapter 1 interface checks.  In particular, F3-owned rows cannot bypass Z1.

## Dependency alternatives and hard gates

G2 compares the following routes in a written human decision.  The comparison
must cover standalone CI reproducibility, immutable pinning, license and
provenance, transitive dependencies/import size, Mathlib coherence, axiom and
`sorry` inventory, semantic coverage, public-name collisions, maintenance
ownership, and the number of bridge declarations.

1. **Reviewed Git dependency (preferred when ready).** Use an immutable accepted
   Hopf--Rinow-DoCarmo commit only after compatible license/toolchain/Mathlib
   pins, green CI, unconditional intrinsic APIs, and no path-only transitive
   dependencies are verified.
2. **Scoped extraction/vendor fallback.** If that repository is not stable or
   lacks required foundations, adapt only the minimum Apache-licensed modules,
   retain provenance, and add a deletion/migration trigger. Never copy 168
   files wholesale.
3. **Mathlib-native construction.** Use Mathlib bundle metrics and the checked
   covariant-derivative substrate if a compatibility spike has a smaller
   reviewed surface than extraction. The current inventory warns that major
   Levi--Civita/geodesic/curvature work may remain.
4. **Wait for upstream.** Not a route at the current pin unless an audit finds
   concrete declarations and semantic equivalences.

Hard gates are recorded in the decision:

- one canonical metric/distance/measure representation and proved coherence;
- curvature sign/order checked by a constant-curvature example at chart,
  Jacobi, index, sectional, and Ricci boundaries;
- finite dimension, dimension lower bounds (including local `2 <= n` gates for
  the uniformization classification and the all-manifold weak Calabi theorem),
  no boundary, Hausdorffness, sigma compactness, connectedness, and completeness
  introduced only where source proofs require them; any stronger public
  hypothesis needs approval;
- arbitrary variation regularity chosen against a chart-local adapter without
  weakening second variation;
- cut-locus measurability/nullity proved using checked measure/Sard/change of
  variables APIs, never an assumed-null predicate;
- `metricexp` checked term by term against Sakai and its sign warning resolved;
- `volinj` retained at source strength, with a human scope decision if its
  covering/compactness theory is project-scale;
- every Lean/Mathlib/shared revision gets a compatibility, namespace,
  signature, instance, axiom, and source-fidelity audit.

## Provisional debt and replacement triggers

| Provisional construction | Permitted use and cost | Replacement trigger |
| --- | --- | --- |
| Chart-coordinate `(J,DJ)` pairs, state-transition flows, chart partitions, parallel frames | Private proof reductions for J1/V1/C1/C2; duplicate coordinates and increase bridge obligations | Intrinsic Jacobi existence plus chart/frame equivalence theorem lands; final theorem signatures contain no chart artifact |
| Complete-space `globalGeodesic`/`expMapGlobal` helpers | F2 exploration only; they hide maximal-domain and local-domain cases | F2 proves the canonical maximal exponential API and a complete-case equivalence |
| `IsRadialJacobi`, polar-density, cut-time, cut-locus, local-isometry, and injectivity-radius facades | A1/A2/N1 integration scaffolding only; producer semantics are otherwise absent | Retire or make private when N1/C2 proves the named geometric producer/equivalence; no final source theorem quantifies over the facade |
| Abstract `expBallVolume` density ratios | Analytic ratio lemmas only; not a manifold volume theorem | C3 proves polar density = Riemannian measure and exp preimage = metric ball off the null cut locus |
| Wrappers duplicating Mathlib/shared declarations | Temporary compatibility only with a named caller | Delete after migration to the canonical declaration |
| Any Chapter 1 to Chapter 2 import | Forbidden in Z1; temporary only if a missing general theorem is being relocated | Move the general theorem to shared or Chapter 1 before Z1 |
| Transparency/heartbeat exceptions | Named failing boundary only; maintenance and reproducibility cost | Re-audit on dependency changes and remove when the boundary is repaired |
| Reference tree's 168-file split | Prior-art navigation only; import and review cost | Consolidate helpers to one owner/proof purpose; split only at stable API boundaries |

## Bibliography and source policy

`docs/references.bib` contains exactly the publications used by this roadmap.
Every key is attached to a precise row or design decision above, and every
publication-backed claim has a chapter/section plus theorem/lemma/proposition
or exact page range.  Edition conflicts are explicit:

- Morgan--Tian's bibliography says do Carmo 1993, while the checked English
  edition commonly catalogued for the relevant material is the 1992
  Birkhauser translation.  The roadmap uses `doCarmo1992` for page anchors and
  records the 1993 citation as the source-text discrepancy.
- Morgan--Tian cites Petersen's 2006 second edition.  This roadmap uses that
  key at the source's actual anchors: the valid Chapter 5 citations,
  pp. 265--268 for the local distance-Laplacian expansion, Lemma 42 on p. 284
  for the weak Calabi statement, and Chapter 9, Section 1 for comparison.
  The retained 2016 third edition is separately keyed only for the checked
  positive-curvature route in Section 6.4, Corollary 6.4.2 and Theorems
  6.4.3/6.4.6, pp. 254--257.  Its numbering never substitutes for a 2006
  anchor.
- Sakai's 1996 English volume is translated from the 1992 Japanese original;
  `metricexp` uses the English Proposition 3.1, p. 41, and records the sign
  conversion against Morgan--Tian.

The primary key `morganTian2007` links both the 2007 book and arXiv v2 source.
`gallotHulinLafontaine2004` is an explicitly unverified cross-check for the
one-form Bochner identity, not a replacement for Morgan--Tian's Lemma 1.10:
Morgan--Tian cites Proposition 4.36, p. 168, but the retained workspace does
not contain the 2004 edition text to recheck that location.  `lee2018` cross-checks connection, geodesic,
curvature, Jacobi, and comparison architecture in the second edition at
Chapter 4 (Connections, Covariant Derivatives Along Curves, Geodesics),
Chapter 5 (Levi--Civita Connection, Exponential Map, Normal Neighborhoods),
Chapter 6 (Geodesics and Minimizing Curves, Completeness), Chapter 7
(Curvature Tensor, Ricci and Scalar Curvatures), Chapter 10 (Jacobi Equation,
Conjugate Points, Second Variation, Cut Points), and Chapter 11 (Jacobi,
Hessian, and Riccati comparisons).  `cheegerGromovTaylor1982` is the
comparison/injectivity proof authority for Proposition 4.1 and Theorem 4.3,
especially (4.22), p. 46.  `cheegerEbin1975` is the alternative proof authority
for Theorem 5.8, p. 96.  The URLs and metadata are checked against arXiv,
Springer, AMS/Clay, and Journal of Differential Geometry records.

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
reviewed commit.  The bootstrap record is:

| Revision | Change | Rechecked evidence | Decision |
| --- | --- | --- | --- |
| `bootstrap` / `e317497422c4e869ca2072f63f19b211a197bedf` | Initial package, Mathlib pin, source inventory, bibliography, and CI contract | Morgan--Tian arXiv v2 Chapter 1 PDF/source; Mathlib commit `520045ab14e26149ee970e2e617ca04b09bde5d6`; Hopf--Rinow main `60c3e1f6493646d667a0bb645f99110a34d26e00`; publication records in `docs/references.bib` | Keep G2 open; no mathematical dependency selected; no provisional facade exposed |
| `review-response` / `32bf9a3179d54c8301ba2c8e48072f474d774978` | Applied the source-correction gates for `k = 0`, `K = 0`, the upper sectional comparison needed by `injvol`, and the `2 <= n` uniformization non-vacuity condition; removed the unused Petersen 2016 key; downgraded the Gallot cross-check to unverified | Morgan--Tian `prelim.tex` Definitions 1.30, Theorem 1.11, SCC, `localdiffeo`, and `injvol`; retained-source inventory confirms no Gallot 2004 text; bibliography/roadmap consistency audit | Keep G2 open; all five requested corrections are documented, and no mathematical implementation is claimed |
| `architecture-response` / `9f1b32d194a904ada7b614d0c12d13314aef4296` | Corrected every DAG edge; added curvature naturality, arbitrary-tensor connection Laplacian, and separate local/weak Calabi rows; reanchored Petersen editions; added A1 ownership of the positive-curvature model used by C1 | Morgan--Tian `prelim.tex` naturality paragraph, tensor-Laplacian definitions, local/weak Calabi passages, Definition 1.30, comparison-section pointer, and upper-bound paragraph; Petersen 2016 Section 6.4 retained pages 254--257 | Keep G2 as the human substrate gate and G0 implementation-free; restore `petersen2016` only as a precise, used cross-check |
| `mathematical-correctness-response` / `a202631d534786fba23bad4c15d434cbb759988f` | Bound `Comparison.sectional_upper` to the regular first-pole interval with explicit lower shape, angular-metric, and Jacobian directions; added `2 <= n` only to the all-manifold weak Calabi theorem | Morgan--Tian `prelim.tex` local/weak Calabi passages and upper-bound paragraph; Petersen 2016 Cor. 6.4.2 and Thms. 6.4.3/6.4.6, pp. 254--257; the one-dimensional `abs` distributional counterexample | Keep the repaired Petersen edition split, A1 producer, hyperbolic SCC branch, C1-to-L1 edge, and local asymptotic unchanged |
| `A1-model-scalar` / `70cc263f77dc9ee70b6246a94edd00f3f7f6a13d` | Added the standalone `Comparison.Model` API for flat/hyperbolic and spherical profiles, their normalized ODEs, positivity and first-pole facts, totalized radial coefficients, the quantitative origin estimate, and scalar Riccati comparison | Morgan--Tian Definition 1.30 and comparison discussion, pp. 48--49; Petersen 2016 Section 6.4, pp. 254--257; pinned Mathlib trigonometric derivative/bound, square-root, and one-variable derivative-monotonicity APIs; focused public-mathlib-PR search found no close packaged comparison-profile analogue | Keep the functions in A1 with no manifold facade; expose the scalar theorem through the Chapter 1 root; leave scalar/vector Sturm, vector/operator/trace Riccati, determinant inequalities, and manifold bridges pending |

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
