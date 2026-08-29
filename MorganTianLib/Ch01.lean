import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic
import MorganTianLib.Ch01.Geodesic.HopfRinow
import MorganTianLib.Ch01.Geodesic.Variation
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Models.Cone
import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Curvature.Tensoriality
import MorganTianLib.Ch01.Curvature.Plane
import MorganTianLib.Ch01.Curvature.Operator
import MorganTianLib.Ch01.Curvature.SectionalProvisional
import MorganTianLib.Ch01.Curvature.OperatorProvisional
import MorganTianLib.Ch01.Comparison.DeterminantDensity
import MorganTianLib.Ch01.Comparison.PositiveRiccati
import MorganTianLib.Ch01.Comparison.OperatorRiccati
import MorganTianLib.Ch01.Comparison.VectorSturm

/-!
# Chapter 1: preliminaries from Riemannian geometry

The public Chapter 1 umbrella.  It exposes finite-dimensional Riemannian metric
existence, the canonical metric, distance, volume, and Levi--Civita connection
coherence layers, the public Christoffel equation bridge, the connection-free
curvature model, and the provisional selected-extension manifold curvature
layer (including its proved tensorial and first-Bianchi subset).  The intrinsic
arbitrary-extension producer remains a named S06 replacement target; the
private chart calculation is kept out of this umbrella.  The public curvature
consumers include the algebraic sectional-curvature and intrinsic-plane layers
and the symmetric second-exterior-power operator.  Their direct-only tangent
adapters are exported
by `Curvature.SectionalProvisional` and `Curvature.OperatorProvisional`; every
plane or operator property retains an explicit algebraic-curvature witness
until the S07 metric symmetry boundary is proved, and these adapters do not
replace the producer.  It also exposes the algebraic curvature-convention
kernel and the standalone scalar, vector/operator, traced Riccati, and
normalized determinant/density comparison layers.  The A2 chart-density and
normalized change-of-variables substrate is available only through the direct
`MorganTianLib.Ch01.Volume.ChangeOfVariables` import until the named N1
cut-locus consumer fixes its stable boundary; it uses Mathlib's
`LinearMap.normDet` and `μHE[finrank ℝ E]` directly and does not install a
competing global measure.  The provisional `Connection.TensorLaplacian`
evaluation layer is likewise direct-only until its bundled,
extension-independent producer is available for S13's Bochner consumer.  The
S19 Hopf--Rinow boundary is exported through the direct
`Geodesic.HopfRinow` import.  It keeps selected-metric completeness,
model-space ODE completeness, and boundarylessness independent, and exposes
the selected-distance completeness bridge, open/order-connected
maximal-lifetime contract, source-facing geodesic-completeness wrapper,
the generic and selected-metric right-endpoint Cauchy lemmas under an explicit
extended-distance Lipschitz premise,
proof-backed affine geodesic/restriction transport, finite subsegment
length-realization, affine path-length and translation compatibility, and an
explicit candidate-versus-competitor inequality.  The universal continuation
form quantifies over every supplied maximal witness, while a subsingleton
regression checks that quantifier independently of the selected producer.  Its
maximal-domain and compactness producers remain explicit inputs; the regressions
cover
subsingleton, Euclidean, bounded-lifetime, disconnected-component, and
incomplete-metric cases without asserting uniqueness.  The metric layer also
exports component-local finite-path and finite-distance witnesses, and the
Hopf--Rinow layer provides component-local minimizer adapters that retain the
explicit producer input.  The S20 geodesic
energy/first-variation contract depends only on the canonical metric/connection
layers.  Later milestones add Jacobi, normal-coordinate, and
manifold-comparison modules without exposing chart plumbing as public API.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
