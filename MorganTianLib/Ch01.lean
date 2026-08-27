import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic
import MorganTianLib.Ch01.Geodesic.HopfRinow
import MorganTianLib.Ch01.Geodesic.Variation
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Curvature.Tensoriality
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
coherence layers, the public Christoffel equation bridge, and the intrinsic
chart geodesic-equation interfaces.  It exports the S19 Hopf--Rinow
continuation/minimizer boundary, which keeps selected-metric completeness,
model-space ODE completeness, and boundarylessness independent.  That boundary
includes the selected-distance completeness bridge, open/order-connected
maximal-lifetime contract, source-facing geodesic-completeness wrapper, proved
affine geodesic/restriction transport, proof-backed finite subsegment
length-realization, affine path-length and translation compatibility, and an
explicit candidate-versus-competitor inequality.  Its maximal-domain and
compactness producers remain explicit inputs, and the exported regressions
cover subsingleton, Euclidean, bounded-lifetime, disconnected-component, and
incomplete-metric cases without asserting uniqueness.

The umbrella also exposes the connection-free curvature model, the provisional
selected-extension manifold curvature layer (including its proved tensorial
and first-Bianchi subset), and the algebraic sectional-curvature and symmetric
second-exterior-power operator consumers.  The direct-only tangent adapters
`Curvature.SectionalProvisional` and `Curvature.OperatorProvisional` retain an
explicit algebraic-curvature witness until the S07 metric-symmetry boundary is
proved; the intrinsic arbitrary-extension producer remains a named target.
The standalone scalar, vector/operator, traced Riccati, and normalized
determinant/density comparison layers are exported as well.  The A2
chart-density and normalized change-of-variables substrate remains direct-only
until the named N1 cut-locus consumer fixes its stable boundary; it uses
Mathlib's `LinearMap.normDet` and `μHE[finrank ℝ E]` directly and does not
install a competing global measure.  The provisional `Connection.TensorLaplacian`
evaluation layer is likewise direct-only until its bundled,
extension-independent producer is available for S13's Bochner consumer.  The
S20 geodesic energy/first-variation contract depends only on the canonical
metric/connection layers.  Later milestones add Jacobi, normal-coordinate,
and manifold-comparison modules without exposing chart plumbing as public API.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
