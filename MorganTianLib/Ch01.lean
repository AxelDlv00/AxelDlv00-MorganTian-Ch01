import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic
import MorganTianLib.Ch01.Geodesic.HopfRinow
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Comparison.DeterminantDensity
import MorganTianLib.Ch01.Comparison.PositiveRiccati
import MorganTianLib.Ch01.Comparison.OperatorRiccati
import MorganTianLib.Ch01.Comparison.VectorSturm

/-!
# Chapter 1: preliminaries from Riemannian geometry

The public Chapter 1 umbrella.  It exposes finite-dimensional Riemannian metric
existence, the canonical metric, distance, volume, and Levi--Civita connection
coherence layers, the chart Christoffel and geodesic-equation bridges, the
algebraic curvature-convention kernel, and the standalone scalar,
vector/operator, traced Riccati, normalized determinant/density comparison,
and the S19 Hopf--Rinow continuation/minimizer interfaces.  The latter keeps
metric completeness, model-space ODE completeness, and boundarylessness
independent.  Its selected-distance completeness bridge,
open/order-connected maximal-lifetime contract, source-facing
geodesic-completeness wrapper, proved affine
geodesic/restriction transport, affine path-length and translation
compatibility, an explicit candidate-versus-competitor length inequality, and
global-witness packaging adapters, together with bounded-lifetime/model-
completion regressions, make those distinctions checkable.  Its
maximal-domain and compactness producers are explicit inputs
for the remaining S19 proof; the geodesic-completeness wrapper is an existence
form and does not assert uniqueness of maximal witnesses.  Later milestones
add maximal geodesic/exponential,
Jacobi, normal-coordinate, and manifold-comparison modules.  The A2
chart-density and normalized change-of-variables substrate remains a direct
provisional leaf until the named N1 cut-locus consumer fixes its stable
boundary; it uses Mathlib's `LinearMap.normDet` and `μHE[finrank ℝ E]`
directly and does not install a competing global measure.
The provisional `Connection.TensorLaplacian` evaluation layer is likewise
direct-only until its bundled, extension-independent producer is available for
S13's Bochner consumer.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
