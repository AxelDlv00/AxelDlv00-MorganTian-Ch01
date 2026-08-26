import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Curvature.Tensoriality
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
private chart calculation is kept out of this umbrella.  Later milestones add
geodesic, Jacobi, normal-coordinate, and manifold-comparison modules without
exposing chart plumbing as public API.  It also exposes the algebraic
curvature-convention kernel and the standalone scalar, vector/operator,
traced Riccati, and normalized determinant/density comparison layers.  The A2
chart-density and normalized change-of-variables substrate, including its
`LinearMap.normDet` and tangent-space Jacobian adapters, remains a direct
provisional leaf until a named N1 cut-locus consumer fixes its stable boundary.
It is available through the direct
`MorganTianLib.Ch01.Volume.ChangeOfVariables` import and is not exported by
this stable umbrella; it does not install a competing global measure.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
