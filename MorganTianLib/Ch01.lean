import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic.Variation
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Comparison.DeterminantDensity
import MorganTianLib.Ch01.Comparison.PositiveRiccati
import MorganTianLib.Ch01.Comparison.OperatorRiccati
import MorganTianLib.Ch01.Comparison.VectorSturm

/-!
# Chapter 1: preliminaries from Riemannian geometry

The public Chapter 1 umbrella.  It exposes finite-dimensional Riemannian metric
existence, the canonical metric, distance, volume, and Levi--Civita connection
coherence layers, the chart Christoffel bridge, the algebraic
curvature-convention kernel, and the standalone scalar, vector/operator,
traced Riccati, and normalized determinant/density comparison layers.  Later
milestones add manifold curvature, geodesic IVP, Jacobi, normal-coordinate, and
manifold-comparison modules.  The S20 geodesic energy/first-variation contract
is exported here and depends only on the canonical metric/connection layers.
The provisional A2 chart-density and
change-of-variables substrate is available through the direct
`MorganTianLib.Ch01.Volume.ChangeOfVariables` import; it is not exported by
this stable umbrella until a named downstream consumer establishes its public
boundary.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
