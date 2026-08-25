import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
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
milestones add manifold curvature, geodesic, Jacobi, normal-coordinate, and
manifold-comparison modules.  The A2 chart-density and normalized
change-of-variables substrate remains a direct provisional leaf until the
named N1 cut-locus consumer fixes its stable boundary; it uses Mathlib's
`LinearMap.normDet` and `μHE[finrank ℝ E]` directly and does not install a
competing global measure.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
