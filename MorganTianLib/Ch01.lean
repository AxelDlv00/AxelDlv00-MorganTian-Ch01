import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic
import MorganTianLib.Ch01.Geodesic.HopfRinow
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Curvature.Tensoriality
import MorganTianLib.Ch01.Jacobi
import MorganTianLib.Ch01.Comparison.DeterminantDensity
import MorganTianLib.Ch01.Comparison.PositiveRiccati
import MorganTianLib.Ch01.Comparison.OperatorRiccati
import MorganTianLib.Ch01.Comparison.VectorSturm

/-!
# Chapter 1: preliminaries from Riemannian geometry

The public Chapter 1 umbrella.  It exposes finite-dimensional Riemannian metric
existence, the canonical metric, distance, volume, and Levi--Civita connection
coherence layers; the chart Christoffel and geodesic-equation bridges; the
canonical source-ordered curvature and tensoriality subset; the local
Hopf--Rinow interfaces; the intrinsic Jacobi/conjugacy contracts; and the
standalone scalar, vector/operator, Riccati, and normalized determinant/density
comparison layers.  The Jacobi variation interface records its
torsion-free/curvature commutation certificate explicitly, while the full
chart-transfer and ODE existence/uniqueness producers remain named roadmap
continuations.  The A2 chart-density substrate uses Mathlib's
`LinearMap.normDet` directly and does not install a competing global measure.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
