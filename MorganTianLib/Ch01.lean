import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
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
coherence layers, the public Christoffel equation bridge, the connection-free
curvature model, and the provisional selected-extension manifold curvature
layer (including its proved tensorial and first-Bianchi subset).  The intrinsic
arbitrary-extension producer remains a named S06 replacement target; the
private chart calculation is kept out of this umbrella.  The public curvature
consumers include the algebraic sectional-curvature layer and the symmetric
second-exterior-power operator.  Their direct-only tangent adapters are exported
by `Curvature.SectionalProvisional` and `Curvature.OperatorProvisional`; every
plane or operator property retains an explicit algebraic-curvature witness
until the S07 metric symmetry boundary is proved, and these adapters do not
replace the producer.  Later milestones add geodesic,
Jacobi, normal-coordinate, and manifold-comparison modules without exposing
chart plumbing as public API.  It
also exposes the algebraic curvature-convention kernel and the standalone
scalar, vector/operator, traced Riccati, and normalized determinant/density
comparison layers.  The
provisional A2 chart-density and
change-of-variables substrate is available through the direct
`MorganTianLib.Ch01.Volume.ChangeOfVariables` import; it is not exported by
this stable umbrella until a named downstream consumer establishes its public
boundary.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
