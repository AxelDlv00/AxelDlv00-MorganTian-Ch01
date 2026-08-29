import MorganTianLib.Ch01.MetricExistence
import MorganTianLib.Ch01.Metric
import MorganTianLib.Ch01.Volume
import MorganTianLib.Ch01.Connection
import MorganTianLib.Ch01.Connection.Christoffel
import MorganTianLib.Ch01.Geodesic.Variation
import MorganTianLib.Ch01.Curvature
import MorganTianLib.Ch01.Models.Cone
import MorganTianLib.Ch01.Curvature.Manifold
import MorganTianLib.Ch01.Curvature.Tensoriality
import MorganTianLib.Ch01.Curvature.Symmetries
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
layer (including its proved tensorial and first-Bianchi subset).  The focused
`Curvature.Symmetries` layer adds metric last-pair skew, pair interchange, and
the source-ordered differential Bianchi identity for explicitly smooth local
fields, together with selected-extension algebraic consequences.  The
`SmoothTensorialAt` local-frame adapter also proves extension independence for
smooth local curvature evaluations; the weaker first-order `TensorialAt`
producer and public chart calculation remain named S07 triggers and are kept
out of this umbrella.  The public
curvature consumers include the algebraic sectional-curvature and
intrinsic-plane layers and the symmetric second-exterior-power operator.
Their direct-only tangent adapters are exported by
`Curvature.SectionalProvisional` and `Curvature.OperatorProvisional`; every
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
extension-independent producer is available for S13's Bochner consumer.
Later milestones add geodesic, Jacobi, normal-coordinate, and
manifold-comparison modules without exposing chart plumbing as public API.  The
S20 geodesic energy/first-variation contract is exported here and depends only
on the canonical metric/connection layers.
-/

namespace MorganTianLib

namespace Ch01

end Ch01

end MorganTianLib
