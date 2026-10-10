import B3AnalyticDonorBridgeV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.ConsumerLinks
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479
open SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Native analytic consumer for the exact same graph: the paid V480 package
supplies integer order, isolated derivative zero and signs, while the local
coefficient package supplies the equation on a common smaller ball. The only
remaining argument is the geometric graph/ambient isolation provider. -/
theorem B3_interior_native_analytic_consumer
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : OriginalPair g J)
    (hgeometry : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      (∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
        U ∩ interiorTangencies D.A.1.embedding D.B.1.embedding = {p}) ∧
      Nonempty (InteriorGraph D.A D.B p)) :
    InteriorTangencyResult E D.A D.B := by
  exact b3_native_interior_result_of_geometric_graphs D hgeometry

#print axioms B3_interior_native_analytic_consumer
end SeifertSurfaces.OriginalEndpoints.Section5.ConsumerLinks
