import B3NativeLocalReplayV481
import B3AnalyticDonorBridgeV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

/-- The actual pair produces every local interior clause, including ambient
isolation; the native equation and all quantitative clauses use its same graph. -/
theorem b3_native_interior_result (D : OriginalPair g J) :
    InteriorTangencyResult E D.A D.B := by
  apply interior_tangency_of_local_equations D ?_ (b3_donor_local_equation D)
  exact interior_tangency_v480_to_v479 D
    (AppendixBOriginalV480.original_pair_interior_tangency_conclusion_v480
      (original_pair_to_v480 D))

#print axioms b3_native_interior_result
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
