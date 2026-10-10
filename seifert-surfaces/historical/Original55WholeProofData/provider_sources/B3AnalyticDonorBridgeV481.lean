import B3NativeAnalyticReplayV481
import B3DonorBridgeV481

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

theorem b3_donor_graph_analysis (D : OriginalPair g J)
    {p : E.Carrier} (c : InteriorGraph D.A D.B p) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c1 c2 R : ℝ,
      0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
      (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
        c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤ ‖fderiv ℝ (graphDifference c) x‖ ∧
        0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
      (∀ x ∈ Metric.ball (0 : E2) R,
        fderiv ℝ (graphDifference c) x = 0 ↔ x = 0) ∧
      (∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
        (∃ x ∈ V ∩ Metric.ball 0 R, 0 < graphDifference c x) ∧
        (∃ x ∈ V ∩ Metric.ball 0 R, graphDifference c x < 0)) := by
  exact AppendixBOriginalV480.original_pair_graph_full_analytic_conclusion
    (original_pair_to_v480 D) (interior_graph_479_to_480 c)

/-- The literal local graph and ambient isolation are the remaining geometric
inputs; every PDE, integer-order, critical-zero and sign clause is produced
from the actual original pair by the paid analytic package. -/
theorem b3_native_interior_result_of_geometric_graphs
    (D : OriginalPair g J)
    (hgeometry : ∀ p ∈ interiorTangencies D.A.1.embedding D.B.1.embedding,
      (∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
        U ∩ interiorTangencies D.A.1.embedding D.B.1.embedding = {p}) ∧
      Nonempty (InteriorGraph D.A D.B p)) :
    InteriorTangencyResult E D.A D.B := by
  apply interior_tangency_of_local_equations D ?_ (b3_donor_local_equation D)
  intro p hp
  obtain ⟨hi, ⟨c⟩⟩ := hgeometry p hp
  exact ⟨hi, c, b3_donor_graph_analysis D c⟩

#print axioms b3_donor_graph_analysis
#print axioms b3_native_interior_result_of_geometric_graphs
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
