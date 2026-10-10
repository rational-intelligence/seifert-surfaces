import Section5GeometricDefinitions
import Section5EllipticAssemblyV480
import Section5VersionTransportV481
import B3NativeCoefficientReplayV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV480
open SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem b3_donor_local_equation
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : AppendixBOriginalV479.OriginalPair g J) :
    ∀ p : E.Carrier, ∀ c : AppendixBOriginalV479.InteriorGraph D.A D.B p,
      ∃ r : ℝ, 0 < r ∧ r ≤ c.R ∧
        Nonempty (LinearGraphEquation (AppendixBOriginalV479.graphDifference c) (Metric.ball 0 r)) := by
  intro p c
  obtain ⟨r, hr, hrr, hnative, a, b, c0, hcoeff, heq⟩ :=
    original_pair_interior_graph_linear_equation
      (original_pair_to_v480 D) (interior_graph_479_to_480 c)
  exact ⟨r, hr, hrr,
    linear_graph_equation_of_native_operator
      (AppendixBOriginalV479.graphDifference c) (Metric.ball 0 r)
      (Metric.isOpen_ball)
      ((c.upper_smooth.sub c.lower_smooth).mono (Metric.ball_subset_ball hrr))
      a b c0 hcoeff heq⟩

#print axioms b3_donor_local_equation
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
