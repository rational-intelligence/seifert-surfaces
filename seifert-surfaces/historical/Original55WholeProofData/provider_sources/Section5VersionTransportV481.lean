import Section5GraphRestrictionV481
import OriginalB2B5V480

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- The unchanged original pair data pass between the two approved versions. -/
def original_pair_to_v480 {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : AppendixBOriginalV479.OriginalPair g J) : AppendixBOriginalV480.OriginalPair g J where
  A := D.A
  B := D.B
  A_minimum := D.A_minimum
  B_minimum := D.B_minimum
  distance_two := D.distance_two
  convex := D.convex
  analytic := D.analytic

/-- Preserve the literal chart, heights and graph images across approved versions. -/
def interior_graph_479_to_480 {A B : IncompressibleSpanningSurface.{0} E}
    {p : E.Carrier} (c : AppendixBOriginalV479.InteriorGraph A B p) :
    AppendixBOriginalV480.InteriorGraph A B p where
  coordinates := c.coordinates
  source_interior := c.source_interior
  smooth := c.smooth
  inverse_smooth := c.inverse_smooth
  base_mem := c.base_mem
  base_zero := c.base_zero
  R := c.R
  R_pos := c.R_pos
  eta := c.eta
  eta_pos := c.eta_pos
  cylinder_inside := c.cylinder_inside
  lower := c.lower
  upper := c.upper
  lower_smooth := c.lower_smooth
  upper_smooth := c.upper_smooth
  lower_zero := c.lower_zero
  upper_zero := c.upper_zero
  lower_tangent := c.lower_tangent
  upper_tangent := c.upper_tangent
  lower_inside := c.lower_inside
  upper_inside := c.upper_inside
  graph_A := c.graph_A
  graph_B := c.graph_B

/-- Preserve the literal chart, heights and graph images across approved versions. -/
def interior_graph_480_to_479 {A B : IncompressibleSpanningSurface.{0} E}
    {p : E.Carrier} (c : AppendixBOriginalV480.InteriorGraph A B p) :
    AppendixBOriginalV479.InteriorGraph A B p where
  coordinates := c.coordinates
  source_interior := c.source_interior
  smooth := c.smooth
  inverse_smooth := c.inverse_smooth
  base_mem := c.base_mem
  base_zero := c.base_zero
  R := c.R
  R_pos := c.R_pos
  eta := c.eta
  eta_pos := c.eta_pos
  cylinder_inside := c.cylinder_inside
  lower := c.lower
  upper := c.upper
  lower_smooth := c.lower_smooth
  upper_smooth := c.upper_smooth
  lower_zero := c.lower_zero
  upper_zero := c.upper_zero
  lower_tangent := c.lower_tangent
  upper_tangent := c.upper_tangent
  lower_inside := c.lower_inside
  upper_inside := c.upper_inside
  graph_A := c.graph_A
  graph_B := c.graph_B

/-- The nodal conclusion is preserved without changing its radius or integer order. -/
theorem interior_tangency_v480_to_v479
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : AppendixBOriginalV479.OriginalPair g J)
    (h : AppendixBOriginalV480.InteriorTangencyConclusion (original_pair_to_v480 D)) :
    AppendixBOriginalV479.InteriorTangencyConclusion D := by
  intro p hp
  obtain ⟨hi, c, m, hm, c1, c2, R, hc1, hc2, hR, hRc, hg, hz, hs⟩ := h p hp
  exact ⟨hi, interior_graph_480_to_479 c, m, hm, c1, c2, R, hc1, hc2, hR, hRc,
    hg, hz, hs⟩

/-- The new two-height operator producer discharges the old protected consumer type. -/
theorem local_equations_v480_to_v479
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : AppendixBOriginalV479.OriginalPair g J)
    (h : ∀ p : E.Carrier, ∀ c : AppendixBOriginalV480.InteriorGraph D.A D.B p,
      ∃ r : ℝ, 0 < r ∧ r ≤ c.R ∧
        Nonempty (LinearGraphEquation (AppendixBOriginalV480.graphDifference c) (Metric.ball 0 r))) :
    ∀ p : E.Carrier, ∀ c : AppendixBOriginalV479.InteriorGraph D.A D.B p,
      ∃ r : ℝ, 0 < r ∧ r ≤ c.R ∧
        Nonempty (LinearGraphEquation (AppendixBOriginalV479.graphDifference c) (Metric.ball 0 r)) := by
  intro p c
  exact h p (interior_graph_479_to_480 c)

/-- All actual collar maps and stratum conditions survive the version change. -/
def one_sided_collar_to_v480 {S : CompactOrientedSurface.{0}}
    {F : NeatEmbedding S E.Carrier} {U : Set E.Carrier}
    (C : AppendixBOriginalV479.OneSidedCollar F U) : AppendixBOriginalV480.OneSidedCollar F U where
  epsilon := C.epsilon
  epsilon_pos := C.epsilon_pos
  map := C.map
  initial := C.initial
  smooth := C.smooth
  embedding := C.embedding
  into_region := C.into_region
  closed_side := C.closed_side
  boundary_strata := C.boundary_strata
  immersion := C.immersion

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
