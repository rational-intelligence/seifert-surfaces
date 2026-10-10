import EndpointGeometry
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ,E3) ∞ N]

theorem boundary_plane_point_congr {h : AmbientMetric N} {M : Set N}
    (C : WarpedBoundaryCollar h M) (p q : N) (hpq : p = q)
    (hp : p ∈ C.coordinates.chart.source) (hq : q ∈ C.coordinates.chart.source) :
    boundaryTangentPlane C p hp = boundaryTangentPlane C q hq := by
  subst q
  rfl

end SeifertSurfaces.OriginalEndpoints.A7Support
