import Section5BoundaryCurveCriterionV488
import Section5CommonLeafRegularParameterV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem longitude_unit_parameter_smoothEmbedding (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ (longitudeUnitParameter g J a) := by
  apply SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488.boundary_curve_isSmoothEmbedding
    (longitude_unit_parameter_smooth g J a)
  · intro z
    have hz : longitudeUnitParameter g J a z ∈ J.leaf a :=
      longitude_unit_parameter_image g J a ▸ mem_range_self z
    obtain ⟨s,hs⟩ := hz
    rw [← hs]
    exact J.torus_lands_boundary (a,s)
  · exact longitude_unit_parameter_differential_injective g J a
  · exact longitude_unit_parameter_embedding g J a

#print axioms longitude_unit_parameter_smoothEmbedding
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
