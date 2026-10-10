import Section5ActualPolarCollarReplayV488
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Set Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

def actualTubeCoordinates : TubeCoordinates T := by
  let h := tube_image_diffeomorph_exists T
  let A := Classical.choose h
  exact ⟨A, Classical.choose_spec h⟩

theorem actual_polar_collar_exists :
    Nonempty (GivenExteriorPolarCollar E (actualTubeCoordinates (T:=T))) := by
  exact given_exterior_polar_collar_diffeomorph E (actualTubeCoordinates (T:=T))

#print axioms actual_polar_collar_exists
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
