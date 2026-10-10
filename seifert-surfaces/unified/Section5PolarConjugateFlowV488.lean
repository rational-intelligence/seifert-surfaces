import Section5LongitudeCollarCoordinatesV488
import Section5FlowRestrictionV488
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section

def longitudeStripFlow : Flow ℝ longitudeProductStrip :=
  longitudeProductFlow.restrict (fun _ _ h => h)

theorem longitude_strip_flow_smooth :
    ContMDiff (𝓘(ℝ).prod (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞
      (fun p : ℝ × longitudeProductStrip => longitudeStripFlow p.1 p.2) := by
  exact restrict_flow_smooth longitudeProductFlow longitudeProductStrip (fun _ _ h => h)
    longitude_product_flow_smooth

theorem longitude_strip_flow_fixed (t : ℝ) (p : longitudeProductStrip)
    (hp : 1/2 ≤ (p.val.2 : ℝ)) : longitudeStripFlow t p = p :=
  Subtype.ext (longitude_product_flow_fixed t p.val hp)

theorem longitude_strip_flow_boundary (t : ℝ) (p : Circle × Circle) :
    longitudeStripFlow t (longitudeBoundarySection p) =
      longitudeBoundarySection (longitudeLabelFlow t p.1,p.2) :=
  Subtype.ext (longitude_product_flow_boundary t p)

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D) (J : LongitudeFoliation.{0} E)

def polarConjugateFlow : Flow ℝ P.image :=
  conjugateFlow (longitudeCollarDiffeomorph P J).toHomeomorph longitudeStripFlow

theorem polar_conjugate_flow_smooth :
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : ℝ × P.image => polarConjugateFlow P J p.1 p.2) :=
  conjugate_flow_smooth (longitudeCollarDiffeomorph P J) longitudeStripFlow
    longitude_strip_flow_smooth

theorem polar_conjugate_flow_coordinates (t : ℝ) (p : longitudeProductStrip) :
    polarConjugateFlow P J t (longitudeCollarDiffeomorph P J p) =
      longitudeCollarDiffeomorph P J (longitudeStripFlow t p) := by
  exact conjugate_flow_coordinates (longitudeCollarDiffeomorph P J).toHomeomorph longitudeStripFlow t p

#print axioms polar_conjugate_flow_smooth
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
