import CollarRemainingH
set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers.CollarCutHelpers
open Foundations MetricFoundations
noncomputable section
theorem given_exterior_polar_collar_diffeomorph {K : OrientedKnot}
    {T : TubularNeighborhood K} (E : SmoothExterior T) (D : TubeCoordinates T) :
    Nonempty (GivenExteriorPolarCollar E D) := by
  obtain ⟨A⟩ := Remaining.H4_exact_polar_inverse E D
  obtain ⟨_,P,_,_,_⟩ := Remaining.H6_polar_positive_scale E D A
  exact ⟨P⟩
theorem given_cut_half_collar_diffeomorph {K : OrientedKnot} {T : TubularNeighborhood K}
    {F : SphereSpanningSurface.{0} K} {R : FramedRibbon T F} (C : CutSurface R) :
    Nonempty (GivenCutHalfCollar C) := by
  obtain ⟨A⟩ := Remaining.H1_unique_half_collar C
  obtain ⟨_,_,_,k,_,_,_⟩ := Remaining.H3_full_half_collar C A
  exact ⟨k⟩

end
end SeifertSurfaces.LongitudeProducers.CollarCutHelpers
