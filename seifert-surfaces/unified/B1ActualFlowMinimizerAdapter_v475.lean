import B1ActualAmbientFlowMinimum_v475
import B1ActualFixedBoundaryMinima_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000

theorem actual_relative_smooth_flow_minima_v475 (D : B1OriginalData g J) :
    (∃ F : GeometricPiecewiseSurface D.A.1.surface E.Carrier,
      ∃ f : ProperSmoothEmbedding D.A.1.surface E.Carrier,
        F.map = f.continuousMap ∧
        FixedBoundaryMinimizer E g F F ∧
        ∀ X : NativeInteriorSmoothVectorField_v475 E,
          IsLocalMin (fun t => area g
            (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0) ∧
    (∃ F : GeometricPiecewiseSurface D.B.1.surface E.Carrier,
      ∃ f : ProperSmoothEmbedding D.B.1.surface E.Carrier,
        F.map = f.continuousMap ∧
        FixedBoundaryMinimizer E g F F ∧
        ∀ X : NativeInteriorSmoothVectorField_v475 E,
          IsLocalMin (fun t => area g
            (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0) := by
  obtain ⟨FA,hFA,hminA⟩ := native_relative_fixed_minimum_v475 D.A D.A_relative_minimum
  obtain ⟨FB,hFB,hminB⟩ := native_relative_fixed_minimum_v475 D.B D.B_relative_minimum
  let fA : ProperSmoothEmbedding D.A.1.surface E.Carrier :=
    ProperSmoothEmbedding.ofNeat D.A.1.embedding
  let fB : ProperSmoothEmbedding D.B.1.surface E.Carrier :=
    ProperSmoothEmbedding.ofNeat D.B.1.embedding
  refine ⟨⟨FA,fA,hFA,hminA,?_⟩,⟨FB,fB,hFB,hminB,?_⟩⟩
  · intro X
    exact native_actual_smooth_ambient_flow_minimum_v475 fA FA hFA hminA X
  · intro X
    exact native_actual_smooth_ambient_flow_minimum_v475 fB FB hFB hminB X

#print axioms actual_relative_smooth_flow_minima_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
