import B1ActualGermLocusClosed_v475
import B1ActualFlowMinimizerAdapter_v475
import B1ActualSurfaceGermTopology_v475
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The complete original local-agreement propagation, with both actual
flow minima, common graphs and analytic continuation paid internally. -/
theorem actual_minimizers_local_agreement_propagates_native_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U ⊆ halfDisc W.R ∧
      ∀ x ∈ U, localHeight D s x=0) : D.A.1.image=D.B.1.image := by
  obtain ⟨FA,hFA,hminA⟩ := native_relative_fixed_minimum_v475 D.A D.A_relative_minimum
  obtain ⟨FB,hFB,hminB⟩ := native_relative_fixed_minimum_v475 D.B D.B_relative_minimum
  have hflowA := native_actual_smooth_ambient_flow_minimum_v475
    (ProperSmoothEmbedding.ofNeat D.A.1.embedding) FA hFA hminA
  have hflowB := native_actual_smooth_ambient_flow_minimum_v475
    (ProperSmoothEmbedding.ofNeat D.B.1.embedding) FB hFB hminB
  apply actual_surface_agreement_of_closed_germ_loci_v475 D s W hzero
  · exact native_actual_minimizer_germ_locus_closed_v475 g D.A.1.embedding D.B.1.embedding hflowA hflowB
  · exact native_actual_minimizer_germ_locus_closed_v475 g D.B.1.embedding D.A.1.embedding hflowB hflowA

#print axioms actual_minimizers_local_agreement_propagates_native_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
