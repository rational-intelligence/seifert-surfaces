import B1GraphEquation_v468
import B1TangencyFiniteOrder
import B1PositiveNormalizationNative_v474
import B1ActualPropagationNative_v475
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem small_half_disc_positive_solution (D : B1OriginalData g J) (s : Circle)
    (W : CollarWindow D s) : Nonempty (PositiveNormalization W) := by
  exact actual_positive_normalization_native_v474 D s W

theorem actual_minimizers_local_agreement_propagates (D : B1OriginalData g J)
    (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set E2, IsOpen U ∧ U.Nonempty ∧ U ⊆ halfDisc W.R ∧
      ∀ x ∈ U, localHeight D s x = 0) : D.A.1.image = D.B.1.image := by
  exact actual_minimizers_local_agreement_propagates_native_v475 D s W hzero
end SeifertSurfaces.OriginalEndpoints.B1Tangency

#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_minimizers_local_agreement_propagates
