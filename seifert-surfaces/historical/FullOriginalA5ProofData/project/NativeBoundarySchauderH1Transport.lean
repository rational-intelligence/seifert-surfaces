import NativeBoundarySchauderCoordinateTransport

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

theorem native_h1_coordinateSwap
    (U : Set E2) (v : E2 → ℝ) (G : E2 → E2) (hv : H1On U v G) :
    H1On (coordinateSwap ⁻¹' U) (fun y => v (coordinateSwap y))
      (fun y => coordinateSwap (G (coordinateSwap y))) := by
  have hh := linear_h1_pullback U coordinateSwap.toContinuousLinearEquiv v G hv
  convert hh using 1
  · rfl
  · rfl
  · funext y
    exact (coordinateSwap_adjoint _).symm

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
