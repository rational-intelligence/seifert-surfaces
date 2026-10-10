import CapRotatedCoordinates
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0

def capPairEquiv : E2 ≃ᵐ ℝ×ℝ :=
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv.trans MeasurableEquiv.finTwoArrow

def capCoordinateEquiv (s : ℝ) : (ℝ×ℝ) ≃ᵐ E2 :=
  capPairEquiv.symm.trans (capRotateEquiv s).toHomeomorph.toMeasurableEquiv

theorem capPairEquiv_measurePreserving : MeasurePreserving capPairEquiv volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

theorem capCoordinateEquiv_measurePreserving (s : ℝ) :
    MeasurePreserving (capCoordinateEquiv s) volume volume :=
  (capRotateEquiv s).measurePreserving.comp (capPairEquiv_measurePreserving.symm capPairEquiv)

theorem capCoordinateEquiv_apply (s : ℝ) (p : ℝ×ℝ) :
    capCoordinateEquiv s p=p.1 • unitCircleParameter s+p.2 • rotateQuarter (unitCircleParameter s) := rfl

theorem capCoordinateEquiv_tangent (s : ℝ) (p : ℝ×ℝ) :
    capTangent s (capCoordinateEquiv s p)=p.2 := capRotateEquiv_tangent s _

theorem capCoordinateEquiv_normal (s : ℝ) (p : ℝ×ℝ) :
    capNormal s (capCoordinateEquiv s p)=p.1 := capRotateEquiv_normal s _
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
