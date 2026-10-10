import IsothermalPDEData
import B1L1DirectWeakLower

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
open SeifertSurfaces.AppendixACoordinates

def dilation (y : E2) (rho : ℝ) (z : E2) : E2 := y + rho • z

def inverseDilation (y : E2) (rho : ℝ) (x : E2) : E2 := rho⁻¹ • (x - y)

def rescaledCoefficient (N : E2 → Mat2) (y : E2) (rho : ℝ) (z : E2) : Mat2 :=
  N (dilation y rho z)

def rescaledError (y : E2) (rho : ℝ) (a : E2 → ℝ) (z : E2) : ℝ :=
  (a (dilation y rho z) - affineDatum y (dilation y rho z)) / rho

def rescaledErrorGradient (y : E2) (rho : ℝ) (da : E2 → E2) (z : E2) : E2 :=
  da (dilation y rho z) - coordinateVector 2 0

def rescaledForcing (N : E2 → Mat2) (y : E2) (rho : ℝ) (z : E2) : E2 :=
  matrixAction (N y - N (dilation y rho z)) (coordinateVector 2 0)

def reconstructedAffine (y : E2) (rho : ℝ) (vC : E2 → ℝ) (x : E2) : ℝ :=
  rho * vC (inverseDilation y rho x) + affineDatum y x

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower
