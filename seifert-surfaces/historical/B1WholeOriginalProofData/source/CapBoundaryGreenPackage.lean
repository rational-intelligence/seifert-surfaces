import CapUpperBoundaryGreen
import CapLowerBoundaryGreen
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cap_native_boundary_Green_package (s q : ℝ) (hq : 0<q) (hq1 : q≤1/2)
    (B b : ℝ→E2) (hB : Continuous B) (hBp : Periodic B (2*Real.pi))
    (hb : ContDiff ℝ ∞ b)
    (hagree : ∀t∈Icc (s-2*Real.arcsin (q/2)) (s+2*Real.arcsin (q/2)), B t=b t)
    (psi : E2→ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) :
    IntegrableOn (capUpperFlux s b psi i j) (Icc (-capLensReach q) (capLensReach q)) ∧
    IntegrableOn (capLowerFlux s q b psi i j) (Icc (-capLensReach q) (capLensReach q)) ∧
    IntegrableOn (fun t => b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j)
      (Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2))) ∧
    IntegrableOn (fun t => B t i * psi (unitCircleParameter t) * unitCircleParameter t j)
      (circlePatch (unitCircleParameter s) q) ∧
    (∫ y in Icc (-capLensReach q) (capLensReach q), capUpperFlux s b psi i j y-capLowerFlux s q b psi i j y) =
      q*(∫ t in Icc (s+Real.pi/2+Real.arcsin (q/2)) (s+3*Real.pi/2-Real.arcsin (q/2)),
        b (capArtificialAngle s q t) i * psi (unitCircleParameter s+q • unitCircleParameter t) * unitCircleParameter t j) +
      (∫ t in circlePatch (unitCircleParameter s) q, B t i * psi (unitCircleParameter t) * unitCircleParameter t j) := by
  have hu := (cap_upper_flux_continuousOn s q hq hq1 b hb.continuous psi hpsi.continuous i j).integrableOn_Icc (μ:=volume)
  have hl := (cap_lower_flux_continuousOn s q hq hq1 b hb.continuous psi hpsi.continuous i j).integrableOn_Icc (μ:=volume)
  refine ⟨hu,hl,cap_artificial_boundary_integrable s q hq hq1 b hb.continuous psi hpsi.continuous i j,
    cap_true_boundary_integrable s q B hB psi hpsi i j,?_⟩
  rw [integral_sub hu hl,cap_true_boundary_to_upper s q hq hq1 B b hBp hb.continuous hagree psi hpsi.continuous i j,
    cap_artificial_boundary_to_lower s q hq hq1 b hb.continuous psi hpsi.continuous i j]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
