import HomogeneousTests
import DifferentialGeometry.External.DeGiorgi.BallScaling

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff ENNReal
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem R3_rescale_homogeneous_to_unit_ball
    (center : E3) (R : ℝ) (hR : 0 < R)
    (A : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball center R))
    (V : E3 → ℝ) (hweak : ProviderHomogeneousEquation (Metric.ball center R) A.1 V) :
    ∃ Aunit : DeGiorgi.NormalizedEllipticCoeff 3 (Metric.ball (0 : E3) 1),
      Aunit.1.Λ = A.1.Λ ∧ (∀ z, Aunit.1.a z = rescaledMatrix center R A.1.a z) ∧
      ProviderHomogeneousEquation (Metric.ball (0 : E3) 1) Aunit.1 (rescaledFunction center R V) ∧
      IntegrableOn (fun z => |rescaledFunction center R V z| ^ (2 : ℝ))
        (Metric.ball (0 : E3) 1) := by
  have hw : DeGiorgi.IsHomogeneousWeakSolution A.1 V := by
    refine ⟨hweak.1, ?_⟩
    intro hV ψ hψ hψw
    exact (hweak.2 hV ψ hψ hψw).2
  have hunit := DeGiorgi.rescaleToUnitBall_isHomogeneousWeakSolution hR A.1 hw
  let Aunit := DeGiorgi.rescaleNormalizedCoeffToUnitBall hR A
  refine ⟨Aunit, rfl, fun z => rfl, ?_, ?_⟩
  · refine ⟨hunit.1, ?_⟩
    intro hV ψ hψ hψw
    exact ⟨DeGiorgi.integrable_bilinFormIntegrandOfCoeff Aunit.1 hV hψw,
      hunit.2 hV ψ hψ hψw⟩
  · simpa [IntegrableOn, Real.norm_eq_abs, rescaledFunction, DeGiorgi.rescaleToUnitBall] using hunit.1.1.integrable_norm_rpow (by norm_num) (by norm_num)

end SeifertSurfaces.QuasilinearProviderBridge
