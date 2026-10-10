import B1MetricVariationalInterfaces
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod
open SeifertSurfaces.AppendixACoordinates

/-- An explicit W1,2 witness has exactly the native supplied gradient. -/
theorem native_h1_w1p_witness
    (u : E2 → ℝ) (du : E2 → E2) (h1 : H1On (disc 1) u du) :
    ∃ hw : DeGiorgi.MemW1pWitness 2 u (disc 1), hw.weakGrad = du := by
  refine ⟨{ memLp := h1.2.1
            weakGrad := du
            weakGrad_component_memLp := ?_
            isWeakGrad := ?_ }, rfl⟩
  · intro j
    exact h1.2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
  · intro j φ hφ hφc hφs
    have hφ' : ContDiff ℝ ∞ φ := hφ.of_le (by simp)
    exact h1.1.2.2 φ hφ' hφc hφs j

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod
