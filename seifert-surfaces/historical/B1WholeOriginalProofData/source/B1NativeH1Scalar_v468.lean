import B1BoundaryMixedWeak_v468

import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Basic
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak
open BoundaryContinuation BoundarySupport
open ChartMetricProvider.Variational.NativeBallCapExtension
set_option maxHeartbeats 40000

/-- Scalar multiplication in the literal native H1 space. -/
theorem native_h1_const_mul_v468 (U : Set E2) (f : E2 → ℝ) (df : E2 → E2)
    (hf : H1On U f df) (a : ℝ) : H1On U (fun x => a*f x) (fun x => a • df x) := by
  have hv := hf.2.1.const_mul a
  have hg := hf.2.2.const_smul a
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hv.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num)),?_⟩,hv,hg⟩
  intro phi hs hc ht i
  have he := hf.1.2.2 phi hs hc ht i
  change (∫ x in U, a*f x*fderiv ℝ phi x (coordinateVector 2 i))=
    -(∫ x in U, a*df x i*phi x)
  simp only [mul_assoc,integral_const_mul]
  rw [he]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_h1_const_mul_v468
