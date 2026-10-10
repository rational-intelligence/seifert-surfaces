import B1NativeBoundaryNirenbergTest_v468
import NativeBoundaryH10WeakTesting
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

/-- The compactly supported boundary Nirenberg test is accepted by the original
native weak equation after extending the equation from smooth tests to H10. -/
theorem native_boundary_nirenberg_equation_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t≠0)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du)
    (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (F x) (planarGradient φ x)-S x*φ x)=0) :
    ∃ G : E2 → E2, H10On (halfDisc R)
      (nirenbergTestFunction 0 t eta ((halfDisc R).indicator u)) G ∧
      (∫ x in halfDisc R,
        inner ℝ (F x) (G x) - S x * nirenbergTestFunction 0 t eta
          ((halfDisc R).indicator u) x)=0 := by
  obtain ⟨G,hG⟩ := native_boundary_nirenberg_test_h10_v468 R r t hroom htne eta hs hc ht u du hu
  have htest := native_h10_flux_source_testing (halfDisc R) F S hF hS hweak
    (nirenbergTestFunction 0 t eta ((halfDisc R).indicator u)) G hG
  exact ⟨G,hG,htest.2.2⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_nirenberg_equation_v468
