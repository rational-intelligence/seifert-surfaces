import B1BoundaryTangentZeroTrace_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open ChartMetricProvider.Variational.DirectWeak
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open ChartMetricProvider.Variational.DirectWeak.BoundarySupport
set_option maxHeartbeats 800000

/-- The original positive normalizer's actual tangential derivative admits
native zero-trace compact localizations at the flat edge. No C1 boundary or
trace premise has been added to the original input. -/
theorem actual_positive_boundary_tangent_zero_trace_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0<R ∧ R<W.R ∧ ∃ h : E2 → ℝ,
      ContinuousOn h (closedHalfDisc R) ∧
      (∀ x ∈ frontier (halfDisc R), h x=1) ∧
      (∀ x ∈ closedHalfDisc R, (1/2 : ℝ)≤h x) ∧
      ContDiffOn ℝ ∞ h (halfDisc R) ∧
      H1On (halfDisc R) h (planarGradient h) ∧
      H10On (halfDisc R) (fun x => h x-1) (planarGradient h) ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h (planarGradient h) ∧
      (∀ x ∈ halfDisc R, classicalL W.a W.b W.c h x=0) ∧
      ∀ chi : E2 → ℝ, ContDiff ℝ ∞ chi → HasCompactSupport chi →
        tsupport chi ⊆ Metric.ball (0:E2) (R/4) →
        H10On (halfDisc (R/4)) (fun x => chi x*planarGradient h x 0)
          (cutoffGradient chi (fun x => planarGradient h x 0)
            (planarGradient (fun x => planarGradient h x 0))) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hwd⟩ :=
    actual_positive_boundary_tangential_H2_v468 D s W
  obtain ⟨w0,hw0,hd0⟩ := hwd 0
  obtain ⟨w1,hw1,hd1⟩ := hwd 1
  have hf := native_zero_extended_tangent_H1_v468 R (R/4) (by linarith)
    (fun x => h x-1) (planarGradient h) h0 w0 w1 hw0 hw1 hd0 hd1
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro chi hc hcc hct
  exact native_tangent_local_zero_trace_v468 R (R/4) (by linarith) (by linarith)
    h hs _ hf chi hc hcc hct
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_tangent_zero_trace_v468
