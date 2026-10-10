import B1BoundaryClassicalTangential_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
set_option maxHeartbeats 800000

/-- The weak quotient derivative is identified with the ordinary second
 tangential derivative on a smaller original half-disc. -/
theorem actual_positive_boundary_tangential_classical_L2_v468
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
      ∀ q : ℝ, 0<q → q<R/4 →
      ∀ i : Fin 2, MemLp
        (fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 0))
        2 (volume.restrict (halfDisc q)) := by
  obtain ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,hw⟩ :=
    actual_positive_boundary_tangential_H2_v468 D s W
  refine ⟨R,hR,hRW,h,hhc,hfront,hpos,hs,h1,h0,heq,hcl,?_⟩
  intro q hq hqR i
  obtain ⟨w,hwLp,hwder⟩ := hw i
  exact native_boundary_classical_tangential_L2_v468 R q (by linarith) h hs i w
    (hwLp.mono_measure (Measure.restrict_mono_set _ (Metric.ball_subset_ball hqR.le)))
    (hwder.restrict Metric.isOpen_ball (Metric.ball_subset_ball hqR.le))
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.actual_positive_boundary_tangential_classical_L2_v468
