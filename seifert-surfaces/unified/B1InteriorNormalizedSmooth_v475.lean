import B1InteriorNormalizedClassical_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Smoothness of the normalized coefficients on the entire actual open
normalization neighborhood follows from compact smaller balls. -/
theorem native_interior_normalized_smooth_v475 (N : InteriorNormalizationData_v475) :
    (∀ i j, ContDiffOn ℝ ∞ (fun x => N.normalizedA x i j) N.O) ∧
    ContDiffOn ℝ ∞ N.normalizedB N.O ∧ ContDiffOn ℝ ∞ N.v N.O := by
  have hlocal (x : E2) (hx : x ∈ N.O) :
      (∀ i j, ContDiffAt ℝ ∞ (fun x => N.normalizedA x i j) x) ∧
      ContDiffAt ℝ ∞ N.normalizedB x := by
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp N.isOpen_O x hx
    let r := ε/2
    have hr : 0 < r := half_pos hε
    have hKO : Metric.closedBall x r ⊆ N.O := by
      intro y hy
      apply hball
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by dsimp [r]; linarith)
    obtain ⟨hE,-,-,-,-⟩ := native_interior_normalized_coefficients_v475 N
      (Metric.closedBall x r) (isCompact_closedBall _ _) (convex_closedBall _ _)
      ⟨x,Metric.mem_closedBall_self hr.le⟩ hKO
    refine ⟨fun i j => ?_,?_⟩
    · exact (hE.1 i j x (Metric.mem_closedBall_self hr.le)).contDiffAt (Metric.closedBall_mem_nhds x hr)
    · exact (hE.2.1 x (Metric.mem_closedBall_self hr.le)).contDiffAt (Metric.closedBall_mem_nhds x hr)
  refine ⟨fun i j x hx => ((hlocal x hx).1 i j).contDiffWithinAt,
    fun x hx => ((hlocal x hx).2).contDiffWithinAt,?_⟩
  exact N.smooth_u.div N.smooth_h (fun x hx => (N.h_positive x hx).ne')

#print axioms native_interior_normalized_smooth_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
