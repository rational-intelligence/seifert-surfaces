import B1ActualGraphPDEClosure_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The actual relative minima satisfy both original graph equations for the
literal supplied collar density. All analytic and geometric premises are
derived from D and W. -/
theorem actual_minimal_graph_equations_native_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    (∀ x ∈ halfDisc W.R, W.residual (localHeight D s) x = 0) ∧
    (∀ x ∈ halfDisc W.R, W.residual (fun _ => 0) x = 0) := by
  obtain ⟨⟨FA,hFA,hminA⟩,⟨FB,hFB,hminB⟩⟩ := actual_relative_fixed_minima_v475 D
  obtain ⟨⟨qA,hqA,hqiA,hqsA⟩,⟨qB,hqB,hqiB,hqsB⟩⟩ := actual_halfdisc_graph_source_parameters_v475 D s W
  have hheight (x : E2) (hx : x ∈ halfDisc W.R) : |localHeight D s x| < D.eta :=
    D.graph_inside _ _ ⟨(actual_halfdisc_radial_membership_v474 D s W x hx).1.le,
      (actual_halfdisc_radial_membership_v474 D s W x hx).2.le⟩
  have hjheight (x : E2) (hx : x ∈ halfDisc W.R) :
      jetPoint (x,localHeight D s x,planarGradient (localHeight D s) x) ∈ W.V := by
    simpa using W.jets_inside x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩ 1 (by simp)
  have hjzero (x : E2) (hx : x ∈ halfDisc W.R) :
      jetPoint (x,0,planarGradient (fun _ : E2 => 0) x) ∈ W.V := by
    simpa [planarGradient] using W.jets_inside x ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩ 0 (by simp)
  have huni := actual_collar_graph_height_unique_v475 D s W
  constructor
  · exact actual_graph_pde_from_native_flow_v475 D s W
      (ProperSmoothEmbedding.ofNeat D.A.1.embedding)
      (fun X => native_actual_smooth_ambient_flow_minimum_v475
        (ProperSmoothEmbedding.ofNeat D.A.1.embedding) FA hFA hminA X)
      (localHeight D s) W.height_smooth hheight hjheight qA hqsA hqA hqiA huni.1
  · exact actual_graph_pde_from_native_flow_v475 D s W
      (ProperSmoothEmbedding.ofNeat D.B.1.embedding)
      (fun X => native_actual_smooth_ambient_flow_minimum_v475
        (ProperSmoothEmbedding.ofNeat D.B.1.embedding) FB hFB hminB X)
      (fun _ => 0) contDiffOn_const (fun x hx => by simpa using D.eta_pos)
      hjzero qB hqsB hqB hqiB (fun y hy hp => huni.2 y hy hp)

#print axioms actual_minimal_graph_equations_native_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
