import EndpointGeometry
set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

theorem halfDisc_isClosed (r : ℝ) : IsClosed (closedHalfDisc r) :=
  Metric.isClosed_closedBall.inter (isClosed_le continuous_const ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0 : Continuous (fun z : E2 => z 0))))

theorem halfDisc_interior_positive {r : ℝ} {z : E2}
    (hz : z ∈ interior (closedHalfDisc r)) : 0 < z 0 := by
  have hi : z ∈ interior ({z : E2 | 0 ≤ z 0}) :=
    interior_mono (inter_subset_right (s := Metric.closedBall 0 r)) hz
  rw [interior_halfSpace] at hi
  exact hi

theorem halfDisc_boundary_of_zero {r : ℝ} {z : E2}
    (hz : z ∈ closedHalfDisc r) (hzero : z 0 = 0) :
    z ∈ frontier (closedHalfDisc r) := by
  rw [(halfDisc_isClosed r).frontier_eq]
  refine ⟨hz,fun hi => ?_⟩
  have hp := halfDisc_interior_positive hi
  rw [hzero] at hp
  exact lt_irrefl _ hp

theorem halfDisc_zero_boundary {r : ℝ} (hr : 0 < r) :
    (0 : E2) ∈ frontier (closedHalfDisc r) := by
  apply halfDisc_boundary_of_zero
  · exact ⟨by simpa using hr.le,by simp⟩
  · simp

end SeifertSurfaces.OriginalEndpoints.A7Support
