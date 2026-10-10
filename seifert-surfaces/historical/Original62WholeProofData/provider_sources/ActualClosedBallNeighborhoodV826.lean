import ActualRadialCompactCompressionV825
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
noncomputable section
namespace CompressionActualClosedBallNeighborhoodV826
abbrev Plane := Schoenflies.Plane

/-- Compactness of the whole closed ball gives a strictly wider closed
    ball in any prescribed open neighborhood. -/
theorem exists_larger_closedBall {r : ℝ} (hr : 0 < r) {U : Set Plane}
    (hU : IsOpen U) (hsub : closedBall 0 r ⊆ U) :
    ∃ s : ℝ,r < s ∧ closedBall 0 s ⊆ U := by
  obtain ⟨δ,hδ,hthick⟩ := (isCompact_closedBall (0 : Plane) r).exists_cthickening_subset_open hU hsub
  refine ⟨r+δ/2,by linarith,?_⟩
  intro x hx
  apply hthick
  by_cases hxr : ‖x‖ ≤ r
  · exact self_subset_cthickening (closedBall (0 : Plane) r) (mem_closedBall_zero_iff.mpr hxr)
  have hn : 0 < ‖x‖ := hr.trans (lt_of_not_ge hxr)
  let y : Plane := (r/‖x‖) • x
  have hyn : ‖y‖ = r := by
    dsimp [y]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hn),div_mul_cancel₀ r hn.ne']
  have hy : y ∈ closedBall (0 : Plane) r := mem_closedBall_zero_iff.mpr hyn.le
  apply closedBall_subset_cthickening hy δ
  rw [mem_closedBall,dist_eq_norm]
  have he : x-y = (1-r/‖x‖) • x := by
    dsimp [y]
    rw [sub_smul,one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by have h := (div_lt_one hn).mpr (lt_of_not_ge hxr); linarith)]
  have hh : (1-r/‖x‖)*‖x‖ = ‖x‖-r := by
    rw [sub_mul,one_mul,div_mul_cancel₀ r hn.ne']
  rw [hh]
  have hxn : ‖x‖ ≤ r+δ/2 := mem_closedBall_zero_iff.mp hx
  linarith

#print axioms exists_larger_closedBall
end CompressionActualClosedBallNeighborhoodV826
