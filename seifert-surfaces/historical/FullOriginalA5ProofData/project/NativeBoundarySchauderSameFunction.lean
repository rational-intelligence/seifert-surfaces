import NativeBoundarySchauderForcingExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_closed_halfDisc_subset_closure_larger_open
    (s r : ℝ) (hsr : s < r) : closedHalfDisc s ⊆ closure (openHalfDisc r) := by
  intro x hx
  have hxr : ‖x‖ < r := (show ‖x‖ ≤ s by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx.1).trans_lt hsr
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min ε (r - ‖x‖) / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min hε (sub_pos.mpr hxr))
  have htε : t < ε := by dsimp [t]; linarith [min_le_left ε (r - ‖x‖)]
  have htr : t < r - ‖x‖ := by dsimp [t]; linarith [min_le_right ε (r - ‖x‖)]
  have hn : ‖t • coordinateVector 2 0‖ = t := by
    simp [norm_smul, coordinateVector, PiLp.norm_single, abs_of_pos ht]
  refine ⟨x + t • coordinateVector 2 0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change dist (x + t • coordinateVector 2 0) 0 < r
      rw [dist_zero_right]
      have hh := norm_add_le x (t • coordinateVector 2 0)
      rw [hn] at hh
      linarith
    · have hx0 : 0 ≤ x 0 := hx.2
      have hcoord : (x + t • coordinateVector 2 0) 0 = x 0 + t := by
        simp [coordinateVector]
      change 0 < (x + t • coordinateVector 2 0) 0
      rw [hcoord]
      linarith
  · have he : x - (x + t • coordinateVector 2 0) = -(t • coordinateVector 2 0) := by abel
    rw [dist_eq_norm, he, norm_neg, hn]
    exact htε

/-- A continuous representative from the scalar provider is the same actual
function at every point of each smaller native CLOSED cap. -/
theorem native_same_continuous_representative_on_smaller_cap
    (r s : ℝ) (hsr : s < r) (v w : E2 → ℝ)
    (hv : ContinuousOn v (closedHalfDisc r)) (hw : ContinuousOn w (closedHalfDisc r))
    (hae : w =ᵐ[volume.restrict (openHalfDisc r)] v) : EqOn w v (closedHalfDisc s) := by
  have he : EqOn w v (openHalfDisc r) := volume.eqOn_open_of_ae_eq hae
    (openHalfDisc_isOpen r) (hw.mono (openHalfDisc_subset_closedHalfDisc r))
    (hv.mono (openHalfDisc_subset_closedHalfDisc r))
  intro x hx
  have hxR : x ∈ closedHalfDisc r := closedHalfDisc_mono hsr.le hx
  have hcl := native_closed_halfDisc_subset_closure_larger_open s r hsr hx
  haveI : (𝓝[openHalfDisc r] x).NeBot := mem_closure_iff_clusterPt.mp hcl
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hw x hxR).mono (openHalfDisc_subset_closedHalfDisc r))
    ((hv x hxR).mono (openHalfDisc_subset_closedHalfDisc r))
    (he.eventuallyEq_of_mem self_mem_nhdsWithin)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
