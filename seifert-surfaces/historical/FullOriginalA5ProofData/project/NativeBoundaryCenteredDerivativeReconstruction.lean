import NativeBoundarySchauderTangentGain

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_smaller_cap_subset_closure_open (c : E2) (r s : ℝ) (hsr : s < r) :
    nativeClosedBoundaryCap c s ⊆ closure (Metric.ball c r ∩ {x : E2 | 0 < x 0}) := by
  intro x hx
  have hxr : ‖x - c‖ < r := (show ‖x - c‖ ≤ s by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hx.1).trans_lt hsr
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min ε (r - ‖x - c‖) / 2
  have ht : 0 < t := by dsimp [t]; exact half_pos (lt_min hε (sub_pos.mpr hxr))
  have htε : t < ε := by dsimp [t]; linarith [min_le_left ε (r - ‖x - c‖)]
  have htr : t < r - ‖x - c‖ := by dsimp [t]; linarith [min_le_right ε (r - ‖x - c‖)]
  have hn : ‖t • coordinateVector 2 0‖ = t := by
    simp [norm_smul, coordinateVector, PiLp.norm_single, abs_of_pos ht]
  refine ⟨x + t • coordinateVector 2 0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · change dist (x + t • coordinateVector 2 0) c < r
      rw [dist_eq_norm, show x + t • coordinateVector 2 0 - c = (x - c) + t • coordinateVector 2 0 by abel]
      have hh := norm_add_le (x - c) (t • coordinateVector 2 0)
      rw [hn] at hh
      linarith
    · have hx0 : 0 ≤ x 0 := hx.2
      change 0 < (x + t • coordinateVector 2 0) 0
      simp [coordinateVector]
      linarith
  · have he : x - (x + t • coordinateVector 2 0) = -(t • coordinateVector 2 0) := by abel
    rw [dist_eq_norm, he, norm_neg, hn]
    exact htε

theorem native_C1_smaller_cap_of_continuous_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r s : ℝ) (hs : 0 < s) (hsr : s < r)
    (v : E2 → F) (D : E2 → E2 →L[ℝ] F)
    (hv : ContinuousOn v (nativeClosedBoundaryCap c r))
    (hD : ContinuousOn D (nativeClosedBoundaryCap c r))
    (hder : ∀ x ∈ Metric.ball c r ∩ {x : E2 | 0 < x 0}, HasFDerivAt v (D x) x) :
    ContDiffOn ℝ 1 v (nativeClosedBoundaryCap c s) ∧
      EqOn (fderivWithin ℝ v (nativeClosedBoundaryCap c s)) D (nativeClosedBoundaryCap c s) := by
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hconv : Convex ℝ U := (convex_ball c r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap)
  have hsub : U ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1, by change 0 ≤ x 0; exact le_of_lt hx.2⟩
  have hclsub : closure U ⊆ nativeClosedBoundaryCap c r :=
    closure_minimal hsub (nativeClosedBoundaryCap_isClosed c r)
  have hsmall : nativeClosedBoundaryCap c s ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hsr.le hx.1, hx.2⟩
  have hdcl : ∀ x ∈ nativeClosedBoundaryCap c s, HasFDerivWithinAt v (D x) (nativeClosedBoundaryCap c s) x := by
    intro x hx
    have hlim : Tendsto (fderiv ℝ v) (𝓝[U] x) (𝓝 (D x)) := by
      apply ((hD x (hsmall hx)).mono hsub).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder y hy).fderiv.symm
    have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt) hconv hU
      (fun y hy => (hv y (hclsub hy)).mono hsub) hlim
    exact hh.mono (native_smaller_cap_subset_closure_open c r s hsr)
  refine ⟨?_, fun x hx => (hdcl x hx).fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf x hx)⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf)]
  exact ⟨by simp, D, contDiffOn_zero.mpr (hD.mono hsmall), hdcl⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
