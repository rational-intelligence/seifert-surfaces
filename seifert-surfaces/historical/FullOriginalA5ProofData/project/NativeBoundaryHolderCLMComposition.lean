import NativeBoundarySecondJetHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_compact_holder_clm_apply_exists
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Set E2) (hK : IsCompact K) (a : E2 → F →L[ℝ] G) (v : E2 → F)
    (α : ℝ≥0) (hα : 0 < α)
    (ha : ∃ A, HolderOnWith A α a K) (hv : ∃ B, HolderOnWith B α v K) :
    ∃ C, HolderOnWith C α (fun x => a x (v x)) K := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hv
  obtain ⟨Ma, hMa⟩ := hK.exists_bound_of_continuousOn (hA.continuousOn hα)
  obtain ⟨Mv, hMv⟩ := hK.exists_bound_of_continuousOn (hB.continuousOn hα)
  exact ⟨A * Real.toNNReal Mv + Real.toNNReal Ma * B,
    native_holder_clm_apply K a v A B (Real.toNNReal Ma) (Real.toNNReal Mv) α hA hB
      (fun x hx => (hMa x hx).trans (Real.le_coe_toNNReal Ma))
      (fun x hx => (hMv x hx).trans (Real.le_coe_toNNReal Mv))⟩

theorem native_compact_holder_clm_comp_exists
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (K : Set E2) (hK : IsCompact K) (a : E2 → F →L[ℝ] G) (v : E2 → E2 →L[ℝ] F)
    (α : ℝ≥0) (hα : 0 < α)
    (ha : ∃ A, HolderOnWith A α a K) (hv : ∃ B, HolderOnWith B α v K) :
    ∃ C, HolderOnWith C α (fun x => (a x).comp (v x)) K := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hv
  obtain ⟨Ma, hMa⟩ := hK.exists_bound_of_continuousOn (hA.continuousOn hα)
  obtain ⟨Mv, hMv⟩ := hK.exists_bound_of_continuousOn (hB.continuousOn hα)
  refine ⟨A * Real.toNNReal Mv + Real.toNNReal Ma * B, ?_⟩
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have hAd : ‖a x - a y‖ ≤ (A : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hA.dist_le hx hy
  have hBd : ‖v x - v y‖ ≤ (B : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hB.dist_le hx hy
  calc
    _ = ‖(a x - a y).comp (v x) + (a y).comp (v x - v y)‖ := by
      congr 1
      simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
      abel
    _ ≤ ‖(a x - a y).comp (v x)‖ + ‖(a y).comp (v x - v y)‖ := norm_add_le _ _
    _ ≤ ‖a x - a y‖ * ‖v x‖ + ‖a y‖ * ‖v x - v y‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ ((A : ℝ) * dist x y ^ (α : ℝ)) * Real.toNNReal Mv +
        (Real.toNNReal Ma : ℝ) * ((B : ℝ) * dist x y ^ (α : ℝ)) := by
      gcongr
      · exact (hMv x hx).trans (Real.le_coe_toNNReal Mv)
      · exact (hMa y hy).trans (Real.le_coe_toNNReal Ma)
    _ = _ := by simp only [NNReal.coe_add, NNReal.coe_mul]; ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
