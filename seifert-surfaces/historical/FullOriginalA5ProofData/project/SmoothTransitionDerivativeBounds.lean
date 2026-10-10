import NativeBoundaryToolbox
set_option maxHeartbeats 2000000
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates

theorem transition_derivative_bounds : ∃ D : ℝ, 0 ≤ D ∧
    (∀ t : ℝ, |deriv Real.smoothTransition t| ≤ D) ∧
    (∀ t : ℝ, deriv Real.smoothTransition t ≠ 0 → 0 ≤ t ∧ t ≤ 1) := by
  have hzero (t : ℝ) (ht : t < 0 ∨ 1 < t) : deriv Real.smoothTransition t = 0 := by
    rcases ht with ht | ht
    · have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 0) := by
        filter_upwards [show ∀ᶠ z in 𝓝 t, z < 0 from isOpen_Iio.mem_nhds ht] with z hz
        exact Real.smoothTransition.zero_of_nonpos hz.le
      rw [he.deriv_eq,deriv_const]
    · have he : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 1) := by
        filter_upwards [show ∀ᶠ z in 𝓝 t, 1 < z from isOpen_Ioi.mem_nhds ht] with z hz
        exact Real.smoothTransition.one_of_one_le hz.le
      rw [he.deriv_eq,deriv_const]
  have hs : tsupport (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
    apply closure_minimal _ isClosed_Icc
    intro t ht
    by_contra hn
    have hh : t < 0 ∨ 1 < t := by
      simpa only [mem_Icc,not_and_or,not_le] using hn
    exact ht (hzero t hh)
  have hc : HasCompactSupport (deriv Real.smoothTransition) := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hτ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hcont : Continuous (deriv Real.smoothTransition) := hτ.continuous_deriv (by simp)
  obtain ⟨D,hD⟩ := hc.exists_bound_of_continuous hcont
  refine ⟨D,by have h := hD 0; exact (norm_nonneg _).trans h,?_,?_⟩
  · intro t
    simpa only [Real.norm_eq_abs] using hD t
  · intro t ht
    exact hs (subset_tsupport _ ht)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
