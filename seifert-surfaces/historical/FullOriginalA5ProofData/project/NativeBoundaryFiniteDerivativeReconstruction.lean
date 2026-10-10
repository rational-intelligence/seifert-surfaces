import NativeBoundaryHigherJetComposition

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_finite_order_smaller_cap_of_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r s : ℝ) (hs : 0 < s) (hsr : s < r)
    (v : E2 → F) (D : E2 → E2 →L[ℝ] F) (n : ℕ)
    (hv : ContinuousOn v (nativeClosedBoundaryCap c r))
    (hD : ContDiffOn ℝ n D (nativeClosedBoundaryCap c r))
    (hder : ∀ x ∈ Metric.ball c r ∩ {x : E2 | 0 < x 0}, HasFDerivAt v (D x) x) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) v (nativeClosedBoundaryCap c s) ∧
      EqOn (fderivWithin ℝ v (nativeClosedBoundaryCap c s)) D (nativeClosedBoundaryCap c s) := by
  have hg := native_C1_smaller_cap_of_continuous_derivative c hcf r s hs hsr v D
    hv hD.continuousOn hder
  have hsub : nativeClosedBoundaryCap c s ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hsr.le hx.1, hx.2⟩
  refine ⟨?_, hg.2⟩
  rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
    contDiffOn_succ_iff_fderivWithin (nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf)]
  refine ⟨hg.1.differentiableOn (by norm_num), by simp, ?_⟩
  exact (hD.mono hsub).congr hg.2

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
