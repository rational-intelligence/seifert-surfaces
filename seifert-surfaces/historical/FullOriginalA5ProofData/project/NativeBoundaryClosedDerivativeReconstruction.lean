import NativeBoundarySchauderFirstGain
import Mathlib.Analysis.Calculus.FDeriv.Extend

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_openHalfDisc_convex (r : ℝ) : Convex ℝ (openHalfDisc r) :=
  (convex_ball (0 : E2) r).inter
    ((convex_Ioi (0 : ℝ)).linear_preimage
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap)

/-- A continuous interior derivative extending to the actual closed cap is
the derivative there. This uses a proved calculus extension theorem. -/
theorem native_C1_smaller_closed_cap_of_continuous_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r s : ℝ) (hs : 0 < s) (hsr : s < r)
    (v : E2 → F) (D : E2 → E2 →L[ℝ] F)
    (hv : ContinuousOn v (closedHalfDisc r))
    (hD : ContinuousOn D (closedHalfDisc r))
    (hder : ∀ x ∈ openHalfDisc r, HasFDerivAt v (D x) x) :
    ContDiffOn ℝ 1 v (closedHalfDisc s) ∧
      EqOn (fderivWithin ℝ v (closedHalfDisc s)) D (closedHalfDisc s) := by
  have hclosed : IsClosed (closedHalfDisc r) :=
    Metric.isClosed_closedBall.inter
      (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hclsub : closure (openHalfDisc r) ⊆ closedHalfDisc r :=
    closure_minimal (openHalfDisc_subset_closedHalfDisc r) hclosed
  have hdcl : ∀ x ∈ closedHalfDisc s, HasFDerivWithinAt v (D x) (closedHalfDisc s) x := by
    intro x hx
    have hxcl := native_closed_halfDisc_subset_closure_larger_open s r hsr hx
    have hxR := hclsub hxcl
    have hlim : Tendsto (fderiv ℝ v) (𝓝[openHalfDisc r] x) (𝓝 (D x)) := by
      apply ((hD x hxR).mono (openHalfDisc_subset_closedHalfDisc r)).congr'
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hder y hy).fderiv.symm
    have hh := hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy => (hder y hy).differentiableAt.differentiableWithinAt)
      (native_openHalfDisc_convex r) (openHalfDisc_isOpen r)
      (fun y hy => (hv y (hclsub hy)).mono (openHalfDisc_subset_closedHalfDisc r)) hlim
    exact hh.mono (native_closed_halfDisc_subset_closure_larger_open s r hsr)
  refine ⟨?_, fun x hx => (hdcl x hx).fderivWithin (closedHalfDisc_uniqueDiffOn hs x hx)⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 by rfl,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (closedHalfDisc_uniqueDiffOn hs)]
  exact ⟨by simp, D, contDiffOn_zero.mpr (hD.mono (closedHalfDisc_mono hsr.le)), hdcl⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
