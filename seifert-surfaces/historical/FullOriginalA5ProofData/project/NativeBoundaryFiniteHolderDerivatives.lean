import NativeBoundaryFiniteHolderCalculus
import NativeBoundaryFiniteDerivativeReconstruction

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem NativeCapHolder.assemble_clm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ}
    (L : E2 → E2 →L[ℝ] F)
    (hL : ∀ i, NativeCapHolder K α n (fun x => L x (coordinateVector 2 i))) :
    NativeCapHolder K α n L := by
  let P (i : Fin 2) : F →L[ℝ] E2 →L[ℝ] F :=
    ContinuousLinearMap.smulRightL ℝ E2 F (EuclideanSpace.proj i)
  have hsum := ((hL 0).comp_linear hKD (P 0)).add hKD ((hL 1).comp_linear hKD (P 1))
  apply hsum.congr
  intro x _
  ext ξ
  have hξ : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector]
  conv_lhs => rw [hξ]
  simp [P]

theorem NativeCapHolder.within_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder K α (n + 1) f) :
    NativeCapHolder K α n (fderivWithin ℝ f K) :=
  NativeCapHolder.assemble_clm hKD _ hf.2

theorem NativeCapHolder.derivative_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → F}
    (hf : NativeCapHolder K α (n + 1) f) (ξ : E2) :
    NativeCapHolder K α n (fun x => fderivWithin ℝ f K x ξ) :=
  (hf.within_derivative hKD).comp_linear hKD (ContinuousLinearMap.apply ℝ F ξ)

theorem NativeCapHolder.gradient_field
    {K : Set E2} (hKD : UniqueDiffOn ℝ K) {α : ℝ≥0} {n : ℕ} {f : E2 → ℝ}
    (hf : NativeCapHolder K α (n + 1) f) :
    NativeCapHolder K α n (planarGradientWithin f K) := by
  let P (i : Fin 2) : ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 i)
  have hsum := ((hf.2 0).comp_linear hKD (P 0)).add hKD ((hf.2 1).comp_linear hKD (P 1))
  apply hsum.congr
  intro x _
  simp only [planarGradientWithin, Fin.sum_univ_two, P, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]

/-- Closure reconstruction preserves every finite Holder derivative, with
the derivative equal to the actual supplied field on the smaller cap. -/
theorem native_capHolder_smaller_cap_of_derivative
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E2) (hcf : c 0 = 0) (r s : ℝ) (hs : 0 < s) (hsr : s < r)
    (α : ℝ≥0) (hα : 0 < α) (n : ℕ)
    (v : E2 → F) (D : E2 → E2 →L[ℝ] F)
    (hv : ContinuousOn v (nativeClosedBoundaryCap c r))
    (hD : NativeCapHolder (nativeClosedBoundaryCap c r) α n D)
    (hder : ∀ x ∈ Metric.ball c r ∩ {x : E2 | 0 < x 0}, HasFDerivAt v (D x) x) :
    NativeCapHolder (nativeClosedBoundaryCap c s) α (n + 1) v := by
  have hg := native_finite_order_smaller_cap_of_derivative c hcf r s hs hsr v D n hv
    (hD.contDiffOn hα) hder
  have hsub : nativeClosedBoundaryCap c s ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall hsr.le hx.1, hx.2⟩
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c s hs hcf
  refine ⟨hg.1, ?_⟩
  intro i
  apply ((hD.restrict hsub hKD).comp_linear hKD (ContinuousLinearMap.apply ℝ F (coordinateVector 2 i))).congr
  intro x hx
  dsimp only
  rw [hg.2 hx]
  rfl

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
