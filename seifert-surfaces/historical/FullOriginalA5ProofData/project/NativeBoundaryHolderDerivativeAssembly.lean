import NativeBoundarySecondOrderHolderGain

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem native_clm_holder_of_coordinate_evaluations
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Set E2) (L : E2 → E2 →L[ℝ] F) (α : ℝ≥0)
    (hH : ∀ i : Fin 2, ∃ C : ℝ≥0, HolderOnWith C α
      (fun x => L x (coordinateVector 2 i)) K) :
    ∃ C : ℝ≥0, HolderOnWith C α L K := by
  obtain ⟨C0, h0⟩ := hH 0
  obtain ⟨C1, h1⟩ := hH 1
  let P (i : Fin 2) : F →L[ℝ] E2 →L[ℝ] F :=
    ContinuousLinearMap.smulRightL ℝ E2 F (EuclideanSpace.proj i)
  have hP0 := native_holder_comp_linear K _ C0 α h0 (P 0)
  have hP1 := native_holder_comp_linear K _ C1 α h1 (P 1)
  have hsum := native_holder_add K _ _ _ _ α hP0 hP1
  have hEq (x : E2) : L x = P 0 (L x (coordinateVector 2 0)) + P 1 (L x (coordinateVector 2 1)) := by
    ext ξ
    have hξ : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    conv_lhs => rw [hξ]
    simp [P]
  refine ⟨‖P 0‖₊ * C0 + ‖P 1‖₊ * C1, ?_⟩
  intro x hx y hy
  rw [hEq x, hEq y]
  exact hsum x hx y hy

theorem C1QuasilinearDirichletSolution.local_C2_holder_first_derivative_fields
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c r) ∧
      ∀ j, ∃ C : ℝ≥0, HolderOnWith C α
        (fderivWithin ℝ (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 j))
          (nativeClosedBoundaryCap c r)) (nativeClosedBoundaryCap c r) := by
  obtain ⟨r, α, hr, hα, hα1, hball, hu, hH⟩ :=
    hsolution.local_C2_holder_closed_boundary_cap hρ c hc
  exact ⟨r, α, hr, hα, hα1, hball, hu, fun j =>
    native_clm_holder_of_coordinate_evaluations _ _ α (fun i => hH i j)⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
