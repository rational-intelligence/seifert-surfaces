import NativeBoundaryFiniteNormalGain

set_option autoImplicit false
set_option maxHeartbeats 50000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- One finite-order gain for the same original function, once the actual
tangential derivative gain has been proved. -/
theorem C1QuasilinearDirichletSolution.finite_order_gain_from_tangential
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) (r : ℝ) (hr : 0 < r)
    (hballr : Metric.closedBall c r ⊆ Metric.ball 0 ρ) (m : ℕ)
    (hu : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) u (nativeClosedBoundaryCap c r))
    (hT : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω)
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
      (nativeClosedBoundaryCap c r)) :
    ContDiffOn ℝ ((m + 2 : ℕ) : ℕ∞ω) u (nativeClosedBoundaryCap c (r / 2)) := by
  have hN := hsolution.finite_order_normal_derivative_from_tangential hρ c hc r hr hballr m hu hT
  let δ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let K := nativeClosedBoundaryCap c δ
  have hKr : K ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (by dsimp [δ]; linarith) hx.1, hx.2⟩
  have hball : Metric.closedBall c δ ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall (by dsimp [δ]; linarith)).trans hballr
  have hKρ : K ⊆ closedHalfDisc ρ := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hpartials : ∀ i : Fin 2, ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω)
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i)) K := by
    intro i
    fin_cases i
    · exact hN
    · exact hT.mono hKr
  have hG : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) (planarGradientWithin u (closedHalfDisc ρ)) K :=
    ContDiffOn.sum (fun i _ => (hpartials i).smul contDiffOn_const)
  have hD : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) (fderivWithin ℝ u K) K := by
    have hInner : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) (fun x => innerSL ℝ (planarGradientWithin u (closedHalfDisc ρ) x)) K :=
      (innerSL ℝ).contDiff.comp_contDiffOn hG
    apply hInner.congr
    intro x hx
    rw [fderivWithin_subset hKρ (nativeClosedBoundaryCap_uniqueDiffOn c δ hδ hc.2 x hx)
      (hsolution.c1.differentiableOn (by norm_num) x (hKρ hx))]
    exact native_fderivWithin_eq_innerSL_planarGradientWithin u (closedHalfDisc ρ) x
  have hsuccessor : ContDiffOn ℝ (((m + 1 : ℕ) : ℕ∞ω) + 1) u K :=
    contDiffOn_succ_of_fderivWithin
      ((hsolution.c1.differentiableOn (by norm_num)).mono hKρ) (by simp) hD
  convert hsuccessor using 1
  simp only [Nat.cast_add, Nat.cast_one]
  norm_num
  abel

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
