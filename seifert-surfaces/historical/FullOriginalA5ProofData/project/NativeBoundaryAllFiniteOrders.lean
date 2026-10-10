import NativeBoundaryQuasilinearFiniteGain

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

theorem C1QuasilinearDirichletSolution.local_all_finite_holder_orders
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) (n : ℕ) :
    ∃ r : ℝ, ∃ α : ℝ≥0, 0 < r ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      NativeCapHolder (nativeClosedBoundaryCap c r) α (n + 2) u := by
  induction n with
  | zero => exact hsolution.local_capHolder_two hρ c hc
  | succ n ih =>
    obtain ⟨r, α, hr, hα, hα1, hball, hu⟩ := ih
    obtain ⟨s, hs, hsball, hgain⟩ :=
      hsolution.local_finite_holder_successor hρ c hc r hr hball α hα hα1 n hu
    exact ⟨s, α, hs, hα, hα1, hsball, hgain⟩

/-- Every finite order holds on the caller's smaller closed half-disc.
The local cap may shrink with the derivative order. -/
theorem C1QuasilinearDirichletSolution.all_finite_orders_on_smaller_closedHalfDisc
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (r : ℝ) (hr : 0 < r) (hrρ : r < ρ) (n : ℕ) :
    ContDiffOn ℝ n u (closedHalfDisc r) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x hx
  have hxball : x ∈ Metric.ball 0 ρ := Metric.closedBall_subset_ball hrρ hx.1
  have hxn : 0 ≤ x 0 := hx.2
  rcases eq_or_lt_of_le hxn with hflat | hpos
  · have hxflat : x ∈ flatBoundary ρ := ⟨hxball, hflat.symm⟩
    obtain ⟨δ, α, hδ, hα, _, _, hH⟩ := hsolution.local_all_finite_holder_orders hρ x hxflat n
    refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
    exact ((hH.contDiffOn hα).of_le (by exact_mod_cast Nat.le_add_right n 2)).mono
      (fun y hy => ⟨Metric.ball_subset_closedBall hy.2, hy.1.2⟩)
  · have hxO : x ∈ openHalfDisc ρ := ⟨hxball, hpos⟩
    exact ⟨openHalfDisc ρ, openHalfDisc_isOpen ρ, hxO,
      (hsolution.smooth_on_openHalfDisc.of_le (by simp)).mono inter_subset_right⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
