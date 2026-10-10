import NativeA5FlatTraceBridgeV471
import NativeBoundarySchauderScalarApplication

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem C1QuasilinearDirichletSolution.local_holder_zero_trace_tangential_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α
        (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1))
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨r, δ, K, α, hr, hδ, hδr, hα, hα1, houter, hquot⟩ :=
    hsolution.uniform_zero_trace_tangential_holder hρ c hc
  have hball : Metric.closedBall c δ ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans houter
  refine ⟨δ, K, α, hδ, hα, hα1, hball, ?_⟩
  intro x hx y hy
  have hlx := native_tangential_quotient_limit hsolution x (hball hx.1) hx.2
  have hly := native_tangential_quotient_limit hsolution y (hball hy.1) hy.2
  apply le_of_tendsto (continuous_edist.tendsto _ |>.comp (hlx.prodMk_nhds hly))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds] with h hh hhr
  have hhpos : 0 < h := hh
  exact hquot h (ne_of_gt hhpos) (by simpa only [abs_of_pos hhpos] using hhr) x hx y hy

/-- Exact frozen flat-trace provider consumed under the original A5 solution
state, with no supplied trace or higher regularity hypothesis. -/
theorem C1QuasilinearDirichletSolution.local_actual_tangential_flat_zero_trace
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c (2 * r) ⊆ Metric.ball 0 ρ ∧
      let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) -
        deriv g.value ((x + c) 1)
      FlatZeroTrace r (fun y => v (coordinateSwap y))
        (fun y => coordinateSwap (planarGradient v (coordinateSwap y))) := by
  have hcf : c 0 = 0 := hc.2
  obtain ⟨s, hs, hsball, hodd⟩ := hsolution.local_tangential_derivative_odd_memW1p hρ c hc
  obtain ⟨δ, K, α, hδ, hα, hα1, hδball, hH⟩ :=
    hsolution.local_holder_zero_trace_tangential_derivative hρ c hc
  let r := min (s / 8) (δ / 4)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrs : 2 * r ≤ s / 2 := by dsimp [r]; linarith [min_le_left (s / 8) (δ / 4)]
  have hrδ : 2 * r ≤ δ := by dsimp [r]; linarith [min_le_right (s / 8) (δ / 4)]
  let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) -
    deriv g.value ((x + c) 1)
  have hmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc (2 * r))
      (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have hh := Metric.closedBall_subset_closedBall hrδ hx.1
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hh
    · change 0 ≤ (x + c) 0
      simp only [PiLp.add_apply, hcf, add_zero]
      exact hx.2
  have hball : Metric.closedBall c (2 * r) ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall hrδ).trans hδball
  have hvo : ContDiffOn ℝ 1 v (openHalfDisc (2 * r)) := by
    have hsub : MapsTo (fun x : E2 => x + c) (openHalfDisc (2 * r)) (openHalfDisc ρ) := by
      intro x hx
      refine ⟨hδball (hmap (openHalfDisc_subset_closedHalfDisc _ hx)).1, ?_⟩
      change 0 < (x + c) 0
      simp only [PiLp.add_apply, hcf, add_zero]
      exact hx.2
    exact ((hsolution.smooth_partial_on_openHalfDisc 1).sub
      (g.smooth_deriv_extension_on_ball.mono (fun x hx => hx.1))).of_le (by simp) |>.comp
        (contDiff_id.add contDiff_const).contDiffOn hsub
  have hholder : HolderOnWith K α v (closedHalfDisc (2 * r)) := by
    intro x hx y hy
    simpa only [v, edist_dist, dist_add_right] using hH (x + c) (hmap hx) (y + c) (hmap hy)
  have hz : ∀ x ∈ flatBoundary (2 * r), v x = 0 := by
    intro x hx
    apply sub_eq_zero.mpr
    apply hsolution.tangential_derivative_trace hρ
    refine ⟨hδball (hmap ⟨Metric.ball_subset_closedBall hx.1, by change 0 ≤ x 0; rw [hx.2]⟩).1, ?_⟩
    change (x + c) 0 = 0
    simp only [PiLp.add_apply, hcf, add_zero]
    exact hx.2
  have hodd' : DeGiorgi.MemW1p 2 (nativeOddExtension v) (Metric.ball 0 (2 * r)) :=
    (hodd.someWitness.restrict Metric.isOpen_ball (Metric.ball_subset_ball hrs)).memW1p
  exact ⟨r, hr, hball,
    (native_flat_zero_trace_of_odd_H1_holder r hr v K α hα hα1 hvo hholder hz hodd').2⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
