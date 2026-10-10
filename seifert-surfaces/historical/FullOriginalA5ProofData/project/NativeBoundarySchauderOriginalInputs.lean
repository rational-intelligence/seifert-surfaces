import NativeBoundarySchauderOriginalTrace
import NativeBoundarySchauderActualWeakGradient

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- Native weak equation, actual gradient and paid flat trace on one common
radius, derived solely from the original solution. -/
theorem C1QuasilinearDirichletSolution.local_actual_tangential_boundary_scalar_inputs
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c (2 * r) ⊆ Metric.ball 0 ρ ∧
      let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) -
        deriv g.value ((x + c) 1)
      ContinuousOn v (closedHalfDisc (2 * r)) ∧
      WeakDivergenceWithData (openHalfDisc r) (fun x => nativePrincipalWithin ρ Q u (x + c))
        (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d (x + c))
        (fun _ => 0) v (planarGradient v) ∧
      FlatZeroTrace r (fun y => v (coordinateSwap y))
        (fun y => coordinateSwap (planarGradient v (coordinateSwap y))) := by
  obtain ⟨t, ht, htball, htrace⟩ := hsolution.local_actual_tangential_flat_zero_trace hρ c hc
  obtain ⟨s, hs, hsball, hweak⟩ := hsolution.local_actual_tangential_classical_weak_divergence hρ c hc
  let r := min t (s / 2)
  have hr : 0 < r := lt_min ht (by positivity)
  have hrt : r ≤ t := min_le_left _ _
  have hrs : r ≤ s := by dsimp [r]; linarith [min_le_right t (s / 2)]
  let v0 := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
  let v := fun x => v0 (x + c)
  let U := Metric.ball c s ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hpre := (native_flat_translation_halfDisc c hc.2 s).1
  have htranslated := native_weak_divergence_translation U hU.measurableSet c
    (nativePrincipalWithin ρ Q u) (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d x)
    v0 (planarGradient v0) hweak
  rw [hpre] at htranslated
  have hg : (fun x => planarGradient v0 (x + c)) = planarGradient v := by
    funext x
    exact (planar_gradient_translation v0 c x).symm
  rw [hg] at htranslated
  have hball : Metric.closedBall c (2 * r) ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hrt (by norm_num))).trans htball
  have hcf : c 0 = 0 := hc.2
  have hmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc (2 * r)) (closedHalfDisc ρ) := by
    intro x hx
    refine ⟨Metric.ball_subset_closedBall (hball ?_), ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    · change 0 ≤ (x + c) 0
      simp only [PiLp.add_apply, hcf, add_zero]
      exact hx.2
  have hvc : ContinuousOn v (closedHalfDisc (2 * r)) := by
    have hd := hsolution.c1.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num)
    have hdv := hd.clm_apply (continuousOn_const (c := coordinateVector 2 1))
    have hg : ContinuousOn (fun x : E2 => deriv g.value (x 1)) (Metric.ball 0 ρ) :=
      g.smooth_deriv_extension_on_ball.continuousOn
    have hmBall : MapsTo (fun x : E2 => x + c) (closedHalfDisc (2 * r)) (Metric.ball 0 ρ) := by
      intro x hx
      apply hball
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    exact (hdv.comp (continuous_id.add continuous_const).continuousOn hmap).sub
      (hg.comp (continuous_id.add continuous_const).continuousOn hmBall)
  have hsub : openHalfDisc r ⊆ openHalfDisc s := fun x hx =>
    ⟨Metric.ball_subset_ball hrs hx.1, hx.2⟩
  exact ⟨r, hr, hball, hvc,
    native_weak_divergence_restrict _ _ hsub _ _ _ _ htranslated,
    native_flat_trace_restrict t r hr hrt _ _ htrace⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
