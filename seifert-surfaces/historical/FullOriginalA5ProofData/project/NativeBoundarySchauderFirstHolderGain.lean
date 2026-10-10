import NativeBoundarySchauderHolderTranslation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- First genuine boundary Schauder gain for the actual tangential derivative
of the original solution. All scalar-provider hypotheses are derived. -/
theorem C1QuasilinearDirichletSolution.local_C1_holder_zero_trace_tangential_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 1
        (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1))
        (nativeClosedBoundaryCap c δ) ∧
      ∀ i, ∃ C : ℝ≥0, HolderOnWith C α
        (fun x => fderivWithin ℝ
          (fun y => fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) - deriv g.value (y 1))
          (nativeClosedBoundaryCap c δ) x (coordinateVector 2 i))
        (nativeClosedBoundaryCap c δ) := by
  obtain ⟨t, ht, htball, hcont, hweak, htrace⟩ :=
    hsolution.local_actual_tangential_boundary_scalar_inputs hρ c hc
  obtain ⟨sA, HA, αA, κ, M, hsA, hαA, hαA1, hκ, hM, hsAball, A, hAEq, hAH, hAb⟩ :=
    hsolution.local_global_holder_principal_extension hρ c hc
  obtain ⟨sE, HE, αE, B, hsE, hαE, hαE1, hB, hsEball, E, hEEq, hEH, hEb⟩ :=
    hsolution.local_global_holder_tangential_forcing_extension hρ c hc
  let r := min t (min sA sE)
  have hr : 0 < r := lt_min ht (lt_min hsA hsE)
  have hrt : r ≤ t := min_le_left _ _
  have hrsA : r ≤ sA := (min_le_right _ _).trans (min_le_left _ _)
  have hrsE : r ≤ sE := (min_le_right _ _).trans (min_le_right _ _)
  let α := min αA αE
  have hα : 0 < α := lt_min hαA hαE
  have hα1 : α < 1 := (min_le_left _ _).trans_lt hαA1
  let Ca := max (Real.toNNReal (2 * M)) HA
  let Ce := max (Real.toNNReal (2 * B)) HE
  have haH : ∀ i j, HolderWith Ca α (fun x => A x i j) := by
    intro i j
    exact native_bounded_holderWith_lower_exponent _ HA αA α M hM.le
      (fun x => by simpa only [Real.norm_eq_abs] using (hAb x 0).2 i j)
      (hAH i j) (min_le_left _ _)
  have heH : HolderWith Ce α E :=
    native_bounded_holderWith_lower_exponent E HE αE α B hB hEb hEH (min_le_right _ _)
  let v0 := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
  let v := fun x => v0 (x + c)
  let a := fun x => A (x + c)
  let e := fun x => E (x + c)
  have htrans : HolderWith 1 1 (fun x : E2 => x + c) :=
    (isometry_add_right c).lipschitz.holderWith
  have hac : ∀ i j, HolderWith Ca α (fun x => a x i j) := by
    intro i j
    convert (haH i j).comp htrans using 1 <;> simp [a, Function.comp_def]
  have hec : HolderWith Ce α e := by
    convert heH.comp htrans using 1 <;> simp [e, Function.comp_def]
  have hsub : openHalfDisc r ⊆ openHalfDisc t := fun x hx =>
    ⟨Metric.ball_subset_ball hrt hx.1, hx.2⟩
  have hw := native_weak_divergence_restrict _ _ hsub _ _ _ _ hweak
  have hcf : c 0 = 0 := hc.2
  have hmap (s : ℝ) (hrs : r ≤ s) : MapsTo (fun x : E2 => x + c) (openHalfDisc r)
      (nativeClosedBoundaryCap c s) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have hh := Metric.closedBall_subset_closedBall hrs (Metric.ball_subset_closedBall hx.1)
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hh
    · change 0 ≤ (x + c) 0
      simp only [PiLp.add_apply, hcf, add_zero]
      exact hx.2.le
  have hwa : WeakDivergenceWithData (openHalfDisc r) a e (fun _ => 0) v (planarGradient v) :=
    native_zero_source_weak_divergence_coefficient_congr _ (openHalfDisc_isOpen r).measurableSet
      _ a _ e v _ (fun x hx => hAEq (hmap sA hrsA hx))
      (fun x hx => hEEq (hmap sE hrsE hx)) hw
  have hvc : ContinuousOn v (closedHalfDisc r) := hcont.mono
    (closedHalfDisc_mono (by linarith))
  have htg := native_flat_trace_restrict t r hr hrt _ _ htrace
  have hvGain := native_zero_source_boundary_C1_holder_gain r hr α hα hα1 a κ M hκ hM
      (fun x ξ => hAb (x + c) ξ) Ca hac e B hB Ce (fun x => hEb (x + c)) hec v
      (planarGradient v) hvc hwa htg
  have hd : 0 < r / 4 := by positivity
  have hback := native_boundary_derivative_holder_translation c hcf (r / 4) hd v0
    hvGain.1 α hvGain.2
  exact ⟨r / 4, α, hd, hα, hα1,
    (Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ 2 * t)).trans htball,
    hback.1, hback.2⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
