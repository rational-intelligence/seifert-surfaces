import NativeBoundaryNormalEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

theorem C1QuasilinearDirichletSolution.smooth_partial_on_openHalfDisc
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))
      (openHalfDisc ρ) := by
  apply ((hsolution.smooth_on_openHalfDisc.fderiv_of_isOpen (openHalfDisc_isOpen ρ) (by simp)).clm_apply
    contDiffOn_const).congr
  intro x hx
  rw [fderivWithin_closedHalfDisc_eq_fderiv u hx]

/-- The full ordinary Hessian is square-integrable on a native cap reaching
the flat boundary. Its normal column is recovered from the actual equation,
without assuming any normal derivative estimate. -/
theorem C1QuasilinearDirichletSolution.local_full_second_gradient_memLp
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ∀ i : Fin 2,
        MemLp (planarGradient (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))) 2
          (volume.restrict (Metric.ball c r ∩ {x : E2 | 0 < x 0})) := by
  obtain ⟨s, hs, hball, hTangent⟩ := hsolution.local_tangential_second_gradient_memLp hρ c hc
  have hcf : c 0 = 0 := hc.2
  obtain ⟨t, κ, M, T, ht, hTop, hconv, hcompact, hTJ, hjets, hκ, hM, hvalues,
    hbounds, hiterated, hcoercive⟩ :=
      hsolution.local_boundary_jet_tube hρ c ⟨Metric.ball_subset_closedBall hc.1, by change 0 ≤ c 0; simp [hcf]⟩
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsmall : U ⊆ Metric.ball c s ∩ {x : E2 | 0 < x 0} :=
    fun x hx => ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
  have hsub : U ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall (hsmall hx).1), hx.2⟩
  have hclosed : Metric.closedBall c r ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hball
  let G (i : Fin 2) := planarGradient (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))
  have hG1 : MemLp (G 1) 2 (volume.restrict U) :=
    hTangent.mono_measure (Measure.restrict_mono_set _ hsmall)
  have hG0meas : AEStronglyMeasurable (G 0) (volume.restrict U) :=
    (QuasilinearLocalization.Helpers.gradient_continuousOn U hU _
      ((hsolution.smooth_partial_on_openHalfDisc 0).mono hsub |>.of_le (by simp))).aestronglyMeasurable
        hU.measurableSet
  haveI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball c r from fun x hx => hx.1))
        Metric.isBounded_ball.measure_lt_top).ne
  let S := 3 * M + 2 * M ^ 2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hbound : ∀ x ∈ U, ‖G 0 x‖ ≤ κ⁻¹ * S + (3 * M * κ⁻¹ + 1) * ‖G 1 x‖ := by
    intro x hx
    have hxΩ := hsub hx
    have hxclosed := openHalfDisc_subset_closedHalfDisc ρ hxΩ
    have hxT : firstJetWithin ρ u x ∈ closure T := by
      apply subset_closure
      apply hjets x
      refine ⟨Metric.mem_closedBall.mpr ?_, hxclosed⟩
      have hd := Metric.mem_ball.mp hx.1
      have hrt : r ≤ t := min_le_right _ _
      linarith
    have hb := hbounds _ hxT
    have hB := native_classical_coefficient_bounds hxΩ κ M (by linarith)
      (hvalues x hxclosed).2 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
      (hcoercive _ hxT)
    exact hsolution.native_normal_second_gradient_bound x hxΩ κ M S hκ (by linarith)
      hS hB.1 hB.2.1 hB.2.2
  have hmajor : MemLp (fun x => κ⁻¹ * S + (3 * M * κ⁻¹ + 1) * ‖G 1 x‖) 2
      (volume.restrict U) := (memLp_const (κ⁻¹ * S)).add
        (hG1.norm.const_mul (3 * M * κ⁻¹ + 1))
  have hG0 : MemLp (G 0) 2 (volume.restrict U) := hmajor.mono' hG0meas (by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hbound x hx)
  refine ⟨r, hr, hclosed, ?_⟩
  intro i
  fin_cases i
  · exact hG0
  · exact hG1

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
