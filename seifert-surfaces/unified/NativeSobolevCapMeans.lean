import NativeSobolevEnergyDensity
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_H1_ae_cap_mean_limit
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i)) :
    ∀ᵐ x ∂volume, x ∈ disc 1 → ∀ r0 : ℝ, 0 < r0 → ∀ i j,
      Tendsto (fun n => capMean (fun z i _j => u z i) x (dyadicRadius r0 n) i j)
        atTop (𝓝 (u x i)) := by
  classical
  let : IsFiniteMeasure (volume.restrict (disc 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hglobal (i : Fin 2) : Integrable ((disc 1).indicator (fun x => u x i)) volume := by
    have hi : IntegrableOn (fun x => u x i) (disc 1) := (hH1 i).2.1.integrable (by norm_num)
    exact hi.integrable_indicator Metric.isOpen_ball.measurableSet
  have hdiff : ∀ᵐ x ∂volume, ∀ i : Fin 2,
      Tendsto (fun s => ⨍ z in s, (disc 1).indicator (fun z => u z i) z)
        ((Besicovitch.vitaliFamily volume).filterAt x)
        (𝓝 ((disc 1).indicator (fun z => u z i) x)) := by
    exact ae_all_iff.mpr (fun i =>
      (Besicovitch.vitaliFamily (volume : Measure E2)).ae_tendsto_average
        (hglobal i).locallyIntegrable)
  filter_upwards [hdiff] with x hx hxDisc r0 hr0 i j
  obtain ⟨e, he, heSub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball x hxDisc
  have hRadiusTendsto : Tendsto (dyadicRadius r0) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r0
      change Tendsto (fun n : ℕ => r0 / (2 : ℝ) ^ n) atTop (𝓝 0)
      simpa [one_div, inv_pow, div_eq_mul_inv] using hh
    · exact Eventually.of_forall (fun n => by
        change 0 < r0 / (2 : ℝ) ^ n
        positivity)
  have ht := (hx i).comp ((Besicovitch.tendsto_filterAt volume x).comp hRadiusTendsto)
  have hevent : ∀ᶠ n : ℕ in atTop,
      (⨍ y in Metric.closedBall x (dyadicRadius r0 n),
        (disc 1).indicator (fun w => u w i) y) =
        capMean (fun z i _j => u z i) x (dyadicRadius r0 n) i j := by
    filter_upwards [(tendsto_nhdsWithin_iff.mp hRadiusTendsto).1.eventually (gt_mem_nhds he)]
      with n hn
    have hsub : Metric.closedBall x (dyadicRadius r0 n) ⊆ disc 1 :=
      (Metric.closedBall_subset_ball hn).trans heSub
    have hclosed : Metric.closedBall x (dyadicRadius r0 n) =ᵐ[volume]
        Metric.ball x (dyadicRadius r0 n) := by
      rw [ae_eq_set]
      refine ⟨?_, ?_⟩
      · rw [Metric.closedBall_diff_ball]
        exact Measure.addHaar_sphere volume x _
      · rw [Set.diff_eq_empty.mpr Metric.ball_subset_closedBall]
        exact measure_empty
    rw [setAverage_congr_fun Metric.isClosed_closedBall.measurableSet
      (Eventually.of_forall (fun y hy => Set.indicator_of_mem (hsub hy) _)),
      setAverage_congr hclosed]
    have hcap : planarCap x (dyadicRadius r0 n) = Metric.ball x (dyadicRadius r0 n) :=
      inter_eq_right.mpr (Metric.ball_subset_closedBall.trans hsub)
    change _ = ((volume (planarCap x (dyadicRadius r0 n))).toReal)⁻¹ *
      ∫ y in planarCap x (dyadicRadius r0 n), u y i
    rw [hcap, average_eq]
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have ht' := ht.congr' hevent
  simpa only [Set.indicator_of_mem hxDisc] using ht'

#print axioms native_H1_ae_cap_mean_limit
