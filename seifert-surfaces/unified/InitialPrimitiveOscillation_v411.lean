import InitialTangentialPrimitive_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem finite_L2_vector_integral_sq_v411
    (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ℝ → E2) (hL2 : MemLp a 2 μ) :
    ‖∫ t, a t ∂μ‖ ^ 2 ≤ (μ univ).toReal * ∫ t, ‖a t‖ ^ 2 ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  let V : ℝ := (μ univ).toReal
  let N : ℝ := ∫ t, ‖a t‖ ∂μ
  let Q : ℝ := ∫ t, ‖a t‖ ^ 2 ∂μ
  have hV : 0 < V := ENNReal.toReal_pos
    (Measure.measure_univ_ne_zero.mpr hμ) (measure_ne_top μ univ)
  have hi : Integrable (fun t => ‖a t‖) μ := hL2.norm.integrable (by norm_num)
  have hi2 : Integrable (fun t => ‖a t‖ ^ 2) μ := hL2.norm.integrable_sq
  have hvariance : 0 ≤ ∫ t, (N - V * ‖a t‖) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have heq : (∫ t, (N - V * ‖a t‖) ^ 2 ∂μ) =
      V * N ^ 2 - (2 * N * V) * N + V ^ 2 * Q := by
    have hexp : (fun t => (N - V * ‖a t‖) ^ 2) =
        (fun t => N ^ 2 - (2 * N * V) * ‖a t‖ + V ^ 2 * ‖a t‖ ^ 2) := by
      funext t; ring
    have hconst : Integrable (fun _ : ℝ => N ^ 2) μ := integrable_const _
    have hfirst : Integrable (fun t => N ^ 2 - (2 * N * V) * ‖a t‖) μ :=
      hconst.sub (hi.const_mul _)
    have hsecond : Integrable (fun t => V ^ 2 * ‖a t‖ ^ 2) μ := hi2.const_mul _
    rw [hexp, integral_add hfirst hsecond,
      integral_sub hconst (hi.const_mul (2 * N * V)), integral_const_mul,
      integral_const_mul, integral_const]
    rfl
  rw [heq] at hvariance
  have hCS : N ^ 2 ≤ V * Q := by
    apply (mul_le_mul_iff_of_pos_left hV).mp
    nlinarith [hvariance]
  have hnorm : ‖∫ t, a t ∂μ‖ ≤ N := norm_integral_le_integral_norm _
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hCS

private theorem circle_primitive_increment_sq_v411
    (a : ℝ → E2) (b0 : E2)
    (hL2 : MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi))) :
    let c : ℝ → E2 := fun t => b0 + ∫ u in (-Real.pi)..t, a u
    ∀ t ∈ Icc (-Real.pi) Real.pi, ∀ u ∈ Icc (-Real.pi) Real.pi,
      ‖c t - c u‖ ^ 2 ≤ |t - u| * ∫ v in Ioo (-Real.pi) Real.pi, ‖a v‖ ^ 2 := by
  classical
  dsimp only
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hL2cc : MemLp a 2 (volume.restrict (Icc (-Real.pi) Real.pi)) := by
    rwa [← restrict_Ioo_eq_restrict_Icc]
  let : IsFiniteMeasure (volume.restrict (Icc (-Real.pi) Real.pi)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hIcc : IntegrableOn a (Icc (-Real.pi) Real.pi) := hL2cc.integrable (by norm_num)
  have hQcc : IntegrableOn (fun t => ‖a t‖ ^ 2) (Icc (-Real.pi) Real.pi) :=
    hL2cc.norm.integrable_sq
  intro t ht u hu
  let S : Set ℝ := uIcc u t
  have hsub : S ⊆ Icc (-Real.pi) Real.pi := by
    intro v hv
    rcases mem_uIcc.mp hv with hv | hv
    · exact ⟨hu.1.trans hv.1, hv.2.trans ht.2⟩
    · exact ⟨ht.1.trans hv.1, hv.2.trans hu.2⟩
  let ν : Measure ℝ := volume.restrict S
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt measure_Icc_lt_top).ne
  have hL2S : MemLp a 2 ν := hL2cc.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hi (v : ℝ) (hv : v ∈ Icc (-Real.pi) Real.pi) :
      IntervalIntegrable a volume (-Real.pi) v := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hv.1]
    exact hIcc.mono_set (fun x hx => ⟨hx.1.le, hx.2.trans hv.2⟩)
  have hdifference : (b0 + ∫ v in (-Real.pi)..t, a v) -
      (b0 + ∫ v in (-Real.pi)..u, a v) = ∫ v in u..t, a v := by
    rw [add_sub_add_left_eq_sub]
    exact intervalIntegral.integral_interval_sub_left (hi t ht) (hi u hu)
  rw [hdifference]
  have hnorm : ‖∫ v in u..t, a v‖ = ‖∫ v in S, a v‖ := by
    dsimp only [S]
    rcases le_total u t with hut | htu
    · rw [intervalIntegral.integral_of_le hut, uIcc_of_le hut, integral_Icc_eq_integral_Ioc]
    · rw [intervalIntegral.integral_of_ge htu, uIcc_of_ge htu, integral_Icc_eq_integral_Ioc, norm_neg]
  rw [hnorm]
  have hCS := finite_L2_vector_integral_sq_v411 ν a hL2S
  have hvol : (ν univ).toReal = |t - u| := by
    rw [Measure.restrict_apply_univ]
    dsimp only [S]
    rcases le_total u t with hut | htu
    · rw [uIcc_of_le hut, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hut),
        abs_of_nonneg (sub_nonneg.mpr hut)]
    · rw [uIcc_of_ge htu, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr htu),
        abs_of_nonpos (sub_nonpos.mpr htu)]
      ring
  rw [hvol] at hCS
  have hQ : (∫ v in S, ‖a v‖ ^ 2) ≤ ∫ v in Ioo (-Real.pi) Real.pi, ‖a v‖ ^ 2 := by
    rw [← integral_Icc_eq_integral_Ioo]
    exact setIntegral_mono_set hQcc (Eventually.of_forall fun v => sq_nonneg _)
      (Eventually.of_forall fun v hv => hsub hv)
  exact hCS.trans (mul_le_mul_of_nonneg_left hQ (abs_nonneg _))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
