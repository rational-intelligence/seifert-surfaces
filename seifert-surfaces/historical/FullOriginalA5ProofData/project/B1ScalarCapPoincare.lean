import B1L1IndependentLower
import SmoothCapL2Uniform
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.Analysis.Integration.LpNorm
import Lean
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
open SeifertSurfaces.AppendixACoordinates L1Independent DeGiorgi

theorem scalar_native_H1_moving_cap_poincare :
  ∀ (u : E2 → ℝ) (du : E2 → E2),
    H1On (disc 1) u du →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ z in planarCap x r,
          (u z - (capVolume x r)⁻¹ * ∫ y in planarCap x r, u y) ^ 2) ≤
          C * r ^ 2 * ∫ z in planarCap x r, ‖du z‖ ^ 2 := by
  have smooth_cap := smooth_cap_l2_uniform
  obtain ⟨A, hA, smooth_bound⟩ := smooth_cap
  intro u du h1
  let hw : MemW1pWitness 2 u (disc 1) :=
    { memLp := h1.2.1
      weakGrad := du
      weakGrad_component_memLp := fun j =>
        h1.2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
      isWeakGrad := fun j φ hφ hφc hφs =>
        h1.1.2.2 φ (hφ.of_le (by simp)) hφc hφs j }
  have happrox := exists_smooth_W1p_approx_on_unitBall (d := 2) (p := (2 : ℝ))
    (u := u) (by norm_num)
  have hnum : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  rw [hnum] at happrox
  obtain ⟨ψ, hψ_smooth, _, hψ_fn, hψ_grad⟩ := happrox hw
  refine ⟨A ^ 2, sq_nonneg A, ?_⟩
  intro x hx r hr hr1
  let U := planarCap x r
  let μ := volume.restrict U
  have hsub : U ⊆ disc 1 := inter_subset_left
  have hμmono : μ ≤ volume.restrict (disc 1) := Measure.restrict_mono hsub le_rfl
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr ((measure_mono hsub).trans_lt measure_ball_lt_top).ne
  have huLp : MemLp u 2 μ := h1.2.1.mono_measure hμmono
  have hdLp : MemLp (fun z => ‖du z‖) 2 μ := (h1.2.2.mono_measure hμmono).norm
  have hu_int : Integrable u μ := huLp.integrable (by norm_num)
  have hψ_int : ∀ n, Integrable (ψ n) μ := fun n =>
    ((hψ_smooth n).continuous.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : E2) 1)).mono_set (hsub.trans Metric.ball_subset_closedBall)
  have hfn : Tendsto (fun n => eLpNorm (fun z => ψ n z - u z) 2 μ) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hψ_fn
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun n => eLpNorm_mono_measure _ hμmono)
  have hgrad : ∀ i : Fin 2, Tendsto
      (fun n => eLpNorm (fun z =>
        (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ)
      atTop (nhds 0) := by
    intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hψ_grad i)
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun n => eLpNorm_mono_measure _ hμmono)
  have hgrad_sum : Tendsto
      (fun n => ∑ i : Fin 2, eLpNorm (fun z =>
        (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ)
      atTop (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ∑ _ : Fin 2, (0 : ℝ≥0∞) from by simp]
    exact tendsto_finsetSum _ fun i _ => hgrad i
  have hgrad_error (n : ℕ) :
      eLpNorm (fun z => ‖fderiv ℝ (ψ n) z‖ - ‖du z‖) 2 μ ≤
        ∑ i : Fin 2, eLpNorm (fun z =>
          (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ := by
    have hpoint (z : E2) : ‖‖fderiv ℝ (ψ n) z‖ - ‖du z‖‖ ≤
        ∑ i : Fin 2, ‖(fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i‖ := by
      let v : E2 := WithLp.toLp 2
        (fun i => (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1))
      calc
        _ = |‖v‖ - ‖du z‖| := by
          rw [Real.norm_eq_abs, norm_fderiv_eq_norm_partials_local (d := 2)]
        _ ≤ ‖v - du z‖ := abs_norm_sub_norm_le v (du z)
        _ ≤ ∑ i : Fin 2, ‖(v - du z) i‖ := by
          have hs : ‖v - du z‖ ^ 2 = ∑ i : Fin 2, ((v - du z) i) ^ 2 :=
            EuclideanSpace.real_norm_sq_eq _
          rw [Fin.sum_univ_two] at hs ⊢
          rw [Real.norm_eq_abs, Real.norm_eq_abs]
          nlinarith [abs_nonneg ((v - du z) 0), abs_nonneg ((v - du z) 1),
            sq_abs ((v - du z) 0), sq_abs ((v - du z) 1), norm_nonneg (v - du z)]
        _ = _ := by simp [v]
    calc
      _ ≤ eLpNorm (fun z => ∑ i : Fin 2,
          ‖(fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i‖) 2 μ :=
        eLpNorm_mono
          (((hψ_smooth n).continuous_fderiv (by simp)).norm.aestronglyMeasurable.sub
            hdLp.aestronglyMeasurable)
          (fun z => (hpoint z).trans_eq
            (Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).symm)
      _ ≤ ∑ i : Fin 2, eLpNorm (fun z =>
          ‖(fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i‖) 2 μ := by
        rw [show (fun z => ∑ i : Fin 2,
          ‖(fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i‖) =
          ∑ i : Fin 2, (fun z =>
            ‖(fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i‖) by
            ext z; simp [Finset.sum_apply]]
        exact eLpNorm_sum_le (by norm_num)
      _ = _ := by
        congr 1; ext i
        exact eLpNorm_norm _
          ((((hψ_smooth n).continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable.sub
            ((h1.2.2.mono_measure hμmono).continuousLinearMap_comp
              (EuclideanSpace.proj (𝕜 := ℝ) i)).aestronglyMeasurable)
  have hderiv_bound (n : ℕ) : eLpNorm (fun z => ‖fderiv ℝ (ψ n) z‖) 2 μ ≤
      eLpNorm (fun z => ‖du z‖) 2 μ +
        ∑ i : Fin 2, eLpNorm (fun z =>
          (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ := by
    calc
      _ = eLpNorm ((fun z => ‖du z‖) +
          (fun z => ‖fderiv ℝ (ψ n) z‖ - ‖du z‖)) 2 μ := by
        congr 1; ext z; simp
      _ ≤ eLpNorm (fun z => ‖du z‖) 2 μ +
          eLpNorm (fun z => ‖fderiv ℝ (ψ n) z‖ - ‖du z‖) 2 μ :=
        eLpNorm_add_le (by norm_num)
      _ ≤ _ := add_le_add le_rfl (hgrad_error n)
  have hmean_le (n : ℕ) :
      eLpNorm (fun _ : E2 => ⨍ z, (ψ n z - u z) ∂μ) 2 μ ≤
        eLpNorm (fun z => ψ n z - u z) 2 μ :=
    eLpNorm_const_average_le (by norm_num) (by norm_num) ((hψ_int n).sub hu_int)
  have hmean : Tendsto
      (fun n => eLpNorm (fun _ : E2 => ⨍ z, (ψ n z - u z) ∂μ) 2 μ)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hfn
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hmean_le)
  let K := ENNReal.ofReal (A * r)
  have hbound (n : ℕ) :
      eLpNorm (fun z => u z - ⨍ y, u y ∂μ) 2 μ ≤
        K * eLpNorm (fun z => ‖du z‖) 2 μ +
          (eLpNorm (fun z => ψ n z - u z) 2 μ +
           eLpNorm (fun _ : E2 => ⨍ z, (ψ n z - u z) ∂μ) 2 μ +
           K * ∑ i : Fin 2, eLpNorm (fun z =>
             (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ) := by
    have havg : (⨍ y, (ψ n y - u y) ∂μ) =
        (⨍ y, ψ n y ∂μ) - (⨍ y, u y ∂μ) := by
      simp only [average_eq, integral_sub (hψ_int n) hu_int, smul_sub]
    calc
      _ = eLpNorm (fun z => -(ψ n z - u z) +
          (ψ n z - ⨍ y, ψ n y ∂μ) + ⨍ y, (ψ n y - u y) ∂μ) 2 μ := by
        congr 1; ext z; rw [havg]; ring
      _ ≤ (eLpNorm (fun z => -(ψ n z - u z)) 2 μ +
          eLpNorm (fun z => ψ n z - ⨍ y, ψ n y ∂μ) 2 μ) +
          eLpNorm (fun _ : E2 => ⨍ y, (ψ n y - u y) ∂μ) 2 μ := by
        calc
          _ ≤ eLpNorm (fun z => -(ψ n z - u z) +
              (ψ n z - ⨍ y, ψ n y ∂μ)) 2 μ +
              eLpNorm (fun _ : E2 => ⨍ y, (ψ n y - u y) ∂μ) 2 μ :=
            eLpNorm_add_le (by norm_num)
          _ ≤ _ := by
            exact add_le_add
              (eLpNorm_add_le (f := fun z => -(ψ n z - u z))
                (g := fun z => ψ n z - ⨍ y, ψ n y ∂μ) (p := 2) (μ := μ) (by norm_num)) le_rfl
      _ = eLpNorm (fun z => ψ n z - u z) 2 μ +
          eLpNorm (fun z => ψ n z - ⨍ y, ψ n y ∂μ) 2 μ +
          eLpNorm (fun _ : E2 => ⨍ y, (ψ n y - u y) ∂μ) 2 μ := by
        congr 1; congr 1
        exact eLpNorm_neg (fun z => ψ n z - u z) 2 μ
      _ ≤ eLpNorm (fun z => ψ n z - u z) 2 μ +
          K * (eLpNorm (fun z => ‖du z‖) 2 μ +
            ∑ i : Fin 2, eLpNorm (fun z =>
              (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ) +
          eLpNorm (fun _ : E2 => ⨍ y, (ψ n y - u y) ∂μ) 2 μ := by
        apply add_le_add _ le_rfl
        apply add_le_add le_rfl
        exact (smooth_bound (ψ n) (hψ_smooth n) x hx r hr hr1).trans
          (mul_le_mul le_rfl (hderiv_bound n) zero_le zero_le)
      _ = _ := by rw [mul_add]; abel
  have herrors : Tendsto (fun n =>
      eLpNorm (fun z => ψ n z - u z) 2 μ +
      eLpNorm (fun _ : E2 => ⨍ z, (ψ n z - u z) ∂μ) 2 μ +
      K * ∑ i : Fin 2, eLpNorm (fun z =>
        (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ)
      atTop (nhds 0) := by
    simpa using (hfn.add hmean).add
      (ENNReal.Tendsto.const_mul hgrad_sum (Or.inr ENNReal.ofReal_ne_top))
  have hnorm : eLpNorm (fun z => u z - ⨍ y, u y ∂μ) 2 μ ≤
      K * eLpNorm (fun z => ‖du z‖) 2 μ := by
    have hrhs : Tendsto (fun n =>
        K * eLpNorm (fun z => ‖du z‖) 2 μ +
          (eLpNorm (fun z => ψ n z - u z) 2 μ +
           eLpNorm (fun _ : E2 => ⨍ z, (ψ n z - u z) ∂μ) 2 μ +
           K * ∑ i : Fin 2, eLpNorm (fun z =>
             (fderiv ℝ (ψ n) z) (EuclideanSpace.single i 1) - du z i) 2 μ))
        atTop (nhds (K * eLpNorm (fun z => ‖du z‖) 2 μ + 0)) :=
      tendsto_const_nhds.add herrors
    rw [add_zero] at hrhs
    exact ge_of_tendsto hrhs (Eventually.of_forall hbound)
  have hlLp : MemLp (fun z => u z - ⨍ y, u y ∂μ) 2 μ :=
    huLp.sub (memLp_const _)
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdLp.eLpNorm_ne_top) hnorm
  have hmean_eq : (⨍ y, u y ∂μ) =
      (capVolume x r)⁻¹ * ∫ y in planarCap x r, u y :=
    setAverage_eq volume u (planarCap x r)
  rw [hmean_eq] at hlLp
  calc
    _ = (eLpNorm (fun z => u z - (capVolume x r)⁻¹ *
        ∫ y in planarCap x r, u y) 2 μ).toReal ^ 2 :=
      DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hlLp
    _ ≤ (K * eLpNorm (fun z => ‖du z‖) 2 μ).toReal ^ 2 := by
      rw [← hmean_eq]
      exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hreal
    _ = _ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hA hr.le),
        DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 hdLp]
      change (A * r * (eLpNorm (fun z => ‖du z‖) 2 μ).toReal) ^ 2 =
        A ^ 2 * r ^ 2 * (eLpNorm (fun z => ‖du z‖) 2 μ).toReal ^ 2
      ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.AnalyticLower
