import NativeBoundaryNormalFluxHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Quantitative normal-gradient recovery along the segment between the
actual jets. No mixed jet outside the original domain is introduced. -/
theorem native_normal_gradient_from_flux_difference
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (j₀ j₁ : Jet) (κ M : ℝ) (hκ : 0 < κ) (hM : 0 ≤ M)
    (hsegments : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • j₀ + t • j₁ ∈ J)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1,
      let j := (1 - t) • j₀ + t • j₁
      ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
        κ ≤ (fluxDp Q j (coordinateVector 2 0)) 0) :
    κ * |j₁.2.2 0 - j₀.2.2 0| ≤
      |Q.flux j₁ 0 - Q.flux j₀ 0| +
        M * (‖j₁.1 - j₀.1‖ + |j₁.2.1 - j₀.2.1| + |j₁.2.2 1 - j₀.2.2 1|) := by
  let s : ℝ → Jet := fun t => (1 - t) • j₀ + t • j₁
  let dp : E2 := j₁.2.2 - j₀.2.2
  let dx : E2 := j₁.1 - j₀.1
  let dz : ℝ := j₁.2.1 - j₀.2.1
  let a : ℝ → ℝ := fun t => fluxDp Q (s t) (coordinateVector 2 0) 0
  let b : ℝ → ℝ := fun t => fluxDx Q (s t) dx 0 +
    dz * fluxDz Q (s t) 0 + dp 1 * fluxDp Q (s t) (coordinateVector 2 1) 0
  have hs : Continuous s := by dsimp [s]; fun_prop
  have ha : ContinuousOn a (Icc (0 : ℝ) 1) :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn
      (((QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp
        hs.continuousOn hsegments).clm_apply continuousOn_const)
  have hbcont : ContinuousOn b (Icc (0 : ℝ) 1) := by
    have hdx := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn
      (((QuotientHelpers.x_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp
        hs.continuousOn hsegments).clm_apply (continuousOn_const (c := dx)))
    have hdz := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn
      ((QuotientHelpers.z_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp hs.continuousOn hsegments)
    have hdp := (EuclideanSpace.proj (0 : Fin 2)).continuous.comp_continuousOn
      (((QuotientHelpers.p_partial_continuousOn J hJ Q.flux Q.flux_smooth).comp
        hs.continuousOn hsegments).clm_apply (continuousOn_const (c := coordinateVector 2 1)))
    exact (hdx.add (continuousOn_const.mul hdz)).add (continuousOn_const.mul hdp)
  have hai : IntegrableOn a (Icc (0 : ℝ) 1) := ha.integrableOn_compact isCompact_Icc
  have hbi : IntegrableOn b (Icc (0 : ℝ) 1) := hbcont.integrableOn_compact isCompact_Icc
  have hAi : κ ≤ ∫ t in Icc (0 : ℝ) 1, a t := by
    rw [← QuotientHelpers.integral_unit_constant κ]
    apply setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top) hai measurableSet_Icc
    intro t ht
    exact (hb t ht).2.2.2
  have hAi0 : 0 ≤ ∫ t in Icc (0 : ℝ) 1, a t := hκ.le.trans hAi
  have hbpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |b t| ≤ M * (‖dx‖ + |dz| + |dp 1|) := by
    have he (L : E2 →L[ℝ] E2) (hL : ‖L‖ ≤ M) (v : E2) : |L v 0| ≤ M * ‖v‖ :=
      (PiLp.norm_apply_le _ 0 (p := 2)).trans
        ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))
    have hz : |fluxDz Q (s t) 0| ≤ M :=
      (PiLp.norm_apply_le _ 0 (p := 2)).trans (hb t ht).2.1
    have hp : |fluxDp Q (s t) (coordinateVector 2 1) 0| ≤ M := by
      simpa [coordinateVector, PiLp.norm_single] using he _ (hb t ht).2.2.1 (coordinateVector 2 1)
    change |_ + _ + _| ≤ _
    calc
      _ ≤ |fluxDx Q (s t) dx 0| + |dz * fluxDz Q (s t) 0| +
          |dp 1 * fluxDp Q (s t) (coordinateVector 2 1) 0| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M * ‖dx‖ + |dz| * M + |dp 1| * M := by
        rw [abs_mul, abs_mul]
        exact add_le_add (add_le_add (he _ (hb t ht).1 dx)
          (mul_le_mul_of_nonneg_left hz (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
      _ = _ := by ring
  have hBi : |∫ t in Icc (0 : ℝ) 1, b t| ≤ M * (‖dx‖ + |dz| + |dp 1|) := by
    simpa [measureReal_def] using norm_setIntegral_le_of_norm_le_const
      (μ := volume) (s := Icc (0 : ℝ) 1) (f := b) isCompact_Icc.measure_lt_top
        (fun t ht => by simpa only [Real.norm_eq_abs] using hbpoint t ht)
  have hFTC := QuotientHelpers.segment_FTC J hJ Q.flux Q.flux_smooth j₀ j₁ hsegments
  have hiF : IntegrableOn (fun t => fderiv ℝ Q.flux (s t) (j₁ - j₀)) (Icc (0 : ℝ) 1) :=
    (((Q.flux_smooth.continuousOn_fderiv_of_isOpen hJ (by simp)).comp
      hs.continuousOn hsegments).clm_apply continuousOn_const).integrableOn_compact isCompact_Icc
  have hproj := congrArg (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) hFTC
  rw [← (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).integral_comp_comm hiF] at hproj
  have hD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (fderiv ℝ Q.flux (s t) (j₁ - j₀)) 0 = a t * dp 0 + b t := by
    have hd := (Q.flux_smooth.contDiffAt (hJ.mem_nhds (hsegments t ht))).differentiableAt (by simp)
    have hdp : dp = dp 0 • coordinateVector 2 0 + dp 1 • coordinateVector 2 1 := by
      ext i
      fin_cases i <;> simp [coordinateVector]
    rw [QuotientHelpers.fderiv_split Q.flux (s t) (j₁ - j₀) hd]
    change (fluxDp Q (s t) dp + dz • fluxDz Q (s t) + fluxDx Q (s t) dx) 0 = _
    rw [hdp]
    simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, a, b]
    norm_num [coordinateVector]
    ring
  have hEq : Q.flux j₁ 0 - Q.flux j₀ 0 =
      (∫ t in Icc (0 : ℝ) 1, a t) * dp 0 + ∫ t in Icc (0 : ℝ) 1, b t := by
    have hi := setIntegral_congr_fun (μ := volume) measurableSet_Icc hD
    rw [integral_add (hai.mul_const _) hbi, integral_mul_const] at hi
    simpa only [map_sub, PiLp.sub_apply, PiLp.proj_apply, Function.comp_def, s] using hproj.trans hi
  calc
    _ = κ * |dp 0| := by simp only [dp, PiLp.sub_apply]
    _ ≤ (∫ t in Icc (0 : ℝ) 1, a t) * |dp 0| := mul_le_mul_of_nonneg_right hAi (abs_nonneg _)
    _ = |(∫ t in Icc (0 : ℝ) 1, a t) * dp 0| := by rw [abs_mul, abs_of_nonneg hAi0]
    _ = |(Q.flux j₁ 0 - Q.flux j₀ 0) - ∫ t in Icc (0 : ℝ) 1, b t| := by rw [hEq]; ring_nf
    _ ≤ |Q.flux j₁ 0 - Q.flux j₀ 0| + |∫ t in Icc (0 : ℝ) 1, b t| := abs_sub _ _
    _ ≤ _ := add_le_add le_rfl hBi

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
