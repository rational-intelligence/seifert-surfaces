import ConstantEnergyDecay

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem identity_cutoff_energy (Ω : Set V) (hΩ : IsOpen Ω)
    (u η : V → ℝ) (hu : H1Witness u Ω)
    (hgrad : ∀ x, hu.weakGrad x = classicalGradient u x)
    (huS : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (hw : WeakEquation (fun _ => (1 : Mat)) hu)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) (hηΩ : tsupport η ⊆ Ω)
    (hηb : ∀ x, |η x| ≤ 1) (B : ℝ) (hB : 0 ≤ B) (hD : ∀ x, ‖fderiv ℝ η x‖ ≤ B) :
    (∫ x in Ω, η x ^ 2 * ‖hu.weakGrad x‖ ^ 2) ≤ 4 * B ^ 2 * ∫ x in Ω, u x ^ 2 := by
  let φ : V → ℝ := fun x => η x ^ 2 * u x
  have hφeq : φ = fun x => η x * (η x * u x) := by funext x; dsimp [φ]; ring
  have hφΩ : tsupport φ ⊆ Ω := by
    rw [hφeq]
    exact tsupport_mul_subset_left.trans hηΩ
  have hφc : HasCompactSupport φ := by rw [hφeq]; exact hηc.mul_right
  have hφS : ContDiff ℝ (⊤ : ℕ∞) φ :=
    ((hη.contDiffOn.pow 2).mul huS).contDiff_of_tsupport_subset hΩ hφΩ
  have heq := constant_weak_smooth_integral 1 Ω hΩ u hu hw φ hφS hφc hφΩ
  have hone (v : V) : DeGiorgi.matMulE (1 : Mat) v = v := by ext i; simp [DeGiorgi.matMulE]
  simp only [hone] at heq
  have hquad (x : V) (hx : x ∈ Ω) :
      η x ^ 2 * ‖hu.weakGrad x‖ ^ 2 ≤
        2 * (fderiv ℝ φ x) (hu.weakGrad x) + 4 * B ^ 2 * u x ^ 2 := by
    have huD := ((huS x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hηD := hη.differentiable (by simp) x
    have hφD := (hηD.hasFDerivAt.pow 2).mul huD.hasFDerivAt
    have hdu : (fderiv ℝ u x) (hu.weakGrad x) = ‖hu.weakGrad x‖ ^ 2 := by
      rw [← gradient_pairing_clm]
      change inner ℝ (hu.weakGrad x) (classicalGradient u x) = _
      rw [← hgrad, real_inner_self_eq_norm_sq]
    have hφeq : (fderiv ℝ φ x) (hu.weakGrad x) =
        η x ^ 2 * ‖hu.weakGrad x‖ ^ 2 +
          2 * η x * u x * (fderiv ℝ η x) (hu.weakGrad x) := by
      rw [show fderiv ℝ φ x = _ from hφD.fderiv]
      simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hdu]
      ring
    have hb := (fderiv ℝ η x).le_opNorm (hu.weakGrad x)
    have hdabs : |(fderiv ℝ η x) (hu.weakGrad x)| ≤ B * ‖hu.weakGrad x‖ :=
      hb.trans (mul_le_mul_of_nonneg_right (hD x) (norm_nonneg _))
    have hcross := neg_abs_le (2 * η x * u x * (fderiv ℝ η x) (hu.weakGrad x))
    have hcrossb : |2 * η x * u x * (fderiv ℝ η x) (hu.weakGrad x)| ≤
        2 * |η x| * |u x| * (B * ‖hu.weakGrad x‖) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      gcongr
    rw [hφeq]
    nlinarith [sq_nonneg (|η x| * ‖hu.weakGrad x‖ - 2 * B * |u x|),
      sq_abs (η x), sq_abs (u x)]
  have hE : IntegrableOn (fun x => η x ^ 2 * ‖hu.weakGrad x‖ ^ 2) Ω := by
    apply hu.weakGrad_memLp.norm.integrable_sq.mono'
      ((hη.continuous.aestronglyMeasurable.pow 2).mul (hu.weakGrad_memLp.aestronglyMeasurable.norm.pow 2))
    filter_upwards [] with x
    change ‖η x ^ 2 * ‖hu.weakGrad x‖ ^ 2‖ ≤ ‖hu.weakGrad x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hηsq : η x ^ 2 ≤ 1 := by nlinarith [hηb x, sq_abs (η x), abs_nonneg (η x)]
    nlinarith [sq_nonneg ‖hu.weakGrad x‖]
  have hI : IntegrableOn (fun x => (fderiv ℝ φ x) (hu.weakGrad x)) Ω := by
    let w : H1Witness φ Ω := DeGiorgi.MemW1pWitness.restrict hΩ (subset_univ Ω)
      (DeGiorgi.MemW1pWitness.ofContDiffHasCompactSupport (p := 2) hφS hφc)
    have he := constant_pairing_integrable (1 : Mat) Ω _ _ hu.weakGrad_component_memLp w.weakGrad_component_memLp
    change IntegrableOn (fun x => inner ℝ (DeGiorgi.matMulE (1 : Mat) (hu.weakGrad x))
      (WithLp.toLp 2 (fun i => (fderiv ℝ φ x) (EuclideanSpace.single i 1)))) Ω at he
    simpa only [hone, gradient_pairing_clm] using he
  have hint := integral_mono_ae hE ((hI.const_mul 2).add (hu.memLp.integrable_sq.const_mul (4 * B ^ 2)))
    ((ae_restrict_mem hΩ.measurableSet).mono fun x hx => hquad x hx)
  simp only [Pi.add_apply] at hint
  rw [integral_add (hI.const_mul 2) (hu.memLp.integrable_sq.const_mul (4 * B ^ 2)),
    integral_const_mul, integral_const_mul, heq, mul_zero, zero_add] at hint
  exact hint

theorem identity_ball_caccioppoli (c : V) (R : ℝ) (hR : 0 < R)
    (u : V → ℝ) (hu : H1Witness u (Metric.ball c R))
    (hgrad : ∀ x, hu.weakGrad x = classicalGradient u x)
    (huS : ContDiffOn ℝ (⊤ : ℕ∞) u (Metric.ball c R))
    (hw : WeakEquation (fun _ => (1 : Mat)) hu) :
    energy hu.weakGrad c (R / 2) ≤
      (64 * (DeGiorgi.Mst : ℝ) ^ 2) * (R ^ (2 : ℕ))⁻¹ *
        ∫ x in Metric.ball c R, u x ^ 2 := by
  obtain ⟨η, -⟩ := DeGiorgi.Cutoff.exists (d := 3) c
    (r := R / 2) (R := 3 * R / 4) (by positivity) (by linarith)
  have hsupp : tsupport η.toFun ⊆ Metric.ball c R :=
    η.support_subset.trans (Metric.closedBall_subset_ball (by linarith))
  have hηc : HasCompactSupport η.toFun :=
    (isCompact_closedBall c (3 * R / 4)).of_isClosed_subset (isClosed_tsupport _) η.support_subset
  have hηb (x : V) : |η.toFun x| ≤ 1 := by
    rw [abs_of_nonneg (η.nonneg x)]
    exact η.le_one x
  have hB : 0 ≤ 4 * (DeGiorgi.Mst : ℝ) / R := by positivity
  have hD (x : V) : ‖fderiv ℝ η.toFun x‖ ≤ 4 * (DeGiorgi.Mst : ℝ) / R := by
    have hb := η.grad_bound x
    convert hb using 1 <;> field_simp <;> ring
  have he := identity_cutoff_energy _ Metric.isOpen_ball u η.toFun hu hgrad huS hw
    η.smooth hηc hsupp hηb _ hB hD
  have hE : IntegrableOn (fun x => η.toFun x ^ 2 * ‖hu.weakGrad x‖ ^ 2) (Metric.ball c R) := by
    apply hu.weakGrad_memLp.norm.integrable_sq.mono'
      ((η.smooth.continuous.aestronglyMeasurable.pow 2).mul (hu.weakGrad_memLp.aestronglyMeasurable.norm.pow 2))
    filter_upwards [] with x
    change ‖η.toFun x ^ 2 * ‖hu.weakGrad x‖ ^ 2‖ ≤ ‖hu.weakGrad x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : η.toFun x ^ 2 ≤ 1 := by nlinarith [η.nonneg x, η.le_one x]
    exact (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)).trans_eq (one_mul _)
  calc
    _ = ∫ x in Metric.ball c (R / 2), η.toFun x ^ 2 * ‖hu.weakGrad x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      simp only [η.eq_one x hx, one_pow, one_mul]
    _ ≤ ∫ x in Metric.ball c R, η.toFun x ^ 2 * ‖hu.weakGrad x‖ ^ 2 :=
      setIntegral_mono_set hE (Eventually.of_forall fun _ => by positivity)
        (Eventually.of_forall fun _ hx => Metric.ball_subset_ball (by linarith) hx)
    _ ≤ 4 * (4 * (DeGiorgi.Mst : ℝ) / R) ^ 2 * ∫ x in Metric.ball c R, u x ^ 2 := he
    _ = _ := by simp only [div_pow, div_eq_mul_inv]; ring

end SeifertSurfaces.WeakSchauder
