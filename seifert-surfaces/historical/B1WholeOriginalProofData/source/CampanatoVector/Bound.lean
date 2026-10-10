import CampanatoVector.Local

noncomputable section
open Set MeasureTheory Metric Filter CampanatoVector
open scoped NNReal ENNReal Topology
namespace SeifertSurfaces.WeakSchauder

lemma norm_ballMean_le {G : V → V} {center x : V} {R r : ℝ}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hsub : ball x r ⊆ ball center R) :
    ‖ballMean G x r‖ ≤
      (volume.real (ball x r))⁻¹ * Real.sqrt (volume.real (ball x r)) *
        Real.sqrt (energy G center R) := by
  have hmem := hG.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hL2 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := fun y => ‖G y‖) (g := fun _ => (1 : ℝ))
    (μ := volume.restrict (ball x r)) (Eventually.of_forall (fun y => norm_nonneg _))
    (Eventually.of_forall (fun _ => zero_le_one))
    (by simpa using hmem.norm) (by simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : V => (1 : ℝ)) 2 (volume.restrict (ball x r))))
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at hL2
  have hsquare : (∫ y in ball x r, ‖G y‖ ^ 2) ≤ energy G center R :=
    setIntegral_mono_set hG.norm.integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _)) hsub.eventuallyLE
  have hnorm : ‖∫ y in ball x r, G y‖ ≤
      Real.sqrt (energy G center R) * Real.sqrt (volume.real (ball x r)) :=
    (norm_integral_le_integral_norm _).trans
      (hL2.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsquare) (Real.sqrt_nonneg _)))
  calc ‖ballMean G x r‖ = (volume.real (ball x r))⁻¹ * ‖∫ y in ball x r, G y‖ := by
        simp [ballMean, norm_smul, measureReal_def]
    _ ≤ (volume.real (ball x r))⁻¹ *
        (Real.sqrt (energy G center R) * Real.sqrt (volume.real (ball x r))) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (measureReal_nonneg))
    _ = _ := by ring

lemma limit_sup_bound {R : ℝ} (hR : 0 < R) {β : NNReal} (hβ : 0 < β)
    {M : ℝ} (hM : 0 ≤ M) {G : V → V} {center : V}
    (hG : MemLp G 2 (volume.restrict (ball center R)))
    (hcamp : CampanatoBound G (ball center (3 * R / 4)) (R / 8) β M)
    {x : V} (hx : x ∈ ball center (R / 2)) :
    ‖campanatoLimit G x‖ ≤
      (((R / 16) ^ 3 * unitBallVolume 3)⁻¹ * Real.sqrt ((R / 16) ^ 3 * unitBallVolume 3)) *
        Real.sqrt (energy G center R) +
      (campanatoLimitConst 3 β * (R / 16) ^ (β : ℝ)) * Real.sqrt M := by
  have hr : 0 < R / 16 := by linarith
  have hsmall : ball x (R / 16) ⊆ ball x (R / 8) := ball_subset_ball (by linarith)
  have hdist := abs_ballAverage_sub_campanatoLimit_le (by exact_mod_cast hβ)
    (Real.sqrt_nonneg M) isOpen_ball
    (hG.mono_measure (Measure.restrict_mono (local_ball_subset hR hx) le_rfl))
    (local_campanato hR hM hx hcamp) (mem_ball_self (by linarith)) hr hsmall
  have hmean := norm_ballMean_le hG (hsmall.trans (local_ball_subset hR hx))
  rw [ballMean_eq_ballAverage, measureReal_ball x hr] at hmean
  calc ‖campanatoLimit G x‖
      ≤ ‖ballAverage G x (R / 16)‖ + ‖ballAverage G x (R / 16) - campanatoLimit G x‖ := by
        have h := norm_sub_le_norm_sub_add_norm_sub (0 : V) (ballAverage G x (R / 16))
          (campanatoLimit G x)
        simpa only [zero_sub, norm_neg] using h
    _ ≤ _ := by nlinarith

end SeifertSurfaces.WeakSchauder
