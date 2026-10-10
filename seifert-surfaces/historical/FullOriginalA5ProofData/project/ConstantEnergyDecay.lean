import LinearEnergyBounds

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem constant_gradient_pointwise_bound
    (c : V) (R : ℝ) (hR : 0 < R) (A : Mat) (P : V ≃L[ℝ] V)
    (hfactor : ∀ ξ : V, DeGiorgi.matMulE (symmetricPart A) ξ =
      P (P.toContinuousLinearMap.adjoint ξ))
    (L N D : ℝ) (hL : 0 < L) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hP : ‖P.toContinuousLinearMap‖ ≤ L) (hPi : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    (hdet : |P.symm.toContinuousLinearMap.det| ≤ D)
    (h : V → ℝ) (hh : H1Witness h (Metric.ball c R))
    (hweak : WeakEquation (fun _ => A) hh) :
    ∀ᵐ x ∂volume.restrict (Metric.ball c (R / 2)),
      ‖hh.weakGrad x‖ ^ 2 ≤
        (24 * DeGiorgi.CMoser 3 * (2 * L) ^ 3 * N ^ 2 * L ^ 2 * D) *
          (R ^ (3 : ℕ))⁻¹ * energy hh.weakGrad c R := by
  obtain ⟨hw, hwgrad, hwl⟩ := constant_equation_to_laplace c R hR A P hfactor h hh hweak
  let Ω := pulledBackBall P c R
  have hΩ : IsOpen Ω := Metric.isOpen_ball.preimage P.continuous
  obtain ⟨f, hae, hf, hgrad⟩ := weak_laplace_smooth_representative Ω hΩ (fun y => h (P y)) hw hwl
  have hdiv := smooth_rep_div_zero Ω hΩ _ f hw hwl hgrad
  have hfp : MemLp (classicalGradient f) 2 (volume.restrict Ω) := hw.weakGrad_memLp.ae_eq hgrad.symm
  have hfi := hfp.norm.integrable_sq
  have hE : (∫ y in Ω, ‖classicalGradient f y‖ ^ 2) ≤ L ^ 2 * D * energy hh.weakGrad c R := by
    calc
      _ = ∫ y in Ω, ‖P.toContinuousLinearMap.adjoint (hh.weakGrad (P y))‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hgrad] with y hy
        rw [hy, hwgrad]
      _ ≤ L ^ 2 * |(LinearMap.det P.toLinearMap)⁻¹| * energy hh.weakGrad c R :=
        pulledBack_gradient_energy_le P _ h hh L hL.le hP
      _ ≤ _ := by
        rw [determinant_inverse_eq]
        gcongr
        exact integral_nonneg fun _ => sq_nonneg _
  have hnorm (x : V) (hx : x ∈ Metric.ball c (R / 2)) :
      ‖classicalGradient f (P.symm x)‖ ^ 2 ≤
        (24 * DeGiorgi.CMoser 3) * (R / (2 * L))⁻¹ ^ 3 *
          (L ^ 2 * D * energy hh.weakGrad c R) := by
    have hsub := pulledBack_ball_contains_closedBall P c x R L hR hL hP hx
    have hb := smooth_harmonic_gradient_center_sq_bound Ω hΩ f hf hdiv
      (P.symm x) (R / (2 * L)) (by positivity) hsub
    have hi : energy (classicalGradient f) (P.symm x) (R / (2 * L)) ≤
        ∫ y in Ω, ‖classicalGradient f y‖ ^ 2 :=
      setIntegral_mono_set hfi (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun y hy => hsub (Metric.ball_subset_closedBall hy))
    calc
      _ ≤ (24 * DeGiorgi.CMoser 3) * (R / (2 * L))⁻¹ ^ 3 *
          energy (classicalGradient f) (P.symm x) (R / (2 * L)) := by simpa only [inv_pow] using hb
      _ ≤ _ := by
        have hp := DeGiorgi.one_le_C_Moser (d := 3)
        exact mul_le_mul_of_nonneg_left (hi.trans hE) (by positivity)
  have hback : (fun x => classicalGradient f (P.symm x)) =ᵐ[volume.restrict (Metric.ball c R)]
      (fun x => P.toContinuousLinearMap.adjoint (hh.weakGrad x)) := by
    have he : classicalGradient f =ᵐ[volume.restrict Ω]
        (fun y => P.toContinuousLinearMap.adjoint (hh.weakGrad (P y))) :=
      hgrad.trans (Eventually.of_forall hwgrad)
    have hm : ∀ᵐ x ∂volume.restrict (P.symm ⁻¹' Ω),
        classicalGradient f (P.symm x) = P.toContinuousLinearMap.adjoint (hh.weakGrad (P (P.symm x))) := by
      have hs := Measure.ae_smul_measure he (ENNReal.ofReal |(LinearMap.det P.symm.toLinearMap)⁻¹|)
      rw [← linear_map_restrict_volume] at hs
      exact (P.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.ae_map_iff
        (p := fun y => classicalGradient f y = P.toContinuousLinearMap.adjoint (hh.weakGrad (P y)))).mp hs
    have hset : P.symm ⁻¹' Ω = Metric.ball c R := by
      ext x
      simp [Ω, pulledBackBall]
    rw [hset] at hm
    simp only [P.apply_symm_apply] at hm
    exact hm
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (by linarith)) hback,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  have hgi : ‖hh.weakGrad x‖ ≤ N * ‖classicalGradient f (P.symm x)‖ := by
    calc
      _ = ‖P.symm.toContinuousLinearMap.adjoint (classicalGradient f (P.symm x))‖ := by
        rw [hx, inverse_adjoint_apply_adjoint]
      _ ≤ ‖P.symm.toContinuousLinearMap.adjoint‖ * ‖classicalGradient f (P.symm x)‖ :=
        P.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ N * ‖classicalGradient f (P.symm x)‖ := by simpa using mul_le_mul_of_nonneg_right hPi (norm_nonneg _)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hgi 2
  rw [mul_pow] at hs
  calc
    _ ≤ N ^ 2 * ‖classicalGradient f (P.symm x)‖ ^ 2 := hs
    _ ≤ N ^ 2 * ((24 * DeGiorgi.CMoser 3) * (R / (2 * L))⁻¹ ^ 3 *
        (L ^ 2 * D * energy hh.weakGrad c R)) :=
      mul_le_mul_of_nonneg_left (hnorm x hxB) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow]; ring

theorem real_volume_ball_three (c : V) (r : ℝ) (hr : 0 < r) :
    (volume (Metric.ball c r)).toReal =
      r ^ (3 : ℕ) * (volume (Metric.ball (0 : V) 1)).toReal := by
  rw [Measure.addHaar_ball_of_pos volume c hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]
  simp

/-- R4a: interior gradient-energy decay with all constants independent of
radius, center, matrix and solution, once ellipticity scales are fixed. -/
theorem constant_gradient_energy_decay (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (center : V) (R : ℝ), 0 < R →
      ∀ (A : Mat), CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ →
      ∀ (h : V → ℝ) (hh : H1Witness h (Metric.ball center R)),
      WeakEquation (fun _ => A) hh →
      ∀ r : ℝ, 0 < r → r ≤ R / 2 →
        energy hh.weakGrad center r ≤ C * (r / R) ^ (3 : ℕ) * energy hh.weakGrad center R := by
  let L := Real.sqrt Λ
  let N := (Real.sqrt κ)⁻¹
  have hL : 0 < L := Real.sqrt_pos.mpr (hκ.trans_le hΛ)
  have hN : 0 < N := inv_pos.mpr (Real.sqrt_pos.mpr hκ)
  obtain ⟨D, hD, hdet⟩ := exists_det_bound_on_norm_ball N
  let K := 24 * DeGiorgi.CMoser 3 * (2 * L) ^ 3 * N ^ 2 * L ^ 2 * D
  let V₁ := (volume (Metric.ball (0 : V) 1)).toReal
  have hK : 0 ≤ K := by
    have hm := DeGiorgi.one_le_C_Moser (d := 3)
    dsimp [K]
    positivity
  have hV₁ : 0 ≤ V₁ := ENNReal.toReal_nonneg
  refine ⟨K * V₁ + 1, by positivity, ?_⟩
  intro c R hR A hA h hh hw r hr hrR
  obtain ⟨P, hfactor, hP, hPi⟩ := constant_linear_factor c R κ Λ hR hκ hΛ A hA
  have hpoint := constant_gradient_pointwise_bound c R hR A P hfactor L N D hL hN.le hD.le
    hP hPi (hdet _ hPi) h hh hw
  have hsub : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball (by linarith)
  have hsub' : Metric.ball c r ⊆ Metric.ball c (R / 2) := Metric.ball_subset_ball hrR
  have hiR : IntegrableOn (fun x => ‖hh.weakGrad x‖ ^ 2) (Metric.ball c R) := hh.weakGrad_memLp.norm.integrable_sq
  have hi := hiR.mono_set hsub
  have hE : 0 ≤ energy hh.weakGrad c R := integral_nonneg fun _ => sq_nonneg _
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c r)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have he := integral_mono_ae hi
    (integrable_const (K * (R ^ (3 : ℕ))⁻¹ * energy hh.weakGrad c R))
    (ae_restrict_of_ae_restrict_of_subset hsub' hpoint)
  change energy hh.weakGrad c r ≤ ∫ x in Metric.ball c r, K * (R ^ 3)⁻¹ * energy hh.weakGrad c R at he
  rw [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    real_volume_ball_three c r hr] at he
  calc
    _ ≤ (r ^ 3 * V₁) * (K * (R ^ 3)⁻¹ * energy hh.weakGrad c R) := he
    _ = K * V₁ * (r / R) ^ 3 * energy hh.weakGrad c R := by
      rw [div_pow, div_eq_mul_inv]
      ring
    _ ≤ (K * V₁ + 1) * (r / R) ^ 3 * energy hh.weakGrad c R := by
      gcongr
      linarith

end SeifertSurfaces.WeakSchauder
