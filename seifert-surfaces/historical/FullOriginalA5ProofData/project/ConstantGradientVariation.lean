import BallMeanBound

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 400000 in
theorem constant_gradient_variation_bound
    (c : V) (R : ℝ) (hR : 0 < R) (A : Mat) (P : V ≃L[ℝ] V)
    (hfactor : ∀ ξ : V, DeGiorgi.matMulE (symmetricPart A) ξ =
      P (P.toContinuousLinearMap.adjoint ξ))
    (L N D : ℝ) (hL : 0 < L) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hP : ‖P.toContinuousLinearMap‖ ≤ L) (hPi : ‖P.symm.toContinuousLinearMap‖ ≤ N)
    (hdet : |P.symm.toContinuousLinearMap.det| ≤ D)
    (h : V → ℝ) (hh : H1Witness h (Metric.ball c R))
    (hweak : WeakEquation (fun _ => A) hh) :
    ∃ a : V, ∀ᵐ x ∂volume.restrict (Metric.ball c (R / 2)),
      ‖hh.weakGrad x - a‖ ^ 2 ≤
        (3 * (12288 * DeGiorgi.CMoser 3 * (DeGiorgi.Mst : ℝ) ^ 2) *
          (2 * L) ^ 5 * N ^ 4 * L ^ 2 * D) *
          (R ^ (5 : ℕ))⁻¹ * excess hh.weakGrad c R * ‖x - c‖ ^ 2 := by
  obtain ⟨hw, hwgrad, hwl⟩ := constant_equation_to_laplace c R hR A P hfactor h hh hweak
  let Ω := pulledBackBall P c R
  let U := pulledBackBall P c (R / 2)
  have hΩ : IsOpen Ω := Metric.isOpen_ball.preimage P.continuous
  have hUΩ : U ⊆ Ω := by
    intro x hx
    exact (Metric.ball_subset_ball (show R / 2 ≤ R by linarith) :
      Metric.ball c (R / 2) ⊆ Metric.ball c R) hx
  obtain ⟨f, hae, hf, hgrad⟩ := weak_laplace_smooth_representative Ω hΩ (fun y => h (P y)) hw hwl
  have hdiv := smooth_rep_div_zero Ω hΩ _ f hw hwl hgrad
  let b := ballMean hh.weakGrad c R
  let q := P.toContinuousLinearMap.adjoint b
  haveI : IsFiniteMeasure (volume.restrict (Metric.ball c R)) :=
    isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
  have hGb : MemLp (fun x => hh.weakGrad x - b) 2 (volume.restrict (Metric.ball c R)) :=
    hh.weakGrad_memLp.sub (memLp_const b)
  have hpb : MemLp (fun y => P.toContinuousLinearMap.adjoint (hh.weakGrad (P y) - b))
      2 (volume.restrict Ω) := by
    have hm := hGb.continuousLinearMap_comp P.toContinuousLinearMap.adjoint
    have hm' : MemLp (fun x => P.toContinuousLinearMap.adjoint (hh.weakGrad x - b))
        2 (Measure.map P (volume.restrict Ω)) := by
      change MemLp _ 2 (Measure.map P (volume.restrict (P ⁻¹' Metric.ball c R)))
      rw [linear_map_restrict_volume]
      exact hm.smul_measure ENNReal.ofReal_ne_top
    exact hm'.comp_of_map P.continuous.measurable.aemeasurable
  have hshift : (fun y => classicalGradient f y - q) =ᵐ[volume.restrict Ω]
      (fun y => P.toContinuousLinearMap.adjoint (hh.weakGrad (P y) - b)) := by
    filter_upwards [hgrad] with y hy
    rw [hy, hwgrad, map_sub]
  have hfi := (hpb.ae_eq hshift.symm).norm.integrable_sq
  have hE : (∫ y in Ω, ‖classicalGradient f y - q‖ ^ 2) ≤ L ^ 2 * D * excess hh.weakGrad c R := by
    calc
      _ = ∫ y in Ω, ‖P.toContinuousLinearMap.adjoint (hh.weakGrad (P y) - b)‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hshift] with y hy
        rw [hy]
      _ ≤ L ^ 2 * |(LinearMap.det P.toLinearMap)⁻¹| * excess hh.weakGrad c R :=
        pulledBack_field_energy_le P _ _ hGb L hP
      _ ≤ _ := by
        rw [determinant_inverse_eq]
        gcongr
        exact integral_nonneg fun _ => sq_nonneg _
  let H := 12288 * DeGiorgi.CMoser 3 * (DeGiorgi.Mst : ℝ) ^ 2
  let Q := H * (R / (2 * L))⁻¹ ^ 5 * (L ^ 2 * D * excess hh.weakGrad c R)
  have hQ : 0 ≤ Q := by
    have hp := DeGiorgi.one_le_C_Moser (d := 3)
    have he : 0 ≤ excess hh.weakGrad c R := integral_nonneg fun _ => sq_nonneg _
    dsimp [Q, H]
    positivity
  have hess : ∀ y ∈ U, ∀ i : Fin 3,
      ‖fderiv ℝ (fun z => classicalGradient f z i) y‖ ^ 2 ≤ Q := by
    intro y hy i
    have hs := pulledBack_ball_contains_closedBall P c (P y) R L hR hL hP hy
    simp only [P.symm_apply_apply] at hs
    have hb := smooth_harmonic_hessian_coordinate_bound Ω hΩ f hf hdiv y
      (R / (2 * L)) (by positivity) hs q i
    have hi : (∫ z in Metric.ball y (R / (2 * L)), ‖classicalGradient f z - q‖ ^ 2) ≤
        ∫ z in Ω, ‖classicalGradient f z - q‖ ^ 2 :=
      setIntegral_mono_set hfi (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall fun z hz => hs (Metric.ball_subset_closedBall hz))
    calc
      _ ≤ H * (R / (2 * L))⁻¹ ^ 5 *
          ∫ z in Metric.ball y (R / (2 * L)), ‖classicalGradient f z - q‖ ^ 2 := by
        simpa only [inv_pow] using hb
      _ ≤ Q := by
        have hp := DeGiorgi.one_le_C_Moser (d := 3)
        exact mul_le_mul_of_nonneg_left (hi.trans hE) (by dsimp [H]; positivity)
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
  refine ⟨P.symm.toContinuousLinearMap.adjoint (classicalGradient f (P.symm c)), ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Metric.ball_subset_ball (by linarith)) hback,
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  have hcx : P.symm c ∈ U := by simpa [U, pulledBackBall] using (show (0 : ℝ) < R / 2 by positivity)
  have hxx : P.symm x ∈ U := by simpa [U, pulledBackBall] using hxB
  have hv := harmonic_gradient_difference_sq Ω U hΩ
    ((convex_ball c (R / 2)).linear_preimage P.toLinearMap) hUΩ f hf Q hQ hess
      (P.symm c) (P.symm x) hcx hxx
  have hdist : ‖P.symm x - P.symm c‖ ≤ N * ‖x - c‖ := by
    rw [← map_sub]
    exact (P.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hPi (norm_nonneg _))
  have hdiff : ‖hh.weakGrad x - P.symm.toContinuousLinearMap.adjoint (classicalGradient f (P.symm c))‖ ≤
      N * ‖classicalGradient f (P.symm x) - classicalGradient f (P.symm c)‖ := by
    calc
      _ = ‖P.symm.toContinuousLinearMap.adjoint
          (classicalGradient f (P.symm x) - classicalGradient f (P.symm c))‖ := by
        rw [map_sub, hx, inverse_adjoint_apply_adjoint]
      _ ≤ ‖P.symm.toContinuousLinearMap.adjoint‖ *
          ‖classicalGradient f (P.symm x) - classicalGradient f (P.symm c)‖ :=
        P.symm.toContinuousLinearMap.adjoint.le_opNorm _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hPi (norm_nonneg _)
  calc
    _ ≤ N ^ 2 * ‖classicalGradient f (P.symm x) - classicalGradient f (P.symm c)‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hdiff 2
    _ ≤ N ^ 2 * (3 * Q * ‖P.symm x - P.symm c‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ ≤ N ^ 2 * (3 * Q * (N ^ 2 * ‖x - c‖ ^ 2)) := by
      gcongr
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hdist 2
    _ = _ := by
      dsimp [Q, H]
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow]
      ring

end SeifertSurfaces.WeakSchauder
