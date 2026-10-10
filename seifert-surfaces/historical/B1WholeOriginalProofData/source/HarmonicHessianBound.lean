import HarmonicCaccioppoli

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem norm_fderiv_eq_classicalGradient (f : V → ℝ) (x : V) :
    ‖fderiv ℝ f x‖ = ‖classicalGradient f x‖ := by
  have he : fderiv ℝ f x = innerSL ℝ (classicalGradient f x) := by
    ext v
    change (fderiv ℝ f x) v = inner ℝ (classicalGradient f x) v
    rw [real_inner_comm]
    exact (gradient_pairing_clm _ _).symm
  rw [he]
  simp

theorem classicalGradient_sub_const (g : V → ℝ) (a : ℝ) :
    classicalGradient (fun x => g x - a) = classicalGradient g := by
  funext x
  unfold classicalGradient
  rw [fderiv_sub_const]

theorem smooth_harmonic_hessian_coordinate_bound
    (Ω : Set V) (hΩ : IsOpen Ω) (f : V → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hd : DeGiorgi.HasWeakDiv (fun _ => 0) (classicalGradient f) Ω)
    (c : V) (R : ℝ) (hR : 0 < R) (hsub : Metric.closedBall c R ⊆ Ω)
    (q : V) (i : Fin 3) :
    ‖fderiv ℝ (fun x => classicalGradient f x i) c‖ ^ 2 ≤
      (12288 * DeGiorgi.CMoser 3 * (DeGiorgi.Mst : ℝ) ^ 2) * (R ^ (5 : ℕ))⁻¹ *
        ∫ y in Metric.ball c R, ‖classicalGradient f y - q‖ ^ 2 := by
  let U := Metric.ball c R
  let g : V → ℝ := fun x => classicalGradient f x i
  have hcl : closure U ⊆ Ω := Metric.closure_ball_subset_closedBall.trans hsub
  have hco : IsCompact (closure U) := (isCompact_closedBall c R).of_isClosed_subset
    isClosed_closure Metric.closure_ball_subset_closedBall
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  obtain ⟨wg, hwgg, hgw⟩ := smooth_partial_identity_equation Ω U hΩ Metric.isOpen_ball hco hcl f hf
    (div_zero_restrict Ω U (subset_closure.trans hcl) _ hd) i
  let z : V → ℝ := fun x => g x - q i
  have hz : ContDiffOn ℝ (⊤ : ℕ∞) z Ω := hg.sub contDiffOn_const
  let wz := smooth_witness_on_precompact Ω U hΩ Metric.isOpen_ball hco hcl z hz
  have hzg : ∀ x, wz.weakGrad x = wg.weakGrad x := by
    intro x
    change classicalGradient z x = _
    rw [hwgg, classicalGradient_sub_const]
    rfl
  have hzw : WeakEquation (fun _ => (1 : Mat)) wz := by
    intro φ hφ hφw
    simpa only [hzg] using hgw φ hφ hφw
  have henergy := identity_ball_caccioppoli c R hR z wz (fun _ => rfl)
    (hz.mono (subset_closure.trans hcl)) hzw
  have hdg := smooth_rep_div_zero U Metric.isOpen_ball z z wz hzw EventuallyEq.rfl
  have hcenter := smooth_harmonic_gradient_center_sq_bound U Metric.isOpen_ball z
    (hz.mono (subset_closure.trans hcl)) hdg c (R / 2) (by positivity)
    (Metric.closedBall_subset_ball (by linarith))
  have hiq : MemLp (fun y => classicalGradient f y - q) 2 (volume.restrict U) := by
    haveI : IsFiniteMeasure (volume.restrict U) :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    exact (smooth_witness_on_precompact Ω U hΩ Metric.isOpen_ball hco hcl f hf).weakGrad_memLp.sub
      (memLp_const q)
  have hzint : IntegrableOn (fun y => z y ^ 2) U := wz.memLp.integrable_sq
  have hi := integral_mono hzint hiq.norm.integrable_sq (fun y => by
    have he := PiLp.norm_apply_le (classicalGradient f y - q) i
    simpa only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, z, g] using pow_le_pow_left₀ (norm_nonneg _) he 2)
  have hp := DeGiorgi.one_le_C_Moser (d := 3)
  rw [norm_fderiv_eq_classicalGradient]
  have heq : classicalGradient z = classicalGradient g := classicalGradient_sub_const g (q i)

  calc
    _ ≤ (24 * DeGiorgi.CMoser 3) * ((R / 2) ^ 3)⁻¹ * energy wz.weakGrad c (R / 2) := by
      change ‖classicalGradient g c‖ ^ 2 ≤ _ * energy (classicalGradient z) c (R / 2)
      rw [← heq]
      exact hcenter
    _ ≤ (24 * DeGiorgi.CMoser 3) * ((R / 2) ^ 3)⁻¹ *
        ((64 * (DeGiorgi.Mst : ℝ) ^ 2) * (R ^ 2)⁻¹ * ∫ y in U, z y ^ 2) := by
      gcongr
    _ ≤ (24 * DeGiorgi.CMoser 3) * ((R / 2) ^ 3)⁻¹ *
        ((64 * (DeGiorgi.Mst : ℝ) ^ 2) * (R ^ 2)⁻¹ * ∫ y in U, ‖classicalGradient f y - q‖ ^ 2) := by
      gcongr
    _ = _ := by dsimp [U]; field_simp; ring

end SeifertSurfaces.WeakSchauder
