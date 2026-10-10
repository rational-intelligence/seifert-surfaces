import HarmonicDerivativeEquation

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

/-- Dimension-three pointwise gradient control from the gradient energy on a
compactly contained ball. The constant is independent of the function and ball. -/
theorem smooth_harmonic_gradient_center_sq_bound
    (Ω : Set V) (hΩ : IsOpen Ω) (f : V → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hd : DeGiorgi.HasWeakDiv (fun _ => 0) (classicalGradient f) Ω)
    (c : V) (R : ℝ) (hR : 0 < R) (hsub : Metric.closedBall c R ⊆ Ω) :
    ‖classicalGradient f c‖ ^ 2 ≤
      (24 * DeGiorgi.CMoser 3) * (R ^ (3 : ℕ))⁻¹ * energy (classicalGradient f) c R := by
  have hclosure : closure (Metric.ball c R) ⊆ Ω :=
    Metric.closure_ball_subset_closedBall.trans hsub
  have hcomp : IsCompact (closure (Metric.ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure Metric.closure_ball_subset_closedBall
  let wf := smooth_witness_on_precompact Ω (Metric.ball c R) hΩ Metric.isOpen_ball
    hcomp hclosure f hf
  have hi : IntegrableOn (fun y => ‖classicalGradient f y‖ ^ 2) (Metric.ball c R) :=
    wf.weakGrad_memLp.norm.integrable_sq
  have hlocal := div_zero_restrict Ω (Metric.ball c R) (Metric.ball_subset_closedBall.trans hsub)
    (classicalGradient f) hd
  have hb (i : Fin 3) : |classicalGradient f c i| ^ 2 ≤
      (8 * DeGiorgi.CMoser 3) * (R ^ (3 : ℕ))⁻¹ * energy (classicalGradient f) c R := by
    let g : V → ℝ := fun x => classicalGradient f x i
    obtain ⟨wg, -, hgw⟩ := smooth_partial_identity_equation Ω (Metric.ball c R) hΩ Metric.isOpen_ball
      hcomp hclosure f hf hlocal i
    have hgc : ContinuousOn g (Metric.ball c R) :=
      ((hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const).mono
        (Metric.ball_subset_closedBall.trans hsub)
    have hb := identity_solution_sq_bound c R hR g wg hgc
      (identity_solution_of_weak _ Metric.isOpen_ball g wg hgw) c
      (Metric.mem_ball_self (by positivity))
    have hgi : IntegrableOn (fun y => |g y| ^ 2) (Metric.ball c R) := by
      simpa only [IntegrableOn, sq_abs, g, classicalGradient] using wg.memLp.integrable_sq
    have him := integral_mono hgi hi (fun y => by
      exact pow_le_pow_left₀ (abs_nonneg _) (PiLp.norm_apply_le (classicalGradient f y) i) 2)
    have hc : 0 ≤ 8 * DeGiorgi.CMoser 3 * (R ^ (3 : ℕ))⁻¹ := by
      have hp := DeGiorgi.one_le_C_Moser (d := 3)
      positivity
    exact hb.trans (mul_le_mul_of_nonneg_left him hc)
  rw [PiLp.norm_sq_eq_of_L2]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  norm_num [Real.norm_eq_abs, Finset.card_fin] at hsum ⊢
  nlinarith only [hsum]

end SeifertSurfaces.WeakSchauder
