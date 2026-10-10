import BallPoincare
import FrozenFormBounded

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

lemma frozenForm_coercive_aux (center : V) (R κ Λ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hΛ : κ ≤ Λ) (A : Mat) (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (p : H01Space (Metric.ball center R)) :
    κ * ‖p.val.ofLp.2‖ ^ 2 ≤ frozenForm A (Metric.ball center R) (p, p) := by
  let Ω := Metric.ball center R
  let g := p.val.ofLp.2
  let f : Lp V 2 (volume.restrict Ω) := (matrixActionLinear A).compLp g
  have hmono : (fun x => κ * ‖g x‖ ^ 2) ≤ᵐ[volume.restrict Ω]
      (fun x => inner ℝ (f x) (g x)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      (matrixActionLinear A).coeFn_compLp g] with x hx hfx
    rw [hfx]
    change κ * ‖g x‖ ^ 2 ≤ inner ℝ (DeGiorgi.matMulE A (g x)) (g x)
    rw [real_inner_comm]
    exact hA.coercive x hx (g x)
  have hgi : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict Ω) :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hfi : Integrable (fun x => inner ℝ (f x) (g x)) (volume.restrict Ω) :=
    MeasureTheory.L2.integrable_inner f g
  have hi := integral_mono_ae (hgi.const_mul κ) hfi hmono
  rw [integral_const_mul] at hi
  rw [← toLp_norm_sq_eq_integral (Lp.memLp _)] at hi
  rw [frozenForm_eq_inner]
  rw [L2.inner_def]
  simpa [f, g, pairGradientLinear, Ω] using hi

theorem frozenForm_bounded_coercive (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ) :
    IsBoundedBilinearMap ℝ (frozenForm A (Metric.ball center R)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ p : H01Space (Metric.ball center R),
        c * ‖p‖ ^ 2 ≤ frozenForm A (Metric.ball center R) (p, p) := by
  refine ⟨frozenForm_bounded A _, ?_⟩
  let K : ℝ := eLpNormLESNormFDerivOfLeConst ℝ (volume : Measure V) (Metric.ball (0 : V) 1) 2 2
  let C : ℝ := R * K
  let c : ℝ := κ / (1 + C ^ 2)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro p
  have hp := H01_pair_norm_poincare center R hR p
  have hgrad := frozenForm_coercive_aux center R κ Λ hR hκ hΛ A hA p
  have hnorm := WithLp.prod_norm_sq_eq_of_L2 p.val
  have hsq : ‖p.val.ofLp.1‖ ^ 2 ≤ C ^ 2 * ‖p.val.ofLp.2‖ ^ 2 := by
    have hsq' := mul_self_le_mul_self (norm_nonneg p.val.ofLp.1) hp
    nlinarith [hsq', sq_nonneg ‖p.val.ofLp.1‖, sq_nonneg ‖p.val.ofLp.2‖]
  dsimp [c]
  have hnorm' : ‖p‖ ^ 2 ≤ (1 + C ^ 2) * ‖p.val.ofLp.2‖ ^ 2 := by
    change ‖WithLp.fst p.val‖ ^ 2 ≤ C ^ 2 * ‖WithLp.snd p.val‖ ^ 2 at hsq
    change ‖p.val‖ ^ 2 ≤ _
    rw [hnorm]
    change _ ≤ (1 + C ^ 2) * ‖WithLp.snd p.val‖ ^ 2
    nlinarith [hsq]
  calc
    κ / (1 + C ^ 2) * ‖p‖ ^ 2 ≤
        κ / (1 + C ^ 2) * ((1 + C ^ 2) * ‖p.val.ofLp.2‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnorm' (by positivity)
    _ = κ * ‖p.val.ofLp.2‖ ^ 2 := by field_simp
    _ ≤ frozenForm A (Metric.ball center R) (p, p) := hgrad

end SeifertSurfaces.WeakSchauder
