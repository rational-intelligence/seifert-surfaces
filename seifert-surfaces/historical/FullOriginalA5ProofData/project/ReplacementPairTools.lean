import FrozenFormCoercive
import HilbertRelease
import LaxMilgramRelease

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000

def witnessSub {Ω : Set V} {v w : V → ℝ} (hv : H1Witness v Ω) (hw : H1Witness w Ω) :
    H1Witness (fun x => v x - w x) Ω where
  memLp := hv.memLp.sub hw.memLp
  weakGrad := fun x => hv.weakGrad x - hw.weakGrad x
  weakGrad_component_memLp := by
    intro i
    exact (hv.weakGrad_component_memLp i).sub (hw.weakGrad_component_memLp i)
  isWeakGrad := by
    simpa only [DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.smul,
      neg_one_mul, neg_one_smul, sub_eq_add_neg] using (hv.add (hw.smul (-1))).isWeakGrad

lemma witnessPair_sub {Ω : Set V} {v w : V → ℝ} (hv : H1Witness v Ω) (hw : H1Witness w Ω) :
    witnessPair (witnessSub hv hw) = witnessPair hv - witnessPair hw := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact MemLp.toLp_sub hv.memLp hw.memLp
  · exact MemLp.toLp_sub (weak_gradient_memLp Ω v hv) (weak_gradient_memLp Ω w hw)

lemma matrix_inner_integrable {Ω : Set V} (A : Mat) {F G : V → V}
    (hF : MemLp F 2 (volume.restrict Ω)) (hG : MemLp G 2 (volume.restrict Ω)) :
    IntegrableOn (fun x => inner ℝ (DeGiorgi.matMulE A (F x)) (G x)) Ω := by
  have h := L2.integrable_inner (𝕜 := ℝ) ((matrixActionLinear A).compLp (hF.toLp F)) (hG.toLp G)
  apply h.congr
  filter_upwards [(matrixActionLinear A).coeFn_compLp (hF.toLp F), hF.coeFn_toLp,
    hG.coeFn_toLp] with x hx hFx hGx
  rw [hx, hFx, hGx]
  rfl

lemma matrix_inner_toLp {Ω : Set V} (A : Mat) {F G : V → V}
    (hF : MemLp F 2 (volume.restrict Ω)) (hG : MemLp G 2 (volume.restrict Ω)) :
    (∫ x in Ω, inner ℝ (DeGiorgi.matMulE A (F x)) (G x)) =
      inner ℝ ((matrixActionLinear A).compLp (hF.toLp F)) (hG.toLp G) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(matrixActionLinear A).coeFn_compLp (hF.toLp F), hF.coeFn_toLp,
    hG.coeFn_toLp] with x hx hFx hGx
  rw [hx, hFx, hGx]
  rfl

lemma matrixAction_norm_le (center : V) (R κ Λ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hΛ : κ ≤ Λ) (A : Mat) (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ) :
    ‖matrixActionLinear A‖ ≤ Λ := by
  have hΛ0 : 0 ≤ Λ := (hκ.trans_le hΛ).le
  apply (matrixActionLinear A).opNorm_le_bound hΛ0
  intro ξ
  have h := hA.mixed center (Metric.mem_ball_self hR) ξ (DeGiorgi.matMulE A ξ)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
  change ‖DeGiorgi.matMulE A ξ‖ ≤ Λ * ‖ξ‖
  by_cases hz : ‖DeGiorgi.matMulE A ξ‖ = 0
  · rw [hz]
    positivity
  · have hn : 0 < ‖DeGiorgi.matMulE A ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [pow_two] at h
    apply le_of_mul_le_mul_right _ hn
    simpa [mul_comm] using h

lemma matrixLp_coercive (center : V) (R κ Λ : ℝ) (hR : 0 < R) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (g : Lp V 2 (volume.restrict (Metric.ball center R))) :
    κ * ‖g‖ ^ 2 ≤ inner ℝ ((matrixActionLinear A).compLp g) g := by
  have hgi : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict (Metric.ball center R)) :=
    (Lp.memLp _).integrable_norm_pow (by norm_num)
  have hmi := L2.integrable_inner (𝕜 := ℝ) ((matrixActionLinear A).compLp g) g
  have hmono : (fun x => κ * ‖g x‖ ^ 2) ≤ᵐ[volume.restrict (Metric.ball center R)]
      (fun x => inner ℝ (((matrixActionLinear A).compLp g) x) (g x)) := by
    filter_upwards [(matrixActionLinear A).coeFn_compLp g] with x hx
    rw [hx]
    change κ * ‖g x‖ ^ 2 ≤ inner ℝ (DeGiorgi.matMulE A (g x)) (g x)
    rw [real_inner_comm]
    exact hA.coercive center (Metric.mem_ball_self hR) (g x)
  have hi := integral_mono_ae (hgi.const_mul κ) hmi hmono
  rw [integral_const_mul, ← toLp_norm_sq_eq_integral (Lp.memLp _)] at hi
  simpa [L2.inner_def] using hi

end SeifertSurfaces.WeakSchauder
