import HarmonicReplacementProof

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000

lemma matMulE_sub_vec (A : Mat) (ξ η : V) :
    DeGiorgi.matMulE A (ξ - η) = DeGiorgi.matMulE A ξ - DeGiorgi.matMulE A η := by
  exact (matrixActionLinear A).map_sub ξ η

lemma matMulE_sub_mat (A B : Mat) (ξ : V) :
    DeGiorgi.matMulE (A - B) ξ = DeGiorgi.matMulE A ξ - DeGiorgi.matMulE B ξ := by
  ext i
  simp [DeGiorgi.matMulE_apply, Matrix.sub_mulVec]

theorem replacement_energy_comparison (center : V) (R κ Λ δ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hδ : 0 ≤ δ)
    (a : V → Mat) (A : Mat)
    (ha : CoefficientBounds a (Metric.ball center R) κ Λ)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (hosc : OscillationBound a A (Metric.ball center R) δ)
    (v h : V → ℝ) (hv : H1Witness v (Metric.ball center R))
    (hh : H1Witness h (Metric.ball center R))
    (hweak : WeakEquation a hv) (hrep : IsHarmonicReplacement A hv hh) :
    energy (fun x => hv.weakGrad x - hh.weakGrad x) center R ≤
      (δ / κ) ^ 2 * energy hv.weakGrad center R := by
  let Ω := Metric.ball center R
  let d := witnessSub hv hh
  let F := fun x => inner ℝ (DeGiorgi.matMulE A (hv.weakGrad x)) (d.weakGrad x)
  let B := fun x => inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x)) (d.weakGrad x)
  let H := fun x => inner ℝ (DeGiorgi.matMulE A (hh.weakGrad x)) (d.weakGrad x)
  let D := fun x => inner ℝ (DeGiorgi.matMulE A (d.weakGrad x)) (d.weakGrad x)
  have hd0 : DeGiorgi.MemH01 (fun x => v x - h x) Ω := hrep.1
  have hHz : (∫ x in Ω, H x) = 0 := (hrep.2 _ hd0 d).2
  have hBz : (∫ x in Ω, B x) = 0 := (hweak _ hd0 d).2
  have hHi : Integrable H (volume.restrict Ω) := (hrep.2 _ hd0 d).1
  have hBi : Integrable B (volume.restrict Ω) := (hweak _ hd0 d).1
  have hFi : Integrable F (volume.restrict Ω) :=
    matrix_inner_integrable A (weak_gradient_memLp Ω v hv) (weak_gradient_memLp Ω _ d)
  have hDi : Integrable D (volume.restrict Ω) :=
    matrix_inner_integrable A (weak_gradient_memLp Ω _ d) (weak_gradient_memLp Ω _ d)
  have hDF : D = F - H := by
    funext x
    change inner ℝ (DeGiorgi.matMulE A (hv.weakGrad x - hh.weakGrad x)) (d.weakGrad x) = _
    rw [matMulE_sub_vec, inner_sub_left]
    rfl
  have hDint : (∫ x in Ω, D x) = ∫ x in Ω, (F - B) x := by
    rw [hDF]
    simp only [Pi.sub_apply]
    rw [integral_sub hFi hHi, integral_sub hFi hBi, hHz, hBz]
  have hdi : Integrable (fun x => ‖d.weakGrad x‖ ^ 2) (volume.restrict Ω) :=
    (weak_gradient_memLp Ω _ d).integrable_norm_pow (by norm_num)
  have hvi : Integrable (fun x => ‖hv.weakGrad x‖ ^ 2) (volume.restrict Ω) :=
    (weak_gradient_memLp Ω v hv).integrable_norm_pow (by norm_num)
  have hco : κ * (∫ x in Ω, ‖d.weakGrad x‖ ^ 2) ≤ ∫ x in Ω, D x := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hdi.const_mul κ) hDi
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    dsimp [D]
    rw [real_inner_comm]
    exact hA.coercive x hx _
  have hpt : (fun x => κ * (F - B) x) ≤ᵐ[volume.restrict Ω]
      (fun x => (κ ^ 2 / 2) * ‖d.weakGrad x‖ ^ 2 + (δ ^ 2 / 2) * ‖hv.weakGrad x‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hoscx := hosc x hx (hv.weakGrad x) (d.weakGrad x)
    rw [matMulE_sub_mat, inner_sub_left] at hoscx
    have hoscx' : |(F - B) x| ≤ δ * ‖hv.weakGrad x‖ * ‖d.weakGrad x‖ := by
      dsimp [F, B]
      rw [abs_sub_comm]
      exact hoscx
    have hleft : κ * (F - B) x ≤ κ * δ * ‖hv.weakGrad x‖ * ‖d.weakGrad x‖ := by
      calc
        _ ≤ κ * |(F - B) x| := mul_le_mul_of_nonneg_left (le_abs_self _) hκ.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hoscx' hκ.le]
    exact hleft.trans (by nlinarith [sq_nonneg (κ * ‖d.weakGrad x‖ - δ * ‖hv.weakGrad x‖)])
  have hi := integral_mono_ae ((hFi.sub hBi).const_mul κ)
    ((hdi.const_mul (κ ^ 2 / 2)).add (hvi.const_mul (δ ^ 2 / 2))) hpt
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, ← hDint,
    integral_add (hdi.const_mul (κ ^ 2 / 2)) (hvi.const_mul (δ ^ 2 / 2)),
    integral_const_mul, integral_const_mul] at hi
  have hco' := mul_le_mul_of_nonneg_left hco hκ.le
  have hfinal : κ ^ 2 * (∫ x in Ω, ‖d.weakGrad x‖ ^ 2) ≤
      δ ^ 2 * (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2) := by
    nlinarith [hi, hco']
  change (∫ x in Ω, ‖d.weakGrad x‖ ^ 2) ≤ (δ / κ) ^ 2 * (∫ x in Ω, ‖hv.weakGrad x‖ ^ 2)
  rw [div_pow, div_mul_eq_mul_div]
  apply (le_div_iff₀ (sq_pos_of_pos hκ)).mpr
  nlinarith [hfinal]

end SeifertSurfaces.WeakSchauder
