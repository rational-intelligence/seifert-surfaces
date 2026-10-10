import HolderEndpoint
import PlanarProducers

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.HolderAssembly
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

lemma planar_part_norm_sq (y : E3) :
    ‖y‖ ^ 2 = ‖planarPart y‖ ^ 2 + (y 2) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, planarPart]
  ring

lemma planar_part_norm_le (y : E3) : ‖planarPart y‖ ≤ ‖y‖ := by
  have h := planar_part_norm_sq y
  nlinarith [sq_nonneg (y 2), norm_nonneg y, norm_nonneg (planarPart y)]

lemma planar_part_sub (x y : E3) : planarPart (x - y) = planarPart x - planarPart y := by
  ext i
  fin_cases i <;> simp [planarPart]

lemma planar_lift_zero (x : E2) : planarPart (liftedPoint x 0) = x := by
  ext i
  fin_cases i <;> simp [planarPart, liftedPoint]

lemma vertical_lift_zero (x : E2) : liftedPoint x 0 2 = 0 := by
  simp [liftedPoint]

lemma lifted_zero_distance (x y : E2) :
    dist (liftedPoint x 0) (liftedPoint y 0) = dist x y := by
  simp only [dist_eq_norm]
  have h := planar_part_norm_sq (liftedPoint x 0 - liftedPoint y 0)
  rw [planar_part_sub, planar_lift_zero, planar_lift_zero] at h
  simp only [PiLp.sub_apply, vertical_lift_zero, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma ball_in_cylinder (x₀ : E2) {r R : ℝ} (hr : 0 < r)
    (hRr : R ≤ r) (hR1 : R ≤ 1 / 2) :
    Metric.ball (liftedPoint x₀ 0) R ⊆ cylinder (Metric.ball x₀ (2 * r)) := by
  intro y hy
  have hd : ‖y - liftedPoint x₀ 0‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hy
  constructor
  · simp only [Metric.mem_ball, dist_eq_norm]
    have hp := planar_part_norm_le (y - liftedPoint x₀ 0)
    rw [planar_part_sub, planar_lift_zero] at hp
    linarith
  · have hv : |y 2| ≤ ‖y - liftedPoint x₀ 0‖ := by
      simpa only [PiLp.sub_apply, vertical_lift_zero, sub_zero, Real.norm_eq_abs] using
        PiLp.norm_apply_le (y - liftedPoint x₀ 0) 2
    linarith

lemma lift_continuous (B : Set E2) (v : E2 → ℝ) (hv : ContinuousOn v B) :
    ContinuousOn (liftFunction v) (cylinder B) := by
  have hp : Continuous planarPart := by
    unfold planarPart
    fun_prop
  have ht : Continuous (fun y : E3 => y 2) := by fun_prop
  exact (hv.comp hp.continuousOn (fun _ hy => hy.1)).add ht.continuousOn

lemma lift_l2_bound (B : Set E2) (v : E2 → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hv : ∀ x ∈ B, |v x| ≤ M) (center : E3) (R : ℝ)
    (hball : Metric.ball center R ⊆ cylinder B) :
    (∫ y in Metric.ball center R, |liftFunction v y| ^ (2 : ℕ)) ≤
      (M + 1) ^ 2 * volume.real (Metric.ball center R) := by
  apply (le_abs_self _).trans
  rw [← Real.norm_eq_abs]
  apply norm_setIntegral_le_of_norm_le_const (Metric.isBounded_ball.measure_lt_top)
  intro y hy
  have hc := hball hy
  have hb : |liftFunction v y| ≤ M + 1 := by
    exact (abs_add_le _ _).trans ((add_le_add (hv _ hc.1) hc.2.le))
  simp only [Real.norm_eq_abs, abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hb 2

lemma holder_on_slice_ball (x₀ : E2) (ρ : ℝ) (v : E2 → ℝ) (K α : NNReal)
    (hv : HolderOnWith K α (liftFunction v) (Metric.ball (liftedPoint x₀ 0) ρ)) :
    HolderOnWith K α v (Metric.ball x₀ ρ) := by
  intro x hx y hy
  have hx' : liftedPoint x 0 ∈ Metric.ball (liftedPoint x₀ 0) ρ := by
    simpa only [Metric.mem_ball, lifted_zero_distance] using hx
  have hy' : liftedPoint y 0 ∈ Metric.ball (liftedPoint x₀ 0) ρ := by
    simpa only [Metric.mem_ball, lifted_zero_distance] using hy
  have h := hv (liftedPoint x 0) hx' (liftedPoint y 0) hy'
  simpa only [liftFunction, planar_lift_zero, vertical_lift_zero, add_zero,
    edist_dist, lifted_zero_distance] using h

end SeifertSurfaces.QuasilinearProviderBridge.HolderAssembly
