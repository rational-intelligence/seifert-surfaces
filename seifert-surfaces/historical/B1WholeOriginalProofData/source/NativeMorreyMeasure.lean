import NativeMorreyBall
import Mathlib.Analysis.MeanInequalities
noncomputable section
open Set Topology Function MeasureTheory Filter Metric
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem morrey_radius_square {p r energy : ℝ} (hp : 2 < p)
    (hr : 0 ≤ r) (hI : 0 ≤ energy) :
    (r^(1-2/p)*energy^(1/p))^2 ≤ r^2+energy := by
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 2/p := le_of_lt (div_pos (by norm_num) hp0)
  have ha : 0 ≤ 1-2/p := by rw [sub_nonneg,div_le_one hp0]; exact hp.le
  have hqa : 2/p ≤ 1 := by exact (div_le_one hp0).mpr hp.le
  have haa : 1-2/p ≤ 1 := by linarith
  have hgm := Real.geom_mean_le_arith_mean2_weighted ha hq (sq_nonneg r) hI (by ring : (1-2/p)+2/p=1)
  have hpow : (r^(1-2/p)*energy^(1/p))^2 = (r^2)^(1-2/p)*energy^(2/p) := by
    rw [mul_pow, Real.rpow_pow_comm hr (1-2/p) 2,← Real.rpow_mul_natCast hI (1/p) 2]
    congr 1
    congr 1
    ring
  rw [hpow]
  exact hgm.trans (by nlinarith [mul_le_mul_of_nonneg_right haa (sq_nonneg r),mul_le_mul_of_nonneg_right hqa hI])
private theorem morrey_image_measure_bound {p : ℝ} (hp : 2 < p)
    {u : E2 → E2} {g : E2 → ℝ} {Ω : Set E2}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict Ω))
    {M : ℝ} (hM : 0 ≤ M) {a : E2} {r : ℝ} (hr : 0 < r)
    (hBΩ : ball a r ⊆ Ω)
    (hosc : ∀ x ∈ ball a r, ∀ y ∈ ball a r,
      ‖u x-u y‖ ≤ M*r^(1-2/p)*(eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball a r))).toReal) :
    volume (u '' ball a r) ≤ ENNReal.ofReal (Real.pi*M^2) *
      (volume (ball a r)+(volume.restrict Ω).withDensity (fun z => ENNReal.ofReal ‖g z‖ ^ p) (ball a r)) := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hgB := hg.mono_measure (Measure.restrict_mono hBΩ le_rfl)
  let energy : ℝ := ∫ z in ball a r, ‖g z‖^p
  have hI : 0 ≤ energy := integral_nonneg (fun z => Real.rpow_nonneg (norm_nonneg _) _)
  have hLp : (eLpNorm g (ENNReal.ofReal p) (volume.restrict (ball a r))).toReal = energy^(1/p) := by
    rw [hgB.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _),ENNReal.toReal_ofReal hp0.le,one_div,energy]
  let R := M*r^(1-2/p)*energy^(1/p)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have himage : u '' ball a r ⊆ closedBall (u a) R := by
    rintro z ⟨x,hx,rfl⟩
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    simpa only [hLp,R] using hosc x hx a (mem_ball_self hr)
  have hsquare : R^2 ≤ M^2*(r^2+energy) := by
    dsimp [R]
    calc
      _ = M^2*(r^(1-2/p)*energy^(1/p))^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (morrey_radius_square hp hr.le hI) (sq_nonneg M)
  have hden : (volume.restrict Ω).withDensity (fun z => ENNReal.ofReal ‖g z‖ ^ p) (ball a r) = ENNReal.ofReal energy := by
    rw [withDensity_apply _ isOpen_ball.measurableSet,Measure.restrict_restrict_of_subset hBΩ]
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    exact (ofReal_integral_eq_lintegral_ofReal (by
      simpa only [ENNReal.toReal_ofReal hp0.le] using hgB.integrable_norm_rpow hpne ENNReal.ofReal_ne_top)
      (ae_of_all _ (fun z => Real.rpow_nonneg (norm_nonneg _) _))).symm
  have hrπ : ENNReal.ofReal (r^2) ≤ volume (ball a r) := by
    rw [EuclideanSpace.volume_ball_fin_two]
    rw [ENNReal.ofReal_pow hr.le]
    exact le_mul_of_one_le_right' (by exact ENNReal.one_le_ofReal.mpr (by linarith [Real.pi_gt_three]))
  calc
    volume (u '' ball a r) ≤ volume (closedBall (u a) R) := measure_mono himage
    _ = ENNReal.ofReal (Real.pi*R^2) := by
      rw [EuclideanSpace.volume_closedBall_fin_two,← ENNReal.ofReal_pow hR,← ENNReal.ofReal_mul (sq_nonneg R)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (Real.pi*M^2*(r^2+energy)) := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hsquare Real.pi_pos.le])
    _ = ENNReal.ofReal (Real.pi*M^2)*(ENNReal.ofReal (r^2)+ENNReal.ofReal energy) := by
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (sq_nonneg r) hI]
    _ ≤ _ := by rw [hden]; gcongr
#print axioms morrey_radius_square
#print axioms morrey_image_measure_bound
