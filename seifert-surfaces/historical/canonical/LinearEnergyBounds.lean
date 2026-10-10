import HarmonicGradientBound
import ConstantSmoothRepresentative

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem exists_det_bound_on_norm_ball (N : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : V →L[ℝ] V, ‖L‖ ≤ N → |L.det| ≤ D := by
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : V →L[ℝ] V) N).exists_bound_of_continuousOn
    ContinuousLinearMap.continuous_det.continuousOn
  refine ⟨max D 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro L hL
  exact (hD L (by simpa only [Metric.mem_closedBall, dist_zero_right] using hL)).trans (le_max_left _ _)

theorem inverse_adjoint_apply_adjoint (P : V ≃L[ℝ] V) (v : V) :
    P.symm.toContinuousLinearMap.adjoint (P.toContinuousLinearMap.adjoint v) = v := by
  have he : P.toContinuousLinearMap.comp P.symm.toContinuousLinearMap = ContinuousLinearMap.id ℝ V := by
    ext1 x
    exact P.apply_symm_apply x
  have ha := congrArg ContinuousLinearMap.adjoint he
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] at ha
  exact congrArg (fun L : V →L[ℝ] V => L v) ha

theorem determinant_inverse_eq (P : V ≃L[ℝ] V) :
    (LinearMap.det P.toLinearMap)⁻¹ = P.symm.toContinuousLinearMap.det := by
  have he : P.toContinuousLinearMap.comp P.symm.toContinuousLinearMap = ContinuousLinearMap.id ℝ V := by
    ext1 x
    exact P.apply_symm_apply x
  have hd := congrArg ContinuousLinearMap.det he
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
  exact inv_eq_of_mul_eq_one_right hd

theorem pulledBack_ball_contains_closedBall (P : V ≃L[ℝ] V)
    (c x : V) (R L : ℝ) (hR : 0 < R) (hL : 0 < L)
    (hP : ‖P.toContinuousLinearMap‖ ≤ L) (hx : x ∈ Metric.ball c (R / 2)) :
    Metric.closedBall (P.symm x) (R / (2 * L)) ⊆ pulledBackBall P c R := by
  intro y hy
  change P y ∈ Metric.ball c R
  have hn := P.toContinuousLinearMap.le_opNorm (y - P.symm x)
  have hd : dist (P y) x ≤ L * dist y (P.symm x) := by
    calc
      _ = ‖P (y - P.symm x)‖ := by simp [dist_eq_norm, map_sub]
      _ ≤ ‖P.toContinuousLinearMap‖ * ‖y - P.symm x‖ := hn
      _ ≤ L * dist y (P.symm x) := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
  have hbound : L * (R / (2 * L)) = R / 2 := by field_simp
  have hd' := hd.trans (mul_le_mul_of_nonneg_left (Metric.mem_closedBall.mp hy) hL.le)
  rw [hbound] at hd'
  exact Metric.mem_ball.mpr (by linarith [Metric.mem_ball.mp hx, dist_triangle (P y) x c])

theorem pulledBack_gradient_energy_le (P : V ≃L[ℝ] V) (Ω : Set V)
    (h : V → ℝ) (hh : H1Witness h Ω) (L : ℝ) (hL : 0 ≤ L)
    (hP : ‖P.toContinuousLinearMap‖ ≤ L) :
    (∫ y in P ⁻¹' Ω, ‖P.toContinuousLinearMap.adjoint (hh.weakGrad (P y))‖ ^ 2) ≤
      L ^ 2 * |(LinearMap.det P.toLinearMap)⁻¹| * ∫ x in Ω, ‖hh.weakGrad x‖ ^ 2 := by
  have hm := hh.weakGrad_memLp.continuousLinearMap_comp P.toContinuousLinearMap.adjoint
  rw [linear_pullback_integral P Ω (fun x => ‖P.toContinuousLinearMap.adjoint (hh.weakGrad x)‖ ^ 2)]
  have hi := integral_mono hm.norm.integrable_sq (hh.weakGrad_memLp.norm.integrable_sq.const_mul (L ^ 2))
    (fun x => by
      have hn := P.toContinuousLinearMap.adjoint.le_opNorm (hh.weakGrad x)
      have he : ‖P.toContinuousLinearMap.adjoint‖ = ‖P.toContinuousLinearMap‖ := by simp
      rw [he] at hn
      have hn' := hn.trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn' 2)
  rw [integral_const_mul] at hi
  calc
    _ ≤ |(LinearMap.det P.toLinearMap)⁻¹| * (L ^ 2 * ∫ x in Ω, ‖hh.weakGrad x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hi (abs_nonneg _)
    _ = _ := by ring

end SeifertSurfaces.WeakSchauder
