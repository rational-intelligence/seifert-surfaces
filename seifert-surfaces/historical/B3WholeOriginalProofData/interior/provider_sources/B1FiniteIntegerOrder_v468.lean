import B1WeakSimilarity_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
theorem similarity_finite_integer_order (R : ℝ) (hR : 0 < R) (w : ℂ → ℂ)
    (S : SimilarityFactorization R w) (hw0 : w 0 = 0) :
    (∀ z ∈ Metric.ball (0 : ℂ) R, w z = 0) ∨
    ∃ m : ℕ, 1 ≤ m ∧ ∃ delta c1 c2 : ℝ,
      0 < delta ∧ delta < R ∧ 0 < c1 ∧ 0 < c2 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) delta,
        c1 * ‖z‖ ^ m ≤ ‖w z‖ ∧ ‖w z‖ ≤ c2 * ‖z‖ ^ m := by
  classical
  have hzR : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have han := S.holomorphic.analyticOnNhd Metric.isOpen_ball
  have hPhi0 : S.Phi 0 = 0 := by
    have heq := S.same_w 0 hzR
    rw [hw0] at heq
    exact (mul_eq_zero.mp heq.symm).resolve_right (Complex.exp_ne_zero _)
  by_cases hzero : ∀ᶠ z in 𝓝 (0 : ℂ), S.Phi z = 0
  · left
    have hglob := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hzR hzero
    intro z hz
    rw [S.same_w z hz, hglob hz, Pi.zero_apply, zero_mul]
  · right
    obtain ⟨m, q, hq, hq0, hfactor⟩ :=
      (han 0 hzR).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hzero
    have hm : 1 ≤ m := by
      have h := Filter.EventuallyEq.eq_of_nhds hfactor
      by_contra hlt
      have hm0 : m = 0 := by omega
      simp [hm0, hPhi0] at h
      exact hq0 h.symm
    obtain ⟨L, hholder⟩ := S.omega_holder
    have homega : ContinuousAt S.omega 0 :=
      (hholder.continuousOn S.alpha_pos).continuousAt (Metric.isOpen_ball.mem_nhds hzR)
    let k : ℂ → ℂ := fun z => q z * Complex.exp (S.omega z)
    have hk : ContinuousAt k 0 := hq.continuousAt.mul (Complex.continuous_exp.continuousAt.comp homega)
    have hk0 : 0 < ‖k 0‖ := norm_pos_iff.mpr (mul_ne_zero hq0 (Complex.exp_ne_zero _))
    have hlow : ∀ᶠ z in 𝓝 (0 : ℂ), ‖k 0‖ / 2 < ‖k z‖ :=
      hk.norm.tendsto.eventually_const_lt (by linarith)
    have hupp : ∀ᶠ z in 𝓝 (0 : ℂ), ‖k z‖ < ‖k 0‖ + 1 :=
      hk.norm.tendsto.eventually_lt_const (by linarith)
    obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff.mp (hfactor.and (hlow.and hupp))
    let delta : ℝ := min d R / 2
    have hdelta : 0 < delta := half_pos (lt_min hd hR)
    have hdeltad : delta < d := by dsimp [delta]; have := min_le_left d R; linarith
    have hdeltaR : delta < R := by dsimp [delta]; have := min_le_right d R; linarith
    refine ⟨m, hm, delta, ‖k 0‖ / 2, ‖k 0‖ + 1, hdelta, hdeltaR, half_pos hk0, by positivity, ?_⟩
    intro z hz
    obtain ⟨hf, hlo, hup⟩ := hnear ((Metric.mem_ball.mp hz).trans hdeltad)
    have heq : w z = z ^ m * k z := by
      rw [S.same_w z (Metric.ball_subset_ball hdeltaR.le hz), hf]
      simp only [sub_zero, smul_eq_mul, k, mul_assoc]
    have hnorm : ‖w z‖ = ‖z‖ ^ m * ‖k z‖ := by rw [heq, norm_mul, norm_pow]
    rw [hnorm]
    constructor
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlo.le (pow_nonneg (norm_nonneg z) m)
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hup.le (pow_nonneg (norm_nonneg z) m)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
