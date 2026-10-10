import WeakDerivativeLimit
import UniformQuotientEnergy

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization
open EnergyHelpers

namespace EnergyHelpers

theorem quotient_tendsto_gradient (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ)
    (hC1 : ContDiffOn ℝ 1 u Ω) (k : Fin 2) (x : E2) (hx : x ∈ Ω) :
    Tendsto (fun h => differenceQuotient u k h x) (𝓝[>] 0)
      (𝓝 (planarGradient u x k)) := by
  have hu := (hC1.differentiableOn (by norm_num) x hx).differentiableAt (hΩ.mem_nhds hx)
  have hl : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 k) (coordinateVector 2 k) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 k)).const_add x
  have hux : HasFDerivAt u (fderiv ℝ u x) (x + (0 : ℝ) • coordinateVector 2 k) := by
    simpa using hu.hasFDerivAt
  have hd := hux.comp_hasDerivAt 0 hl
  have ht := hd.tendsto_slope_zero_right
  simpa [differenceQuotient, shift, SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_apply,
    div_eq_mul_inv, smul_eq_mul, mul_comm] using ht

end EnergyHelpers

theorem R2_first_derivatives_memW1p
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∀ k : Fin 2, DeGiorgi.MemW1p 2 (fun x => planarGradient u x k) (Metric.ball x₀ r) := by
  obtain ⟨C, hC, henergy⟩ := R2_uniform_differenceQuotient_energy Ω hΩ J hJ Q u hC1 hjets
    hweak x₀ r κ M hr T hball hT hTJ hjetsT hbound
  let hseq : ℕ → ℝ := fun n => r / ((n : ℝ) + 2)
  have hpos (n : ℕ) : 0 < hseq n := by dsimp [hseq]; positivity
  have hsmall (n : ℕ) : |hseq n| < r := by
    rw [abs_of_pos (hpos n)]
    exact div_lt_self hr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hzero : Tendsto hseq atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat r).comp (tendsto_add_atTop_nat 2)
    simpa [hseq, Nat.cast_add, Nat.cast_ofNat, Function.comp_def] using ht
  have hright : Tendsto hseq atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, Eventually.of_forall hpos⟩
  have hTJ' : T ⊆ J := subset_closure.trans hTJ
  have hclosed : Metric.closedBall x₀ r ⊆ Ω :=
    (Metric.closedBall_subset_closedBall (by linarith)).trans hball
  have hinner : Metric.ball x₀ r ⊆ Metric.ball x₀ (2 * r) := Metric.ball_subset_ball (by linarith)
  intro k
  have hmem : MemLp (fun x => planarGradient u x k) 2 (volume.restrict (Metric.ball x₀ r)) := by
    apply Helpers.continuousOn_closedBall_memLp
    exact (((EuclideanSpace.proj k).continuous.continuousOn).comp
      (SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1)
      (mapsTo_univ _ _)).mono hclosed
  have hqc (n : ℕ) : ContDiffOn ℝ 1 (differenceQuotient u k (hseq n)) (Metric.ball x₀ (2 * r)) :=
    (R2_differenceQuotient_weak_equation Ω hΩ J hJ Q u hC1 hjets hweak x₀ r hr T hball hT hTJ'
      hjetsT k (hseq n) (by simpa only [abs_of_pos (hpos n)] using hpos n) (hsmall n)).1
  have he (n : ℕ) := henergy k (hseq n) (by simpa only [abs_of_pos (hpos n)] using hpos n) (hsmall n)
  apply memW1p_of_classical_energy_limit (Metric.ball x₀ r) Metric.isOpen_ball _
    (fun n => differenceQuotient u k (hseq n)) hmem (fun n => (hqc n).mono hinner)
    (fun n => (he n).1) C hC (fun n => (he n).2)
  intro i φ hφ hφc hφB
  let dφ : E2 → ℝ := fun x => (fderiv ℝ φ x) (EuclideanSpace.single i 1)
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply (𝕜 := ℝ) _
  have hboundq (n : ℕ) (x : E2) (hx : x ∈ Metric.ball x₀ r) :
      |differenceQuotient u k (hseq n) x| ≤ M :=
    (R2_uniform_coefficient_and_quotient_bounds Ω hΩ J hJ Q u hC1 x₀ r κ M hr T hball hT hTJ
      hjetsT hbound k (hseq n) (by simpa only [abs_of_pos (hpos n)] using hpos n) (hsmall n)).2 x (hinner hx)
  apply tendsto_integral_of_dominated_convergence (fun x => M * ‖dφ x‖)
  · intro n
    exact (((hqc n).mono hinner).continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet).mul
      hdφ.aestronglyMeasurable
  · exact ((hdφ.integrable_of_hasCompactSupport hdφc).integrableOn.norm).const_mul M
  · intro n
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hboundq n x hx) (norm_nonneg _)
  · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact ((quotient_tendsto_gradient Ω hΩ u hC1 k x (hclosed (Metric.ball_subset_closedBall hx))).comp
      hright).mul_const (dφ x)

end SeifertSurfaces.QuasilinearProviderBridge
