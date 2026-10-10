import CoefficientLimit
import GradientWeakLimit
import WeakEquationLimit

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization EnergyHelpers

set_option maxHeartbeats 800000 in
theorem R2_differentiated_weak_equation
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∀ k : Fin 2, ProviderLinearWeakEquation (Metric.ball x₀ r)
      (differentiatedCoefficients Q u k) (fun x => planarGradient u x k) := by
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
  have hlimit : ∀ (i : Fin 2) (φ : E2 → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ Metric.ball x₀ r →
      Tendsto (fun n => ∫ x in Metric.ball x₀ r, differenceQuotient u k (hseq n) x *
        (fderiv ℝ φ x) (EuclideanSpace.single i 1)) atTop
        (𝓝 (∫ x in Metric.ball x₀ r, planarGradient u x k *
          (fderiv ℝ φ x) (EuclideanSpace.single i 1))) := by
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
  let B := Metric.ball x₀ r
  let v : E2 → ℝ := fun x => planarGradient u x k
  let vn : ℕ → E2 → ℝ := fun n => differenceQuotient u k (hseq n)
  let Cn : ℕ → LinearizedCoefficients := fun n => averagedCoefficients Q u k (hseq n)
  let D := differentiatedCoefficients Q u k
  obtain ⟨G, s, hs, hGn, hGw, hGderiv⟩ := exists_classical_gradient_weak_limit B Metric.isOpen_ball v vn
    hmem (fun n => (hqc n).mono hinner) (fun n => (he n).1) C hC (fun n => (he n).2) hlimit
  let Gn : ℕ → Lp E2 2 (volume.restrict B) := fun n => (he (s n)).1.toLp (planarGradient (vn (s n)))
  let hw : DeGiorgi.MemW1pWitness 2 v B :=
    ⟨hmem, G, vector_component_memLp _ G (Lp.memLp G), hGderiv⟩
  have hD : CoefficientBounds B D κ M :=
    differentiated_coefficients_bounds J Q u x₀ r κ M hr T hjetsT hbound k
  have hDcont := differentiated_coefficients_continuous Ω hΩ J hJ Q u hC1 hjets k
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hclosed
  have hDm : CoefficientMeasurableOn B D :=
    ⟨(hDcont.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    (hDcont.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    (hDcont.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    (hDcont.2.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    (hDcont.2.2.2.2.1.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    (hDcont.2.2.2.2.2.mono hBΩ).aestronglyMeasurable Metric.isOpen_ball.measurableSet⟩
  have hCb (n : ℕ) := R2_uniform_coefficient_and_quotient_bounds Ω hΩ J hJ Q u hC1 x₀ r κ M hr T
    hball hT hTJ hjetsT hbound k (hseq n) (by simpa only [abs_of_pos (hpos n)] using hpos n) (hsmall n)
  have hCm (n : ℕ) := (R2_averaged_coefficients_continuous Ω hΩ J hJ Q u hC1 x₀ r hr T
    hball hT hTJ' hjetsT k (hseq n) (by simpa only [abs_of_pos (hpos n)] using hpos n) (hsmall n)).1
  have hCnb (n : ℕ) : CoefficientBounds B (Cn n) κ M :=
    ⟨(hCb n).1.1, (hCb n).1.2.1,
      fun x hx => (hCb n).1.2.2.1 x (hinner hx),
      fun x hx => (hCb n).1.2.2.2 x (hinner hx)⟩
  have hCnm (n : ℕ) : CoefficientMeasurableOn B (Cn n) :=
    ⟨((hCm n).1.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    ((hCm n).2.1.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    ((hCm n).2.2.1.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    ((hCm n).2.2.2.1.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    ((hCm n).2.2.2.2.1.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet,
    ((hCm n).2.2.2.2.2.mono hinner).aestronglyMeasurable Metric.isOpen_ball.measurableSet⟩
  have hvmn (n : ℕ) : MemLp (vn n) 2 (volume.restrict B) := by
    haveI : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    apply MemLp.of_bound (((hqc n).mono hinner).continuousOn.aestronglyMeasurable Metric.isOpen_ball.measurableSet) M
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (hCb n).2 x (hinner hx)
  have hweq (n : ℕ) : LinearWeakEquation B (Cn (s n)) (vn (s n)) (Gn n) := by
    have hn := (R2_differenceQuotient_weak_equation Ω hΩ J hJ Q u hC1 hjets hweak x₀ r hr T
      hball hT hTJ' hjetsT k (hseq (s n))
      (by simpa only [abs_of_pos (hpos (s n))] using hpos (s n)) (hsmall (s n))).2
    apply linear_weak_equation_congr_grad B (Cn (s n)) (vn (s n)) (planarGradient (vn (s n))) (Gn n)
      ((he (s n)).1.coeFn_toLp.symm)
    exact linear_weak_equation_restrict B _ hinner _ _ _ hn
  have hsolution : LinearWeakEquation B D v G := by
    apply linear_weak_equation_of_limits B Metric.isOpen_ball Metric.isBounded_ball
      (fun n => Cn (s n)) D (fun n => vn (s n)) v Gn G κ M (C + 1)
      (fun n => hCnb (s n)) hD (fun n => hCnm (s n)) hDm (fun n => hvmn (s n)) hmem
      (fun n x hx => (hCb (s n)).2 x (hinner hx)) hGn hGw hweq
    · intro x hx
      exact ((quotient_tendsto_gradient Ω hΩ u hC1 k x (hBΩ hx)).comp hright).comp hs.tendsto_atTop
    · intro x hx
      have hc := averaged_coefficients_tendsto Ω hΩ J hJ Q u hC1 hjets x₀ r κ M hr T
        hball hT hTJ hjetsT hbound k hseq hzero hsmall x hx
      exact ⟨hc.1.comp hs.tendsto_atTop, hc.2.1.comp hs.tendsto_atTop,
        hc.2.2.1.comp hs.tendsto_atTop, hc.2.2.2.1.comp hs.tendsto_atTop,
        hc.2.2.2.2.1.comp hs.tendsto_atTop, hc.2.2.2.2.2.comp hs.tendsto_atTop⟩
  exact rough_smooth_tests_extend_to_H01 B Metric.isOpen_ball Metric.isBounded_ball
    D v κ M hD hDm hw hsolution

end SeifertSurfaces.QuasilinearProviderBridge
