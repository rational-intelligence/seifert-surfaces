import HolderEndpoint
import HolderGeometry
import QuasilinearProviderBridge
import H01ExtensionProducer
import PlanarProducers
import QuotientWeakEquation
import DifferentialGeometry.External.DeGiorgi.Holder.PublicEstimate

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

theorem R3_uniform_holder_differenceQuotients
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∃ ρ : ℝ, ∃ K α : NNReal, 0 < ρ ∧ ρ ≤ r ∧ 0 < α ∧ α < 1 ∧
      ∀ (k : Fin 2) (h : ℝ), 0 < |h| → |h| < r →
        HolderOnWith K α (differenceQuotient u k h) (Metric.ball x₀ ρ) := by
  let R : ℝ := min r (1 / 2)
  have hR : 0 < R := lt_min hr (by norm_num)
  have hRr : R ≤ r := min_le_left _ _
  have hR1 : R ≤ 1 / 2 := min_le_right _ _
  let center : E3 := liftedPoint x₀ 0
  let S : ℝ := Real.sqrt ((M + 1) ^ 2 * volume.real (Metric.ball center R))
  have hM : 1 ≤ M := hbound.2.1
  have hM0 : 0 ≤ M := by linarith
  obtain ⟨K, α, hα, hα1, hholder⟩ := R3_uniform_holder_actual_homogeneous_solutions
    center R (liftLambda κ M M) S hR (by
      unfold liftLambda
      exact one_le_pow₀ (le_max_left (1 : ℝ) _) ) (Real.sqrt_nonneg _)
  refine ⟨R / 2, K, α, by positivity, by linarith, hα, hα1, ?_⟩
  intro k h hh hhr
  let B : Set E2 := Metric.ball x₀ (2 * r)
  let v : E2 → ℝ := differenceQuotient u k h
  let C : LinearizedCoefficients := averagedCoefficients Q u k h
  have hTJ' : T ⊆ J := subset_closure.trans hTJ
  obtain ⟨hC1v, hweakv⟩ := R2_differenceQuotient_weak_equation Ω hΩ J hJ Q u hC1 hjets
    hweak x₀ r hr T hball hT hTJ' hjetsT k h hh hhr
  obtain ⟨hCb, hvb⟩ := R2_uniform_coefficient_and_quotient_bounds Ω hΩ J hJ Q u hC1
    x₀ r κ M hr T hball hT hTJ hjetsT hbound k h hh hhr
  have hmeas : CoefficientMeasurableOn B C :=
    (R2_averaged_coefficients_continuous Ω hΩ J hJ Q u hC1 x₀ r hr T
      hball hT hTJ' hjetsT k h hh hhr).2
  let Ωv : Set E2 := Ω ∩ (shift k h) ⁻¹' Ω
  have hs : ContDiff ℝ 1 (shift k h) := by unfold shift; fun_prop
  have hΩv : IsOpen Ωv := hΩ.inter (hΩ.preimage hs.continuous)
  have hvC1 : ContDiffOn ℝ 1 v Ωv := by
    have htrans : ContDiffOn ℝ 1 (u ∘ shift k h) Ωv :=
      hC1.comp hs.contDiffOn (fun _ hx => hx.2)
    have hu := hC1.mono (show Ωv ⊆ Ω from fun _ hx => hx.1)
    have he : v = h⁻¹ • (u ∘ shift k h - u) := by
      funext x
      simp [v, differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [he]
    exact (htrans.sub hu).const_smul h⁻¹
  have hclosed : Metric.closedBall x₀ (2 * r) ⊆ Ωv := by
    intro x hx
    refine ⟨hball (Metric.closedBall_subset_closedBall (by linarith) hx), ?_⟩
    exact hball (QuotientHelpers.shift_mem_closedBall x₀ x r hr
      (Metric.closedBall_subset_closedBall (by linarith) hx) k h hhr)
  have hmem : DeGiorgi.MemW1p 2 v B :=
    (R1_C1_memW1p_on_ball Ωv hΩv v hvC1 x₀ (2 * r) (by positivity) hclosed).1
  have hprovider : ProviderLinearWeakEquation B C v :=
    R2_smooth_tests_extend_to_H01 B Metric.isOpen_ball Metric.isBounded_ball C v hC1v
      κ M hCb hmeas hmem hweakv
  have hball3 : Metric.ball center R ⊆ cylinder B :=
    HolderAssembly.ball_in_cylinder x₀ hr hRr hR1
  obtain ⟨A, hΛA, _, _, hhomogeneous, _⟩ := R3_lift_homogeneous_on_ball B Metric.isOpen_ball
    Metric.isBounded_ball C v κ M M hbound.1 hM hM0 hmeas hCb hvb hprovider center R hR hball3
  have hcont : ContinuousOn (liftFunction v) (Metric.ball center R) :=
    (HolderAssembly.lift_continuous B v hC1v.continuousOn).mono hball3
  have hL2 : (∫ y in Metric.ball center R, |liftFunction v y| ^ (2 : ℕ)) ≤ S ^ 2 := by
    have hbound2 := HolderAssembly.lift_l2_bound B v hM0 hvb center R hball3
    exact hbound2.trans_eq (Real.sq_sqrt (by positivity)).symm
  exact HolderAssembly.holder_on_slice_ball x₀ (R / 2) v K α
    (hholder A (liftFunction v) hΛA.le hcont hhomogeneous hL2)

theorem R3_local_holder_gradient
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T) :
    ∃ ρ : ℝ, ∃ K α : NNReal, 0 < ρ ∧ ρ ≤ r ∧ 0 < α ∧ α < 1 ∧
      ∀ k : Fin 2, HolderOnWith K α (fun x => planarGradient u x k) (Metric.ball x₀ ρ) := by
  obtain ⟨ρ, K, α, hρ, hρr, hα, hα1, h⟩ := R3_uniform_holder_differenceQuotients
    Ω hΩ J hJ Q u hC1 hjets hweak x₀ r κ M hr T hball hT hTJ hjetsT hbound
  have hBΩ : Metric.ball x₀ ρ ⊆ Ω := by
    apply Subset.trans _ hball
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))
  refine ⟨ρ, K, α, hρ, hρr, hα, hα1, ?_⟩
  intro k
  exact R3_holder_derivative_of_differenceQuotients Ω (Metric.ball x₀ ρ) hΩ hBΩ
    u hC1 k r hr K α (h k)
end SeifertSurfaces.QuasilinearProviderBridge
