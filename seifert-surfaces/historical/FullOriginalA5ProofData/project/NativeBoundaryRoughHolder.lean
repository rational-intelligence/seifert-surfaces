import NativeBoundaryUniformHolder
import RoughTestExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

/-- Full-ball Hölder gain for a continuous actual H1 solution. No C1
regularity of its even reflection is required. -/
theorem uniform_holder_native_continuous_sobolev_linear_solutions
    (ρ κ M L : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ δ < ρ ∧ 0 < α ∧ α < 1 ∧
      ∀ (C : LinearizedCoefficients) (v : E2 → ℝ),
        ContinuousOn v (Metric.ball 0 ρ) →
        CoefficientBounds (Metric.ball 0 ρ) C κ M →
        CoefficientMeasurableOn (Metric.ball 0 ρ) C →
        (∀ x ∈ Metric.ball 0 ρ, |v x| ≤ L) →
        ∀ hsol : DeGiorgi.MemW1pWitness 2 v (Metric.ball 0 ρ),
          LinearWeakEquation (Metric.ball 0 ρ) C v hsol.weakGrad →
          HolderOnWith K α v (Metric.closedBall 0 δ) := by
  let r := ρ / 4
  let R := min r (1 / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := lt_min hr (by norm_num)
  have hRr : R ≤ r := min_le_left _ _
  have hR1 : R ≤ 1 / 2 := min_le_right _ _
  let center : E3 := liftedPoint (0 : E2) 0
  let S := Real.sqrt ((L + 1) ^ 2 * volume.real (Metric.ball center R))
  obtain ⟨K, α, hα, hα1, he⟩ := R3_uniform_holder_actual_homogeneous_solutions
    center R (liftLambda κ M L) S hR
    (by unfold liftLambda; exact one_le_pow₀ (le_max_left (1 : ℝ) _)) (Real.sqrt_nonneg _)
  let δ := R / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ < ρ := by dsimp [δ, r] at *; linarith
  refine ⟨δ, K, α, hδ, hδρ, hα, hα1, ?_⟩
  intro C v hv hb hm hvalue hsol hw
  let B := Metric.ball (0 : E2) (2 * r)
  have hBO : B ⊆ Metric.ball (0 : E2) ρ := Metric.ball_subset_ball (by dsimp [r]; linarith)
  let hBsol := hsol.restrict Metric.isOpen_ball hBO
  have hboundB : CoefficientBounds B C κ M :=
    ⟨hb.1, hb.2.1, fun x hx => hb.2.2.1 x (hBO hx), fun x hx => hb.2.2.2 x (hBO hx)⟩
  have hmeasB : CoefficientMeasurableOn B C :=
    ⟨hm.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm.2.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm.2.2.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm.2.2.2.2.2.mono_measure (Measure.restrict_mono hBO le_rfl)⟩
  have hweakB : LinearWeakEquation B C v hBsol.weakGrad :=
    native_linear_weak_restrict (Metric.ball 0 ρ) B Metric.isOpen_ball hBO C v hsol.weakGrad hw
  have hprovider : ProviderLinearWeakEquation B C v :=
    EnergyHelpers.rough_smooth_tests_extend_to_H01 B Metric.isOpen_ball Metric.isBounded_ball
      C v κ M hboundB hmeasB hBsol hweakB
  have hvbound : ∀ x ∈ B, |v x| ≤ L := fun x hx => hvalue x (hBO hx)
  have hball3 : Metric.ball center R ⊆ cylinder B := HolderAssembly.ball_in_cylinder 0 hr hRr hR1
  obtain ⟨A, hΛA, _, _, hhomogeneous, _⟩ := R3_lift_homogeneous_on_ball B Metric.isOpen_ball
    Metric.isBounded_ball C v κ M L hκ hM hL hmeasB hboundB hvbound hprovider center R hR hball3
  have hcont : ContinuousOn (liftFunction v) (Metric.ball center R) :=
    (HolderAssembly.lift_continuous B v (hv.mono hBO)).mono hball3
  have hL2 : (∫ y in Metric.ball center R, |liftFunction v y| ^ (2 : ℕ)) ≤ S ^ 2 :=
    (HolderAssembly.lift_l2_bound B v hL hvbound center R hball3).trans_eq
      (Real.sq_sqrt (by positivity)).symm
  have hholder := HolderAssembly.holder_on_slice_ball 0 (R / 2) v K α
    (he A (liftFunction v) hΛA.le hcont hhomogeneous hL2)
  exact hholder.mono (Metric.closedBall_subset_ball (by dsimp [δ]; linarith))

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
