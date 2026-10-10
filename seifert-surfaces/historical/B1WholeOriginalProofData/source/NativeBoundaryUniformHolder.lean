import NativeBoundaryReflectedMeasurability
import HolderQuotients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_linear_weak_restrict
    (Ω B : Set E2) (hB : IsOpen B) (hsub : B ⊆ Ω)
    (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2)
    (hw : LinearWeakEquation Ω C v G) : LinearWeakEquation B C v G := by
  intro φ hs hc ht
  obtain ⟨hiF, hiS, heq⟩ := hw φ hs hc (ht.trans hsub)
  refine ⟨hiF.mono_set hsub, hiS.mono_set hsub, ?_⟩
  have hz : ∀ x, x ∉ B → inner ℝ (linearizedFlux C v G x) (planarGradient φ x) -
      linearizedSource C v G x * φ x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ := fun hh => hx (ht hh)
    simp [Helpers.gradient_zero_off_tsupport φ hx', image_eq_zero_of_notMem_tsupport hx']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hz x (fun hb => hx (hsub hb)))] at heq
  exact heq

/-- Uniform boundary Hölder estimate for actual C1 zero-Dirichlet linear
solutions. Constants precede every coefficient/solution datum. No modulus
of continuity of the principal coefficients is assumed. -/
theorem uniform_holder_native_zero_trace_linear_solutions
    (ρ κ M L : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ) (hM : 1 ≤ M) (hL : 0 ≤ L) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ δ < ρ ∧ 0 < α ∧ α < 1 ∧
      ∀ (C : LinearizedCoefficients) (v : E2 → ℝ),
        ContDiffOn ℝ 1 v (closedHalfDisc ρ) →
        (∀ x ∈ flatBoundary ρ, v x = 0) →
        CoefficientBounds (openHalfDisc ρ) C κ M →
        CoefficientMeasurableOn (openHalfDisc ρ) C →
        LinearWeakEquation (openHalfDisc ρ) C v (planarGradient v) →
        (∀ x ∈ closedHalfDisc ρ, |v x| ≤ L) →
        HolderOnWith K α v (closedHalfDisc δ) := by
  let r := ρ / 4
  let R := min r (1 / 2)
  let M' := M + κ
  have hr : 0 < r := by dsimp [r]; positivity
  have hR : 0 < R := lt_min hr (by norm_num)
  have hRr : R ≤ r := min_le_left _ _
  have hR1 : R ≤ 1 / 2 := min_le_right _ _
  have hM' : 1 ≤ M' := by dsimp [M']; linarith
  let center : E3 := liftedPoint (0 : E2) 0
  let S := Real.sqrt ((L + 1) ^ 2 * volume.real (Metric.ball center R))
  obtain ⟨K, α, hα, hα1, he⟩ := R3_uniform_holder_actual_homogeneous_solutions
    center R (liftLambda κ M' L) S hR
    (by unfold liftLambda; exact one_le_pow₀ (le_max_left (1 : ℝ) _)) (Real.sqrt_nonneg _)
  let δ := R / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ < ρ := by dsimp [δ, r] at *; linarith
  refine ⟨δ, K, α, hδ, hδρ, hα, hα1, ?_⟩
  intro C v hv hz hb hm hw hvalue
  let w := nativeOddExtension v
  let C' := reflectLinearizedCoefficients C κ
  obtain ⟨hwC1, hb', hw'⟩ := native_c1_zero_trace_reflected_linear_equation ρ κ M hρ C v hv hz hb hm hw
  have hm' := native_reflected_coefficients_measurable 0 (by simp) ρ κ C hm
  let B := Metric.ball (0 : E2) (2 * r)
  have hBO : B ⊆ Metric.ball (0 : E2) ρ := Metric.ball_subset_ball (by dsimp [r]; linarith)
  have hC1B : ContDiffOn ℝ 1 w B := hwC1.mono hBO
  have hboundB : CoefficientBounds B C' κ M' :=
    ⟨hb'.1, hb'.2.1, fun x hx => hb'.2.2.1 x (hBO hx), fun x hx => hb'.2.2.2 x (hBO hx)⟩
  have hmeasB : CoefficientMeasurableOn B C' :=
    ⟨hm'.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm'.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm'.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm'.2.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm'.2.2.2.2.1.mono_measure (Measure.restrict_mono hBO le_rfl),
      hm'.2.2.2.2.2.mono_measure (Measure.restrict_mono hBO le_rfl)⟩
  have hweakB := native_linear_weak_restrict (Metric.ball 0 ρ) B Metric.isOpen_ball hBO
    C' w (planarGradient w) hw'
  have hclosed : Metric.closedBall (0 : E2) (2 * r) ⊆ Metric.ball 0 ρ :=
    Metric.closedBall_subset_ball (by dsimp [r]; linarith)
  have hmem : DeGiorgi.MemW1p 2 w B :=
    (R1_C1_memW1p_on_ball (Metric.ball 0 ρ) Metric.isOpen_ball w hwC1 0 (2 * r)
      (by positivity) hclosed).1
  have hprovider : ProviderLinearWeakEquation B C' w :=
    R2_smooth_tests_extend_to_H01 B Metric.isOpen_ball Metric.isBounded_ball C' w hC1B
      κ M' hboundB hmeasB hmem hweakB
  have hwbound : ∀ x ∈ B, |w x| ≤ L := by
    intro x hx
    have hxO := hBO hx
    by_cases hn : 0 ≤ x 0
    · have hh := hvalue x ⟨Metric.ball_subset_closedBall hxO, hn⟩
      simpa only [w, nativeOddExtension, ite_eq_left hn] using hh
    · have hxR : normalReflection x ∈ closedHalfDisc ρ := by
        refine ⟨Metric.ball_subset_closedBall (normalReflection_maps_ball ρ hxO), ?_⟩
        change 0 ≤ normalReflection x 0
        rw [normalReflection_zero]
        linarith [not_le.mp hn]
      simpa only [w, nativeOddExtension, ite_eq_right hn, abs_neg] using hvalue _ hxR
  have hball3 : Metric.ball center R ⊆ cylinder B := HolderAssembly.ball_in_cylinder 0 hr hRr hR1
  obtain ⟨A, hΛA, _, _, hhomogeneous, _⟩ := R3_lift_homogeneous_on_ball B Metric.isOpen_ball
    Metric.isBounded_ball C' w κ M' L hκ hM' hL hmeasB hboundB hwbound hprovider center R hR hball3
  have hcont : ContinuousOn (liftFunction w) (Metric.ball center R) :=
    (HolderAssembly.lift_continuous B w hC1B.continuousOn).mono hball3
  have hL2 : (∫ y in Metric.ball center R, |liftFunction w y| ^ (2 : ℕ)) ≤ S ^ 2 := by
    exact (HolderAssembly.lift_l2_bound B w hL hwbound center R hball3).trans_eq
      (Real.sq_sqrt (by positivity)).symm
  have hholder := HolderAssembly.holder_on_slice_ball 0 (R / 2) w K α
    (he A (liftFunction w) hΛA.le hcont hhomogeneous hL2)
  have hsmall : closedHalfDisc δ ⊆ Metric.ball (0 : E2) (R / 2) := by
    intro x hx
    exact Metric.closedBall_subset_ball (by dsimp [δ]; linarith) hx.1
  intro x hx y hy
  have hh := hholder x (hsmall hx) y (hsmall hy)
  have hxpos : 0 ≤ x 0 := hx.2
  have hypos : 0 ≤ y 0 := hy.2
  simpa only [w, nativeOddExtension, ite_eq_left hxpos, ite_eq_left hypos] using hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
