import CoefficientContinuity

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearLocalization
open SeifertSurfaces.AppendixACoordinates

namespace QuotientHelpers

lemma integral_unit_constant (c : ℝ) : (∫ t in Icc (0 : ℝ) 1, c) = c := by
  simp [setIntegral_const, measureReal_def]

lemma norm_unit_average_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (M : ℝ) (hf : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ M) :
    ‖∫ t in Icc (0 : ℝ) 1, f t‖ ≤ M := by
  simpa [measureReal_def] using norm_setIntegral_le_of_norm_le_const
    (μ := volume) (s := Icc (0 : ℝ) 1) isCompact_Icc.measure_lt_top hf

lemma coercive_unit_average (a : ℝ → E2 →L[ℝ] E2)
    (ha : IntegrableOn a (Icc (0 : ℝ) 1)) (κ : ℝ)
    (hκ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (a t ξ) ξ) :
    ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ ((∫ t in Icc (0 : ℝ) 1, a t) ξ) ξ := by
  intro ξ
  have happ : IntegrableOn (fun t => a t ξ) (Icc (0 : ℝ) 1) :=
    (ContinuousLinearMap.apply ℝ E2 ξ).integrable_comp ha
  have hinner : IntegrableOn (fun t => inner ℝ ξ (a t ξ)) (Icc (0 : ℝ) 1) :=
    ((InnerProductSpace.toDual ℝ E2) ξ).integrable_comp happ
  have hconst : IntegrableOn (fun _ : ℝ => κ * ‖ξ‖ ^ 2) (Icc (0 : ℝ) 1) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  rw [ContinuousLinearMap.integral_apply ha ξ, real_inner_comm,
    ← InnerProductSpace.toDual_apply_apply,
    ← ((InnerProductSpace.toDual ℝ E2) ξ).integral_comp_comm happ]
  change κ * ‖ξ‖ ^ 2 ≤ ∫ t in Icc (0 : ℝ) 1, inner ℝ ξ (a t ξ)
  calc
    κ * ‖ξ‖ ^ 2 = ∫ t in Icc (0 : ℝ) 1, κ * ‖ξ‖ ^ 2 := (integral_unit_constant _).symm
    _ ≤ ∫ t in Icc (0 : ℝ) 1, inner ℝ ξ (a t ξ) := by
      apply integral_mono_ae hconst hinner
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa [real_inner_comm] using hκ t ht ξ

end QuotientHelpers

theorem R2_uniform_coefficient_and_quotient_bounds
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (x₀ : E2) (r κ M : ℝ) (hr : 0 < r) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * r) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ r κ M T)
    (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hhr : |h| < r) :
    CoefficientBounds (Metric.ball x₀ (2 * r)) (averagedCoefficients Q u k h) κ M ∧
      ∀ x ∈ Metric.ball x₀ (2 * r), |differenceQuotient u k h x| ≤ M := by
  have hseg : ∀ x ∈ Metric.ball x₀ (2 * r), ∀ t ∈ Icc (0 : ℝ) 1,
      jetSegment u k h x t ∈ closure T := by
    intro x hx t ht
    exact subset_closure (QuotientHelpers.jetSegment_mem u x₀ r hr T hT hjetsT k h hhr x
      (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx) t ht)
  constructor
  · refine ⟨hbound.1, hbound.2.1, ?_, ?_⟩
    · intro x hx
      have hi := R2_segment_derivatives_integrable J hJ Q u k h x (fun t ht => hTJ (hseg x hx t ht))
      exact QuotientHelpers.coercive_unit_average _ hi.1 κ (fun t ht => hbound.2.2.2.2.2 _ (hseg x hx t ht))
    · intro x hx
      have hc := fun t ht => hbound.2.2.2.1 (jetSegment u k h x t) (hseg x hx t ht)
      have heA : ∀ t ∈ Icc (0 : ℝ) 1, ‖fluxDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
        intro t ht
        calc
          _ ≤ ‖fluxDx Q (jetSegment u k h x t)‖ * ‖coordinateVector 2 k‖ :=
            (fluxDx Q (jetSegment u k h x t)).le_opNorm _
          _ ≤ M := by simpa [QuotientHelpers.coordinate_norm] using (hc t ht).2.2.1
      have heB : ∀ t ∈ Icc (0 : ℝ) 1, ‖lowerDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
        intro t ht
        calc
          _ ≤ ‖lowerDx Q (jetSegment u k h x t)‖ * ‖coordinateVector 2 k‖ :=
            (lowerDx Q (jetSegment u k h x t)).le_opNorm _
          _ ≤ M := by simpa [QuotientHelpers.coordinate_norm] using (hc t ht).2.2.2.2.2.1
      exact ⟨QuotientHelpers.norm_unit_average_le _ M (fun t ht => (hc t ht).2.2.2.2.1),
        QuotientHelpers.norm_unit_average_le _ M (fun t ht => (hc t ht).2.2.2.1),
        QuotientHelpers.norm_unit_average_le _ M heA,
        QuotientHelpers.norm_unit_average_le _ M (fun t ht => (hc t ht).2.2.2.2.2.2.2),
        by simpa only [averagedCoefficients, Real.norm_eq_abs] using
          QuotientHelpers.norm_unit_average_le (fun t => lowerDz Q (jetSegment u k h x t)) M
            (fun t ht => by simpa only [Real.norm_eq_abs] using (hc t ht).2.2.2.2.2.2.1),
        by simpa only [averagedCoefficients, Real.norm_eq_abs] using QuotientHelpers.norm_unit_average_le _ M heB⟩
  · exact QuotientHelpers.quotient_bound Ω hΩ u hC1 x₀ r M hr hball
      (fun x hx => (hbound.2.2.1 x hx).2) k h hh hhr

end SeifertSurfaces.QuasilinearLocalization
