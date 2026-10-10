import NativeBoundaryWeakQuotients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The exact averaged linearized equation on a genuine one-sided domain.
There is no full-ball premise across the flat boundary and no assumption
that the solution is smooth beyond its starting C1 state. -/
theorem native_linearized_quotient_equation_on
    (Ω B : Set E2) (hΩ : IsOpen Ω) (hB : IsOpen B)
    (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (hBΩ : B ⊆ Ω) (k : Fin 2) (h : ℝ) (hh : h ≠ 0)
    (hshiftΩ : MapsTo (shift k h) B Ω)
    (hsegments : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ J) :
    ContDiffOn ℝ 1 (differenceQuotient u k h) B ∧
      LinearWeakEquation B (averagedCoefficients Q u k h)
        (differenceQuotient u k h) (planarGradient (differenceQuotient u k h)) := by
  have hs : ContDiff ℝ 1 (shift k h) := by unfold shift; fun_prop
  have huc := (hC1.comp hs.contDiffOn hshiftΩ).sub (hC1.mono hBΩ)
  have heq : differenceQuotient u k h = h⁻¹ • (u ∘ shift k h - u) := by
    funext x
    simp [differenceQuotient, div_eq_mul_inv, mul_comm]
  have hflux : ∀ x ∈ B,
      linearizedFlux (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x =
          h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)) := by
    intro x hx
    simpa [linearizedFlux, R2_differenceQuotient_gradient Ω hΩ u hC1 k h hh x
      (hBΩ hx) (hshiftΩ hx)] using
        (R2_segment_flux_and_source_identity J hJ Q u k h hh x (hsegments x hx)).1.symm
  have hsource : ∀ x ∈ B,
      linearizedSource (averagedCoefficients Q u k h) (differenceQuotient u k h)
        (planarGradient (differenceQuotient u k h)) x =
          (Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h := by
    intro x hx
    simpa [linearizedSource, R2_differenceQuotient_gradient Ω hΩ u hC1 k h hh x
      (hBΩ hx) (hshiftΩ hx)] using
        (R2_segment_flux_and_source_identity J hJ Q u k h hh x (hsegments x hx)).2.symm
  refine ⟨by rw [heq]; exact huc.const_smul h⁻¹, ?_⟩
  intro φ hφ hsupp hsub
  have hw := native_difference_weak_identity_on Ω B hΩ J Q u hC1 hjets hweak hBΩ
    k h hshiftΩ φ hφ hsupp hsub
  refine ⟨hw.1.congr_fun (fun x hx => by rw [hflux x hx]) hB.measurableSet,
    hw.2.1.congr_fun (fun x hx => by rw [hsource x hx]) hB.measurableSet, ?_⟩
  calc
    _ = ∫ x in B, inner ℝ
      (h⁻¹ • (Q.flux (firstJet u (shift k h x)) - Q.flux (firstJet u x)))
      (planarGradient φ x) -
      ((Q.lowerOrder (firstJet u (shift k h x)) - Q.lowerOrder (firstJet u x)) / h) * φ x := by
        apply setIntegral_congr_fun hB.measurableSet
        intro x hx
        dsimp only
        rw [hflux x hx, hsource x hx]
    _ = 0 := hw.2.2

/-- Bounds for all six actual averaged coefficients, uniform in the quotient
step. The compact tube and its bounds are constructed from the original C1
boundary state in `local_boundary_jet_tube`. -/
theorem native_average_coefficient_bounds_on
    (B : Set E2) (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (T : Set Jet) (hTJ : closure T ⊆ J)
    (κ M : ℝ) (hκ : 0 < κ) (hM : 1 ≤ M) (k : Fin 2) (h : ℝ)
    (hsegments : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u k h x t ∈ closure T)
    (hcoefficients : ∀ j ∈ closure T, ‖Q.flux j‖ ≤ M ∧ |Q.lowerOrder j| ≤ M ∧
      ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
      ‖lowerDx Q j‖ ≤ M ∧ |lowerDz Q j| ≤ M ∧ ‖lowerDp Q j‖ ≤ M)
    (hcoercive : ∀ j ∈ closure T, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ (fluxDp Q j ξ) ξ) :
    CoefficientBounds B (averagedCoefficients Q u k h) κ M := by
  refine ⟨hκ, hM, ?_, ?_⟩
  · intro x hx
    have hi := R2_segment_derivatives_integrable J hJ Q u k h x
      (fun t ht => hTJ (hsegments x hx t ht))
    exact QuotientHelpers.coercive_unit_average _ hi.1 κ
      (fun t ht => hcoercive _ (hsegments x hx t ht))
  · intro x hx
    have hc := fun t ht => hcoefficients (jetSegment u k h x t) (hsegments x hx t ht)
    have heA : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fluxDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
      intro t ht
      calc
        _ ≤ ‖fluxDx Q (jetSegment u k h x t)‖ * ‖coordinateVector 2 k‖ :=
          (fluxDx Q (jetSegment u k h x t)).le_opNorm _
        _ ≤ M := by simpa [QuotientHelpers.coordinate_norm] using (hc t ht).2.2.1
    have heB : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖lowerDx Q (jetSegment u k h x t) (coordinateVector 2 k)‖ ≤ M := by
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
      by simpa only [averagedCoefficients, Real.norm_eq_abs] using
        QuotientHelpers.norm_unit_average_le _ M heB⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
