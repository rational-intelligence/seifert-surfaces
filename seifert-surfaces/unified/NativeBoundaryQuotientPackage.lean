import NativeBoundaryCoefficientContinuity

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_quotient_bound_of_lipschitz
    {U : Set E2} {u : E2 → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u U)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0) {x : E2} (hx : x ∈ U)
    (hshift : shift k h x ∈ U) : |differenceQuotient u k h x| ≤ L := by
  have hd := hu.dist_le_mul (shift k h x) hshift x hx
  have hdist : dist (shift k h x) x = |h| := QuotientHelpers.shift_distance k h x
  rw [Real.dist_eq, hdist] at hd
  unfold differenceQuotient
  rw [abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hh)).mpr
  exact hd

/-- All inputs for the first tangential boundary gain, under the literal
starting solution hypotheses. The constants and convex tube precede every
quotient step. Every coefficient is the native segment average for Q and u. -/
theorem C1QuasilinearDirichletSolution.local_boundary_quotient_package
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x₀ : E2) (hx₀ : x₀ ∈ flatBoundary ρ) :
    ∃ r κ M : ℝ, ∃ L : ℝ≥0, ∃ T : Set Jet,
      0 < r ∧ 0 < κ ∧ 1 ≤ M ∧ IsOpen T ∧ Convex ℝ T ∧
      IsCompact (closure T) ∧ closure T ⊆ J ∧
      Metric.closedBall x₀ (4 * r) ⊆ Metric.ball 0 ρ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < r →
        let B := Metric.ball x₀ (2 * r) ∩ {x : E2 | 0 < x 0}
        ContDiffOn ℝ 1 (differenceQuotient u 1 h) B ∧
        LinearWeakEquation B (averagedCoefficients Q u 1 h)
          (differenceQuotient u 1 h) (planarGradient (differenceQuotient u 1 h)) ∧
        CoefficientBounds B (averagedCoefficients Q u 1 h) κ M ∧
        coefficientsContinuousOn B (averagedCoefficients Q u 1 h) ∧
        CoefficientMeasurableOn B (averagedCoefficients Q u 1 h) ∧
        (∀ x ∈ B, |differenceQuotient u 1 h x| ≤ L) := by
  obtain ⟨s, κ, M, T, hs, hTopen, hTconvex, hTcompact, hTJ,
    hjetsT, hκ, hM, _, hcoeff, _, hcoercive⟩ :=
      hsolution.local_boundary_jet_tube hρ x₀ (flatBoundary_subset_closedHalfDisc ρ hx₀)
  obtain ⟨δ, hδ, hδball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (Metric.isOpen_ball.mem_nhds hx₀.1)
  let r := min s (δ / 4)
  have hr : 0 < r := lt_min hs (div_pos hδ (by norm_num))
  have hrs : r ≤ s := min_le_left _ _
  have hrδ : 4 * r ≤ δ := by
    have h := min_le_right s (δ / 4)
    dsimp only [r]
    linarith
  have houter : Metric.closedBall x₀ (4 * r) ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall hrδ).trans hδball
  have hcapT : ∀ x ∈ Metric.closedBall x₀ (4 * r) ∩ closedHalfDisc ρ,
      firstJetWithin ρ u x ∈ T := by
    intro x hx
    exact hjetsT x ⟨Metric.closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  obtain ⟨L, hL⟩ := hsolution.lipschitz_on_closedHalfDisc hρ
  refine ⟨r, κ, M, L, T, hr, hκ, hM, hTopen, hTconvex, hTcompact, hTJ, houter, ?_⟩
  intro h hh hhr
  let B := Metric.ball x₀ (2 * r) ∩ {x : E2 | 0 < x 0}
  have hBopen : IsOpen B := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hBlarge : B ⊆ Metric.closedBall x₀ (4 * r) := by
    intro x hx
    exact Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hx.1)
  have hBΩ : B ⊆ openHalfDisc ρ := fun x hx => ⟨houter (hBlarge hx), hx.2⟩
  have hshiftlarge : ∀ x ∈ B, shift 1 h x ∈ Metric.closedBall x₀ (4 * r) := by
    intro x hx
    exact QuotientHelpers.shift_mem_closedBall x₀ x r hr
      (QuotientHelpers.ball_two_subset_closed_three x₀ r hr hx.1) 1 h hhr
  have hshiftΩ : MapsTo (shift 1 h) B (openHalfDisc ρ) := by
    intro x hx
    refine ⟨houter (hshiftlarge x hx), ?_⟩
    simpa only [mem_ofPred_eq, tangent_shift_normal] using hx.2
  have hjet0 : ∀ x ∈ B, firstJet u x ∈ T := by
    intro x hx
    have h0 := hcapT x ⟨hBlarge hx, openHalfDisc_subset_closedHalfDisc ρ (hBΩ hx)⟩
    simpa only [firstJetWithin_eq_firstJet u (hBΩ hx)] using h0
  have hjet1 : ∀ x ∈ B, firstJet u (shift 1 h x) ∈ T := by
    intro x hx
    have h1 := hcapT (shift 1 h x)
      ⟨hshiftlarge x hx, openHalfDisc_subset_closedHalfDisc ρ (hshiftΩ hx)⟩
    simpa only [firstJetWithin_eq_firstJet u (hshiftΩ hx)] using h1
  have hsegments : ∀ x ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, jetSegment u 1 h x t ∈ T := by
    intro x hx t ht
    apply hTconvex (hjet0 x hx) (hjet1 x hx) (by linarith [ht.2]) ht.1
    ring
  have hC1 := hsolution.c1.mono (openHalfDisc_subset_closedHalfDisc ρ)
  have hjets : ∀ x ∈ openHalfDisc ρ, firstJet u x ∈ J := by
    intro x hx
    have hj := hsolution.attained_jets x (openHalfDisc_subset_closedHalfDisc ρ hx)
    simpa only [firstJetWithin_eq_firstJet u hx] using hj
  have hlinear := native_linearized_quotient_equation_on (openHalfDisc ρ) B
    (openHalfDisc_isOpen ρ) hBopen J hsolution.jet_domain_open Q u hC1 hjets
    hsolution.weak_equation hBΩ 1 h hh hshiftΩ
    (fun x hx t ht => hTJ (subset_closure (hsegments x hx t ht)))
  have hbounds := native_average_coefficient_bounds_on B J hsolution.jet_domain_open Q u
    T hTJ κ M hκ hM 1 h (fun x hx t ht => subset_closure (hsegments x hx t ht))
    hcoeff hcoercive
  have hcontinuous := native_averaged_coefficients_continuousOn (openHalfDisc ρ) B
    (openHalfDisc_isOpen ρ) hBopen J hsolution.jet_domain_open Q u hC1 hBΩ 1 h hshiftΩ
    T hTJ (fun x hx t ht => subset_closure (hsegments x hx t ht)) M hcoeff
  refine ⟨hlinear.1, hlinear.2, hbounds, hcontinuous.1, hcontinuous.2, ?_⟩
  intro x hx
  exact native_quotient_bound_of_lipschitz hL 1 hh
    (openHalfDisc_subset_closedHalfDisc ρ (hBΩ hx))
    (openHalfDisc_subset_closedHalfDisc ρ (hshiftΩ hx))

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
