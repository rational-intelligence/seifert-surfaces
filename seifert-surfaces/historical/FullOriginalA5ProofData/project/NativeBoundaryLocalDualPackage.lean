import NativeBoundaryDualCoefficientContinuity

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- All dual coefficient constants and measurability come from the original
closed-domain jet and the original smooth datum. -/
theorem C1QuasilinearDirichletSolution.local_native_normal_flux_coefficient_bounds
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r κ M : ℝ, 0 < r ∧ 0 < κ ∧ 1 ≤ M ∧
      Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      CoefficientBounds (Metric.ball c r ∩ {x : E2 | 0 < x 0})
        (nativeNormalFluxCoefficients ρ Q g u) κ M ∧
      CoefficientMeasurableOn (Metric.ball c r ∩ {x : E2 | 0 < x 0})
        (nativeNormalFluxCoefficients ρ Q g u) := by
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (Metric.isOpen_ball (x := (0 : E2)) (ε := ρ)) c hc.1
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hclosed : Metric.closedBall c r ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_ball (by dsimp [r]; linarith)).trans hball
  have hcompact := closedHalfDisc_isCompact ρ
  obtain ⟨G, hG⟩ := hcompact.exists_bound_of_continuousOn
    (continuousOn_planarGradientWithin_closedHalfDisc hρ hsolution.c1)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn
    (hsolution.continuous_boundary_coefficients hρ).2.1
  obtain ⟨hxD, hzD, hpD⟩ := hsolution.continuous_native_flux_slices hρ
  obtain ⟨Dx, hDx⟩ := hcompact.exists_bound_of_continuousOn hxD
  obtain ⟨Dz, hDz⟩ := hcompact.exists_bound_of_continuousOn hzD
  obtain ⟨Dp, hDp⟩ := hcompact.exists_bound_of_continuousOn hpD
  let M := 1 + |G| + |B| + |Dx| + |Dz| + |Dp|
  have hM : 1 ≤ M := by dsimp [M]; linarith [abs_nonneg G, abs_nonneg B, abs_nonneg Dx, abs_nonneg Dz, abs_nonneg Dp]
  have hM0 : 0 ≤ M := by linarith
  have hGM : G ≤ M := (le_abs_self G).trans (by dsimp [M]; linarith [abs_nonneg B, abs_nonneg Dx, abs_nonneg Dz, abs_nonneg Dp])
  have hBM : B ≤ M := (le_abs_self B).trans (by dsimp [M]; linarith [abs_nonneg G, abs_nonneg Dx, abs_nonneg Dz, abs_nonneg Dp])
  have hDxM : Dx ≤ M := (le_abs_self Dx).trans (by dsimp [M]; linarith [abs_nonneg G, abs_nonneg B, abs_nonneg Dz, abs_nonneg Dp])
  have hDzM : Dz ≤ M := (le_abs_self Dz).trans (by dsimp [M]; linarith [abs_nonneg G, abs_nonneg B, abs_nonneg Dx, abs_nonneg Dp])
  have hDpM : Dp ≤ M := (le_abs_self Dp).trans (by dsimp [M]; linarith [abs_nonneg G, abs_nonneg B, abs_nonneg Dx, abs_nonneg Dz])
  obtain ⟨D, hD⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (g.smooth_second_deriv_extension_on_ball.continuousOn.mono hclosed)
  obtain ⟨κ, hκ, hell⟩ := hsolution.uniformly_elliptic
  let κ' := κ / (2 * M ^ 2 + 1)
  let A := 4 * (M / ((κ / 2) ^ 2))
  let M' := max 1 (max A (A * (3 * M + 2 * M ^ 2) + D))
  have hκ' : 0 < κ' := by dsimp [κ']; positivity
  have hM' : 1 ≤ M' := le_max_left _ _
  have hAM : A ≤ M' := (le_max_left _ _).trans (le_max_right _ _)
  have hdM : A * (3 * M + 2 * M ^ 2) + D ≤ M' :=
    (le_max_right _ _).trans (le_max_right _ _)
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsub : U ⊆ closedHalfDisc ρ ∩ Metric.ball 0 ρ := by
    intro x hx
    have hb := hclosed (Metric.ball_subset_closedBall hx.1)
    exact ⟨⟨Metric.ball_subset_closedBall hb, show 0 ≤ x 0 from le_of_lt hx.2⟩, hb⟩
  have hb (x : E2) (hx : x ∈ U) := native_normal_flux_pointwise_dual_bounds ρ Q g u x κ M D hκ hM0
    (fun ξ => hell x (u x) (planarGradientWithin u (closedHalfDisc ρ) x) ξ
      (hsolution.attained_jets x (hsub hx).1))
    ((hDp x (hsub hx).1).trans hDpM) ((hG x (hsub hx).1).trans hGM)
    (by simpa only [Real.norm_eq_abs] using (hB x (hsub hx).1).trans hBM)
    ((hDx x (hsub hx).1).trans hDxM) ((hDz x (hsub hx).1).trans hDzM)
    (by simpa only [Real.norm_eq_abs] using hD x (Metric.ball_subset_closedBall hx.1))
  have hcont := hsolution.continuous_native_normal_flux_coefficients hρ
  refine ⟨r, κ', M', hr, hκ', hM', hclosed, ⟨hκ', hM', ?_, ?_⟩, ?_⟩
  · intro x hx ξ
    exact (hb x hx).1 ξ
  · intro x hx
    have hzero : 0 ≤ M' := by linarith
    refine ⟨(hb x hx).2.1.trans hAM, ?_, (hb x hx).2.2.trans hdM, ?_, ?_, ?_⟩ <;>
      simpa only [nativeNormalFluxCoefficients, Pi.zero_apply, norm_zero, abs_zero] using hzero
  · exact ⟨(hcont.1.mono hsub).aestronglyMeasurable hU.measurableSet,
      (hcont.2.1.mono hsub).aestronglyMeasurable hU.measurableSet,
      (hcont.2.2.1.mono hsub).aestronglyMeasurable hU.measurableSet,
      (hcont.2.2.2.1.mono hsub).aestronglyMeasurable hU.measurableSet,
      (hcont.2.2.2.2.1.mono hsub).aestronglyMeasurable hU.measurableSet,
      (hcont.2.2.2.2.2.mono hsub).aestronglyMeasurable hU.measurableSet⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
