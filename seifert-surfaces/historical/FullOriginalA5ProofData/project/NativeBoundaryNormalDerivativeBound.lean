import NativeBoundaryNormalInversion

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_within_gradient_component (ρ : ℝ) (u : E2 → ℝ) (x : E2) (i : Fin 2) :
    planarGradientWithin u (closedHalfDisc ρ) x i =
      fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i) := by
  fin_cases i <;> simp [planarGradientWithin, coordinateVector, Fin.sum_univ_two]

/-- The quantitative inversion bound is obtained on the actual local jet
tube of the original solution, including the flat edge. -/
theorem C1QuasilinearDirichletSolution.local_normal_derivative_difference_bound
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r κ M : ℝ, ∃ L : ℝ≥0,
      0 < r ∧ 0 < κ ∧ 1 ≤ M ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ∀ x ∈ Metric.closedBall c r ∩ {x : E2 | 0 ≤ x 0},
      ∀ y ∈ Metric.closedBall c r ∩ {x : E2 | 0 ≤ x 0},
        κ * |fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0) -
          fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0)| ≤
        |Q.flux (firstJetWithin ρ u y) 0 - Q.flux (firstJetWithin ρ u x) 0| +
          M * (((L : ℝ) + 1) * dist x y +
            |fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) -
              fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)|) := by
  have hcc : c ∈ closedHalfDisc ρ := flatBoundary_subset_closedHalfDisc ρ hc
  obtain ⟨t, κ, M, T, ht, hTop, hTconv, hTcompact, hTJ, hjets, hκ, hM,
    hvalue, hcoeff, hiter, hcoercive⟩ := hsolution.local_boundary_jet_tube hρ c hcc
  obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball c hc.1
  let r := min t (s / 2)
  have hr : 0 < r := lt_min ht (half_pos hs)
  have hrt : r ≤ t := min_le_left _ _
  have hclosed : Metric.closedBall c r ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith : s / 2 < s))).trans hball
  obtain ⟨L, hL⟩ := hsolution.lipschitz_on_closedHalfDisc hρ
  refine ⟨r, κ, M, L, hr, hκ, hM, hclosed, ?_⟩
  intro x hx y hy
  have hxρ : x ∈ closedHalfDisc ρ := ⟨Metric.ball_subset_closedBall (hclosed hx.1), hx.2⟩
  have hyρ : y ∈ closedHalfDisc ρ := ⟨Metric.ball_subset_closedBall (hclosed hy.1), hy.2⟩
  have hxT : firstJetWithin ρ u x ∈ T := hjets x
    ⟨Metric.closedBall_subset_closedBall (by linarith : r ≤ 4 * t) hx.1, hxρ⟩
  have hyT : firstJetWithin ρ u y ∈ T := hjets y
    ⟨Metric.closedBall_subset_closedBall (by linarith : r ≤ 4 * t) hy.1, hyρ⟩
  have hsegmentsT (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      (1 - a) • firstJetWithin ρ u x + a • firstJetWithin ρ u y ∈ T :=
    hTconv hxT hyT (by linarith [ha.2]) ha.1 (by ring)
  have hsegments := fun a ha => hTJ (subset_closure (hsegmentsT a ha))
  have hbound (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
      let j := (1 - a) • firstJetWithin ρ u x + a • firstJetWithin ρ u y
      ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
        κ ≤ (fluxDp Q j (coordinateVector 2 0)) 0 := by
    let j := (1 - a) • firstJetWithin ρ u x + a • firstJetWithin ρ u y
    have hj : j ∈ closure T := subset_closure (hsegmentsT a ha)
    refine ⟨(hcoeff j hj).2.2.1, (hcoeff j hj).2.2.2.1, (hcoeff j hj).2.2.2.2.1, ?_⟩
    simpa [coordinateVector, PiLp.norm_single, PiLp.inner_apply, Fin.sum_univ_two] using
      hcoercive j hj (coordinateVector 2 0)
  have hh := native_normal_gradient_from_flux_difference J hsolution.jet_domain_open Q
    (firstJetWithin ρ u x) (firstJetWithin ρ u y) κ M hκ (by linarith) hsegments hbound
  simp only [firstJetWithin, native_within_gradient_component] at hh
  have hux : |u y - u x| ≤ (L : ℝ) * dist x y := by
    simpa only [Real.dist_eq, dist_comm y x] using hL.dist_le_mul y hyρ x hxρ
  calc
    _ ≤ |Q.flux (firstJetWithin ρ u y) 0 - Q.flux (firstJetWithin ρ u x) 0| +
        M * (dist x y + |u y - u x| +
          |fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) -
            fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)|) := by
      simpa only [firstJetWithin, native_within_gradient_component, dist_eq_norm, norm_sub_rev] using hh
    _ ≤ _ := by gcongr; linarith

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
