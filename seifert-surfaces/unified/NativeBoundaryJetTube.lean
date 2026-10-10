import NativeBoundaryPreliminaries

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The actual closed-domain jets admit a convex local tube with uniform bounds
on the coefficients and their first two derivatives. No modulus of continuity
of the solution's gradient is used or supplied. -/
theorem C1QuasilinearDirichletSolution.local_boundary_jet_tube
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (x₀ : E2) (hx₀ : x₀ ∈ closedHalfDisc ρ) :
    ∃ r κ M : ℝ, ∃ T : Set Jet,
      0 < r ∧ IsOpen T ∧ Convex ℝ T ∧ IsCompact (closure T) ∧ closure T ⊆ J ∧
      (∀ x ∈ Metric.closedBall x₀ (4 * r) ∩ closedHalfDisc ρ, firstJetWithin ρ u x ∈ T) ∧
      0 < κ ∧ 1 ≤ M ∧
      (∀ x ∈ closedHalfDisc ρ, |u x| ≤ M ∧
        ‖planarGradientWithin u (closedHalfDisc ρ) x‖ ≤ M) ∧
      (∀ j ∈ closure T, ‖Q.flux j‖ ≤ M ∧ |Q.lowerOrder j| ≤ M ∧
        ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
        ‖lowerDx Q j‖ ≤ M ∧ |lowerDz Q j| ≤ M ∧ ‖lowerDp Q j‖ ≤ M) ∧
      (∀ j ∈ closure T, ∀ m : ℕ, m ≤ 2 →
        ‖iteratedFDeriv ℝ m Q.flux j‖ ≤ M ∧
        ‖iteratedFDeriv ℝ m Q.lowerOrder j‖ ≤ M) ∧
      (∀ j ∈ closure T, ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (fluxDp Q j ξ) ξ) := by
  have hjet := continuousOn_firstJetWithin hρ hsolution.c1
  obtain ⟨ε, hε, hεJ⟩ := Metric.isOpen_iff.mp hsolution.jet_domain_open
    (firstJetWithin ρ u x₀) (hsolution.attained_jets x₀ hx₀)
  let T := Metric.ball (firstJetWithin ρ u x₀) (ε / 2)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hclosure : closure T = Metric.closedBall (firstJetWithin ρ u x₀) (ε / 2) :=
    closure_ball _ hε2.ne'
  have hTcompact : IsCompact (closure T) := by
    rw [hclosure]
    exact isCompact_closedBall _ _
  have hTJ : closure T ⊆ J := by
    rw [hclosure]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεJ
  have hpre : firstJetWithin ρ u ⁻¹' T ∈ 𝓝[closedHalfDisc ρ] x₀ :=
    (hjet x₀ hx₀) (Metric.ball_mem_nhds _ hε2)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let r := δ / 8
  have hr : 0 < r := div_pos hδ (by norm_num)
  have h4r : 4 * r < δ := by dsimp [r]; linarith
  have hjetT : ∀ x ∈ Metric.closedBall x₀ (4 * r) ∩ closedHalfDisc ρ,
      firstJetWithin ρ u x ∈ T := by
    intro x hx
    exact hδsub ⟨Metric.closedBall_subset_ball h4r hx.1, hx.2⟩
  obtain ⟨κ, hκ, hcoercive⟩ := hsolution.uniformly_elliptic
  obtain ⟨U, hU⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    hsolution.c1.continuousOn
  obtain ⟨G, hG⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    (continuousOn_planarGradientWithin_closedHalfDisc hρ hsolution.c1)
  obtain ⟨A, hA⟩ := Helpers.compact_C2_bounds J (closure T) hsolution.jet_domain_open
    hTcompact hTJ Q.flux Q.flux_smooth
  obtain ⟨B, hB⟩ := Helpers.compact_C2_bounds J (closure T) hsolution.jet_domain_open
    hTcompact hTJ Q.lowerOrder Q.lowerOrder_smooth
  let M := max 1 (max U (max G (max A B)))
  have h1M : 1 ≤ M := le_max_left _ _
  have hUM : U ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hGM : G ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAM : A ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hBM : B ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨r, κ, M, T, hr, Metric.isOpen_ball, convex_ball _ _, hTcompact,
    hTJ, hjetT, hκ, h1M, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨by simpa only [Real.norm_eq_abs] using (hU x hx).trans hUM,
      (hG x hx).trans hGM⟩
  · intro j hj
    have hAf := (Q.flux_smooth.contDiffAt
      (hsolution.jet_domain_open.mem_nhds (hTJ hj))).differentiableAt (by simp)
    have hBf := (Q.lowerOrder_smooth.contDiffAt
      (hsolution.jet_domain_open.mem_nhds (hTJ hj))).differentiableAt (by simp)
    have ha := (hA j hj).2.1.trans hAM
    have hb := (hB j hj).2.1.trans hBM
    refine ⟨(hA j hj).1.trans hAM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Real.norm_eq_abs] using (hB j hj).1.trans hBM
    · exact (Helpers.norm_fderiv_x_slice_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_z_slice_one_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_p_slice_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_x_slice_le Q.lowerOrder j hBf).trans hb
    · simpa only [Real.norm_eq_abs, lowerDz] using
        (Helpers.norm_fderiv_z_slice_one_le Q.lowerOrder j hBf).trans hb
    · exact (Helpers.norm_fderiv_p_slice_le Q.lowerOrder j hBf).trans hb
  · intro j hj m hm
    exact ⟨((hA j hj).2.2 m hm).trans hAM, ((hB j hj).2.2 m hm).trans hBM⟩
  · intro j hj ξ
    exact hcoercive j.1 j.2.1 j.2.2 ξ (hTJ hj)

theorem C1QuasilinearDirichletSolution.lipschitz_on_closedHalfDisc
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ∃ L : ℝ≥0, LipschitzOnWith L u (closedHalfDisc ρ) := by
  obtain ⟨B, hB⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    (hsolution.c1.continuousOn_fderivWithin (closedHalfDisc_uniqueDiffOn hρ) (by norm_num))
  refine ⟨Real.toNNReal (max 0 B), ?_⟩
  apply (closedHalfDisc_convex ρ).lipschitzOnWith_of_nnnorm_fderivWithin_le
    (hsolution.c1.differentiableOn (by norm_num))
  intro x hx
  change ‖fderivWithin ℝ u (closedHalfDisc ρ) x‖ ≤ (Real.toNNReal (max 0 B) : ℝ)
  rw [Real.coe_toNNReal _ (le_max_left _ _)]
  exact (hB x hx).trans (le_max_right _ _)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
