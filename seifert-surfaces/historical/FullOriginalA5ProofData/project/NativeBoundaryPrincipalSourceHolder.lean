import NativeBoundaryJetHolder
import NativeBoundarySmoothJetCoefficients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap

/-- Principal and source Holder bounds use the same actual within jets and
one positive exponent; both are conclusions from the original solution. -/
theorem C1QuasilinearDirichletSolution.local_holder_principal_source
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      (∀ i j : Fin 2, HolderOnWith K α (fun x => nativePrincipalWithin ρ Q u x i j)
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0})) ∧
      HolderOnWith K α (nativeClassicalSourceWithin ρ Q u)
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δ, K, α, hδ, hα, hα1, hball, hH⟩ := hsolution.local_holder_jet_composition hρ c hc
    (fun j : Jet => (fluxDp Q j, nativeClassicalSourceJet Q j))
    ((native_principal_source_jet_smooth J hsolution.jet_domain_open Q).of_le (by simp))
  refine ⟨δ, K, α, hδ, hα, hα1, hball, ?_, ?_⟩
  · intro i j
    apply native_holder_of_real_distance_bound
    intro x hx y hy
    have hdiff := hH.dist_le hx hy
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hdiff
    have hp : ‖fluxDp Q (firstJetWithin ρ u x) - fluxDp Q (firstJetWithin ρ u y)‖ ≤
        (K : ℝ) * dist x y ^ (α : ℝ) := (le_max_left _ _).trans hdiff
    calc
      |nativePrincipalWithin ρ Q u x i j - nativePrincipalWithin ρ Q u y i j| =
          ‖((fluxDp Q (firstJetWithin ρ u x) - fluxDp Q (firstJetWithin ρ u y))
            (coordinateVector 2 j)) i‖ := by
        simp only [nativePrincipalWithin, ContinuousLinearMap.sub_apply, PiLp.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖(fluxDp Q (firstJetWithin ρ u x) - fluxDp Q (firstJetWithin ρ u y))
          (coordinateVector 2 j)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fluxDp Q (firstJetWithin ρ u x) - fluxDp Q (firstJetWithin ρ u y)‖ := by
        simpa only [QuotientHelpers.coordinate_norm, mul_one] using
          (fluxDp Q (firstJetWithin ρ u x) - fluxDp Q (firstJetWithin ρ u y)).le_opNorm (coordinateVector 2 j)
      _ ≤ _ := hp
  · apply native_holder_of_real_distance_bound
    intro x hx y hy
    have hdiff := hH.dist_le hx hy
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub] at hdiff
    simpa only [nativeClassicalSourceWithin, Real.norm_eq_abs, dist_eq_norm] using (le_max_right _ _).trans hdiff

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
