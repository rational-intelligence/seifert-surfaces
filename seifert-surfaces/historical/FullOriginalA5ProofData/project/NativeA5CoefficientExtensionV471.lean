import NativeBoundaryCoefficientExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Original caller: actual principal matrix from the original solution has a
global Holder extension agreeing on its literal local native closed cap. All
local radii, bounds, coercivity, and Holder data are conclusions. -/
theorem C1QuasilinearDirichletSolution.local_global_holder_principal_extension
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ H α : ℝ≥0, ∃ κ M : ℝ,
      0 < δ ∧ 0 < α ∧ α < 1 ∧ 0 < κ ∧ 0 < M ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ∃ A : E2 → Matrix (Fin 2) (Fin 2) ℝ,
        EqOn A (nativePrincipalWithin ρ Q u) (nativeClosedBoundaryCap c δ) ∧
        (∀ i j, HolderWith H α (fun x => A x i j)) ∧
        (∀ x : E2, ∀ ξ : E2,
          κ * ‖ξ‖ ^ 2 ≤ inner ℝ
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (A x) ξ) ξ ∧
          ∀ i j, |A x i j| ≤ M) := by
  obtain ⟨δ, H, α, hδ, hα, hα1, hball, hholder, _⟩ :=
    hsolution.local_holder_principal_source hρ c hc
  obtain ⟨κ, hκ, hell⟩ := hsolution.uniformly_elliptic
  obtain ⟨B, hB⟩ := (closedHalfDisc_isCompact ρ).exists_bound_of_continuousOn
    (hsolution.continuous_native_flux_slices hρ).2.2
  let M := max B 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hcap : nativeClosedBoundaryCap c δ ⊆ closedHalfDisc ρ := by
    intro x hx
    exact ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  have hbound : ∀ x ∈ nativeClosedBoundaryCap c δ, ∀ ξ : E2,
      κ * ‖ξ‖ ^ 2 ≤ inner ℝ
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) (nativePrincipalWithin ρ Q u x) ξ) ξ ∧
      ∀ i j, |nativePrincipalWithin ρ Q u x i j| ≤ M := by
    intro x hx ξ
    refine ⟨?_, ?_⟩
    · rw [native_principalWithin_toEuclideanCLM]
      exact hell x (u x) (planarGradientWithin u (closedHalfDisc ρ) x) ξ
        (hsolution.attained_jets x (hcap hx))
    · intro i j
      calc
        _ ≤ ‖fluxDp Q (firstJetWithin ρ u x) (coordinateVector 2 j)‖ :=
          PiLp.norm_apply_le _ i (p := 2)
        _ ≤ ‖fluxDp Q (firstJetWithin ρ u x)‖ * ‖coordinateVector 2 j‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ M := by
          rw [QuotientHelpers.coordinate_norm, mul_one]
          exact (hB x (hcap hx)).trans (le_max_left _ _)
  obtain ⟨A, heq, hAholder, hAbound⟩ := native_holder_matrix_extension_on_cap
    c δ hδ.le (by change 0 ≤ c 0; exact hc.2.ge) (nativePrincipalWithin ρ Q u)
    H α κ M hholder hbound
  exact ⟨δ, H, α, κ, M, hδ, hα, hα1, hκ, hM, hball, A, heq, hAholder, hAbound⟩


end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
