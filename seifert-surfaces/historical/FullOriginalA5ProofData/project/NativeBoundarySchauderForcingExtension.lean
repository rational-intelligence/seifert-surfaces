import NativeBoundaryCoefficientExtension

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- The true negative forcing in the tangential divergence equation has a
bounded global Holder extension. No forcing estimate is an input. -/
theorem C1QuasilinearDirichletSolution.local_global_holder_tangential_forcing_extension
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ H α : ℝ≥0, ∃ B : ℝ,
      0 < δ ∧ 0 < α ∧ α < 1 ∧ 0 ≤ B ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      ∃ e : E2 → E2,
        EqOn e (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d x)
          (nativeClosedBoundaryCap c δ) ∧
        HolderWith H α e ∧ ∀ x, ‖e x‖ ≤ B := by
  obtain ⟨δ, H, α, hδ, hα, hα1, hball, _, hd⟩ :=
    hsolution.local_holder_tangential_schauder_coefficients hρ c hc
  have hcompact : IsCompact (nativeClosedBoundaryCap c δ) :=
    (isCompact_closedBall c δ).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨B0, hB0⟩ := hcompact.exists_bound_of_continuousOn (hd.continuousOn hα)
  let B := max B0 0
  have hB : 0 ≤ B := le_max_right _ _
  have hn : HolderOnWith H α
      (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d x)
        (nativeClosedBoundaryCap c δ) := by
    intro x hx y hy
    simpa only [edist_neg_neg] using hd x hx y hy
  have hnb : ∀ x ∈ nativeClosedBoundaryCap c δ,
      ‖-(nativeTangentialSchauderCoefficients ρ Q g u).d x‖ ≤ B := by
    intro x hx
    rw [norm_neg]
    exact (hB0 x hx).trans (le_max_left _ _)
  obtain ⟨e, he, hh, hb⟩ := native_holder_field_extension_on_cap c δ hδ.le
    (by rw [hc.2]) _ H α B hn hnb
  exact ⟨δ, H, α, B, hδ, hα, hα1, hB, hball, e, he, hh, hb⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
