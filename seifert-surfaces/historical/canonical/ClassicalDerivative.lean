import WeakGradientBridge

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

theorem classical_derivative_of_continuous_weak_gradient
    (Ω : Set V) (hΩ : IsOpen Ω) (v : V → ℝ) (hv : H1Witness v Ω)
    (hcont : ContinuousOn v Ω) (G : V → V) (hGcont : ContinuousOn G Ω)
    (hGae : G =ᵐ[volume.restrict Ω] hv.weakGrad) :
    (∀ x ∈ Ω, HasFDerivAt v (innerSL ℝ (G x)) x) ∧ ContDiffOn ℝ 1 v Ω := by
  have hd : ∀ x ∈ Ω, HasFDerivAt v (innerSL ℝ (G x)) x :=
    continuous_weak_gradient_hasFDerivAt Ω hΩ v hv hcont G hGcont hGae
  refine ⟨hd, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
    contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  apply ((innerSL ℝ).continuous.comp_continuousOn hGcont).congr
  intro x hx
  exact (hd x hx).fderiv

end SeifertSurfaces.WeakSchauder
