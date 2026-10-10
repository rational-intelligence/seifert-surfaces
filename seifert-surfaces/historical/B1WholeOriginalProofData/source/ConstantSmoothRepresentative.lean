import WeakSmoothRepresentative
import ConstantLinearFactor

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace SeifertSurfaces.WeakSchauder

theorem linear_pullback_ae_eq (P : V ≃L[ℝ] V) (Ω : Set V) (f g : V → ℝ)
    (hfg : f =ᵐ[volume.restrict Ω] g) :
    (fun y => f (P y)) =ᵐ[volume.restrict (P ⁻¹' Ω)] (fun y => g (P y)) := by
  have hm : f =ᵐ[Measure.map P (volume.restrict (P ⁻¹' Ω))] g := by
    rw [linear_map_restrict_volume]
    exact Measure.ae_smul_measure hfg _
  exact (P.toHomeomorph.toMeasurableEquiv.measurableEmbedding.ae_map_iff
    (p := fun x => f x = g x)).mp hm

/-- Actual smooth interior representative of a constant-coefficient weak
solution, with the derivative identified a.e.; no pre-existing classical
second derivative is assumed. -/
theorem constant_solution_smooth_representative (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (h : V → ℝ) (hh : H1Witness h (Metric.ball center R))
    (hweak : WeakEquation (fun _ => A) hh) :
    ∃ h' : V → ℝ,
      h' =ᵐ[volume.restrict (Metric.ball center R)] h ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h' (Metric.ball center R) ∧
      (classicalGradient h' =ᵐ[volume.restrict (Metric.ball center R)] hh.weakGrad) := by
  obtain ⟨P, hP, -, -⟩ := constant_linear_factor center R κ Λ hR hκ hΛ A hA
  obtain ⟨hw, -, hwl⟩ := constant_equation_to_laplace center R hR A P hP h hh hweak
  obtain ⟨f, hae, hf, -⟩ := weak_laplace_smooth_representative
    (pulledBackBall P center R) (Metric.isOpen_ball.preimage P.continuous)
    (fun y => h (P y)) hw hwl
  let g : V → ℝ := fun x => f (P.symm x)
  have hset : P.symm ⁻¹' pulledBackBall P center R = Metric.ball center R := by
    ext x
    simp [pulledBackBall]
  have hgh : g =ᵐ[volume.restrict (Metric.ball center R)] h := by
    have he := linear_pullback_ae_eq P.symm (pulledBackBall P center R) f (fun y => h (P y)) hae
    simpa only [hset, P.apply_symm_apply] using he
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Metric.ball center R) := by
    apply hf.comp P.symm.contDiff.contDiffOn
    intro x hx
    change P (P.symm x) ∈ Metric.ball center R
    simpa using hx
  exact ⟨g, hgh, hg,
    classicalGradient_ae_eq_of_smooth_representative _ Metric.isOpen_ball h g hh hg hgh⟩

end SeifertSurfaces.WeakSchauder
