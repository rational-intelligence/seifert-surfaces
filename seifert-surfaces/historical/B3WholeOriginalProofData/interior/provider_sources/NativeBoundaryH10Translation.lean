import NativeBoundaryH10WeakTesting
import NativeTranslation

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

theorem native_h10_translation
    (U : Set E2) (hU : MeasurableSet U) (c : E2)
    (v : E2 → ℝ) (G : E2 → E2) (hv : H10On U v G) :
    H10On ((fun x : E2 => x + c) ⁻¹' U) (fun x => v (x + c)) (fun x => G (x + c)) := by
  let W := (fun x : E2 => x + c) ⁻¹' U
  have hmp : MeasurePreserving (fun x : E2 => x + c) (volume.restrict W) (volume.restrict U) :=
    (measurePreserving_add_right volume c).restrict_preimage hU
  have hemb : MeasurableEmbedding (fun x : E2 => x + c) :=
    (Homeomorph.addRight c).measurableEmbedding
  refine ⟨native_h1_translation U hU c v G hv.1, ?_⟩
  intro ε hε
  obtain ⟨ψ, hs, hc, ht, he⟩ := hv.2 ε hε
  refine ⟨fun x => ψ (x + c), hs.comp (contDiff_id.add contDiff_const),
    hc.comp_homeomorph (Homeomorph.addRight c), ?_, ?_⟩
  · intro x hx
    exact ht (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hx)
  · simp_rw [planar_gradient_translation]
    rw [hmp.integral_comp hemb (fun x => |v x - ψ x| ^ 2 + ‖G x - planarGradient ψ x‖ ^ 2)]
    exact he

/-- Smooth flat-zero tests on an arbitrary actual boundary-centered ball. -/
theorem native_smooth_flat_zero_h10_centered
    (c : E2) (hcf : c 0 = 0) (ρ : ℝ) (ψ : E2 → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ Metric.ball c ρ)
    (hflat : ∀ x : E2, x 0 = 0 → ψ x = 0) :
    H10On (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) ψ (planarGradient ψ) := by
  let ψc : E2 → ℝ := fun x => ψ (x + c)
  have hs : ContDiff ℝ ∞ ψc := hψ.comp (contDiff_id.add contDiff_const)
  have hc' : HasCompactSupport ψc := hc.comp_homeomorph (Homeomorph.addRight c)
  have ht' : tsupport ψc ⊆ Metric.ball 0 ρ := by
    intro x hx
    have hh := ht (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hx)
    change (x + c) ∈ Metric.ball c ρ at hh
    change dist x 0 < ρ
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hh
  have hf' : ∀ x : E2, x 0 = 0 → ψc x = 0 := by
    intro x hx
    exact hflat _ (by simp only [PiLp.add_apply, hx, hcf, add_zero])
  have hh := native_h10_translation (openHalfDisc ρ) (openHalfDisc_isOpen ρ).measurableSet
    (-c) ψc (planarGradient ψc) (native_smooth_flat_zero_h10 ρ ψc hs hc' ht' hf')
  have hpre : (fun x : E2 => x + -c) ⁻¹' openHalfDisc ρ =
      Metric.ball c ρ ∩ {x : E2 | 0 < x 0} := by
    ext x
    change (dist (x + -c) 0 < ρ ∧ 0 < (x + -c) 0) ↔ (dist x c < ρ ∧ 0 < x 0)
    simp only [dist_eq_norm, sub_zero, sub_eq_add_neg, PiLp.add_apply, PiLp.neg_apply,
      hcf, neg_zero, add_zero]
  have hval : (fun x => ψc (x + -c)) = ψ := by
    funext x
    simp only [ψc, neg_add_cancel_right]
  have hgrad : (fun x => planarGradient ψc (x + -c)) = planarGradient ψ := by
    funext x
    rw [show planarGradient ψc (x + -c) = planarGradient ψ ((x + -c) + c) from
      planar_gradient_translation ψ c _, neg_add_cancel_right]
  rw [hpre, hval, hgrad] at hh
  exact hh

theorem native_zero_flat_flux_source_testing_centered
    (c : E2) (hcf : c 0 = 0) (ρ : ℝ) (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (Metric.ball c ρ ∩ {x : E2 | 0 < x 0})))
    (hS : MemLp S 2 (volume.restrict (Metric.ball c ρ ∩ {x : E2 | 0 < x 0})))
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball c ρ ∩ {x : E2 | 0 < x 0} →
        (∫ x in Metric.ball c ρ ∩ {x : E2 | 0 < x 0},
          inner ℝ (F x) (planarGradient φ x) - S x * φ x) = 0)
    (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ Metric.ball c ρ)
    (hflat : ∀ x : E2, x 0 = 0 → ψ x = 0) :
    IntegrableOn (fun x => inner ℝ (F x) (planarGradient ψ x))
      (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) ∧
    IntegrableOn (fun x => S x * ψ x) (Metric.ball c ρ ∩ {x : E2 | 0 < x 0}) ∧
    (∫ x in Metric.ball c ρ ∩ {x : E2 | 0 < x 0},
      inner ℝ (F x) (planarGradient ψ x) - S x * ψ x) = 0 :=
  native_h10_flux_source_testing _ F S hF hS hweak ψ (planarGradient ψ)
    (native_smooth_flat_zero_h10_centered c hcf ρ ψ hψ hc ht hflat)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
