import NativeBoundaryZeroTraceTesting

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet

/-- Smooth-test identities with actual L2 flux and source extend to the native
H10 graph. Both terms stay integrable, including the scalar source. -/
theorem native_h10_flux_source_testing
    (U : Set E2) (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict U)) (hS : MemLp S 2 (volume.restrict U))
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (F x) (planarGradient φ x) - S x * φ x) = 0)
    (φ : E2 → ℝ) (Dφ : E2 → E2) (hφ : H10On U φ Dφ) :
    IntegrableOn (fun x => inner ℝ (F x) (Dφ x)) U ∧
      IntegrableOn (fun x => S x * φ x) U ∧
      (∫ x in U, inner ℝ (F x) (Dφ x) - S x * φ x) = 0 := by
  classical
  let μ := volume.restrict U
  have pairVector (g : E2 → E2) (hg : MemLp g 2 μ) :
      Integrable (fun x => inner ℝ (F x) (g x)) μ ∧
        (∫ x, inner ℝ (F x) (g x) ∂μ) = inner ℝ (hF.toLp F) (hg.toLp g) := by
    refine ⟨(L2.integrable_inner (𝕜 := ℝ) (hF.toLp F) (hg.toLp g)).congr ?_, ?_⟩
    · filter_upwards [hF.coeFn_toLp, hg.coeFn_toLp] with x hx hx'
      rw [hx, hx']
    · rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hg.coeFn_toLp] with x hx hx'
      rw [hx, hx']
  have pairScalar (v : E2 → ℝ) (hv : MemLp v 2 μ) :
      Integrable (fun x => S x * v x) μ ∧
        (∫ x, S x * v x ∂μ) = inner ℝ (hS.toLp S) (hv.toLp v) := by
    refine ⟨hS.integrable_mul hv, ?_⟩
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp, hv.coeFn_toLp] with x hx hx'
    rw [hx, hx', Real.inner_apply]
  let P : Pair U := WithLp.toLp 2 (-(hS.toLp S), hF.toLp F)
  have packIdentity (v : E2 → ℝ) (G : E2 → E2)
      (hv : MemLp v 2 μ) (hG : MemLp G 2 μ) :
      inner ℝ P (pack U v G hv hG) =
        ∫ x in U, inner ℝ (F x) (G x) - S x * v x := by
    change inner ℝ (-(hS.toLp S)) (hv.toLp v) +
      inner ℝ (hF.toLp F) (hG.toLp G) = _
    rw [inner_neg_left, ← (pairScalar v hv).2, ← (pairVector G hG).2,
      integral_sub (pairVector G hG).1 (pairScalar v hv).1]
    ring
  have hspan : Submodule.span ℝ (SmoothGraph U) ≤ (innerSL ℝ P).ker := by
    apply Submodule.span_le.mpr
    rintro p ⟨v, hv, hG, hs, hc, ht, rfl⟩
    change inner ℝ P (pack U v (planarGradient v) hv hG) = 0
    rw [packIdentity]
    exact hweak v hs hc ht
  have hclosed : space U ≤ (innerSL ℝ P).ker :=
    (Submodule.span ℝ (SmoothGraph U)).topologicalClosure_minimal hspan
      (innerSL ℝ P).isClosed_ker
  have hp := (h10_pair_bridge U φ Dφ hφ.1.2.1 hφ.1.2.2).mp hφ
  have hzero := hclosed hp
  change inner ℝ P (pack U φ Dφ hφ.1.2.1 hφ.1.2.2) = 0 at hzero
  rw [packIdentity] at hzero
  exact ⟨(pairVector Dφ hφ.1.2.2).1, (pairScalar φ hφ.1.2.1).1, hzero⟩

theorem native_zero_flat_flux_source_testing
    (ρ : ℝ) (F : E2 → E2) (S : E2 → ℝ)
    (hF : MemLp F 2 (volume.restrict (openHalfDisc ρ)))
    (hS : MemLp S 2 (volume.restrict (openHalfDisc ρ)))
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ openHalfDisc ρ →
        (∫ x in openHalfDisc ρ, inner ℝ (F x) (planarGradient φ x) - S x * φ x) = 0)
    (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (ht : tsupport ψ ⊆ Metric.ball 0 ρ)
    (hflat : ∀ x : E2, x 0 = 0 → ψ x = 0) :
    IntegrableOn (fun x => inner ℝ (F x) (planarGradient ψ x)) (openHalfDisc ρ) ∧
      IntegrableOn (fun x => S x * ψ x) (openHalfDisc ρ) ∧
      (∫ x in openHalfDisc ρ, inner ℝ (F x) (planarGradient ψ x) - S x * ψ x) = 0 :=
  native_h10_flux_source_testing (openHalfDisc ρ) F S hF hS hweak ψ (planarGradient ψ)
    (native_smooth_flat_zero_h10 ρ ψ hψ hc ht hflat)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
