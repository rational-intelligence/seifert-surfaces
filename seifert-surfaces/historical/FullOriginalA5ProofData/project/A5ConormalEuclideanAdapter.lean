import A5NativeCoordinateTransport
import A5SeamTangents

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A tangent-space conormal calculation is unchanged after applying an
ambient chart's linear coordinate equivalence.  This is the metric-free
adapter used by the native seam argument: the metric covector is pulled back
through the actual chart equivalence, while the derivative is transported by
the same equivalence. -/
theorem tangent_ranges_eq_after_chart_transport
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : V ≃L[ℝ] Euc 3)
    (M₁ M₂ : Euc 2 →L[ℝ] V)
    (hM₁ : Function.Injective M₁) (hM₂ : Function.Injective M₂)
    (v n₁ n₂ : V) (hv : v ≠ 0)
    (hv₁ : v ∈ M₁.toLinearMap.range) (hv₂ : v ∈ M₂.toLinearMap.range)
    (hn₁ : n₁ ∈ M₁.toLinearMap.range) (hn₂ : n₂ ∈ M₂.toLinearMap.range)
    (inner : V →L[ℝ] V →L[ℝ] ℝ)
    (hunit : inner n₁ n₁ = 1) (horth : inner n₁ v = 0)
    (hopp : n₁ + n₂ = 0) :
    (C.toContinuousLinearMap.comp M₁).toLinearMap.range = (C.toContinuousLinearMap.comp M₂).toLinearMap.range := by
  let L : Euc 3 →L[ℝ] ℝ := (inner n₁).comp C.symm.toContinuousLinearMap
  have hLunit : L (C n₁) = 1 := by
    dsimp [L]
    simpa only [ContinuousLinearMap.comp_apply, C.symm_apply_apply] using hunit
  have hLorth : L (C v) = 0 := by
    dsimp [L]
    simpa only [ContinuousLinearMap.comp_apply, C.symm_apply_apply] using horth
  have hC₁ : Function.Injective (C.toContinuousLinearMap.comp M₁) := C.injective.comp hM₁
  have hC₂ : Function.Injective (C.toContinuousLinearMap.comp M₂) := C.injective.comp hM₂
  have hvC₁ : C v ∈ (C.toContinuousLinearMap.comp M₁).toLinearMap.range := by
    obtain ⟨z, hz⟩ := hv₁
    exact ⟨z, congrArg C hz⟩
  have hvC₂ : C v ∈ (C.toContinuousLinearMap.comp M₂).toLinearMap.range := by
    obtain ⟨z, hz⟩ := hv₂
    exact ⟨z, congrArg C hz⟩
  have hnC₁ : C n₁ ∈ (C.toContinuousLinearMap.comp M₁).toLinearMap.range := by
    obtain ⟨z, hz⟩ := hn₁
    exact ⟨z, congrArg C hz⟩
  have hnC₂ : C n₂ ∈ (C.toContinuousLinearMap.comp M₂).toLinearMap.range := by
    obtain ⟨z, hz⟩ := hn₂
    exact ⟨z, congrArg C hz⟩
  have hbal : C n₁ + C n₂ = 0 := by
    rw [← C.map_add, hopp, C.map_zero]
  exact tangent_ranges_eq_of_opposite_conormals
    (C.toContinuousLinearMap.comp M₁) (C.toContinuousLinearMap.comp M₂) hC₁ hC₂ (C v) (C n₁) (C n₂)
    (by simpa only [C.map_zero] using C.injective.ne hv) hvC₁ hvC₂ hnC₁ hnC₂ L hLunit hLorth hbal

/-- The coordinate velocity is the actual chart derivative applied to the
actual manifold velocity. -/
theorem ambient_chart_curve_derivative_transport
    {N : Type*} [TopologicalSpace N] [ChartedSpace (Euc 3) N]
    [IsManifold 𝓘(ℝ, Euc 3) ∞ N]
    (γ : ℝ → N) (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, Euc 3) γ t)
    (c : SmoothAmbientChart N) (hc : γ t ∈ c.chart.source) :
    deriv (c.chart ∘ γ) t =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.chart (γ t)))
        (mfderiv 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) c.chart (γ t)
          (mfderiv 𝓘(ℝ) 𝓘(ℝ, Euc 3) γ t 1)) := by
  have hca := ((c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)).mdifferentiableAt (by simp)
  have hd := mfderiv_comp_apply (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, Euc 3))
    (I'' := 𝓘(ℝ, Euc 3)) t hca hγ 1
  have he := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) (c.chart (γ t))) hd
  rw [mfderiv_eq_fderiv] at he
  change fderiv ℝ (c.chart ∘ γ) t 1 = _ at he
  simpa only [fderiv_eq_smul_deriv, one_smul] using he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
