import A5NativeMetricGraphOperator

set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

/-- Covariant trace depends only on the germ of the actual parametrization. -/
theorem tracedAcceleration_eq_of_eventuallyEq
    (g : MetricTensor) (F H : E2 → E3) (x : E2) (he : F =ᶠ[𝓝 x] H) :
    tracedAcceleration g F x = tracedAcceleration g H x := by
  have hd := he.fderiv_eq (𝕜 := ℝ)
  have ht (j : Fin 2) : (fun z => graphTangent F z j) =ᶠ[𝓝 x]
      (fun z => graphTangent H z j) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with z hz
    exact congrArg (fun L : E2 →L[ℝ] E3 => L (coordinateVector 2 j)) hz
  have hm : inducedMetric g F x = inducedMetric g H x := by
    unfold inducedMetric graphTangent
    rw [he.self_of_nhds, hd]
  unfold tracedAcceleration
  rw [hm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold covariantAcceleration
  rw [(ht j).fderiv_eq, he.self_of_nhds]
  simp only [graphTangent, hd]

theorem coordinate_minimality_congr
    (g : MetricTensor) (F H : E2 → E3) (U : Set E2) (hU : IsOpen U)
    (hF : IsMinimalParametrizationOn g F U) (he : EqOn H F U) :
    IsMinimalParametrizationOn g H U := by
  refine ⟨hF.1.congr he, ?_⟩
  intro x hx
  have hgerm : H =ᶠ[𝓝 x] F := he.eventuallyEq_of_mem (hU.mem_nhds hx)
  rw [tracedAcceleration_eq_of_eventuallyEq g H F x hgerm, hgerm.fderiv_eq]
  exact hF.2 x hx

/-- Actual metric minimality is invariant under a smooth regular change of
source coordinates, using the paid covariant-trace transformation law. -/
theorem coordinate_minimality_reparametrization
    (V : Set E3) (hV : IsOpen V) (g : CoordinateMetric V)
    (Ω U : Set E2) (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Φ : E2 → E3) (hminimal : IsMinimalParametrizationOn g.tensor Φ Ω)
    (hΦimage : MapsTo Φ Ω V)
    (hΦregular : ∀ y ∈ Ω, Function.Injective (fderiv ℝ Φ y))
    (κ : E2 → E2) (hκ : ContDiffOn ℝ ∞ κ U) (hκimage : MapsTo κ U Ω)
    (hκregular : ∀ x ∈ U, Function.Bijective (fderiv ℝ κ x)) :
    IsMinimalParametrizationOn g.tensor (Φ ∘ κ) U := by
  refine ⟨hminimal.1.comp hκ hκimage, ?_⟩
  intro x hx
  obtain ⟨_, hrange, htrace⟩ := SourceReparametrization.source_reparametrization_covariant_trace
    V hV g Ω U hΩ hU Φ hminimal.1 hΦimage hΦregular κ hκ hκimage hκregular x hx
  have hm : tracedAcceleration g.tensor Φ (κ x) ∈
      (fderiv ℝ (Φ ∘ κ) x).toLinearMap.range := by
    rw [hrange]
    exact hminimal.2 (κ x) (hκimage hx)
  have he := (fderiv ℝ (Φ ∘ κ) x).toLinearMap.range.add_mem htrace hm
  simpa only [sub_add_cancel] using he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
