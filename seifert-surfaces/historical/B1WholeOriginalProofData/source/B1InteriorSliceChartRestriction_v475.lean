import B1InteriorGraphSplitting_v475
import B1ExteriorInteriorOpen_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Restrict a genuine sphere slice to an actual interior open neighborhood
and read the same chart in its three coordinate vectors. -/
theorem native_interior_slice_chart_restriction_v475
    (Φ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (U : Set ThreeSphere) (hU : IsOpen U) (hUΦ : U ⊆ Φ.source) :
    ∃ c : SmoothAmbientChart ThreeSphere,
      c.chart.source=U ∧
      (∀ a, c.chart a=native_interior_graph_splitting_v475 (Φ a)) ∧
      (∀ y, c.chart.symm y=Φ.symm (native_interior_graph_splitting_v475.symm y)) := by
  let e := (Φ.restrOpen U hU).transHomeomorph native_interior_graph_splitting_v475.toHomeomorph
  have hesource : e.source=U := by
    change Φ.source ∩ U=U
    exact inter_eq_right.mpr hUΦ
  have hes : ContMDiffOn (𝓡 3) 𝓘(ℝ,E3) ∞ e e.source :=
    native_interior_graph_splitting_v475.contDiff.contMDiff.comp_contMDiffOn
      (hΦ.mono (by rw [hesource]; exact hUΦ))
  have het : ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞ e.symm e.target := by
    change ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞
      (Φ.symm ∘ native_interior_graph_splitting_v475.symm) e.target
    apply hΦi.comp native_interior_graph_splitting_v475.symm.contDiff.contMDiff.contMDiffOn
    intro y hy
    exact hy.1
  exact ⟨⟨e,hes,het⟩,hesource,fun _ => rfl,fun _ => rfl⟩

/-- Restrict the coordinate target to a genuinely open cylinder while
preserving both actual smooth chart maps. -/
theorem native_interior_chart_restrict_target_v475
    (c : SmoothAmbientChart ThreeSphere) (V : Set E3) (hV : IsOpen V)
    (hVc : V ⊆ c.chart.target) :
    ∃ d : SmoothAmbientChart ThreeSphere,
      d.chart.target=V ∧ d.chart.source⊆c.chart.source ∧
      (∀ a, d.chart a=c.chart a) ∧ (∀ y, d.chart.symm y=c.chart.symm y) ∧
      (∀ a ∈ c.chart.source, c.chart a ∈ V → a ∈ d.chart.source) := by
  let e := (c.chart.symm.restrOpen V hV).symm
  have hetarget : e.target=V := by
    change c.chart.target ∩ V=V
    exact inter_eq_right.mpr hVc
  have hsource : e.source⊆c.chart.source := inter_subset_left
  have hes : ContMDiffOn (𝓡 3) 𝓘(ℝ,E3) ∞ e e.source := c.smooth.mono hsource
  have het : ContMDiffOn 𝓘(ℝ,E3) (𝓡 3) ∞ e.symm e.target :=
    c.inverse_smooth.mono (by rw [hetarget]; exact hVc)
  refine ⟨⟨e,hes,het⟩,hetarget,hsource,fun _ => rfl,fun _ => rfl,?_⟩
  intro a ha hv
  exact ⟨ha,hv⟩

#print axioms native_interior_slice_chart_restriction_v475
#print axioms native_interior_chart_restrict_target_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
