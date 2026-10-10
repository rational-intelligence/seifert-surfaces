import A5RegularArcGeometry
import A5NativeMetricGraphConstruction

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- A smooth planar change of projection coordinates lifts to an actual
smooth ambient chart. Keeping the height coordinate gives the exact
straightened projection formula, so the native metric graph machinery
computes the changed metric without postulating a PDE transport identity. -/
theorem ambient_chart_of_projected_coordinate_change
    {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ,E3) ∞ N]
    (c : SmoothAmbientChart N) (L : E3 ≃L[ℝ] E2 × ℝ)
    (d : OpenPartialHomeomorph E2 E2)
    (hd : ContDiffOn ℝ ∞ d d.source)
    (hdi : ContDiffOn ℝ ∞ d.symm d.target) :
    ∃ c' : SmoothAmbientChart N,
      (∀ x, c'.chart x = L.symm (d (L (c.chart x)).1, (L (c.chart x)).2)) ∧
      (∀ x, x ∈ c'.chart.source ↔ x ∈ c.chart.source ∧ (L (c.chart x)).1 ∈ d.source) ∧
      (∀ x ∈ c'.chart.source,
        (L (c'.chart x)).1 = d (L (c.chart x)).1 ∧
        (L (c'.chart x)).2 = (L (c.chart x)).2) := by
  let b := d.prod (OpenPartialHomeomorph.refl ℝ)
  let e := L.toHomeomorph.toOpenPartialHomeomorph.trans
    (b.trans L.symm.toHomeomorph.toOpenPartialHomeomorph)
  have hb : ContDiffOn ℝ ∞ b b.source := by
    exact (hd.comp contDiffOn_fst (fun z hz => hz.1)).prodMk contDiffOn_snd
  have hbi : ContDiffOn ℝ ∞ b.symm b.target := by
    exact (hdi.comp contDiffOn_fst (fun z hz => hz.1)).prodMk contDiffOn_snd
  have he : ContDiffOn ℝ ∞ e e.source := by
    apply L.symm.contDiff.comp_contDiffOn
    exact hb.comp L.contDiff.contDiffOn (fun z hz => hz.2.1)
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    apply L.symm.contDiff.comp_contDiffOn
    exact hbi.comp L.contDiff.contDiffOn (fun z hz => hz.1.2)
  let c' : SmoothAmbientChart N := {
    chart := c.chart.trans e
    smooth := he.contMDiffOn.comp (c.smooth.mono inter_subset_left) (fun z hz => hz.2)
    inverse_smooth := c.inverse_smooth.comp
      (hei.contMDiffOn.mono inter_subset_left) (fun z hz => hz.2) }
  refine ⟨c',fun _ => rfl,?_,?_⟩
  · intro x
    change (x ∈ c.chart.source ∧ c.chart x ∈ e.source) ↔ _
    change (x ∈ c.chart.source ∧ (True ∧ ((L (c.chart x)).1 ∈ d.source ∧ True) ∧ True)) ↔ _
    tauto
  · intro x _
    have hh := L.apply_symm_apply (d (L (c.chart x)).1,(L (c.chart x)).2)
    have hfst := congrArg Prod.fst hh
    have hsnd := congrArg Prod.snd hh
    exact ⟨hfst,hsnd⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
