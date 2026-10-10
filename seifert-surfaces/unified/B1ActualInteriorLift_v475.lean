import B1ExteriorInteriorOpen_v475
import B1ActualChartVectorField_v475
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

/-- A sphere chart supported in the actual exterior interior has an actual
smooth inverse into that exterior; inverse regularity follows from the supplied
inclusion immersion and the inducing topology. -/
theorem native_actual_interior_chart_lift_v475
    (c : SmoothAmbientChart ThreeSphere) (r : E.Carrier)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier) :
    ∃ χ : E3 → E.Carrier,
      ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target ∧
      (∀ y ∈ c.chart.target, E.toSphere (χ y)=c.chart.symm y) ∧
      (∀ y ∈ c.chart.target, χ y ∈ (𝓡∂ 3).interior E.Carrier) ∧
      (∀ y ∈ c.chart.target, c.chart (E.toSphere (χ y))=y) ∧
      (∀ a : E.Carrier, E.toSphere a ∈ c.chart.source → χ (c.chart (E.toSphere a))=a) := by
  classical
  have hpoint (y : E3) (hy : y ∈ c.chart.target) := hcE (c.chart.map_target hy)
  let χ : E3 → E.Carrier := fun y => if hy : y ∈ c.chart.target then (hpoint y hy).choose else r
  have heq (y : E3) (hy : y ∈ c.chart.target) : E.toSphere (χ y)=c.chart.symm y := by
    simp only [χ,dif_pos hy]
    exact (hpoint y hy).choose_spec.2
  have hinterior (y : E3) (hy : y ∈ c.chart.target) : χ y ∈ (𝓡∂ 3).interior E.Carrier := by
    simp only [χ,dif_pos hy]
    exact (hpoint y hy).choose_spec.1
  have hinc : Manifold.IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ E.toSphere := E.inclusion
  have hχcont : ContinuousOn χ c.chart.target := by
    apply hinc.isEmbedding.isInducing.continuousOn_iff.mpr
    exact c.inverse_smooth.continuousOn.congr heq
  have hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target := by
    intro y hy
    have hcont := (hχcont y hy).continuousAt (c.chart.open_target.mem_nhds hy)
    have hcomp : ContMDiffAt 𝓘(ℝ,E3) (𝓡 3) ∞ (E.toSphere ∘ χ) y := by
      apply (c.inverse_smooth.contMDiffAt (c.chart.open_target.mem_nhds hy)).congr_of_eventuallyEq
      exact Filter.eventuallyEq_of_mem (c.chart.open_target.mem_nhds hy) (fun z hz => heq z hz)
    exact ((ContMDiffAt.iff_comp_isImmersionAt (I := 𝓘(ℝ,E3))
      (hinc.isImmersion.isImmersionAt (χ y))).mpr ⟨hcont,hcomp⟩).contMDiffWithinAt
  refine ⟨χ,hχ,heq,hinterior,?_,?_⟩
  · intro y hy
    rw [heq y hy,c.chart.right_inv hy]
  · intro a ha
    apply hinc.isEmbedding.injective
    rw [heq _ (c.chart.map_source ha),c.chart.left_inv ha]

#print axioms native_actual_interior_chart_lift_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
