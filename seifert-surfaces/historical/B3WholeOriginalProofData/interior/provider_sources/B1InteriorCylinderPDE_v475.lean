import B1InteriorCommonCylinder_v475
import B1ActualInteriorParameter_v475
import B1InteriorActualGraphPDE_v475
noncomputable section
open Set Topology Function Filter MeasureTheory
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Both literal original images solve the same actual coordinate-metric
graph equation. Source parameters and metric pullback are internal outputs. -/
theorem native_interior_common_cylinder_pdes_v475
    (metric : SmoothMetric E.Carrier)
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (r : E.Carrier) (f₀ : S) (g₀ : B)
    (hminf : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area metric (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (hming : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area metric (native_actual_exterior_flow_v475 X t ∘ g.toFun)) 0)
    (c : SmoothAmbientChart ThreeSphere)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
    (hpoints : ∀ z ∈ O, jetPoint (z,0,0) ∈ c.chart.target ∧
      jetPoint (z,u z,0) ∈ c.chart.target)
    (hAf : ∀ z ∈ O, c.chart.symm (jetPoint (z,0,0)) ∈ range (E.toSphere ∘ f.toFun))
    (hBg : ∀ z ∈ O, c.chart.symm (jetPoint (z,u z,0)) ∈ range (E.toSphere ∘ g.toFun))
    (hgraphf : ∀ a : S, E.toSphere (f.toFun a) ∈ c.chart.source →
      (c.chart (E.toSphere (f.toFun a))) 2=0)
    (hgraphg : ∀ a : B, E.toSphere (g.toFun a) ∈ c.chart.source →
      (c.chart (E.toSphere (g.toFun a))) 2=
      u (native_collar_base_v475 (c.chart (E.toSphere (g.toFun a))))) :
    ∃ H : CoordinateMetric c.chart.target,
      (∀ z ∈ O, native_interior_graph_residual_v475 H (fun _ => 0) z=0) ∧
      (∀ z ∈ O, native_interior_graph_residual_v475 H u z=0) := by
  obtain ⟨χ,hχ,hχeq,hχI,hχright,hχleft⟩ := native_actual_interior_chart_lift_v475 c r hcE
  obtain ⟨H,hH⟩ := native_actual_lift_coordinate_metric_v475 metric c χ hχ hχeq
  have smoothgraph (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
      (ht : ∀ z ∈ O, jetPoint (z,u z,0) ∈ c.chart.target) :
      ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 3) ∞ (fun z => χ (jetPoint (z,u z,0))) O := by
    have hs : ContDiffOn ℝ ∞ (fun z => jetPoint (z,u z,0)) O :=
      native_interior_graph_splitting_v475.contDiff.comp_contDiffOn (contDiffOn_id.prodMk hu)
    exact hχ.comp hs.contMDiffOn ht
  have hmapsf : ∀ z ∈ O, χ (jetPoint (z,0,0)) ∈ f.image := by
    intro z hz
    obtain ⟨a,ha⟩ := hAf z hz
    exact ⟨a,Subtype.ext (ha.trans (hχeq _ (hpoints z hz).1).symm)⟩
  have hmapsg : ∀ z ∈ O, χ (jetPoint (z,u z,0)) ∈ g.image := by
    intro z hz
    obtain ⟨a,ha⟩ := hBg z hz
    exact ⟨a,Subtype.ext (ha.trans (hχeq _ (hpoints z hz).2).symm)⟩
  obtain ⟨qf,hqf,hqfi,hqfs⟩ := native_actual_interior_source_parameter_v475 f f₀ O hO
    (fun z => χ (jetPoint (z,0,0)))
    (smoothgraph (fun _ => 0) contDiffOn_const (fun z hz => (hpoints z hz).1))
    hmapsf
    (fun z hz => hχI _ (hpoints z hz).1)
  obtain ⟨qg,hqg,hqgi,hqgs⟩ := native_actual_interior_source_parameter_v475 g g₀ O hO
    (fun z => χ (jetPoint (z,u z,0))) (smoothgraph u hu (fun z hz => (hpoints z hz).2))
    hmapsg
    (fun z hz => hχI _ (hpoints z hz).2)
  exact ⟨H,
    native_interior_actual_graph_pde_from_flow_v475 metric c hcE χ hχ hχeq H hH
      (ProperSmoothEmbedding.ofNeat f) hminf O hO (fun _ => 0) contDiffOn_const qf hqfs
      hqf (fun z hz => (hpoints z hz).1) hqfi hgraphf,
    native_interior_actual_graph_pde_from_flow_v475 metric c hcE χ hχ hχeq H hH
      (ProperSmoothEmbedding.ofNeat g) hming O hO u hu qg hqgs
      hqg (fun z hz => (hpoints z hz).2) hqgi hgraphg⟩

#print axioms native_interior_common_cylinder_pdes_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
