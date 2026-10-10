import B1InteriorActualGraphMinimum_v475
import B1InteriorGraphPDE_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The actual supported-flow minimum implies the graph equation throughout
an arbitrary common interior chart, localizing each test in a source chart. -/
theorem native_interior_actual_graph_pde_from_flow_v475
    (g : SmoothMetric E.Carrier) (c : SmoothAmbientChart ThreeSphere)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (χ : E3 → E.Carrier) (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target)
    (hχeq : ∀ y ∈ c.chart.target, E.toSphere (χ y)=c.chart.symm y)
    (H : CoordinateMetric c.chart.target) (hH : H.tensor=native_actual_lift_tensor_v475 g χ)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (hmin : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
    (q : E2 → S) (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O)
    (hqgraph : ∀ x ∈ O, f.toFun (q x)=χ (jetPoint (x,u x,0)))
    (hqt : ∀ x ∈ O, jetPoint (x,u x,0) ∈ c.chart.target)
    (hqi : ∀ x ∈ O, q x ∉ S.boundary)
    (hgraph : ∀ z : S, E.toSphere (f.toFun z) ∈ c.chart.source →
      (c.chart (E.toSphere (f.toFun z))) 2 =
        u (native_collar_base_v475 (c.chart (E.toSphere (f.toFun z))))) :
    ∀ x ∈ O, native_interior_graph_residual_v475 H u x=0 := by
  intro x hx
  let p := q x
  let N := O ∩ q ⁻¹' (surfaceChart p).source
  have hN : IsOpen N := hq.continuousOn.isOpen_inter_preimage hO (isOpen_extChartAt_source p)
  have hxN : x ∈ N := ⟨hx,mem_extChartAt_source p⟩
  have hminimum := fun φ hφ hφc ht => native_interior_actual_compact_graph_minimum_v475
    g c hcE χ hχ hχeq H hH f hmin N hN u (hu.mono inter_subset_left) q
    (hq.mono inter_subset_left) (fun z hz => hqgraph z hz.1) (fun z hz => hqt z hz.1)
    (fun z hz => hqi z hz.1) hgraph p (fun z hz => hz.2) φ hφ hφc ht
  have hPDE := native_interior_graph_pde_from_compact_minima_v475 c.chart.target c.chart.open_target
    H N hN u (hu.mono inter_subset_left) (fun z hz => by simpa [jetPoint] using hqt z hz.1) hminimum
  exact hPDE x hxN

#print axioms native_interior_actual_graph_pde_from_flow_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
