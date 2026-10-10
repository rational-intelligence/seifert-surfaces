import B1InteriorCylinderPDE_v475
import B1InteriorCylinderContinuation_v475
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

/-- The actual full-image agreement germ locus is closed. All interior
coordinates, graph equations, coefficients and continuation data are outputs
of the original embeddings and their native supported-flow minima. -/
theorem native_actual_minimizer_germ_locus_closed_v475
    (metric : SmoothMetric E.Carrier)
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (hminf : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area metric (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (hming : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area metric (native_actual_exterior_flow_v475 X t ∘ g.toFun)) 0) :
    IsClosed {x : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image g.image (f.toFun x)} := by
  classical
  apply isClosed_of_closure_subset
  intro x hx
  obtain ⟨y,Φ,Ψ,P,p,e,u,hy,hP,hPo,hpP,hpe,heP,hΦ,hΦi,hΨ,hΨi,hA,hB,
    hxcharts,hpair,hes,hei,hu,hup,hgrad,hgraph,hgraphS,hebase,hacc⟩ :=
      native_actual_common_interior_graph_v475 f g x hx
  have heO : e.source ⊆ {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩
      interior (range (𝓡∂ 2)) := by rwa [← hP]
  have hxI : f.toFun x ∈ (𝓡∂ 3).interior E.Carrier := by
    rw [← (𝓡∂ 3).compl_boundary]
    intro hbd
    have hxnb : (x : S) ∉ S.boundary := by
      have hn (a : S) (ha : a ∈ (𝓡∂ 2).interior S) : a ∉ S.boundary := by
        rw [← (𝓡∂ 2).compl_boundary] at ha
        exact ha
      exact hn x x.property
    apply hxnb
    rwa [← f.boundary_preimage]
  have hrpair : Ψ (E.toSphere (f.toFun x))=(p,0) := by rwa [hy] at hpair
  obtain ⟨c,O,η,hO,hpO,hOe,hη,hcE,hcV,hcΦ,hciΦ,hpoints,hAf,hBg,hgraphf,hgraphg⟩ :=
    native_interior_common_graph_cylinder_v475 f g (f.toFun x) hxI Φ Ψ hΦ hΦi
      hxcharts.1 hxcharts.2 hA hB p e u hpe hrpair heO hu hup hgraph hgraphS hebase
  obtain ⟨H,heq0,hequ⟩ := native_interior_common_cylinder_pdes_v475 metric f g (f.toFun x) x y
    hminf hming c hcE O hO u (hu.mono hOe) hpoints hAf hBg hgraphf hgraphg
  have haccO := native_planar_zero_germ_accumulation_restrict_v475 e.target O hO hOe u
    (e p) hpO hacc
  obtain ⟨Z,hZ,hpZ,hZO,hZu⟩ := native_interior_cylinder_zero_continuation_v475 O hO
    (e p) hpO u (hu.mono hOe) c.chart.target c.chart.open_target η hη hcV H hpoints
    heq0 hequ haccO
  exact native_interior_zero_graph_surface_germ_v475 f g (f.toFun x) Φ Ψ hxcharts.1 hxcharts.2
    hA hB p e u hpe hrpair heO hgraph hgraphS hebase
    ⟨Z,hZ,hpZ,hZO.trans hOe,hZu⟩

#print axioms native_actual_minimizer_germ_locus_closed_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
