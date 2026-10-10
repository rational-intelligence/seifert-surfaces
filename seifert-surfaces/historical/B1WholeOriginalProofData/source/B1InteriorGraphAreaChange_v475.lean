import B1InteriorParametricGraphDensity_v475
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

/-- Exact total area change in a common interior graph of the actual metric. -/
theorem native_interior_graph_parameter_area_change_v475
    (g : SmoothMetric E.Carrier) (V : Set E3) (hV : IsOpen V)
    (χ : E3 → E.Carrier) (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ V)
    (Hmetric : CoordinateMetric V) (hmetric : Hmetric.tensor=native_actual_lift_tensor_v475 g χ)
    {S : CompactOrientedSurface.{u}}
    (F H : S → E.Carrier) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (p : S) (q : E2 → S) (O A : Set E2)
    (hO : IsOpen O) (hA : IsCompact A) (hAO : A ⊆ O)
    (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O)
    (hqs : MapsTo q O (surfaceChart p).source)
    (hqi : ∀ x ∈ O, q x ∉ S.boundary) (hqinj : InjOn q O)
    (u v : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O)
    (hgraphF : ∀ x ∈ O, F (q x)=χ (jetPoint (x,u x,0)))
    (hgraphH : ∀ x ∈ O, H (q x)=χ (jetPoint (x,v x,0)))
    (hpointu : ∀ x ∈ A, jetPoint (x,u x,0) ∈ V)
    (hpointv : ∀ x ∈ A, jetPoint (x,v x,0) ∈ V)
    (heq : EqOn F H (q '' A)ᶜ) :
    area g H-area g F =
      (∫ x in A, native_interior_graph_density_v475 Hmetric (x,v x,planarGradient v x))-
      (∫ x in A, native_interior_graph_density_v475 Hmetric (x,u x,planarGradient u x)) := by
  have hden (L : S → E.Carrier) (w : E2 → ℝ) (hw : ContDiffOn ℝ ∞ w O)
      (hgraphL : ∀ x ∈ O, L (q x)=χ (jetPoint (x,w x,0)))
      (hpoint : ∀ x ∈ A, jetPoint (x,w x,0) ∈ V) (x : E2) (hx : x ∈ A) :
      native_parametric_density_v475 g (L ∘ q) x=
        native_interior_graph_density_v475 Hmetric (x,w x,planarGradient w x) := by
    change native_parametric_density_v475 g (fun z => L (q z)) x = _
    rw [native_parametric_density_of_local_equality_v475 g _ _ x
      (Filter.eventuallyEq_of_mem (hO.mem_nhds (hAO hx)) (fun z hz => hgraphL z hz))]
    exact native_interior_parametric_graph_density_v475 g V hV χ hχ Hmetric hmetric w x
      ((hw.contDiffAt (hO.mem_nhds (hAO hx))).differentiableAt (by simp)) (hpoint x hx)
  rw [native_parameter_area_change_v475 g F H hF hH p q O A hO hA hAO hq hqs hqi hqinj heq]
  rw [setIntegral_congr_fun hA.measurableSet (hden H v hv hgraphH hpointv),
    setIntegral_congr_fun hA.measurableSet (hden F u hu hgraphF hpointu)]

#print axioms native_interior_graph_parameter_area_change_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
