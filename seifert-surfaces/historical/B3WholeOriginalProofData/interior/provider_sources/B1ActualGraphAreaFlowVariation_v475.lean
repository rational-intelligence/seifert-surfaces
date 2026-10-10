import B1ActualParametricGraphDensity_v475
import B1CompactVerticalFlow_v475
import B1GraphStationarityAdapter_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The exact local geometric area change is the supplied density integral
change, once an actual smooth graph parameter and its varied map are identified. -/
theorem actual_graph_parameter_area_change_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    {S : CompactOrientedSurface.{u}}
    (F H : S → E.Carrier) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (p : S) (q : E2 → S) (O A : Set E2)
    (hO : IsOpen O) (hA : IsCompact A) (hAO : A ⊆ O) (hOhalf : O ⊆ halfDisc W.R)
    (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O)
    (hqs : MapsTo q O (surfaceChart p).source)
    (hqi : ∀ x ∈ O, q x ∉ S.boundary) (hqinj : InjOn q O)
    (u v : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hv : ContDiffOn ℝ ∞ v O)
    (hgraphF : ∀ x ∈ O, F (q x) = localCollar D s (jetPoint (x,u x,0)))
    (hgraphH : ∀ x ∈ O, H (q x) = localCollar D s (jetPoint (x,v x,0)))
    (hheightu : ∀ x ∈ A, |u x| < D.eta) (hheightv : ∀ x ∈ A, |v x| < D.eta)
    (hjetu : ∀ x ∈ A, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (hjetv : ∀ x ∈ A, jetPoint (x,v x,planarGradient v x) ∈ W.V)
    (heq : EqOn F H (q '' A)ᶜ) :
    area g H - area g F =
      (∫ x in A, W.density (x,v x,planarGradient v x)) -
      (∫ x in A, W.density (x,u x,planarGradient u x)) := by
  have hdenF (x : E2) (hx : x ∈ A) :
      native_parametric_density_v475 g (F ∘ q) x = W.density (x,u x,planarGradient u x) := by
    change native_parametric_density_v475 g (fun z => F (q z)) x = _
    rw [native_parametric_density_of_local_equality_v475 g _ _ x
      (Filter.eventuallyEq_of_mem (hO.mem_nhds (hAO hx)) (fun z hz => hgraphF z hz))]
    exact actual_parametric_graph_density_v475 D s W u x (hOhalf (hAO hx))
      ((hu.contDiffAt (hO.mem_nhds (hAO hx))).differentiableAt (by simp))
      (hheightu x hx) (hjetu x hx)
  have hdenH (x : E2) (hx : x ∈ A) :
      native_parametric_density_v475 g (H ∘ q) x = W.density (x,v x,planarGradient v x) := by
    change native_parametric_density_v475 g (fun z => H (q z)) x = _
    rw [native_parametric_density_of_local_equality_v475 g _ _ x
      (Filter.eventuallyEq_of_mem (hO.mem_nhds (hAO hx)) (fun z hz => hgraphH z hz))]
    exact actual_parametric_graph_density_v475 D s W v x (hOhalf (hAO hx))
      ((hv.contDiffAt (hO.mem_nhds (hAO hx))).differentiableAt (by simp))
      (hheightv x hx) (hjetv x hx)
  rw [native_parameter_area_change_v475 g F H hF hH p q O A hO hA hAO hq hqs hqi hqinj heq]
  rw [setIntegral_congr_fun hA.measurableSet hdenH,setIntegral_congr_fun hA.measurableSet hdenF]

#print axioms actual_graph_parameter_area_change_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
