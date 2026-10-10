import A5NativeMetricGraphEquation
import A5CurvedSeamAnalyticBridge
import A5VertexAnalyticBridge

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

theorem NativeMetricGraph.height_C1_disc (G : NativeMetricGraph h) :
    ContDiffOn ℝ 1 G.height G.disc := by
  apply G.height_C1.mono
  intro x hx
  change dist x 0 ≤ 2 * G.radius
  have hxr : dist x 0 < G.radius := hx
  linarith [G.radius_pos]

/-- The same actual metric graph is smooth across a curved seam, starting
with only C1 regularity across the seam and smooth minimality on its open
sides. The elliptic operator and the whole weak equation are constructed. -/
theorem native_metric_graph_smooth_across_arc
    (G : NativeMetricGraph h) (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (hgeom : SignedArcGeometry G.disc s γ left right)
    (hsmooth : ∀ p : Bool, ContDiffOn ℝ ∞ G.height (signedDomain G.disc s p))
    (hminimal : ∀ p : Bool, IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (signedDomain G.disc s p)) :
    ContDiffOn ℝ ∞ G.height G.disc := by
  obtain ⟨C⟩ := native_graph_actual_metric_operator_control G
  apply smooth_C1_graph_across_curved_arc G.disc s γ left right hgeom
    C.jetDomain C.jetDomain_open (G.operator C) C.elliptic G.height G.height_C1_disc
    C.attained hsmooth
  intro p x hx
  have hopen : IsOpen (signedDomain G.disc s p) := by
    cases p
    · exact hgeom.signed_smooth.continuousOn.isOpen_inter_preimage hgeom.disc_open isOpen_Iio
    · exact hgeom.signed_smooth.continuousOn.isOpen_inter_preimage hgeom.disc_open isOpen_Ioi
  have he := native_graph_classical_equation G (signedDomain G.disc s p) hopen
    (fun _ hy => hy.1) (hsmooth p) (hminimal p) x hx
  exact eq_neg_of_add_eq_zero_left he

/-- At a remaining isolated vertex, the explicit actual metric operator
from the C1 graph combines with the paid point-removal and interior bootstrap. -/
theorem native_metric_graph_smooth_across_vertex
    (G : NativeMetricGraph h) (q : E2) (hq : q ∈ G.disc)
    (hweak : IsWeakDivergenceSolutionOn (G.disc \ {q})
      G.metricFlux G.metricLowerOrder G.height) :
    ContDiffOn ℝ ∞ G.height G.disc := by
  obtain ⟨C⟩ := native_graph_actual_metric_operator_control G
  exact smooth_C1_graph_of_punctured_weak_equation G.disc Metric.isOpen_ball q hq
    C.jetDomain C.jetDomain_open (G.operator C) C.elliptic G.height G.height_C1_disc
    C.attained hweak

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
