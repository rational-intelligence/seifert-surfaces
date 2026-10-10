import A5ClassicalWeakEquation
import A5NativeGraphImageChart

set_option autoImplicit false
open scoped Manifold ContDiff BigOperators
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

/-- Actual smooth metric minimality on an open graph region constructs
the full weak equation with the same explicit flux and lower-order term. -/
theorem native_metric_graph_weak_of_minimal
    (G : NativeMetricGraph h) (U : Set E2) (hU : IsOpen U)
    (hUG : U ⊆ G.disc) (hsmooth : ContDiffOn ℝ ∞ G.height U)
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U) :
    IsWeakDivergenceSolutionOn U G.metricFlux G.metricLowerOrder G.height := by
  obtain ⟨C⟩ := native_graph_actual_metric_operator_control G
  have hgrad : ContDiffOn ℝ ∞ (planarGradient G.height) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact (((hsmooth.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul
      contDiffOn_const)
  have hj : ContDiffOn ℝ ∞ G.attainedJet U :=
    contDiffOn_id.prodMk (hsmooth.prodMk hgrad)
  have hf : ContDiffOn ℝ ∞ G.attainedFlux U :=
    C.flux_smooth.comp hj (fun x hx => C.attained x (hUG hx))
  have hb : ContDiffOn ℝ ∞ G.attainedLowerOrder U :=
    C.lowerOrder_smooth.comp hj (fun x hx => C.attained x (hUG hx))
  intro φ hφ hc hs
  apply weak_flux_identity_of_classical_equation U hU G.attainedFlux
    G.attainedLowerOrder (hf.of_le (by simp)) hb.continuousOn
  · exact native_graph_classical_equation G U hU hUG hsmooth hminimal
  · exact hφ
  · exact hc
  · exact hs

/-- Once the punctured graph is smooth and genuinely minimal for the
actual ambient metric, its remaining vertex is removable. The weak PDE
and its elliptic operator are constructed inside the proof. -/
theorem native_metric_graph_smooth_of_punctured_minimal
    (G : NativeMetricGraph h) (q : E2) (hq : q ∈ G.disc)
    (hsmooth : ContDiffOn ℝ ∞ G.height (G.disc \ {q}))
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (G.disc \ {q})) :
    ContDiffOn ℝ ∞ G.height G.disc := by
  apply native_metric_graph_smooth_across_vertex G q hq
  exact native_metric_graph_weak_of_minimal G (G.disc \ {q})
    (Metric.isOpen_ball.sdiff isClosed_singleton) sdiff_subset hsmooth hminimal

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
