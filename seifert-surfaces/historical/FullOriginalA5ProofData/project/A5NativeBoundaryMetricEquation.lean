import A5NativeVertexRemoval
import NativeBoundaryPreliminaries

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ,E3) ∞ N] {h : AmbientMetric N}

/-- A native metric graph, including one in an ambient chart that straightens
its projected longitude, supplies the complete actual Dirichlet bootstrap
context. The operator is exactly its metric area-density operator. -/
theorem native_metric_graph_boundary_dirichlet_context
    (G : NativeMetricGraph h) (ρ : ℝ) (hρ : 0 < ρ) (hρG : ρ < G.radius)
    (g : SmoothDirichletDatum ρ)
    (hboundary : ∀ x ∈ flatBoundary ρ, G.height x = g.value (x 1))
    (hsmooth : ContDiffOn ℝ ∞ G.height (openHalfDisc ρ))
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (openHalfDisc ρ)) :
    ∃ C : G.OperatorControl,
      C1QuasilinearDirichletSolution ρ C.jetDomain (G.operator C) g G.height := by
  obtain ⟨C⟩ := native_graph_actual_metric_operator_control G
  have hsub : closedHalfDisc ρ ⊆ G.disc := by
    intro x hx
    exact (Metric.mem_closedBall.mp hx.1).trans_lt hρG
  have hj (x : E2) (hx : x ∈ closedHalfDisc ρ) :
      firstJetWithin ρ G.height x = G.attainedJet x := by
    have hd : fderivWithin ℝ G.height (closedHalfDisc ρ) x = fderiv ℝ G.height x :=
      fderivWithin_eq_fderiv (closedHalfDisc_uniqueDiffOn hρ x hx)
        ((G.height_C1_disc.contDiffAt (Metric.isOpen_ball.mem_nhds (hsub hx))).differentiableAt
          (by norm_num))
    simp only [firstJetWithin, NativeMetricGraph.attainedJet,
      planarGradientWithin, planarGradient, hd]
  refine ⟨C,⟨C.jetDomain_open,C.elliptic,G.height_C1_disc.mono hsub,?_,?_,hboundary⟩⟩
  · intro x hx
    rw [hj x hx]
    exact C.attained x (hsub hx)
  · exact native_metric_graph_weak_of_minimal G (openHalfDisc ρ)
      (openHalfDisc_isOpen ρ) ((openHalfDisc_subset_closedHalfDisc ρ).trans hsub)
      hsmooth hminimal

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
