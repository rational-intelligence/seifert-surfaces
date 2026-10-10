import A5NativeMetricGraphRegularity

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

/-- Radius restriction retains the exact native graph, chart and metric
operator. Only its compact region of control is reduced. -/
def NativeMetricGraph.restrictRadius (G : NativeMetricGraph h)
    (r : ℝ) (hr : 0 < r) (hle : r ≤ G.radius) : NativeMetricGraph h where
  coordinates := G.coordinates
  origin := G.origin
  plane := G.plane
  normal := G.normal
  splitting := G.splitting
  height := G.height
  radius := r
  radius_pos := hr
  height_C1 := G.height_C1.mono (Metric.closedBall_subset_closedBall (by linarith))
  graph_in_chart := G.graph_in_chart.mono_left
    (Metric.closedBall_subset_closedBall (by linarith))

theorem signed_arc_geometry_restrict
    {D V : Set E2} {s : E2 → ℝ} {γ : ℝ → E2} {left right : ℝ}
    (G : SignedArcGeometry D s γ left right) (hV : IsOpen V) (hVD : V ⊆ D) :
    SignedArcGeometry V s γ left right := by
  refine ⟨hV, G.signed_smooth.mono hVD,
    fun x hx => G.signed_regular x (hVD hx), G.arc_smooth,
    G.arc_embedding, G.arc_regular, ?_, ?_⟩
  · ext x
    constructor
    · intro hx
      have hm : x ∈ {y ∈ D | s y = 0} := ⟨hVD hx.1, hx.2⟩
      rw [G.zero_set_exact] at hm
      exact ⟨hm.1, hx.1⟩
    · intro hx
      have hm : x ∈ (γ '' Ioo left right) ∩ D := ⟨hx.1, hVD hx.2⟩
      rw [← G.zero_set_exact] at hm
      exact ⟨hx.2, hm.2⟩
  · intro K hK hKV
    exact G.compact_parameter_control K hK (hKV.trans hVD)

/-- The independently constructed native graph and projected arc need not
have the same radius. Smoothness follows on a common positive radius,
with the exact original height function and actual metric retained. -/
theorem native_metric_graph_smooth_on_common_arc_radius
    (G : NativeMetricGraph h) (ρ : ℝ) (hρ : 0 < ρ)
    (s : E2 → ℝ) (γ : ℝ → E2) (left right : ℝ)
    (hgeom : SignedArcGeometry (Metric.ball 0 ρ) s γ left right)
    (hsmooth : ∀ p : Bool, ContDiffOn ℝ ∞ G.height
      (signedDomain (G.disc ∩ Metric.ball 0 ρ) s p))
    (hminimal : ∀ p : Bool, IsMinimalParametrizationOn
      (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height)
      (signedDomain (G.disc ∩ Metric.ball 0 ρ) s p)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ G.radius ∧ r ≤ ρ ∧
      ContDiffOn ℝ ∞ G.height (Metric.ball 0 r) := by
  let r := min G.radius ρ
  have hr : 0 < r := lt_min G.radius_pos hρ
  have hrG : r ≤ G.radius := min_le_left _ _
  have hrρ : r ≤ ρ := min_le_right _ _
  let H := G.restrictRadius r hr hrG
  have hHG : H.disc ⊆ G.disc := Metric.ball_subset_ball hrG
  have hHρ : H.disc ⊆ Metric.ball 0 ρ := Metric.ball_subset_ball hrρ
  have hside (p : Bool) : signedDomain H.disc s p ⊆
      signedDomain (G.disc ∩ Metric.ball 0 ρ) s p := by
    intro x hx
    exact ⟨⟨hHG hx.1, hHρ hx.1⟩, hx.2⟩
  have hgeomH := signed_arc_geometry_restrict hgeom Metric.isOpen_ball hHρ
  have hs : ContDiffOn ℝ ∞ H.height H.disc := by
    apply native_metric_graph_smooth_across_arc H s γ left right hgeomH
    · intro p
      exact (hsmooth p).mono (hside p)
    · intro p
      rcases hminimal p with ⟨hc, hm⟩
      exact ⟨hc.mono (hside p), fun x hx => hm x (hside p hx)⟩
  exact ⟨r, hr, hrG, hrρ, hs⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
