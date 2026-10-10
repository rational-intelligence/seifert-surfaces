import A5MinimalReparametrization

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

/-- The native immersion condition gives the rank of its actual coordinate
map; the source region is an honest open subset of the native patch. -/
theorem native_minimal_patch_coordinate_rank
    (Φ : E2 → N) (D Ω : Set E2) (hΩ : IsOpen Ω)
    (hminimal : IsMinimalPatch h Φ D) (c : SmoothAmbientChart N)
    (hinside : Ω ⊆ D ∩ Φ ⁻¹' c.chart.source) :
    ∀ x ∈ Ω, Function.Injective (fderiv ℝ (c.chart ∘ Φ) x) := by
  intro x hx
  have hp : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E3) Φ x :=
    ((hminimal.1.mono (fun y hy => (hinside hy).1)).contMDiffAt
      (hΩ.mem_nhds hx)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (Φ x) :=
    (c.smooth.contMDiffAt (c.chart.open_source.mem_nhds (hinside hx).2)).mdifferentiableAt
      (by simp)
  have hd : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hm : Function.Injective (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E3) (c.chart ∘ Φ) x) := by
    rw [mfderiv_comp x hc hp]
    exact (hd.mfderiv_injective (hinside hx).2).comp (hminimal.2.1 x (hinside hx).1)
  rw [mfderiv_eq_fderiv] at hm
  intro v w hvw
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm.injective
    (hm (a₁ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v)
      (a₂ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w) (by simpa using hvw))

/-- An actual native minimal patch supplies the minimality of the same
metric graph after a regular smooth source-coordinate change. The actual
metric, chart, graph map and source image identity are retained. -/
theorem native_metric_graph_minimal_of_native_reparametrization
    (G : NativeMetricGraph h) (Φ : E2 → N) (D Ω U : Set E2)
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hminimal : IsMinimalPatch h Φ D)
    (hinside : Ω ⊆ D ∩ Φ ⁻¹' G.coordinates.chart.source)
    (κ : E2 → E2) (hκ : ContDiffOn ℝ ∞ κ U) (hκimage : MapsTo κ U Ω)
    (hκregular : ∀ x ∈ U, Function.Bijective (fderiv ℝ κ x))
    (hgraph : EqOn (graphMap G.origin G.plane G.normal G.height)
      ((G.coordinates.chart ∘ Φ) ∘ κ) U) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  obtain ⟨hsmooth, hsymm, hpos⟩ := native_graph_actual_chart_metric G
  let g : CoordinateMetric G.coordinates.chart.target :=
    ⟨actualChartTensor h G.coordinates, hsmooth, hsymm, hpos⟩
  have hcoord : IsMinimalParametrizationOn g.tensor (G.coordinates.chart ∘ Φ) Ω :=
    ⟨(hminimal.2.2 G.coordinates).1.mono hinside,
      fun x hx => (hminimal.2.2 G.coordinates).2 x (hinside hx)⟩
  have himage : MapsTo (G.coordinates.chart ∘ Φ) Ω G.coordinates.chart.target :=
    fun x hx => G.coordinates.chart.map_source (hinside hx).2
  have he := coordinate_minimality_reparametrization G.coordinates.chart.target
    G.coordinates.chart.open_target g Ω U hΩ hU (G.coordinates.chart ∘ Φ) hcoord
    himage (native_minimal_patch_coordinate_rank Φ D Ω hΩ hminimal G.coordinates hinside)
    κ hκ hκimage hκregular
  exact coordinate_minimality_congr g.tensor _ _ U hU he hgraph

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
