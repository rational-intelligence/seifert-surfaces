import A5SmoothProjectionInverse
import A5NativeMetricGraphRegularity

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

theorem native_graph_height_smooth_of_graph_smooth
    (G : NativeMetricGraph h) (U : Set E2)
    (hsmooth : ContDiffOn ℝ ∞ (graphMap G.origin G.plane G.normal G.height) U) :
    ContDiffOn ℝ ∞ G.height U := by
  let L : (E2 × ℝ) →L[ℝ] E3 :=
    G.plane.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight G.normal
  have hL : Function.Bijective L := G.splitting
  let e : (E2 × ℝ) ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  have hc : ContDiffOn ℝ ∞
      (fun x => (e.symm (graphMap G.origin G.plane G.normal G.height x - G.origin)).2) U :=
    (e.symm.contDiff.comp_contDiffOn (hsmooth.sub contDiffOn_const)).snd
  apply hc.congr
  intro x hx
  have he : graphMap G.origin G.plane G.normal G.height x - G.origin =
      e (x, G.height x) := by
    change G.origin + G.plane x + G.height x • G.normal - G.origin =
      G.plane x + G.height x • G.normal
    abel
  rw [he, e.symm_apply_apply]

/-- On an actual open native-piece region, continuity of the coordinate
lift suffices. Its smoothness, regular derivative, smooth graph height and
actual metric minimality are all derived. -/
theorem native_graph_open_side_of_continuous_lift
    (G : NativeMetricGraph h) (Φ : E2 → N) (D Ω U : Set E2)
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hminimal : IsMinimalPatch h Φ D)
    (hinside : Ω ⊆ D ∩ Φ ⁻¹' G.coordinates.chart.source)
    (P : E3 →L[ℝ] E2) (κ : E2 → E2)
    (hκ : ContinuousOn κ U) (hκimage : MapsTo κ U Ω)
    (htransverse : ∀ y ∈ Ω, Function.Bijective
      (fderiv ℝ (fun z => P (G.coordinates.chart (Φ z) - G.origin)) y))
    (hsection : ∀ x ∈ U, P (G.coordinates.chart (Φ (κ x)) - G.origin) = x)
    (hgraph : EqOn (graphMap G.origin G.plane G.normal G.height)
      ((G.coordinates.chart ∘ Φ) ∘ κ) U) :
    ContDiffOn ℝ ∞ G.height U ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) U := by
  have hΦ : ContDiffOn ℝ ∞ (G.coordinates.chart ∘ Φ) Ω :=
    (hminimal.2.2 G.coordinates).1.mono hinside
  have hQ : ContDiffOn ℝ ∞
      (fun z => P (G.coordinates.chart (Φ z) - G.origin)) Ω :=
    P.contDiff.comp_contDiffOn (hΦ.sub contDiffOn_const)
  obtain ⟨hk, hkr⟩ := smooth_regular_continuous_inverse_section _ κ Ω U hΩ hU
    hQ htransverse hκ hκimage hsection
  have hm := native_metric_graph_minimal_of_native_reparametrization G Φ D Ω U
    hΩ hU hminimal hinside κ hk hκimage hkr hgraph
  exact ⟨native_graph_height_smooth_of_graph_smooth G U hm.1, hm⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
