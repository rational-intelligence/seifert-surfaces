import A5MinimalityClosure

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N] {h : AmbientMetric N}

theorem native_metric_graph_exists_projection (G : NativeMetricGraph h) :
    ∃ P : E3 →L[ℝ] E2, (∀ v, P (G.plane v) = v) ∧ P G.normal = 0 := by
  let L : (E2 × ℝ) →L[ℝ] E3 :=
    G.plane.comp (ContinuousLinearMap.fst ℝ E2 ℝ) +
      (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight G.normal
  have hL : Function.Bijective L := G.splitting
  let e : (E2 × ℝ) ≃L[ℝ] E3 := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hL.1) (LinearMap.range_eq_top.mpr hL.2)
  let P := (ContinuousLinearMap.fst ℝ E2 ℝ).comp e.symm.toContinuousLinearMap
  refine ⟨P, ?_, ?_⟩
  · intro v
    have he : e (v, 0) = G.plane v := by
      change G.plane v + (0 : ℝ) • G.normal = G.plane v
      simp
    change (e.symm (G.plane v)).1 = v
    rw [← he, e.symm_apply_apply]
  · have he : e (0, 1) = G.normal := by
      change G.plane 0 + (1 : ℝ) • G.normal = G.normal
      simp
    change (e.symm G.normal).1 = 0
    rw [← he, e.symm_apply_apply]

/-- Smoothness obtained by regularity preserves actual metric minimality
across any closed exceptional set whose complement is dense. -/
theorem native_metric_graph_minimal_of_dense
    (G : NativeMetricGraph h) (W : Set E2) (hW : W ⊆ G.disc)
    (hdense : G.disc ⊆ closure W) (hsmooth : ContDiffOn ℝ ∞ G.height G.disc)
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) W) :
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) G.disc := by
  obtain ⟨hgs, hsymm, hpos⟩ := native_graph_actual_chart_metric G
  let g : CoordinateMetric G.coordinates.chart.target :=
    ⟨actualChartTensor h G.coordinates, hgs, hsymm, hpos⟩
  let Φ := graphMap G.origin G.plane G.normal G.height
  have hΦ : ContDiffOn ℝ ∞ Φ G.disc :=
    (contDiffOn_const.add G.plane.contDiff.contDiffOn).add (hsmooth.smul_const G.normal)
  obtain ⟨P, hP, hn⟩ := native_metric_graph_exists_projection G
  apply coordinate_minimality_of_dense_projected_patch G.coordinates.chart.target
    G.coordinates.chart.open_target g G.disc W Metric.isOpen_ball hW hdense Φ hΦ
    (fun x hx => G.graph_in_chart (by
      have hh : dist x 0 < G.radius := hx
      change dist x 0 ≤ 2 * G.radius
      linarith [G.radius_pos])) P _ hminimal
  intro x hx
  have hu := (hsmooth.contDiffAt (Metric.isOpen_ball.mem_nhds hx)).differentiableAt (by simp)
  have hd : HasFDerivAt Φ (G.plane + (fderiv ℝ G.height x).smulRight G.normal) x :=
    (G.plane.hasFDerivAt.const_add G.origin).add (hu.hasFDerivAt.smul_const G.normal)
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  change P (G.plane v + fderiv ℝ G.height x v • G.normal) = v
  rw [map_add, map_smul, hP, hn, smul_zero, add_zero]

/-- The punctured minimal graph extends to a smooth minimal graph with
the same height, coordinates, metric, and image. -/
theorem native_metric_graph_smooth_minimal_of_punctured_minimal
    (G : NativeMetricGraph h) (q : E2) (hq : q ∈ G.disc)
    (hsmooth : ContDiffOn ℝ ∞ G.height (G.disc \ {q}))
    (hminimal : IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) (G.disc \ {q})) :
    ContDiffOn ℝ ∞ G.height G.disc ∧
    IsMinimalParametrizationOn (actualChartTensor h G.coordinates)
      (graphMap G.origin G.plane G.normal G.height) G.disc := by
  have hs := native_metric_graph_smooth_of_punctured_minimal G q hq hsmooth hminimal
  refine ⟨hs, native_metric_graph_minimal_of_dense G (G.disc \ {q}) sdiff_subset ?_ hs hminimal⟩
  exact (dense_compl_singleton q).open_subset_closure_inter Metric.isOpen_ball

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
