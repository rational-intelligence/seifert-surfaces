import B1L1DirectWeakLower

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false

private theorem same_holder_minimum_transfer
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (P : SameHolderRepresentative Ω f d theta sigma beta) :
    SimultaneousMetricMinimum Ω M P.u d := by
  have harea : metricAreaDensity M P.u d =ᵐ[volume.restrict (disc 1)]
      metricAreaDensity M f d := by
    filter_upwards [P.same_map] with x hx
    simp only [metricAreaDensity, hx]
  have hdir : metricDirichletDensity M P.u d =ᵐ[volume.restrict (disc 1)]
      metricDirichletDensity M f d := by
    filter_upwards [P.same_map] with x hx
    simp only [metricDirichletDensity, metricE, metricH, hx]
  have harea_eq : metricArea M P.u d = metricArea M f d := integral_congr_ae harea
  have hdir_eq : metricDirichlet M P.u d = metricDirichlet M f d := by
    unfold metricDirichlet
    rw [integral_congr_ae hdir]
  refine ⟨⟨P.same_H1, theta, sigma, P.original_lift, P.same_Green⟩,
    minimum.area_integrable.congr harea.symm,
    minimum.dirichlet_integrable.congr hdir.symm, ?_, ?_, ?_⟩
  · intro q dq hq
    rw [harea_eq]
    exact minimum.area_minimum q dq hq
  · intro q dq hq
    rw [hdir_eq]
    exact minimum.dirichlet_minimum q dq hq
  · filter_upwards [minimum.weak_conformality, P.same_map] with x hx heq
    simpa only [metricE, metricH, metricF, heq] using hx

#print axioms same_holder_minimum_transfer
