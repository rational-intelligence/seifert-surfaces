import NativeBoundarySchauderCapLp

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

/-- The original actual tangential derivative satisfies the scalar divergence
equation with the original principal matrix and negative actual forcing. -/
theorem C1QuasilinearDirichletSolution.local_actual_tangential_weak_divergence
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
      let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
      ∃ hV : DeGiorgi.MemW1pWitness 2 v U,
        WeakDivergenceWithData U (nativePrincipalWithin ρ Q u)
          (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d x)
          (fun _ => 0) v hV.weakGrad := by
  obtain ⟨t, ht, htball, hMem, _, hWeak⟩ :=
    hsolution.local_actual_tangential_schauder_weak hρ c hc
  obtain ⟨δ, H, α, hδ, hα, _, hδball, _, hd⟩ :=
    hsolution.local_holder_tangential_schauder_coefficients hρ c hc
  let r := min t δ
  have hr : 0 < r := lt_min ht hδ
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hUt : U ⊆ Metric.ball c t ∩ {x : E2 | 0 < x 0} := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
  have hUδ : U ⊆ Metric.ball c δ ∩ {x : E2 | 0 < x 0} := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
  let hVr := hMem.someWitness.restrict hU hUt
  have hWr : LinearWeakEquation U (nativeTangentialSchauderCoefficients ρ Q g u)
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1))
      hVr.weakGrad :=
    native_linear_weak_restrict _ U hU hUt _ _ _ (hWeak hMem.someWitness)
  have hdLp : MemLp (nativeTangentialSchauderCoefficients ρ Q g u).d 2 (volume.restrict U) :=
    (native_continuous_closed_cap_memLp c δ _ (hd.continuousOn hα)).mono_measure
      (Measure.restrict_mono hUδ le_rfl)
  refine ⟨r, hr, (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans htball, hVr, ?_⟩
  exact native_zero_source_linear_to_weak_divergence U hU.measurableSet
    (nativeTangentialSchauderCoefficients ρ Q g u) (nativePrincipalWithin ρ Q u) _ hVr
    rfl rfl rfl rfl (fun x _ => native_principalWithin_toEuclideanCLM ρ Q u x) hdLp hWr

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
