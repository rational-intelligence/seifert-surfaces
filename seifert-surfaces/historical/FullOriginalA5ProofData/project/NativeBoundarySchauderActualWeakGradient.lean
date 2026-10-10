import NativeBoundarySchauderOriginalWeak

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

theorem native_memW1pWitness_actual_classical_gradient
    (U : Set E2) (hU : IsOpen U) (v : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v U) (hV : DeGiorgi.MemW1pWitness 2 v U) :
    ∃ hC : DeGiorgi.MemW1pWitness 2 v U, hC.weakGrad = planarGradient v := by
  have heq := R1_classical_weak_gradient_agrees U hU v hv hV
  let hC : DeGiorgi.MemW1pWitness 2 v U :=
    { memLp := hV.memLp
      weakGrad := planarGradient v
      weakGrad_component_memLp := fun i => (memLp_congr_ae (heq.fun_comp (fun q : E2 => q i))).mp
        (hV.weakGrad_component_memLp i)
      isWeakGrad := by
        intro i ψ hs hc ht
        have he := hV.isWeakGrad i ψ hs hc ht
        have hr : (∫ x in U, hV.weakGrad x i * ψ x) =
            ∫ x in U, planarGradient v x i * ψ x := by
          apply integral_congr_ae
          filter_upwards [heq] with x hx
          rw [hx]
        rwa [hr] at he }
  exact ⟨hC, rfl⟩

theorem native_zero_source_weak_divergence_gradient_congr
    (U : Set E2) (a : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (e : E2 → E2) (v : E2 → ℝ) (G D : E2 → E2)
    (hw : WeakDivergenceWithData U a e (fun _ => 0) v G)
    (hD : H1On U v D) (he : G =ᵐ[volume.restrict U] D) :
    WeakDivergenceWithData U a e (fun _ => 0) v D := by
  refine ⟨hD, ?_⟩
  intro ψ hs hc ht
  obtain ⟨hi, hie, hEq⟩ := hw.2 ψ hs hc ht
  have hflux : (fun x => inner ℝ (matrixAction (a x) (G x)) (planarGradient ψ x)) =ᵐ[volume.restrict U]
      (fun x => inner ℝ (matrixAction (a x) (D x)) (planarGradient ψ x)) := by
    filter_upwards [he] with x hx
    rw [hx]
  exact ⟨hi.congr hflux, hie, (integral_congr_ae hflux).symm.trans hEq⟩

/-- The exact original scalar equation uses its own actual classical interior
gradient, so its paid flat trace and scalar provider share identical data. -/
theorem C1QuasilinearDirichletSolution.local_actual_tangential_classical_weak_divergence
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
      let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
      WeakDivergenceWithData U (nativePrincipalWithin ρ Q u)
        (fun x => -(nativeTangentialSchauderCoefficients ρ Q g u).d x)
        (fun _ => 0) v (planarGradient v) := by
  obtain ⟨r, hr, hball, hV, hw⟩ := hsolution.local_actual_tangential_weak_divergence hρ c hc
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsub : U ⊆ openHalfDisc ρ := fun x hx => ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have hv : ContDiffOn ℝ 1 v U :=
    ((hsolution.smooth_partial_on_openHalfDisc 1).mono hsub |>.of_le (by simp)).sub
      ((g.smooth_deriv_extension_on_ball.mono (fun x hx => (hsub hx).1)).of_le (by simp))
  obtain ⟨hC, hCEq⟩ := native_memW1pWitness_actual_classical_gradient U hU v hv hV
  have hH := native_h1_of_memW1pWitness U v hC
  rw [hCEq] at hH
  exact ⟨r, hr, hball, native_zero_source_weak_divergence_gradient_congr U _ _ v _ _ hw hH
    (R1_classical_weak_gradient_agrees U hU v hv hV)⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
