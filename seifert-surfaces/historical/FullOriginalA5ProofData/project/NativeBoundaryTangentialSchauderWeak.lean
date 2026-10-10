import NativeBoundaryTangentialSchauderData

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization QuasilinearBootstrap
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_zero_source_linear_weak_of_negative_curl
    (U : Set E2) (hU : IsOpen U) (C : LinearizedCoefficients) (v f : E2 → ℝ)
    (hv : ContDiffOn ℝ 1 v U) (hf : ContDiffOn ℝ 1 f U)
    (hc : C.c = 0) (hb : C.b = 0) (hq : C.q = 0) (hCf : C.f = 0)
    (hV : DeGiorgi.MemW1pWitness 2 v U) (hF : DeGiorgi.MemW1pWitness 2 f U)
    (hrel : ∀ x ∈ U, C.a x (planarGradient v x) + C.d x =
      -nativeQuarterTurn (planarGradient f x)) :
    LinearWeakEquation U C v hV.weakGrad := by
  have hvEq := R1_classical_weak_gradient_agrees U hU v hv hV
  have hfEq := R1_classical_weak_gradient_agrees U hU f hf hF
  have hEq : (fun x => linearizedFlux C v hV.weakGrad x) =ᵐ[volume.restrict U]
      (fun x => -nativeQuarterTurn (hF.weakGrad x)) := by
    filter_upwards [hvEq, hfEq, ae_restrict_mem hU.measurableSet] with x hxv hxf hx
    simp only [linearizedFlux, hc, Pi.zero_apply, smul_zero, add_zero, hxv, hxf]
    exact hrel x hx
  intro ψ hs hψc ht
  obtain ⟨hi, hz⟩ := native_rotated_weak_gradient_divergence_zero U f hF ψ hs hψc ht
  have hiNeg : IntegrableOn (fun x => inner ℝ (-nativeQuarterTurn (hF.weakGrad x))
      (planarGradient ψ x)) U := by
    apply hi.neg.congr
    exact Eventually.of_forall (fun x => by simp only [Pi.neg_apply, inner_neg_left])
  have hiFlux : IntegrableOn (fun x => inner ℝ (linearizedFlux C v hV.weakGrad x)
      (planarGradient ψ x)) U := by
    apply hiNeg.congr
    filter_upwards [hEq] with x hx
    rw [hx]
  have hsource (x : E2) : linearizedSource C v hV.weakGrad x = 0 := by
    simp [linearizedSource, hb, hq, hCf]
  refine ⟨hiFlux, by simp only [hsource, zero_mul]; exact integrable_zero _ _ _, ?_⟩
  simp only [hsource, zero_mul, sub_zero]
  calc
    _ = ∫ x in U, inner ℝ (-nativeQuarterTurn (hF.weakGrad x)) (planarGradient ψ x) := by
      apply integral_congr_ae
      filter_upwards [hEq] with x hx
      rw [hx]
    _ = -(∫ x in U, inner ℝ (nativeQuarterTurn (hF.weakGrad x)) (planarGradient ψ x)) := by
      simp only [inner_neg_left, integral_neg]
    _ = 0 := by rw [hz, neg_zero]

/-- Actual tangential zero-trace derivative, actual H1 gradients, and its
zero-scalar-source weak equation under only the original solution state. -/
theorem C1QuasilinearDirichletSolution.local_actual_tangential_schauder_weak
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      let V := Metric.ball c r ∩ {x : E2 | 0 < x 0}
      let v := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1)
      DeGiorgi.MemW1p 2 v V ∧
      (∀ x ∈ Metric.ball c r ∩ {x : E2 | x 0 = 0}, v x = 0) ∧
      ∀ hV : DeGiorgi.MemW1pWitness 2 v V,
        LinearWeakEquation V (nativeTangentialSchauderCoefficients ρ Q g u) v hV.weakGrad := by
  obtain ⟨s, hs, hsball, hflux⟩ := hsolution.local_native_flux_memW1p hρ c hc
  obtain ⟨t, ht, htball, hD⟩ := hsolution.local_tangential_derivative_memW1p hρ c hc
  let r := min s t
  have hr : 0 < r := lt_min hs ht
  let V := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hVopen : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hVs : V ⊆ Metric.ball c s ∩ {x : E2 | 0 < x 0} := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
  have hVt : V ⊆ Metric.ball c t ∩ {x : E2 | 0 < x 0} := fun x hx =>
    ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
  have hball : Metric.closedBall c r ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hsball
  have hVO : V ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  let D := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let G := fun x : E2 => deriv g.value (x 1)
  let v := fun x => D x - G x
  have hGball := (R1_C1_memW1p_on_ball (Metric.ball 0 ρ) Metric.isOpen_ball G
    (g.smooth_deriv_extension_on_ball.of_le (by simp)) c r hr hball).1
  let hGw := hGball.someWitness.restrict hVopen (fun x hx => hx.1)
  let hDw := hD.someWitness.restrict hVopen hVt
  have hvSob : DeGiorgi.MemW1p 2 v V := by
    have hh := (hDw.add (hGw.smul (-1))).memW1p
    simpa only [Pi.add_apply, Pi.smul_apply, neg_one_smul, neg_one_mul, sub_eq_add_neg, v] using hh
  have hvC1 : ContDiffOn ℝ 1 v V :=
    ((hsolution.smooth_partial_on_openHalfDisc 1).mono hVO |>.of_le (by simp)).sub
      ((g.smooth_deriv_extension_on_ball.mono (fun x hx => (hVO hx).1)).of_le (by simp))
  let F := fun x => Q.flux (firstJetWithin ρ u x) 0
  let hFw := (hflux 0).2.someWitness.restrict hVopen hVs
  have hFC1 : ContDiffOn ℝ 1 F V := (hsolution.smooth_flux_component_on_openHalfDisc 0).mono hVO |>.of_le (by simp)
  refine ⟨r, hr, hball, hvSob, ?_, ?_⟩
  · intro x hx
    have hxFlat : x ∈ flatBoundary ρ := ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
    change fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1) - deriv g.value (x 1) = 0
    exact sub_eq_zero.mpr (hsolution.tangential_derivative_trace hρ hxFlat)
  · intro hV
    exact native_zero_source_linear_weak_of_negative_curl V hVopen
      (nativeTangentialSchauderCoefficients ρ Q g u) v F hvC1 hFC1 rfl rfl rfl rfl hV hFw
      (fun x hx => hsolution.native_tangential_schauder_conjugate_relation x (hVO hx))

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
