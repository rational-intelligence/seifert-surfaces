import NativeBoundaryNormalFluxCoefficients

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation

/-- The original C1 solution supplies the same normal flux, a continuous H1
even extension, and its actual reflected dual equation at every flat center.
The tangential conjugate and all weak gradients are constructed from that
solution. -/
theorem C1QuasilinearDirichletSolution.local_actual_normal_flux_neumann_equation
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      let F := fun x => Q.flux (firstJetWithin ρ u (x + c)) 0
      let C := translateLinearizedCoefficients (nativeNormalFluxCoefficients ρ Q g u) c
      ContinuousOn (nativeEvenExtension F) (Metric.ball 0 r) ∧
      DeGiorgi.MemW1p 2 (nativeEvenExtension F) (Metric.ball 0 r) ∧
      ∀ κ : ℝ, ∀ hF : DeGiorgi.MemW1pWitness 2 (nativeEvenExtension F) (Metric.ball 0 r),
        LinearWeakEquation (Metric.ball 0 r) (nativeNeumannCoefficients r κ C)
          (nativeEvenExtension F) hF.weakGrad := by
  obtain ⟨s, hs, hball, hflux⟩ := hsolution.local_native_flux_memW1p hρ c hc
  obtain ⟨t, ht, htball, hOdd⟩ := hsolution.local_tangential_derivative_odd_memW1p hρ c hc
  let r := min s (t / 2)
  have hr : 0 < r := lt_min hs (half_pos ht)
  have hrs : r ≤ s := min_le_left _ _
  have hrt : r ≤ t / 2 := min_le_right _ _
  have hcf : c 0 = 0 := hc.2
  let U := Metric.ball c s ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hpre : (fun x : E2 => x + c) ⁻¹' U = openHalfDisc s :=
    (native_flat_translation_halfDisc c hcf s).1
  let F : E2 → ℝ := fun x => Q.flux (firstJetWithin ρ u (x + c)) 0
  let w : E2 → ℝ := fun x =>
    fderivWithin ℝ u (closedHalfDisc ρ) (x + c) (coordinateVector 2 1) - deriv g.value ((x + c) 1)
  let C := translateLinearizedCoefficients (nativeNormalFluxCoefficients ρ Q g u) c
  have hshift : DeGiorgi.MemW1p 2 F (openHalfDisc s) := by
    rw [← hpre]
    exact native_memW1p_translation U hU.measurableSet c
      (fun x => Q.flux (firstJetWithin ρ u x) 0) (hflux 0).2
  have hsub : openHalfDisc r ⊆ openHalfDisc s :=
    fun x hx => ⟨Metric.ball_subset_ball hrs hx.1, hx.2⟩
  have hEven : DeGiorgi.MemW1p 2 (nativeEvenExtension F) (Metric.ball 0 r) :=
    native_even_extension_memW1p r F
      ((hshift.someWitness.restrict (openHalfDisc_isOpen r) hsub).memW1p)
  have hOddSmall : DeGiorgi.MemW1p 2 (nativeOddExtension w) (Metric.ball 0 r) :=
    (hOdd.someWitness.restrict Metric.isOpen_ball (Metric.ball_subset_ball hrt)).memW1p
  have hclosed : Metric.closedBall c r ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall hrs).trans hball
  have hmap : MapsTo (fun x : E2 => x + c) (closedHalfDisc r) (closedHalfDisc ρ) := by
    intro x hx
    refine ⟨Metric.ball_subset_closedBall (hclosed ?_), ?_⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx.1
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hx.2
  have hmapOpen : MapsTo (fun x : E2 => x + c) (openHalfDisc r) (openHalfDisc ρ) := by
    intro x hx
    refine ⟨hclosed ?_, ?_⟩
    · have hb := Metric.ball_subset_closedBall hx.1
      simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero] using hb
    · simpa only [mem_ofPred_eq, PiLp.add_apply, hcf, add_zero] using hx.2
  have hFc : ContinuousOn F (closedHalfDisc r) :=
    (((EuclideanSpace.proj (0 : Fin 2)).continuous.continuousOn.comp
      (hsolution.continuous_boundary_coefficients hρ).1 (mapsTo_univ _ _)).comp
        (continuous_id.add continuous_const).continuousOn hmap)
  have hFs : ContDiffOn ℝ 1 F (openHalfDisc r) :=
    (hsolution.smooth_flux_component_on_openHalfDisc 0).of_le (by simp) |>.comp
      (contDiff_id.add contDiff_const).contDiffOn hmapOpen
  have hws : ContDiffOn ℝ 1 w (openHalfDisc r) :=
    (((hsolution.smooth_partial_on_openHalfDisc 1).sub
      (g.smooth_deriv_extension_on_ball.mono (fun x hx => hx.1))).of_le (by simp)).comp
        (contDiff_id.add contDiff_const).contDiffOn hmapOpen
  have hrel : ∀ x ∈ openHalfDisc r, C.a x (planarGradient F x) + C.d x =
      nativeQuarterTurn (planarGradient w x) := by
    intro x hx
    have hh := hsolution.native_normal_flux_conjugate_relation (x + c) (hmapOpen hx)
    have hFg : planarGradient F x =
        planarGradient (fun y => Q.flux (firstJetWithin ρ u y) 0) (x + c) :=
      planar_gradient_translation (fun y => Q.flux (firstJetWithin ρ u y) 0) c x
    have hwg : planarGradient w x = planarGradient (fun y =>
        fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) - deriv g.value (y 1)) (x + c) :=
      planar_gradient_translation (fun y =>
        fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) - deriv g.value (y 1)) c x
    rw [hFg, hwg]
    exact hh
  refine ⟨r, hr, hclosed, continuous_native_even_extension r F hFc, hEven, ?_⟩
  intro κ hF
  exact native_neumann_reflected_equation_of_conjugacy r κ C F w hFs hws hEven hOddSmall hrel hF

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
