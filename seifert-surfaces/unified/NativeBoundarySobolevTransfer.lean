import NativeBoundarySobolevLimit

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization
open SeifertSurfaces.QuasilinearProviderBridge

theorem native_memW1p_congr
    (U : Set E2) (hU : MeasurableSet U) (f F : E2 → ℝ) (he : EqOn f F U)
    (hf : DeGiorgi.MemW1p 2 f U) : DeGiorgi.MemW1p 2 F U := by
  have hae : f =ᵐ[volume.restrict U] F := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact he hx
  refine ⟨(memLp_congr_ae hae).mp hf.1, ?_⟩
  intro i
  obtain ⟨G, hG, hw⟩ := hf.2 i
  refine ⟨G, hG, ?_⟩
  intro φ hs hc ht
  have hi : (∫ x in U, F x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  rw [hi]
  exact hw φ hs hc ht

theorem native_memW1p_translation
    (U : Set E2) (hU : MeasurableSet U) (c : E2) (f : E2 → ℝ)
    (hf : DeGiorgi.MemW1p 2 f U) :
    DeGiorgi.MemW1p 2 (fun x => f (x + c)) ((fun x : E2 => x + c) ⁻¹' U) := by
  let W := (fun x : E2 => x + c) ⁻¹' U
  have hmp : MeasurePreserving (fun x : E2 => x + c) (volume.restrict W) (volume.restrict U) :=
    (measurePreserving_add_right volume c).restrict_preimage hU
  have hemb : MeasurableEmbedding (fun x : E2 => x + c) := (Homeomorph.addRight c).measurableEmbedding
  refine ⟨hf.1.comp_measurePreserving hmp, ?_⟩
  intro i
  obtain ⟨G, hG, hw⟩ := hf.2 i
  refine ⟨fun x => G (x + c), hG.comp_measurePreserving hmp, ?_⟩
  intro φ hφ hc ht
  let ψ : E2 → ℝ := fun y => φ (y + -c)
  have hs : ContDiff ℝ ∞ ψ := hφ.comp (contDiff_id.add contDiff_const)
  have hcompact : HasCompactSupport ψ := hc.comp_homeomorph (Homeomorph.addRight (-c))
  have ht' : tsupport ψ ⊆ U := by
    intro y hy
    have hh := ht (tsupport_comp_subset_preimage φ (continuous_id.add continuous_const) hy)
    change (y + -c) + c ∈ U at hh
    simpa only [neg_add_cancel_right] using hh
  have heq := hw ψ hs hcompact ht'
  have hi (F : E2 → ℝ) : (∫ x in W, F (x + c)) = ∫ y in U, F y := hmp.integral_comp hemb F
  rw [← hi (fun y => f y * fderiv ℝ ψ y (EuclideanSpace.single i 1)),
    ← hi (fun y => G y * ψ y)] at heq
  simpa only [ψ, fderiv_comp_add_right, add_neg_cancel_right] using heq

theorem SmoothDirichletDatum.smooth_deriv_extension_on_ball
    {ρ : ℝ} (g : SmoothDirichletDatum ρ) :
    ContDiffOn ℝ ∞ (fun x : E2 => deriv g.value (x 1)) (Metric.ball 0 ρ) := by
  apply (g.smooth.deriv_of_isOpen isOpen_Ioo (by simp)).comp
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.contDiffOn
  intro x hx
  have hn : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hh : |x 1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x (1 : Fin 2) (p := 2)
  exact abs_lt.mp (hh.trans_lt hn)

theorem C1QuasilinearDirichletSolution.local_tangential_derivative_memW1p
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      DeGiorgi.MemW1p 2 (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
        (Metric.ball c r ∩ {x : E2 | 0 < x 0}) := by
  obtain ⟨r, hr, houter, hSob⟩ := hsolution.local_tangential_derivative_odd_memW1p hρ c hc
  let R := r / 2
  have hR : 0 < R := by dsimp [R]; positivity
  let D : E2 → ℝ := fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)
  let G : E2 → ℝ := fun x => deriv g.value (x 1)
  let F : E2 → ℝ := fun x => D (x + c) - G (x + c)
  let U := Metric.ball c R ∩ {x : E2 | 0 < x 0}
  have hcf : c 0 = 0 := hc.2
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hUr : U ⊆ Metric.ball c R := fun x hx => hx.1
  have hball : Metric.closedBall c R ⊆ Metric.ball (0 : E2) ρ :=
    (Metric.closedBall_subset_closedBall (by dsimp [R]; linarith)).trans houter
  have hcap : openHalfDisc R ⊆ Metric.ball (0 : E2) R := fun x hx => hx.1
  have hsF : DeGiorgi.MemW1p 2 F (openHalfDisc R) := by
    have hw := hSob.someWitness.restrict (openHalfDisc_isOpen R) hcap
    apply native_memW1p_congr _ (openHalfDisc_isOpen R).measurableSet (nativeOddExtension F) F ?_ hw.memW1p
    intro x hx
    have hn : 0 ≤ x 0 := le_of_lt hx.2
    simp only [nativeOddExtension, ite_eq_left hn]
  have htF := native_memW1p_translation (openHalfDisc R) (openHalfDisc_isOpen R).measurableSet (-c) F hsF
  have hpre : (fun x : E2 => x + -c) ⁻¹' openHalfDisc R = U := by
    ext x
    change (dist (x + -c) 0 < R ∧ 0 < (x + -c) 0) ↔ (dist x c < R ∧ 0 < x 0)
    simp only [dist_eq_norm, sub_zero, sub_eq_add_neg, PiLp.add_apply, PiLp.neg_apply, hcf, neg_zero, add_zero]
  have hF : (fun x => F (x + -c)) = D - G := by
    funext x
    simp only [F, neg_add_cancel_right, Pi.sub_apply]
  rw [hpre, hF] at htF
  have hG := (R1_C1_memW1p_on_ball (Metric.ball 0 ρ) Metric.isOpen_ball G
    (g.smooth_deriv_extension_on_ball.of_le (by simp)) c R hR hball).1
  have hGw := hG.someWitness.restrict hU hUr
  have hDw := htF.someWitness.add hGw
  have he : (fun x => (D - G) x + G x) = D := by funext x; simp
  refine ⟨R, hR, hball, ?_⟩
  simpa only [he] using hDw.memW1p

theorem C1QuasilinearDirichletSolution.smooth_tangential_derivative_on_openHalfDisc
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))
      (openHalfDisc ρ) := by
  apply ((hsolution.smooth_on_openHalfDisc.fderiv_of_isOpen (openHalfDisc_isOpen ρ) (by simp)).clm_apply
    contDiffOn_const).congr
  intro x hx
  rw [fderivWithin_closedHalfDisc_eq_fderiv u hx]

theorem C1QuasilinearDirichletSolution.local_tangential_second_gradient_memLp
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      MemLp (planarGradient (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1))) 2
        (volume.restrict (Metric.ball c r ∩ {x : E2 | 0 < x 0})) := by
  obtain ⟨r, hr, hball, hSob⟩ := hsolution.local_tangential_derivative_memW1p hρ c hc
  let U := Metric.ball c r ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hsub : U ⊆ openHalfDisc ρ := fun x hx =>
    ⟨hball (Metric.ball_subset_closedBall hx.1), hx.2⟩
  have he := R1_classical_weak_gradient_agrees U hU _
    (hsolution.smooth_tangential_derivative_on_openHalfDisc.mono hsub |>.of_le (by simp)) hSob.someWitness
  exact ⟨r, hr, hball, (memLp_congr_ae he).mp hSob.someWitness.weakGrad_memLp⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
