import B1HalfDiscNativeClassical_v468

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The literal native weak equation yields the classical equation on its
specified interior domain once its native representative is smooth there. -/
theorem actual_halfdisc_native_weak_classical_at_radius_v468
    (D : B1OriginalData (g := g) J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (f : E2 → ℝ)
    (hf : ContDiffOn ℝ ∞ f (halfDisc R))
    (heq : WeakLinearEquationOn (halfDisc R) W.a W.b W.c f (planarGradient f)) :
    ∀ x ∈ halfDisc R, classicalL W.a W.b W.c f x = 0 := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨O,hO,hclosed,hOU,hjets,hlocal,hgradlocal,ha,hq,hlg,hlh,hb,hc⟩ :=
    actual_coefficient_open_tube D s W
  have hUclosed : halfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hRW.le hx.1),hx.2.le⟩
  have hcoeff_a (i j : Fin 2) :
      ContDiffOn ℝ ∞ (fun x => W.a x i j) (halfDisc R) :=
    (ha i j).mono (hUclosed.trans hclosed)
  have hcoeff_b : ContDiffOn ℝ ∞ W.b (halfDisc R) := hb.mono (hUclosed.trans hclosed)
  have hcoeff_c : ContDiffOn ℝ ∞ W.c (halfDisc R) := hc.mono (hUclosed.trans hclosed)
  have hgrad : ContDiffOn ℝ 1 (planarGradient f) (halfDisc R) := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul_const _
  have hflux (i : Fin 2) : ContDiffOn ℝ 1
      (fun x => matrixAction (W.a x) (planarGradient f x) i) (halfDisc R) := by
    change ContDiffOn ℝ 1 (fun x => ∑ j : Fin 2, W.a x i j * planarGradient f x j) _
    apply ContDiffOn.sum
    intro j hj
    exact (hcoeff_a i j).of_le (by simp) |>.mul
      (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hgrad))
  have hdiv (i : Fin 2) : ContinuousOn
      (fun x => fderiv ℝ (fun y => matrixAction (W.a y) (planarGradient f y) i) x
        (coordinateVector 2 i)) (halfDisc R) :=
    ((hflux i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hlower : ContinuousOn
      (fun x => inner ℝ (W.b x) (planarGradient f x) + W.c x * f x) (halfDisc R) :=
    (hcoeff_b.continuousOn.inner hgrad.continuousOn).add
      (hcoeff_c.continuousOn.mul hf.continuousOn)
  have hLcont : ContinuousOn (classicalL W.a W.b W.c f) (halfDisc R) := by
    unfold classicalL
    convert ((hdiv 0).add (hdiv 1)).add hlower using 1
    funext x
    simp only [Fin.sum_univ_two,Pi.add_apply]
    ring
  have hae : (classicalL W.a W.b W.c f) =ᵐ[volume.restrict (halfDisc R)] 0 := by
    change ∀ᵐ x ∂volume.restrict (halfDisc R), classicalL W.a W.b W.c f x = 0
    rw [ae_restrict_iff' hU.measurableSet]
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hLcont.locallyIntegrableOn hU.measurableSet)
    intro φ hφ hsupp hsub
    have hweak := heq.2 φ hφ hsupp hsub
    have hform := halfdisc_local_classical_form_identity_v468 R (halfDisc R) hU
      (by rfl) W.a W.b W.c f hcoeff_a hcoeff_b hcoeff_c hf φ hφ hsupp hsub
    have hzero : (∫ x in halfDisc R,
        inner ℝ (matrixAction (W.a x) (planarGradient f x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (planarGradient f x) + W.c x * f x) * φ x) = 0 := hweak.2
    have hneg := hform.2.2
    rw [hzero] at hneg
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := halfDisc R)
      (fun x hx => show φ x • classicalL W.a W.b W.c f x = 0 by
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hsub hh)),zero_smul])]
    simp only [smul_eq_mul]
    simp_rw [mul_comm (φ _)]
    linarith
  have hpoint : ∀ x ∈ halfDisc R, classicalL W.a W.b W.c f x = 0 := by
    intro x hx
    exact (MeasureTheory.Measure.eqOn_open_of_ae_eq hae hU hLcont continuousOn_const) hx
  exact hpoint

end SeifertSurfaces.OriginalEndpoints.B1Tangency
