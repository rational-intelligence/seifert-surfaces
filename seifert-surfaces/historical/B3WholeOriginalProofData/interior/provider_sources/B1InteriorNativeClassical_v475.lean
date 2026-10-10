import B1InteriorNativeRegularity_v475
import B1HalfDiscNativeClassicalInterior_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem interior_leOn_of_ae_le_v475 (U : Set E2) (hU : IsOpen U) (f : E2 → ℝ) (C : ℝ)
    (hf : ContinuousOn f U) (hae : ∀ᵐ x ∂volume.restrict U, f x ≤ C) :
    ∀ x ∈ U, f x ≤ C := by
  have he : (fun x => min (f x) C) =ᵐ[volume.restrict U] f :=
    hae.mono fun x hx => min_eq_left hx
  have hp := Measure.eqOn_open_of_ae_eq he hU (hf.inf continuousOn_const) hf
  intro x hx
  exact min_eq_left_iff.mp (hp hx)

theorem interior_window_native_smooth_positive_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du)
    (h10 : H10On (halfDisc W.R) (fun x => u x - 1) du)
    (heq : WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c u du)
    (hpos : ∀ᵐ x ∂volume.restrict (halfDisc W.R), (1/2 : ℝ) ≤ u x) :
    ∃ f : E2 → ℝ, ∃ df : E2 → E2,
      ContDiffOn ℝ ∞ f (halfDisc W.R) ∧
      H1On (halfDisc W.R) f df ∧
      H10On (halfDisc W.R) (fun x => f x - 1) df ∧
      WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c f df ∧
      (∀ x ∈ halfDisc W.R, (1/2 : ℝ) ≤ f x) := by
  let R := W.R
  obtain ⟨f,hf,hae⟩ := interior_window_native_smooth_interior_v475 W u du hu heq
  have hdf : du =ᵐ[volume.restrict (halfDisc R)] planarGradient f :=
    native_smooth_gradient_ae_v468 (halfDisc R)
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)) u f du hu hf hae
  have h1f := native_h1_congr_ae_v468 (halfDisc R) u f du (planarGradient f) hu hae hdf
  have h10f := native_h10_congr_ae_v468 (halfDisc R) (fun x => u x - 1)
    (fun x => f x - 1) du (planarGradient f) h10
    (hae.mono fun x hx => by dsimp only; rw [hx]) hdf
  have heqf := native_linear_congr_ae_v468 (halfDisc R) W.a W.b W.c u f du
    (planarGradient f) hu heq hae hdf
  have hposf : ∀ᵐ x ∂volume.restrict (halfDisc R), (1/2 : ℝ) ≤ f x := by
    filter_upwards [hpos,hae] with x hx he
    rw [← he]
    exact hx
  have hpoint : ∀ x ∈ halfDisc R, (1/2 : ℝ) ≤ f x := by
    intro x hx
    have hn := interior_leOn_of_ae_le_v475 (halfDisc R)
      (Metric.isOpen_ball.inter (isOpen_lt continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous))
      (fun y => -f y) (-(1/2 : ℝ))
      (hf.continuousOn.neg) (hposf.mono fun y hy => by linarith)
    have hh := hn x hx
    linarith
  exact ⟨f,planarGradient f,hf,h1f,h10f,heqf,hpoint⟩

theorem interior_window_classical_positive_v475
    (W : InteriorCoefficientWindow_v475) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc W.R) u du)
    (h10 : H10On (halfDisc W.R) (fun x => u x - 1) du)
    (heq : WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c u du)
    (hpos : ∀ᵐ x ∂volume.restrict (halfDisc W.R), (1/2 : ℝ) ≤ u x) :
    ∃ f : E2 → ℝ,
      ContDiffOn ℝ ∞ f (halfDisc W.R) ∧
      H1On (halfDisc W.R) f (planarGradient f) ∧
      H10On (halfDisc W.R) (fun x => f x - 1) (planarGradient f) ∧
      WeakLinearEquationOn (halfDisc W.R) W.a W.b W.c f (planarGradient f) ∧
      (∀ x ∈ halfDisc W.R, (1/2 : ℝ) ≤ f x) ∧
      (∀ x ∈ halfDisc W.R, classicalL W.a W.b W.c f x = 0) := by
  let R := W.R
  obtain ⟨f,df,hf,h1,h10,heq,hpos⟩ :=
    interior_window_native_smooth_positive_v475 W u du hu h10 heq hpos
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hdf : df =ᵐ[volume.restrict (halfDisc R)] planarGradient f :=
    native_smooth_gradient_ae_v468 (halfDisc R) hU f f df h1 hf EventuallyEq.rfl
  have h1 := native_h1_congr_ae_v468 (halfDisc R) f f df (planarGradient f)
    h1 EventuallyEq.rfl hdf
  have h10 := native_h10_congr_ae_v468 (halfDisc R) (fun x => f x - 1)
    (fun x => f x - 1) df (planarGradient f) h10 EventuallyEq.rfl hdf
  have heq := native_linear_congr_ae_v468 (halfDisc R) W.a W.b W.c f f df
    (planarGradient f) (native_h1_congr_ae_v468 (halfDisc R) f f (planarGradient f) df
      h1 EventuallyEq.rfl hdf.symm) heq EventuallyEq.rfl hdf
  let O := W.O
  have hO := W.isOpen_O
  have hclosed := W.closed_subset
  have ha := W.smooth_a
  have hb := W.smooth_b
  have hc := W.smooth_c
  have hUclosed : halfDisc R ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
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
  exact ⟨f,hf,h1,h10,heq,hpos,hpoint⟩

#print axioms interior_window_classical_positive_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
