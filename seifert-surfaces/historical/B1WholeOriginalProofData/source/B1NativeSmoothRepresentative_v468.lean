import B1HalfDiscInteriorRepresentative_v468
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 0

theorem planar_continuousOn_mul_test_v468 (Ω : Set E2) (hΩ : IsOpen Ω)
    (f g : E2 → ℝ) (hf : ContinuousOn f Ω) (hg : Continuous g)
    (hgΩ : tsupport g ⊆ Ω) : Continuous (fun x => f x * g x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxΩ : x ∈ Ω := hgΩ (tsupport_mul_subset_right hx)
  exact (hf.continuousAt (hΩ.mem_nhds hxΩ)).mul hg.continuousAt

/-- Integration by parts only requires smoothness on the open test domain. -/
theorem planar_weak_partial_of_contDiffOn_v468 (Ω : Set E2) (hΩ : IsOpen Ω)
    (f : E2 → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (i : Fin 2) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ f x) (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφc hφΩ
  let v := EuclideanSpace.single i (1 : ℝ)
  have hdΩ : tsupport (fun x => (fderiv ℝ φ x) v) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφΩ
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => (fderiv ℝ f x) v) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((planar_continuousOn_mul_test_v468 Ω hΩ _ φ hdf hφ.continuous hφΩ).integrable_of_hasCompactSupport
      hφc.mul_left)
    ((planar_continuousOn_mul_test_v468 Ω hΩ f _ hf.continuousOn hdφ hdΩ).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v).mul_left)
    ((planar_continuousOn_mul_test_v468 Ω hΩ f φ hf.continuousOn hφ.continuous hφΩ).integrable_of_hasCompactSupport
      hφc.mul_left)
    (fun x hx => ((hf x (hφΩ hx)).contDiffAt (hΩ.mem_nhds (hφΩ hx))).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)
  change (∫ x in Ω, f x * (fderiv ℝ φ x) v) = -∫ x in Ω, (fderiv ℝ f x) v * φ x
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact he
  · intro x hx
    rw [show φ x = 0 from  image_eq_zero_of_notMem_tsupport (fun h => hx (hφΩ h)), mul_zero]
  · intro x hx
    rw [show (fderiv ℝ φ x) v = 0 from image_eq_zero_of_notMem_tsupport (f := fun x => (fderiv ℝ φ x) v) (fun h => hx (hdΩ h)), mul_zero]


/-- Smooth interior representatives have the literal supplied native derivative a.e. -/
theorem native_smooth_gradient_ae_v468
    (U : Set E2) (hU : IsOpen U) (u f : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) (hf : ContDiffOn ℝ ∞ f U)
    (hae : u =ᵐ[volume.restrict U] f) :
    du =ᵐ[volume.restrict U] planarGradient f := by
  have hcoord (x : E2) (i : Fin 2) : planarGradient f x i =
      fderiv ℝ f x (EuclideanSpace.single i 1) := by
    fin_cases i <;> simp [planarGradient,coordinateVector,Fin.sum_univ_two]
  have hpart (i : Fin 2) : (fun x => du x i) =ᵐ[volume.restrict U]
      (fun x => planarGradient f x i) := by
    have hw := (native_regular_witness_v468 U u du hu).isWeakGrad i
    have hwf := hw.congr_ae hae EventuallyEq.rfl
    have hc : ContinuousOn (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) U :=
      ((hf.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const)
    have hn := planar_weak_partial_of_contDiffOn_v468 U hU f hf i
    let g := fun x : E2 => fderiv ℝ f x (EuclideanSpace.single i 1)
    have hg : ContinuousOn g U := hc
    suffices hz : ∀ᵐ x ∂volume.restrict U, g x - du x i = 0 by
      filter_upwards [hz] with x hx
      rw [hcoord]
      exact (sub_eq_zero.mp hx).symm
    rw [ae_restrict_iff' hU.measurableSet]
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU
    · exact (hg.locallyIntegrableOn hU.measurableSet).sub
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((hu.2.2.eval_piLp i).locallyIntegrable (by norm_num)))
    · intro φ hs hc ht
      have heq : (∫ x in U, g x * φ x) = ∫ x in U, du x i * φ x := by
        have h1 := hn φ hs hc ht
        have h2 := hwf φ hs hc ht
        change (∫ x in U, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
          -(∫ x in U, du x i * φ x) at h2
        linarith
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
        (fun x hx => show φ x • (g x - du x i) = 0 by
          rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (ht hh)),zero_smul])]
      simp only [smul_eq_mul,mul_sub]
      rw [integral_sub]
      · simpa only [mul_comm (φ _),heq,sub_self]
      · exact ((planar_continuousOn_mul_test_v468 U hU g φ hg hs.continuous ht).integrable_of_hasCompactSupport
          hc.mul_left).restrict (s := U) |>.congr (Eventually.of_forall fun x => mul_comm _ _)
      · simpa only [smul_eq_mul] using
          ((hu.2.2.eval_piLp i).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
            hs.continuous hc
  filter_upwards [ae_all_iff.mpr hpart] with x hx
  exact PiLp.ext fun i => hx i

/-- Changing only a.e. representatives preserves the original native H1 data. -/
theorem native_h1_congr_ae_v468
    (U : Set E2) (u f : E2 → ℝ) (du df : E2 → E2)
    (hu : H1On U u du) (hae : u =ᵐ[volume.restrict U] f)
    (hdae : du =ᵐ[volume.restrict U] df) : H1On U f df := by
  have hflp := hu.2.1.ae_eq hae
  have hdflp := hu.2.2.ae_eq hdae
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hflp.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdflp.locallyIntegrable (by norm_num)),?_⟩,hflp,hdflp⟩
  intro φ hs hc ht i
  have hw := (native_regular_witness_v468 U u du hu).isWeakGrad i
  exact hw.congr_ae hae (hdae.mono fun x hx => congrArg (fun v : E2 => v i) hx)
    φ (hs.of_le (by simp)) hc ht

/-- Native H10 retains the same compact approximation after changing representatives. -/
theorem native_h10_congr_ae_v468
    (U : Set E2) (u f : E2 → ℝ) (du df : E2 → E2)
    (hu : H10On U u du) (hae : u =ᵐ[volume.restrict U] f)
    (hdae : du =ᵐ[volume.restrict U] df) : H10On U f df := by
  refine ⟨native_h1_congr_ae_v468 U u f du df hu.1 hae hdae,?_⟩
  intro ε hε
  obtain ⟨φ,hs,hc,ht,herr⟩ := hu.2 ε hε
  refine ⟨φ,hs,hc,ht,?_⟩
  have he : (∫ x in U, |f x-φ x|^2 + ‖df x-planarGradient φ x‖^2) =
      ∫ x in U, |u x-φ x|^2 + ‖du x-planarGradient φ x‖^2 := by
    apply integral_congr_ae
    filter_upwards [hae,hdae] with x hx hdx
    rw [hx,hdx]
  rw [he]
  exact herr

/-- The full linear weak equation is insensitive to a.e. representatives. -/
theorem native_linear_congr_ae_v468
    (U : Set E2) (a : E2 → Mat2) (b : E2 → E2) (c u f : E2 → ℝ)
    (du df : E2 → E2) (hu : H1On U u du)
    (heq : WeakLinearEquationOn U a b c u du)
    (hae : u =ᵐ[volume.restrict U] f) (hdae : du =ᵐ[volume.restrict U] df) :
    WeakLinearEquationOn U a b c f df := by
  refine ⟨(native_h1_congr_ae_v468 U u f du df hu hae hdae).1,?_⟩
  intro φ hs hc ht
  have hg : (fun x => inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x) -
      (inner ℝ (b x) (du x) + c x * u x) * φ x) =ᵐ[volume.restrict U]
      (fun x => inner ℝ (matrixAction (a x) (df x)) (planarGradient φ x) -
      (inner ℝ (b x) (df x) + c x * f x) * φ x) := by
    filter_upwards [hae,hdae] with x hx hdx
    rw [hx,hdx]
  obtain ⟨hi,he⟩ := heq.2 φ hs hc ht
  exact ⟨hi.congr hg,(integral_congr_ae hg).symm.trans he⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
