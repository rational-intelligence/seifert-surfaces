import B1InteriorClassicalWeak_v475
import B1WeakTransportReflection
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open WeakTransport
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Interior C1 change of coordinates.  Its source and target are open; all
jet data are ordinary first derivatives. -/
structure NativeInteriorChart_v475 where
  chart : PartialHomeomorph E2 E2
  source_open : IsOpen chart.source
  target_open : IsOpen chart.target
  forward_C1 : ContDiffOn ℝ 1 chart chart.source
  inverse_C1 : ContDiffOn ℝ 1 chart.symm chart.target
  forward_det : ∀ x ∈ chart.source, Matrix.det (jacobian chart x) ≠ 0

namespace NativeInteriorChart_v475
def vhat (F : NativeInteriorChart_v475) (u : E2 → ℝ) : E2 → ℝ := u ∘ F.chart.symm
def bhat (F : NativeInteriorChart_v475) (b : E2 → E2) (z : E2) : E2 :=
  densityDrift b F.chart (F.chart.symm z)
def pullback (F : NativeInteriorChart_v475) (φ : E2 → ℝ) (x : E2) : ℝ :=
  @ite ℝ (x ∈ F.chart.source) (Classical.propDecidable _) (φ (F.chart x)) 0
end NativeInteriorChart_v475

theorem native_local_C1_weak_gradient_v475 (U : Set E2) (hU : IsOpen U) (u : E2 → ℝ)
    (hu : ∀ x ∈ U, ContDiffAt ℝ 1 u x) : WeakGradientOn U u (planarGradient u) := by
  have huc : ContinuousOn u U := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hdu : ContinuousOn (fderiv ℝ u) U :=
    fun x hx => ((hu x hx).fderiv_right (m := 0) (by simp)).continuousAt.continuousWithinAt
  have hgrad : ContinuousOn (planarGradient u) U := by
    unfold planarGradient
    apply continuousOn_finset_sum
    intro i hi
    exact (hdu.clm_apply continuousOn_const).smul continuousOn_const
  refine ⟨huc.locallyIntegrableOn hU.measurableSet, hgrad.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hc hs i
  have integral_product (F ψ : E2 → ℝ) (hF : ContinuousOn F U)
      (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ U) :
      Integrable (fun x => F x * ψ x) := by
    apply (integrableOn_iff_integrable_of_support_subset ?_).mp
      (((hF.mono hψs).mul hψ.continuousOn).integrableOn_compact hψc)
    intro x hx
    exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
  have hi1 : Integrable (fun x => fderiv ℝ u x (coordinateVector 2 i) * φ x) :=
    integral_product _ _ (hdu.clm_apply continuousOn_const) hφ.continuous hc hs
  have hi2 : Integrable (fun x => u x * fderiv ℝ φ x (coordinateVector 2 i)) :=
    integral_product _ _ huc ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)
  have hi3 : Integrable (fun x => u x * φ x) :=
    integral_product _ _ huc hφ.continuous hc hs
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi1 hi2 hi3
    (fun x hx => (hu x (hs hx)).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)
  have hgcoord : ∀ x, planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    intro x
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  simp_rw [hgcoord]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hibp
  · intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hs h))]
    simp

/-- The literal weak density law under an interior C1 chart, including
compact C1 pullback tests.  Isothermal density is its explicit analytic input,
which will be constructed from the determinant-one metric. -/
theorem native_interior_density_weak_transport_v475
    (F : NativeInteriorChart_v475) (O : Set E2) (hO : IsOpen O)
    (hsrc : F.chart.source ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (u : E2 → ℝ)
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) O)
    (hb : ContinuousOn b O) (hu : ContDiffOn ℝ 1 u O)
    (heq : WeakLinearEquationOn O a b (fun _ => 0) u (planarGradient u))
    (hdensity : ∀ z ∈ F.chart.target, densityLeading a F.chart (F.chart.symm z) = 1) :
    ContDiffOn ℝ 1 (F.vhat u) F.chart.target ∧
    ContinuousOn (F.bhat b) F.chart.target ∧
    WeakLinearEquationOn F.chart.target (fun _ => 1) (F.bhat b) (fun _ => 0)
      (F.vhat u) (planarGradient (F.vhat u)) := by
  classical
  have hfd (x : E2) (hx : x ∈ F.chart.source) : DifferentiableAt ℝ F.chart x :=
    ((F.forward_C1 x hx).contDiffAt (F.source_open.mem_nhds hx)).differentiableAt (by simp)
  have hid (z : E2) (hz : z ∈ F.chart.target) : DifferentiableAt ℝ F.chart.symm z :=
    ((F.inverse_C1 z hz).contDiffAt (F.target_open.mem_nhds hz)).differentiableAt (by simp)
  have hdetbridge (x : E2) :
      (fderiv ℝ F.chart x).toLinearMap.det = Matrix.det (jacobian F.chart x) := by
    have hjac : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (fderiv ℝ F.chart x).toLinearMap = jacobian F.chart x := by
      ext i j
      simp [LinearMap.toMatrix_apply,jacobian,coordinateVector,EuclideanSpace.basisFun_apply]
    rw [← hjac]
    exact (LinearMap.det_toMatrix _ _).symm
  have hvdiff (x : E2) (hx : x ∈ F.chart.source) : DifferentiableAt ℝ u x :=
    ((hu x (hsrc hx)).contDiffAt (hO.mem_nhds (hsrc hx))).differentiableAt (by simp)
  have hvC1 : ContDiffOn ℝ 1 (F.vhat u) F.chart.target :=
    hu.comp F.inverse_C1 (fun z hz => hsrc (F.chart.map_target hz))
  have hvhatdiff (z : E2) (hz : z ∈ F.chart.target) : DifferentiableAt ℝ (F.vhat u) z :=
    ((hvC1 z hz).contDiffAt (F.target_open.mem_nhds hz)).differentiableAt (by simp)
  have hgradcoord (u : E2 → ℝ) (x : E2) (i : Fin 2) :
      planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient, coordinateVector, Fin.sum_univ_two]
  have hchain (u : E2 → ℝ) (f : E2 → E2) (x : E2)
      (hu : DifferentiableAt ℝ u (f x)) (hf : DifferentiableAt ℝ f x) :
      planarGradient (u ∘ f) x = matrixAction (jacobian f x).transpose (planarGradient u (f x)) := by
    ext i
    rw [hgradcoord, fderiv_comp x hu hf]
    have he (w : E2) : w = ∑ j : Fin 2, w j • coordinateVector 2 j := by
      ext j
      fin_cases j <;> simp [coordinateVector, Fin.sum_univ_two]
    change fderiv ℝ u (f x) (fderiv ℝ f x (coordinateVector 2 i)) = _
    rw [he (fderiv ℝ f x (coordinateVector 2 i)), map_sum]
    simp only [map_smul, smul_eq_mul, matrixAction, Matrix.transpose_apply, jacobian, hgradcoord]
    rfl
  have hgradient (z : E2) (hz : z ∈ F.chart.target) :
      planarGradient u (F.chart.symm z) =
        matrixAction (jacobian F.chart (F.chart.symm z)).transpose (planarGradient (F.vhat u) z) := by
    have hx := F.chart.map_target hz
    have hevent : u =ᶠ[𝓝 (F.chart.symm z)] (F.vhat u) ∘ F.chart := by
      filter_upwards [F.source_open.mem_nhds hx] with x hx'
      exact congrArg u (F.chart.left_inv hx').symm
    have hg : planarGradient u (F.chart.symm z) =
        planarGradient ((F.vhat u) ∘ F.chart) (F.chart.symm z) := by
      unfold planarGradient
      rw [hevent.fderiv_eq]
    rw [hg, hchain (F.vhat u) F.chart _ (by simpa only [F.chart.right_inv hz] using hvhatdiff z hz)
      (hfd _ hx), F.chart.right_inv hz]
  have hgradcontinuous (v : E2 → ℝ) (U : Set E2) (hU : IsOpen U)
      (hv : ContDiffOn ℝ 1 v U) : ContinuousOn (planarGradient v) U := by
    unfold planarGradient
    apply continuousOn_finsetSum
    intro i hi
    exact ((hv.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const).smul continuousOn_const
  have hNg := hgradcontinuous u O hO hu
  have hvg := hgradcontinuous (F.vhat u) F.chart.target F.target_open hvC1
  have hflux : ContinuousOn (fun x => matrixAction (a x) (planarGradient u x)) O := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_finsetSum
    intro j hj
    exact (ha i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn hNg)
  have hlower : ContinuousOn (fun x => inner ℝ (b x) (planarGradient u x)) O := hb.inner hNg
  have hbcont : ContinuousOn (F.bhat b) F.chart.target := by
    have hj (i j : Fin 2) : ContinuousOn (fun x => jacobian F.chart x i j) F.chart.source :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn
        ((F.forward_C1.continuousOn_fderiv_of_isOpen F.source_open (by simp)).clm_apply continuousOn_const)
    have hdet : ContinuousOn (fun x => Matrix.det (jacobian F.chart x)) F.chart.source := by
      simp only [Matrix.det_fin_two]
      exact ((hj 0 0).mul (hj 1 1)).sub ((hj 0 1).mul (hj 1 0))
    have hact : ContinuousOn (fun x => matrixAction (jacobian F.chart x) (b x)) F.chart.source := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_continuousOn
      apply continuousOn_pi.mpr
      intro i
      apply continuousOn_finsetSum
      intro j hjj
      exact (hj i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp_continuousOn (hb.mono hsrc))
    exact ((hdet.abs.inv₀ (fun x hx => abs_ne_zero.mpr (F.forward_det x hx))).smul hact).comp
      F.chart.continuousOn_symm (fun z hz => F.chart.map_target hz)
  refine ⟨hvC1,hbcont,native_local_C1_weak_gradient_v475 F.chart.target F.target_open
    (F.vhat u) (fun z hz => (hvC1 z hz).contDiffAt (F.target_open.mem_nhds hz)),?_⟩
  intro φ hφ hc hs
  let C : Set E2 := F.chart.symm '' tsupport φ
  have hC : IsCompact C := hc.image_of_continuousOn
    (F.chart.symm.continuousOn.mono hs)
  have hCsrc : C ⊆ F.chart.source := by
    rintro x ⟨z, hz, rfl⟩
    exact F.chart.map_target (hs hz)
  have hsupp : Function.support (F.pullback φ) ⊆ C := by
    intro x hx
    change F.pullback φ x ≠ 0 at hx
    by_cases hxS : x ∈ F.chart.source
    · have hn : φ (F.chart x) ≠ 0 := by simpa only [NativeInteriorChart_v475.pullback, if_pos hxS] using hx
      exact ⟨F.chart x, subset_tsupport φ hn, F.chart.left_inv hxS⟩
    · exact False.elim (hx (by simp only [NativeInteriorChart_v475.pullback, if_neg hxS]))
  have htsupp : tsupport (F.pullback φ) ⊆ C := closure_minimal hsupp hC.isClosed
  have htsrc : tsupport (F.pullback φ) ⊆ F.chart.source := htsupp.trans hCsrc
  have hlocal (x : E2) (hx : x ∈ F.chart.source) :
      F.pullback φ =ᶠ[𝓝 x] φ ∘ F.chart := by
    filter_upwards [F.source_open.mem_nhds hx] with y hy
    simp only [NativeInteriorChart_v475.pullback, if_pos hy, Function.comp_apply]
  have hC1 : ContDiff ℝ 1 (F.pullback φ) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ F.chart.source
    · apply (((hφ.of_le (by norm_num : (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contDiffAt).comp x
        ((F.forward_C1 x hx).contDiffAt (F.source_open.mem_nhds hx))).congr_of_eventuallyEq
      exact hlocal x hx
    · exact contDiffAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (htsrc h)))
  have hgrad (x : E2) (hx : x ∈ F.chart.source) :
      planarGradient (F.pullback φ) x =
        matrixAction (jacobian F.chart x).transpose (planarGradient φ (F.chart x)) := by
    have he : planarGradient (F.pullback φ) x = planarGradient (φ ∘ F.chart) x := by
      unfold planarGradient
      rw [(hlocal x hx).fderiv_eq]
    rw [he]
    exact hchain φ F.chart x (hφ.differentiable (by simp) _) (hfd x hx)
  have hψcompact : HasCompactSupport (F.pullback φ) := hC.of_isClosed_subset isClosed_closure htsupp
  have hψO : tsupport (F.pullback φ) ⊆ O := htsrc.trans hsrc
  obtain ⟨-,hiSource,hzeroSource⟩ := compact_C1_test_extension O hO a b (fun _ => 0) u
    (planarGradient u) heq (hflux.locallyIntegrableOn hO.measurableSet)
    (by simpa only [zero_mul,add_zero] using hlower.locallyIntegrableOn hO.measurableSet)
    (F.pullback φ) hC1 hψcompact hψO
  have hpoint (x : E2) (hx : x ∈ F.chart.source) :
      weakIntegrand a b (fun _ => 0) u (planarGradient u) (F.pullback φ) x =
      |(fderiv ℝ F.chart x).toLinearMap.det| •
        weakIntegrand (fun _ => 1) (F.bhat b) (fun _ => 0)
          (F.vhat u) (planarGradient (F.vhat u)) φ (F.chart x) := by
    have hg := hgradient (F.chart x) (F.chart.map_source hx)
    rw [F.chart.left_inv hx] at hg
    have hd := hdensity (F.chart x) (F.chart.map_source hx)
    rw [F.chart.left_inv hx] at hd
    have hnonzero : |Matrix.det (jacobian F.chart x)| ≠ 0 :=
      abs_ne_zero.mpr (F.forward_det x hx)
    rw [← hd]
    simp only [weakIntegrand,zero_mul,add_zero,hgrad x hx,hg,
      NativeInteriorChart_v475.pullback,if_pos hx,hdetbridge,
      NativeInteriorChart_v475.bhat,densityDrift,densityLeading,F.chart.left_inv hx,smul_eq_mul]
    simp [PiLp.inner_apply,matrixAction,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]
    field_simp
    <;> ring
  have hzero (x : E2) (hx : x ∉ F.chart.source) :
      weakIntegrand a b (fun _ => 0) u (planarGradient u) (F.pullback φ) x = 0 := by
    have hn : x ∉ tsupport (F.pullback φ) := fun h => hx (htsrc h)
    simp [weakIntegrand,planarGradient,fderiv_of_notMem_tsupport ℝ hn,
      image_eq_zero_of_notMem_tsupport hn]
  have hsubstitution := integral_image_eq_integral_abs_det_fderiv_smul volume F.source_open.measurableSet
    (fun x hx => (hfd x hx).hasFDerivAt.hasFDerivWithinAt) F.chart.injOn
    (weakIntegrand (fun _ => 1) (F.bhat b) (fun _ => 0)
      (F.vhat u) (planarGradient (F.vhat u)) φ)
  rw [F.chart.image_source_eq_target,← setIntegral_congr_fun F.source_open.measurableSet hpoint] at hsubstitution
  have htransport : (∫ z in F.chart.target,
      weakIntegrand (fun _ => 1) (F.bhat b) (fun _ => 0)
        (F.vhat u) (planarGradient (F.vhat u)) φ z) =
      ∫ x in O, weakIntegrand a b (fun _ => 0) u (planarGradient u) (F.pullback φ) x := by
    rw [hsubstitution,setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    exact hzero x (fun h => hx (hsrc h))
  have htargetIntegrable : IntegrableOn
      (weakIntegrand (fun _ => 1) (F.bhat b) (fun _ => 0)
        (F.vhat u) (planarGradient (F.vhat u)) φ) F.chart.target := by
    have htestGrad : Continuous (planarGradient φ) := continuous_planarGradient hφ
    have htestGradCompact : HasCompactSupport (planarGradient φ) := by
      apply hc.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal _ hc.isClosed
      intro x hx
      by_contra hn
      exact hx (by simp [planarGradient,fderiv_of_notMem_tsupport ℝ hn])
    have hgradSupport : tsupport (planarGradient φ) ⊆ tsupport φ := by
      apply closure_minimal _ hc.isClosed
      intro x hx
      by_contra hn
      exact hx (by simp [planarGradient,fderiv_of_notMem_tsupport ℝ hn])
    have hprod (F₀ ψ : E2 → ℝ) (hF : ContinuousOn F₀ F.chart.target)
        (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ F.chart.target) :
        Integrable (fun x => F₀ x*ψ x) := by
      apply (integrableOn_iff_integrable_of_support_subset ?_).mp
        (((hF.mono hsψ).mul hψ.continuousOn).integrableOn_compact hcψ)
      intro x hx
      exact subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2)
    have hleading (i : Fin 2) : IntegrableOn
        (fun z => planarGradient (F.vhat u) z i*planarGradient φ z i) F.chart.target :=
      (hprod _ _ ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hvg)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp htestGrad)
        (htestGradCompact.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _))
        ((tsupport_comp_subset (map_zero (EuclideanSpace.proj (𝕜 := ℝ) i)) _).trans
          (hgradSupport.trans hs))).restrict
    have hlower : IntegrableOn (fun z => inner ℝ (F.bhat b z)
        (planarGradient (F.vhat u) z)*φ z) F.chart.target :=
      (hprod _ φ (hbcont.inner hvg) hφ.continuous hc hs).restrict
    have hone (p : E2) : matrixAction (1:Mat2) p = p := by ext i; simp [matrixAction,Matrix.one_apply]
    unfold weakIntegrand
    simp only [hone,zero_mul,add_zero]
    convert ((hleading 0).add (hleading 1)).sub hlower using 1
    funext z
    simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two]
    ring
  exact ⟨htargetIntegrable,htransport.trans hzeroSource⟩

#print axioms native_interior_density_weak_transport_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
