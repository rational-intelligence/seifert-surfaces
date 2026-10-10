import B1ActualBoundaryTangentialH2_v468
import ProviderLocalHelpers
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open SeifertSurfaces.QuasilinearProviderBridge
set_option maxHeartbeats 800000

/-- The native flat-edge derivative is the actual classical tangential
second derivative on the whole smaller open half-disc, hence controls its L2
norm right up to the flat edge. -/
theorem native_boundary_classical_tangential_L2_v468
    (R q : ℝ) (hqR : q<R) (h : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ h (halfDisc R))
    (i : Fin 2) (w : E2 → ℝ)
    (hw : MemLp w 2 (volume.restrict (Metric.ball (0:E2) q)))
    (hwd : DeGiorgi.HasWeakPartialDeriv 0 w
      (fun y => (halfDisc R).indicator (planarGradient h) y i)
      (Metric.ball (0:E2) q)) :
    MemLp (fun x => fderiv ℝ (fun y => planarGradient h y i) x
      (coordinateVector 2 0)) 2 (volume.restrict (halfDisc q)) := by
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hUR : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR.le hx.1,hx.2⟩
  have hUs : halfDisc q ⊆ Metric.ball (0:E2) q := fun x hx => hx.1
  have hR : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  let f : E2 → ℝ := fun y => planarGradient h y i
  have hfs : ContDiffOn ℝ ∞ f (halfDisc q) := by
    have hg := hs.fderiv_of_isOpen hR (m:=∞) (by simp)
    have he : f = fun y => fderiv ℝ h y (coordinateVector 2 i) := by
      funext y
      exact QuasilinearLocalization.Helpers.gradient_apply h y i
    rw [he]
    exact (hg.clm_apply contDiffOn_const).mono hUR
  have hd : DeGiorgi.HasWeakPartialDeriv 0 w f (halfDisc q) := by
    have hd := hwd.restrict hU hUs
    intro phi hp hc ht
    have he := hd phi hp hc ht
    have heI : (∫ x in halfDisc q,
        ((halfDisc R).indicator (planarGradient h) x i)*fderiv ℝ phi x (coordinateVector 2 0)) =
        ∫ x in halfDisc q, f x*fderiv ℝ phi x (coordinateVector 2 0) := by
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      simp only [indicator_of_mem (hUR hx)]
      rfl
    simpa only [coordinateVector] using heI.symm.trans he
  have hfc := hfs.of_le (by simp : (1:ℕ∞ω)≤(∞:ℕ∞ω))
  have hclass := Helpers.C1_hasWeakGrad _ hU f hfc 0
  have hdc : ContinuousOn (fun x => planarGradient f x 0) (halfDisc q) := by
    have he : (fun x => planarGradient f x 0) = fun x => fderiv ℝ f x (coordinateVector 2 0) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply f x 0
    rw [he]
    exact (hfc.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hwU := hw.mono_measure (Measure.restrict_mono_set _ hUs)
  have hae : w =ᵐ[volume.restrict (halfDisc q)] (fun x => planarGradient f x 0) := by
    suffices hz : ∀ᵐ x ∂volume.restrict (halfDisc q),
        (w x-planarGradient f x 0)=0 by
      filter_upwards [hz] with x hx
      exact sub_eq_zero.mp hx
    rw [ae_restrict_iff' hU.measurableSet]
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hU
    · exact (locallyIntegrableOn_of_locallyIntegrable_restrict
        (hwU.locallyIntegrable (by norm_num))).sub
        (hdc.locallyIntegrableOn hU.measurableSet)
    · intro phi hp hc ht
      have e1 := hd phi hp hc ht
      have e2 := hclass phi hp hc ht
      have he : (∫ x in halfDisc q, w x*phi x)=
          ∫ x in halfDisc q, planarGradient f x 0*phi x := by linarith
      have hz : ∀ x∉halfDisc q, phi x • (w x-planarGradient f x 0)=0 := by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (ht hh)),zero_smul]
      rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
      simp only [smul_eq_mul,mul_sub]
      have hphi2 : MemLp phi 2 (volume.restrict (halfDisc q)) :=
        (hp.continuous.memLp_of_hasCompactSupport hc).restrict _
      have hiw : Integrable (fun x => phi x*w x) (volume.restrict (halfDisc q)) :=
        hphi2.integrable_mul hwU
      have hic : Integrable (fun x => phi x*planarGradient f x 0) (volume.restrict (halfDisc q)) := by
        apply Integrable.restrict
        apply QuasilinearLocalization.Helpers.continuousOn_supported_integrable
          (halfDisc q) (tsupport phi) _ hc ht
          (hp.continuous.continuousOn.mul hdc)
        intro x hx
        exact subset_tsupport _ ((mul_ne_zero_iff.mp hx).1)
      rw [integral_sub hiw hic]
      simp_rw [mul_comm (phi _)]
      exact sub_eq_zero.mpr he
  have hLp := hwU.ae_eq hae
  convert hLp using 1
  funext x
  exact (QuasilinearLocalization.Helpers.gradient_apply f x 0).symm
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_classical_tangential_L2_v468
