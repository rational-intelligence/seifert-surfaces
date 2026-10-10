import B1MetricVariationalInterfaces

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03
open SeifertSurfaces.AppendixACoordinates

private theorem continuousOn_mul_test (U : Set E2) (hU : IsOpen U)
    (f g : E2 → ℝ) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgU : tsupport g ⊆ U) : Continuous (fun x => f x * g x) := by
  apply continuous_of_tsupport
  intro x hx
  have hxU : x ∈ U := hgU (tsupport_mul_subset_right hx)
  exact (hf.continuousAt (hU.mem_nhds hxU)).mul hg.continuousAt

/-- C1 integration by parts against the same compact smooth test class as WeakGradientOn. -/
private theorem C1_test_identity (U : Set E2) (hU : IsOpen U)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ 1 u U)
    (j : Fin 2) (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ U) :
    (∫ x in U, u x * fderiv ℝ phi x (coordinateVector 2 j)) =
      -(∫ x in U, fderiv ℝ u x (coordinateVector 2 j) * phi x) := by
  let v := coordinateVector 2 j
  have hdU : tsupport (fun x => fderiv ℝ phi x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hs
  have hdp : Continuous (fun x => fderiv ℝ phi x v) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdu : ContinuousOn (fun x => fderiv ℝ u x v) U :=
    (hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((continuousOn_mul_test U hU _ phi hdu hphi.continuous hs).integrable_of_hasCompactSupport
      hc.mul_left)
    ((continuousOn_mul_test U hU u _ hu.continuousOn hdp hdU).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) v).mul_left)
    ((continuousOn_mul_test U hU u phi hu.continuousOn hphi.continuous hs).integrable_of_hasCompactSupport
      hc.mul_left)
    (fun x hx => (hu.contDiffAt (hU.mem_nhds (hs hx))).differentiableAt one_ne_zero)
    (fun x _ => hphi.differentiable (by simp) x)
  change (∫ x in U, u x * fderiv ℝ phi x v) = -(∫ x in U, fderiv ℝ u x v * phi x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hi
  · intro x hx
    rw [show phi x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  · intro x hx
    rw [show fderiv ℝ phi x v = 0 from image_eq_zero_of_notMem_tsupport
      (f := fun x => fderiv ℝ phi x v) (fun h => hx (hdU h)), mul_zero]

/-- A C1 representative of the supplied scalar H1 function retains its supplied weak derivatives.
The C1 witness is a conditional input to this helper only; constructing it remains VM03 debt. -/
theorem weak_derivative_of_C1_representative
    (U : Set E2) (hU : IsOpen U) (u v : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) (hv : ContDiffOn ℝ 1 v U)
    (hvu : v =ᵐ[volume.restrict U] u) (j : Fin 2) :
    (fun x => fderiv ℝ v x (coordinateVector 2 j)) =ᵐ[volume.restrict U]
      (fun x => du x j) := by
  let g := fun x => fderiv ℝ v x (coordinateVector 2 j)
  have hgc : ContinuousOn g U :=
    (hv.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdu : LocallyIntegrable (fun x => du x j) (volume.restrict U) :=
    fun x => (EuclideanSpace.proj (𝕜 := ℝ) j).integrableAtFilter_comp
      (hu.2.2.locallyIntegrable (by norm_num) x)
  suffices hz : ∀ᵐ x ∂volume.restrict U, g x - du x j = 0 by
    filter_upwards [hz] with x hx using sub_eq_zero.mp hx
  rw [ae_restrict_iff' hU.measurableSet]
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hgc.locallyIntegrableOn hU.measurableSet).sub
      (locallyIntegrableOn_of_locallyIntegrable_restrict hdu))
  intro phi hphi hc hs
  have hw := hu.1.2.2 phi hphi hc hs j
  have hvw := C1_test_identity U hU v hv j phi hphi hc hs
  have heq : (∫ x in U, v x * fderiv ℝ phi x (coordinateVector 2 j)) =
      ∫ x in U, u x * fderiv ℝ phi x (coordinateVector 2 j) :=
    integral_congr_ae (hvu.mul EventuallyEq.rfl)
  have hgint : Integrable (fun x => phi x * g x) (volume.restrict U) := by
    exact ((continuousOn_mul_test U hU g phi hgc hphi.continuous hs).integrable_of_hasCompactSupport
      hc.mul_left).restrict (s := U) |>.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hduint : Integrable (fun x => phi x * du x j) (volume.restrict U) := by
    simpa only [smul_eq_mul] using hdu.integrable_smul_left_of_hasCompactSupport hphi.continuous hc
  change (∫ x : E2, phi x • (g x - du x j)) = 0
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
    (fun x hx => show phi x • (g x - du x j) = 0 by
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), zero_smul])]
  simp only [smul_eq_mul, mul_sub]
  rw [integral_sub hgint hduint]
  simp_rw [mul_comm (phi _)]
  change (∫ x in U, g x * phi x) - (∫ x in U, du x j * phi x) = 0
  change _ = -(∫ x in U, g x * phi x) at hvw
  linarith

/-- VM03's same-weak-jets output follows from its same-map and forward-C1 outputs.
No trace equivalence, minimizer reselection, inverse regularity, or PDE theorem is used. -/
theorem same_weak_jets_of_C1_representative
    {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f tau : E2 → E2) (d : Fin 2 → E2 → E2)
    (hadm : MetricAdmissible Ω f d) (htau : ContDiffOn ℝ 1 tau (closedDisc 1))
    (hae : tau =ᵐ[volume.restrict (disc 1)] f) :
    ∀ i j, (fun z => jacobianWithin tau (closedDisc 1) z i j) =ᵐ[volume.restrict (disc 1)]
      (fun z => d i z j) := by
  intro i j
  have hopen : IsOpen (disc 1) := Metric.isOpen_ball
  have hsub : disc 1 ⊆ closedDisc 1 := Metric.ball_subset_closedBall
  have ht := htau.mono hsub
  have hcoord : ContDiffOn ℝ 1 (fun x => tau x i) (disc 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.comp ht (mapsTo_univ _ _)
  have haecoord : (fun x => tau x i) =ᵐ[volume.restrict (disc 1)] (fun x => f x i) := by
    filter_upwards [hae] with x hx using congrArg (fun y : E2 => y i) hx
  have hw := weak_derivative_of_C1_representative (disc 1) hopen
    (fun x => f x i) (fun x => tau x i) (d i) (hadm.1 i) hcoord haecoord j
  filter_upwards [ae_restrict_mem hopen.measurableSet, hw] with x hx hjet
  have hdx : DifferentiableAt ℝ tau x :=
    (ht.contDiffAt (hopen.mem_nhds hx)).differentiableAt one_ne_zero
  have hder := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hdx.hasFDerivAt).fderiv
  have hnb : closedDisc 1 ∈ 𝓝 x := Filter.mem_of_superset (hopen.mem_nhds hx) hsub
  change (fderivWithin ℝ tau (closedDisc 1) x (coordinateVector 2 j)) i = d i x j
  rw [fderivWithin_of_mem_nhds hnb]
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ tau) x (coordinateVector 2 j) = d i x j at hjet
  rw [hder] at hjet
  exact hjet

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.VM03
