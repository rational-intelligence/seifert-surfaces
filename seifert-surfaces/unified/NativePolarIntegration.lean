import NativeBallCone

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 0

 theorem polar_integral_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (x : E2) (q : ℝ) (hq : 0 < q) (f : E2 → F)
    (H : ℝ → ℝ → F)
    (hH : IntegrableOn (fun rt : ℝ × ℝ => H rt.2 rt.1)
      (Icc (0 : ℝ) q ×ˢ Icc (-Real.pi) Real.pi))
    (hEq : ∀ r ∈ Ioo (0 : ℝ) q, ∀ t ∈ Ioo (-Real.pi) Real.pi,
      r • f (x + r • unitCircleParameter t) = H t r) :
    IntegrableOn f (Metric.ball x q) ∧
    (∫ z in Metric.ball x q, f z) =
      ∫ t in Icc (-Real.pi) Real.pi, ∫ r in Icc (0 : ℝ) q, H t r := by
  classical
  let Q : Set (ℝ × ℝ) := Ioo (0 : ℝ) q ×ˢ Ioo (-Real.pi) Real.pi
  have hQ : MeasurableSet Q := measurableSet_Ioo.prod measurableSet_Ioo
  have hQi : IntegrableOn (fun rt : ℝ × ℝ => H rt.2 rt.1) Q :=
    hH.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hQsub : Q ⊆ polarCoord.target := fun z hz => ⟨hz.1.1, hz.2⟩
  let e0 : E2 ≃ᵐ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv.trans
      MeasurableEquiv.finTwoArrow
  have he0 : MeasurePreserving e0 volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  let e : (ℝ × ℝ) ≃ᵐ E2 := e0.symm.trans (MeasurableEquiv.addLeft x)
  have he : MeasurePreserving e volume volume :=
    (measurePreserving_add_left volume x).comp (he0.symm e0)
  have hepolar (rt : ℝ × ℝ) : e (polarCoord.symm rt) =
      x + rt.1 • unitCircleParameter rt.2 := by
    congr 1
    ext k
    fin_cases k <;> rfl
  let ft : ℝ × ℝ → F := fun z => (Metric.ball x q).indicator f (e z)
  have htransform (z : ℝ × ℝ) (hz : z ∈ polarCoord.target) :
      z.1 • ft (polarCoord.symm z) = Q.indicator (fun rt => H rt.2 rt.1) z := by
    have hr : 0 < z.1 := hz.1
    have hm : e (polarCoord.symm z) ∈ Metric.ball x q ↔ z ∈ Q := by
      rw [hepolar, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, circle_norm, mul_one]
      change z.1 < q ↔ (0 < z.1 ∧ z.1 < q) ∧ (-Real.pi < z.2 ∧ z.2 < Real.pi)
      exact ⟨fun h => ⟨⟨hr, h⟩, hz.2⟩, fun h => h.1.2⟩
    dsimp only [ft]
    by_cases hzQ : z ∈ Q
    · rw [indicator_of_mem (hm.mpr hzQ), indicator_of_mem hzQ, hepolar]
      exact hEq z.1 hzQ.1 z.2 hzQ.2
    · rw [indicator_of_notMem (mt hm.mp hzQ), indicator_of_notMem hzQ, smul_zero]
  have hJac : IntegrableOn
      (fun z => |(fderivPolarCoordSymm z).det| • ft (polarCoord.symm z)) polarCoord.target := by
    have hind : Integrable (Q.indicator (fun rt => H rt.2 rt.1)) :=
      (integrable_indicator_iff hQ).mpr hQi
    apply hind.integrableOn.congr_fun _ polarCoord.open_target.measurableSet
    intro z hz
    dsimp only
    rw [det_fderivPolarCoordSymm, abs_of_pos hz.1]
    exact (htransform z hz).symm
  have hfti : Integrable ft := by
    have himage : IntegrableOn ft (polarCoord.symm '' polarCoord.target) :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
        polarCoord.open_target.measurableSet
        (fun z _ => (hasFDerivAt_polarCoord_symm z).hasFDerivWithinAt)
        polarCoord.symm.injOn ft).mpr hJac
    rw [polarCoord.symm_image_target_eq_source] at himage
    have hu : IntegrableOn ft univ := himage.congr_set_ae polarCoord_source_ae_eq_univ.symm
    simpa only [IntegrableOn, Measure.restrict_univ] using hu
  have hfi : IntegrableOn f (Metric.ball x q) := by
    apply (integrable_indicator_iff measurableSet_ball).mp
    exact (he.integrable_comp_emb e.measurableEmbedding).mp hfti
  refine ⟨hfi, ?_⟩
  have hpolar : (∫ z in Metric.ball x q, f z) = ∫ z in Q, H z.2 z.1 := by
    calc
      _ = ∫ z, (Metric.ball x q).indicator f z := (integral_indicator measurableSet_ball).symm
      _ = ∫ z, ft z := (he.integral_comp' ((Metric.ball x q).indicator f)).symm
      _ = ∫ z in polarCoord.target, z.1 • ft (polarCoord.symm z) :=
        (integral_comp_polarCoord_symm ft).symm
      _ = ∫ z in polarCoord.target, Q.indicator (fun rt => H rt.2 rt.1) z :=
        setIntegral_congr_fun polarCoord.open_target.measurableSet htransform
      _ = ∫ z in Q, H z.2 z.1 := by
        rw [setIntegral_indicator hQ, inter_eq_right.mpr hQsub]
  rw [hpolar]
  have hrectangle : (∫ z in Q, H z.2 z.1) =
      ∫ z in Icc (0 : ℝ) q ×ˢ Icc (-Real.pi) Real.pi, H z.2 z.1 :=
    setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)
  rw [hrectangle]
  change (∫ z in Icc (0 : ℝ) q ×ˢ Icc (-Real.pi) Real.pi,
    H z.2 z.1 ∂(volume.prod volume)) = _
  rw [← Measure.prod_restrict]
  have hprod : Integrable (fun rt : ℝ × ℝ => H rt.2 rt.1)
      ((volume.restrict (Icc (0 : ℝ) q)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact hH
  exact integral_prod_symm _ hprod

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
