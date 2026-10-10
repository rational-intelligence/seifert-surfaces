import B1MetricVariationalInterfaces
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CourantAnalyticB
open SeifertSurfaces.AppendixACoordinates

theorem native_translated_polar_rows
    (d : Fin 2 → E2 → E2)
    (row_measurable : ∀ i, AEStronglyMeasurable (d i) (volume.restrict (disc 1)))
    (row_L2 : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)))
    (p : E2) (a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    let D := disc 1
    let angles := Ioo (-Real.pi) Real.pi
    let radii := Ioo a z
    let d0 : Fin 2 → E2 → E2 := fun i => D.indicator (d i)
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let Q : (Fin 2 → E2 → E2) → E2 → ℝ := fun rows x =>
      ‖rows 0 x‖ ^ 2 + ‖rows 1 x‖ ^ 2
    let angular : Fin 2 → ℝ → ℝ → E2 := fun i r t => d0 i (p + r • unitCircleParameter t)
    let flux : Fin 2 → ℝ → ℝ := fun i r =>
      r * ∫ t in angles, inner ℝ (angular i r t) (J (unitCircleParameter t))
    let energy : ℝ → ℝ := fun r => ∫ t in angles, Q d0 (p + r • unitCircleParameter t)
    let annulus : Set E2 := {x | x ∈ D ∧ a < ‖x - p‖ ∧ ‖x - p‖ < z}
    (∀ i, AEStronglyMeasurable (d0 i) volume ∧ MemLp (d0 i) 2 volume) ∧
    (∀ i, AEStronglyMeasurable (fun rt : ℝ × ℝ => angular i rt.1 rt.2)
        (volume.restrict (radii ×ˢ angles)) ∧
      MemLp (fun rt : ℝ × ℝ => angular i rt.1 rt.2) 2
        (volume.restrict (radii ×ˢ angles))) ∧
    (∀ᵐ r ∂volume.restrict radii,
      (∀ i, AEStronglyMeasurable (angular i r) (volume.restrict angles) ∧
        MemLp (angular i r) 2 (volume.restrict angles) ∧
        IntegrableOn (fun t => ‖angular i r t‖ ^ 2) angles volume ∧
        IntegrableOn (fun t => inner ℝ (angular i r t) (J (unitCircleParameter t))) angles volume) ∧
      IntegrableOn (fun t => Q d0 (p + r • unitCircleParameter t)) angles volume) ∧
    AEStronglyMeasurable energy (volume.restrict radii) ∧
    IntegrableOn (fun r => r * energy r) radii volume ∧
    IntegrableOn (Q d) annulus volume ∧
    (∫ r in radii, r * energy r) = ∫ x in annulus, Q d x ∧
    (∀ i, AEStronglyMeasurable (flux i) (volume.restrict radii) ∧
      IntegrableOn (flux i) radii volume) ∧
    (∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo (a ^ 2) (z ^ 2) →
      let rho2 : E2 → ℝ := fun x => (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2
      let chi : Fin 2 → E2 → ℝ := ![
        fun x => -(x 1 - p 1) * h (rho2 x),
        fun x => (x 0 - p 0) * h (rho2 x)]
      ∀ i, IntegrableOn (fun x => d i x 0 * chi 0 x + d i x 1 * chi 1 x) D volume ∧
        IntegrableOn (fun r => r * h (r ^ 2) * flux i r) radii volume ∧
        (∫ x in D, d i x 0 * chi 0 x + d i x 1 * chi 1 x) =
          ∫ r in radii, r * h (r ^ 2) * flux i r) := by
  classical
  dsimp only
  let D : Set E2 := disc 1
  let T : Set ℝ := Ioo (-Real.pi) Real.pi
  let U : Set ℝ := Ioo a z
  let R : Set (ℝ × ℝ) := U ×ˢ T
  let d0 : Fin 2 → E2 → E2 := fun i => D.indicator (d i)
  let c : ℝ → E2 := unitCircleParameter
  let J : E2 → E2 := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let Q : (Fin 2 → E2 → E2) → E2 → ℝ := fun rows x => ‖rows 0 x‖ ^ 2 + ‖rows 1 x‖ ^ 2
  let angular : Fin 2 → ℝ → ℝ → E2 := fun i r t => d0 i (p + r • c t)
  let pair : Fin 2 → ℝ × ℝ → ℝ := fun i rt => inner ℝ (angular i rt.1 rt.2) (J (c rt.2))
  let energy : ℝ → ℝ := fun r => ∫ t in T, Q d0 (p + r • c t)
  let flux : Fin 2 → ℝ → ℝ := fun i r => r * ∫ t in T, pair i (r, t)
  let A : Set E2 := {x | a < ‖x - p‖ ∧ ‖x - p‖ < z}
  have hD : MeasurableSet D := measurableSet_ball
  have hT : MeasurableSet T := measurableSet_Ioo
  have hU : MeasurableSet U := measurableSet_Ioo
  have hR : MeasurableSet R := hU.prod hT
  have hA : MeasurableSet A := (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).measurableSet.inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const).measurableSet
  letI : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  letI : IsFiniteMeasure (volume.restrict T) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hRsub : R ⊆ polarCoord.target := fun rt hrt => ⟨ha.trans hrt.1.1, hrt.2⟩
  let e0 : E2 ≃ᵐ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv.trans MeasurableEquiv.finTwoArrow
  have he0 : MeasurePreserving e0 volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
  let e : (ℝ × ℝ) ≃ᵐ E2 := e0.symm.trans (MeasurableEquiv.addLeft p)
  have he : MeasurePreserving e volume volume := (measurePreserving_add_left volume p).comp (he0.symm e0)
  have hepolar (rt : ℝ × ℝ) : e (polarCoord.symm rt) = p + rt.1 • c rt.2 := by
    congr 1
    ext k
    fin_cases k <;> rfl
  have hc : Continuous c := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    exact continuous_pi fun k : Fin 2 => by fin_cases k <;> simp <;> fun_prop
  have hJ : Continuous J := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    exact continuous_pi fun k : Fin 2 => by fin_cases k <;> simp <;> fun_prop
  have hn (t : ℝ) : ‖c t‖ = 1 := by
    have hs : ‖c t‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      exact Real.cos_sq_add_sin_sq t
    nlinarith [norm_nonneg (c t)]
  have hJn (v : E2) : ‖J v‖ = ‖v‖ := by
    have hs : ‖J v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Fin.sum_univ_two]
      change (-v 1) ^ 2 + v 0 ^ 2 = v 0 ^ 2 + v 1 ^ 2
      ring
    nlinarith [norm_nonneg (J v), norm_nonneg v]
  have hpolar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : E2 → V) (hf : Integrable f) :
      IntegrableOn (fun rt : ℝ × ℝ => rt.1 • f (p + rt.1 • c rt.2)) polarCoord.target := by
    have hG : Integrable (f ∘ e) := (he.integrable_comp_emb e.measurableEmbedding).mpr hf
    have hGimage : IntegrableOn (f ∘ e) (polarCoord.symm '' polarCoord.target) := hG.integrableOn
    have h := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      polarCoord.open_target.measurableSet
      (fun rt _ => (hasFDerivAt_polarCoord_symm rt).hasFDerivWithinAt)
      polarCoord.symm.injOn (f ∘ e)).mp hGimage
    apply h.congr_fun _ polarCoord.open_target.measurableSet
    intro rt hrt
    dsimp only
    rw [det_fderivPolarCoordSymm, abs_of_pos hrt.1]
    simp only [comp_apply, hepolar]
  have hchange (f : E2 → ℝ) :
      (∫ x, f x) = ∫ rt in polarCoord.target, rt.1 * f (p + rt.1 • c rt.2) := by
    calc
      (∫ x, f x) = ∫ rt, f (e rt) := (he.integral_comp' f).symm
      _ = ∫ rt in polarCoord.target, rt.1 • f (e (polarCoord.symm rt)) :=
        (integral_comp_polarCoord_symm (f ∘ e)).symm
      _ = _ := by simp only [hepolar, smul_eq_mul]
  have hinv : MemLp (fun rt : ℝ × ℝ => rt.1⁻¹) ∞ (volume.restrict R) := by
    apply memLp_top_of_bound ((continuous_fst.continuousOn.inv₀
      (fun rt hrt => (ha.trans hrt.1.1).ne')).aestronglyMeasurable hR) a⁻¹
    filter_upwards [ae_restrict_mem hR] with rt hrt
    change ‖rt.1⁻¹‖ ≤ a⁻¹
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (ha.trans hrt.1.1))]
    exact (inv_le_inv₀ (ha.trans hrt.1.1) ha).mpr hrt.1.1.le
  have hunweight {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : E2 → V) (hf : Integrable f) :
      IntegrableOn (fun rt : ℝ × ℝ => f (p + rt.1 • c rt.2)) R := by
    have h := ((hpolar f hf).mono_set hRsub).smul_of_top_right hinv
    apply h.congr
    filter_upwards [ae_restrict_mem hR] with rt hrt
    change rt.1⁻¹ • (rt.1 • f (p + rt.1 • c rt.2)) = f (p + rt.1 • c rt.2)
    simp only [smul_smul, inv_mul_cancel₀ (ha.trans hrt.1.1).ne', one_smul]
  have hzero (i : Fin 2) : MemLp (d0 i) 2 volume :=
    (memLp_indicator_iff_restrict hD.nullMeasurableSet).mpr (row_L2 i)
  have hi (i : Fin 2) : Integrable (d0 i) :=
    (integrable_indicator_iff hD).mpr (MemLp.integrable (by norm_num) (row_L2 i))
  have hrow (i : Fin 2) : IntegrableOn (fun rt : ℝ × ℝ => angular i rt.1 rt.2) R := hunweight _ (hi i)
  have hsq (i : Fin 2) : IntegrableOn (fun rt : ℝ × ℝ => ‖angular i rt.1 rt.2‖ ^ 2) R :=
    hunweight _ ((hzero i).integrable_norm_pow (by decide : 2 ≠ 0))
  have hrowL2 (i : Fin 2) : MemLp (fun rt : ℝ × ℝ => angular i rt.1 rt.2) 2 (volume.restrict R) :=
    (memLp_two_iff_integrable_sq_norm (hrow i).aestronglyMeasurable).mpr (hsq i)
  have hQ : Integrable (Q d0) :=
    ((hzero 0).integrable_norm_pow (by decide : 2 ≠ 0)).add
      ((hzero 1).integrable_norm_pow (by decide : 2 ≠ 0))
  have hQR : IntegrableOn (fun rt : ℝ × ℝ => Q d0 (p + rt.1 • c rt.2)) R := (hsq 0).add (hsq 1)
  have hprod : (volume.restrict U).prod (volume.restrict T) = volume.restrict R := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hpair (i : Fin 2) : IntegrableOn (pair i) R := by
    apply (hrow i).norm.mono' ((hrow i).aestronglyMeasurable.inner
      ((hJ.comp (hc.comp continuous_snd)).aestronglyMeasurable.restrict))
    filter_upwards [] with rt
    exact (norm_inner_le_norm _ _).trans_eq (by rw [hJn, hn, mul_one])
  have hemeas : AEStronglyMeasurable energy (volume.restrict U) := by
    have h := hQR.aestronglyMeasurable
    rw [← hprod] at h
    exact h.integral_prod_right'
  have henergy : IntegrableOn (fun r => r * energy r) U := by
    change Integrable (fun r => r * energy r) (volume.restrict U)
    have h := (hpolar _ hQ).mono_set hRsub
    change IntegrableOn (fun rt : ℝ × ℝ => rt.1 * Q d0 (p + rt.1 • c rt.2)) R at h
    rw [IntegrableOn, ← hprod] at h
    have hg := h.integral_prod_left
    simpa only [energy, integral_const_mul] using hg
  have hflux (i : Fin 2) : AEStronglyMeasurable (flux i) (volume.restrict U) ∧ IntegrableOn (flux i) U := by
    have hp := hpair i
    rw [IntegrableOn, ← hprod] at hp
    have hrad : MemLp (fun r : ℝ => r) ∞ (volume.restrict U) := by
      apply memLp_top_of_bound continuous_id.aestronglyMeasurable z
      filter_upwards [ae_restrict_mem hU] with r hr
      change ‖r‖ ≤ z
      rw [Real.norm_eq_abs, abs_of_pos (ha.trans hr.1)]
      exact hr.2.le
    have hf : Integrable (flux i) (volume.restrict U) := hp.integral_prod_left.smul_of_top_right hrad
    exact ⟨hf.aestronglyMeasurable, hf⟩
  have hslices : ∀ᵐ r ∂volume.restrict U,
      (∀ i, AEStronglyMeasurable (angular i r) (volume.restrict T) ∧
        MemLp (angular i r) 2 (volume.restrict T) ∧
        IntegrableOn (fun t => ‖angular i r t‖ ^ 2) T volume ∧
        IntegrableOn (fun t => inner ℝ (angular i r t) (J (c t))) T volume) ∧
      IntegrableOn (fun t => Q d0 (p + r • c t)) T volume := by
    have hrows : ∀ i, ∀ᵐ r ∂volume.restrict U,
        AEStronglyMeasurable (angular i r) (volume.restrict T) ∧
        MemLp (angular i r) 2 (volume.restrict T) ∧
        IntegrableOn (fun t => ‖angular i r t‖ ^ 2) T volume ∧
        IntegrableOn (fun t => inner ℝ (angular i r t) (J (c t))) T volume := by
      intro i
      have hm := (hrow i).aestronglyMeasurable
      have hs := hsq i
      have hp := hpair i
      rw [IntegrableOn, ← hprod] at hs hp
      rw [← hprod] at hm
      filter_upwards [hm.prodMk_left, hs.prod_right_ae, hp.prod_right_ae] with r hmr hsr hpr
      exact ⟨hmr, (memLp_two_iff_integrable_sq_norm hmr).mpr hsr, hsr, hpr⟩
    have hq := hQR
    rw [IntegrableOn, ← hprod] at hq
    filter_upwards [ae_all_iff.mpr hrows, hq.prod_right_ae] with r hr hqr
    exact ⟨hr, hqr⟩
  have hbulk : IntegrableOn (Q d) (D ∩ A) := by
    apply ((row_L2 0).integrable_norm_pow (by decide : 2 ≠ 0)).add
      ((row_L2 1).integrable_norm_pow (by decide : 2 ≠ 0)) |>.mono_measure
    exact Measure.restrict_mono (inter_subset_left) le_rfl
  have heidentity : (∫ r in U, r * energy r) = ∫ x in D ∩ A, Q d x := by
    have hQindic : Q d0 = D.indicator (Q d) := by
      funext x
      by_cases hx : x ∈ D
      · simp only [Q, d0, indicator_of_mem hx]
      · simp only [Q, d0, indicator_of_notMem hx, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
    have htransform (rt : ℝ × ℝ) (hrt : rt ∈ polarCoord.target) :
        rt.1 * A.indicator (Q d0) (p + rt.1 • c rt.2) =
          R.indicator (fun rt : ℝ × ℝ => rt.1 * Q d0 (p + rt.1 • c rt.2)) rt := by
      have hrpos : 0 < rt.1 := hrt.1
      have hnorm : ‖p + rt.1 • c rt.2 - p‖ = rt.1 := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hn, mul_one]
      have hm : p + rt.1 • c rt.2 ∈ A ↔ rt ∈ R := by
        change (a < ‖p + rt.1 • c rt.2 - p‖ ∧ ‖p + rt.1 • c rt.2 - p‖ < z) ↔
          (rt.1 ∈ U ∧ rt.2 ∈ T)
        rw [hnorm]
        exact ⟨fun h => ⟨h, hrt.2⟩, fun h => h.1⟩
      by_cases hr : rt ∈ R
      · rw [indicator_of_mem (hm.mpr hr), indicator_of_mem hr]
      · rw [indicator_of_notMem (mt hm.mp hr), indicator_of_notMem hr, mul_zero]
    have hj := (hpolar _ hQ).mono_set hRsub
    change IntegrableOn (fun rt : ℝ × ℝ => rt.1 * Q d0 (p + rt.1 • c rt.2)) R at hj
    calc
      (∫ r in U, r * energy r) = ∫ rt in R, rt.1 * Q d0 (p + rt.1 • c rt.2) := by
        rw [IntegrableOn, ← hprod] at hj
        rw [← hprod]
        rw [integral_prod _ hj]
        simp only [energy, integral_const_mul]
      _ = ∫ rt in polarCoord.target,
          R.indicator (fun rt : ℝ × ℝ => rt.1 * Q d0 (p + rt.1 • c rt.2)) rt := by
        rw [setIntegral_indicator hR, inter_eq_right.mpr hRsub]
      _ = ∫ rt in polarCoord.target, rt.1 * A.indicator (Q d0) (p + rt.1 • c rt.2) :=
        setIntegral_congr_fun polarCoord.open_target.measurableSet fun rt hrt => (htransform rt hrt).symm
      _ = ∫ x, A.indicator (Q d0) x := (hchange _).symm
      _ = ∫ x in D ∩ A, Q d x := by
        rw [integral_indicator hA, hQindic, setIntegral_indicator hD, inter_comm]
  have htest : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      tsupport h ⊆ Ioo (a ^ 2) (z ^ 2) →
      let rho2 : E2 → ℝ := fun x => (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2
      let chi : Fin 2 → E2 → ℝ := ![fun x => -(x 1 - p 1) * h (rho2 x), fun x => (x 0 - p 0) * h (rho2 x)]
      ∀ i, IntegrableOn (fun x => d i x 0 * chi 0 x + d i x 1 * chi 1 x) D volume ∧
        IntegrableOn (fun r => r * h (r ^ 2) * flux i r) U volume ∧
        (∫ x in D, d i x 0 * chi 0 x + d i x 1 * chi 1 x) =
          ∫ r in U, r * h (r ^ 2) * flux i r := by
    intro h hh hhc hhs
    dsimp only
    let rho2 : E2 → ℝ := fun x => (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2
    let chi : Fin 2 → E2 → ℝ := ![
      fun x => -(x 1 - p 1) * h (rho2 x),
      fun x => (x 0 - p 0) * h (rho2 x)]
    have hcchi (j : Fin 2) : Continuous (chi j) := by
      have hch := hh.continuous
      fin_cases j
      · change Continuous (fun x : E2 => -(x 1 - p 1) * h ((x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2))
        fun_prop
      · change Continuous (fun x : E2 => (x 0 - p 0) * h ((x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2))
        fun_prop
    have hcoord (i j : Fin 2) : IntegrableOn (fun x => d i x j) D :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp
        (MemLp.integrable (μ := volume.restrict D) (by norm_num) (row_L2 i))
    have hterm (i j : Fin 2) : IntegrableOn (fun x => d i x j * chi j x) D := by
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn (hcchi j).continuousOn
      apply (hcoord i j).mul_bdd (hcchi j).aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem hD] with x hx
      exact hC x (Metric.mem_closedBall.mpr (Metric.mem_ball.mp hx).le)
    have hbound : ∃ C, ∀ r ∈ U, ‖r * h (r ^ 2)‖ ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (show ContinuousOn (fun r : ℝ => r * h (r ^ 2)) (Icc a z) from
          (continuous_id.mul (hh.continuous.comp (continuous_id.pow 2))).continuousOn)
      exact ⟨C, fun r hr => hC r ⟨hr.1.le, hr.2.le⟩⟩
    have hrho (r t : ℝ) : rho2 (p + r • c t) = r ^ 2 := by
      change ((p 0 + r * Real.cos t) - p 0) ^ 2 + ((p 1 + r * Real.sin t) - p 1) ^ 2 = r ^ 2
      calc
        _ = r ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
        _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    have hinner (v : E2) (t : ℝ) : inner ℝ v (J (c t)) =
        v 0 * (-Real.sin t) + v 1 * Real.cos t := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      change inner ℝ (v 0) (-Real.sin t) + inner ℝ (v 1) (Real.cos t) = _
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    intro i
    let f : E2 → ℝ := fun x => d i x 0 * chi 0 x + d i x 1 * chi 1 x
    have hfi : IntegrableOn f D := (hterm i 0).add (hterm i 1)
    have hrad : IntegrableOn (fun r => r * h (r ^ 2) * flux i r) U := by
      obtain ⟨C, hC⟩ := hbound
      apply (hflux i).2.bdd_mul
        (continuous_id.mul (hh.continuous.comp (continuous_id.pow 2))).aestronglyMeasurable.restrict
      filter_upwards [ae_restrict_mem hU] with r hr
      exact hC r hr
    have hprofile (rt : ℝ × ℝ) : D.indicator f (p + rt.1 • c rt.2) =
        rt.1 * h (rt.1 ^ 2) * pair i rt := by
      by_cases hx : p + rt.1 • c rt.2 ∈ D
      · rw [indicator_of_mem hx]
        dsimp only [pair, angular, d0]
        rw [indicator_of_mem hx, hinner]
        dsimp only [f, chi, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hrho]
        change d i (p + rt.1 • c rt.2) 0 * (-(p 1 + rt.1 * Real.sin rt.2 - p 1) * h (rt.1 ^ 2)) +
          d i (p + rt.1 • c rt.2) 1 * ((p 0 + rt.1 * Real.cos rt.2 - p 0) * h (rt.1 ^ 2)) = _
        ring
      · rw [indicator_of_notMem hx]
        dsimp only [pair, angular, d0]
        rw [indicator_of_notMem hx, inner_zero_left, mul_zero]
    have houtside (r : ℝ) (hr : 0 < r) (hrU : r ∉ U) : h (r ^ 2) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      have hs' := hhs hs
      have hr1 : a < r := (sq_lt_sq₀ ha.le hr.le).mp hs'.1
      have hr2 : r < z := (sq_lt_sq₀ hr.le (ha.trans haz).le).mp hs'.2
      exact hrU ⟨hr1, hr2⟩
    have htransform (rt : ℝ × ℝ) (hrt : rt ∈ polarCoord.target) :
        rt.1 * D.indicator f (p + rt.1 • c rt.2) =
          R.indicator (fun rt : ℝ × ℝ => rt.1 * (rt.1 * h (rt.1 ^ 2) * pair i rt)) rt := by
      rw [hprofile]
      by_cases hr : rt ∈ R
      · rw [indicator_of_mem hr]
      · rw [indicator_of_notMem hr]
        have hrU : rt.1 ∉ U := fun hU => hr ⟨hU, hrt.2⟩
        rw [houtside rt.1 hrt.1 hrU]
        ring
    have htestR : IntegrableOn
        (fun rt : ℝ × ℝ => rt.1 * (rt.1 * h (rt.1 ^ 2) * pair i rt)) R := by
      have h := (hpolar _ ((integrable_indicator_iff hD).mpr hfi)).mono_set hRsub
      apply h.congr_fun _ hR
      intro rt hrt
      dsimp only
      rw [smul_eq_mul, hprofile]
    refine ⟨hfi, hrad, ?_⟩
    calc
      (∫ x in D, f x) = ∫ x, D.indicator f x := (integral_indicator hD).symm
      _ = ∫ rt in polarCoord.target, rt.1 * D.indicator f (p + rt.1 • c rt.2) := hchange _
      _ = ∫ rt in polarCoord.target,
          R.indicator (fun rt : ℝ × ℝ => rt.1 * (rt.1 * h (rt.1 ^ 2) * pair i rt)) rt :=
        setIntegral_congr_fun polarCoord.open_target.measurableSet htransform
      _ = ∫ rt in R, rt.1 * (rt.1 * h (rt.1 ^ 2) * pair i rt) := by
        rw [setIntegral_indicator hR, inter_eq_right.mpr hRsub]
      _ = ∫ r in U, r * h (r ^ 2) * flux i r := by
        rw [IntegrableOn, ← hprod] at htestR
        rw [← hprod, integral_prod _ htestR]
        simp only [integral_const_mul, flux]
        apply integral_congr_ae
        filter_upwards [] with r
        ring
  exact ⟨fun i => ⟨(hzero i).aestronglyMeasurable, hzero i⟩,
    fun i => ⟨(hrow i).aestronglyMeasurable, hrowL2 i⟩,
    hslices, hemeas, henergy, hbulk, heidentity, hflux, htest⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.CourantAnalyticB
