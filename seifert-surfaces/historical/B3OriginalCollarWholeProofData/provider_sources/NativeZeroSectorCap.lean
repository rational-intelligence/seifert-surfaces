import NativeCapSectorGeometry
import NativeBallRotationTransport

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem integral_inter_of_zero_off {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U V : Set E2) (hU : MeasurableSet U) (hV : MeasurableSet V) (f : E2 → F)
    (hf : ∀ z ∈ U, z ∉ V → f z = 0) :
    (∫ z in V ∩ U, f z) = ∫ z in U, f z := by
  rw [inter_comm, ← setIntegral_indicator hV]
  apply setIntegral_congr_fun hU
  intro z hz
  by_cases hzV : z ∈ V
  · rw [indicator_of_mem hzV]
  · rw [indicator_of_notMem hzV, hf z hz hzV]

theorem scalar_zero_cap_extension (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (f : ℝ → ℝ)
    (hfa : AbsolutelyContinuousOnInterval f (Real.arcsin (q / 2) - Real.pi / 2)
      (Real.pi / 2 - Real.arcsin (q / 2)))
    (hfleft : f (Real.arcsin (q / 2) - Real.pi / 2) = 0)
    (hfright : f (Real.pi / 2 - Real.arcsin (q / 2)) = 0)
    (hfd : MemLp (deriv f) 2 (volume.restrict
      (Icc (Real.arcsin (q / 2) - Real.pi / 2) (Real.pi / 2 - Real.arcsin (q / 2))))) :
    let a := Real.arcsin (q / 2) - Real.pi / 2
    let b := Real.pi / 2 - Real.arcsin (q / 2)
    ∃ (h : E2 → ℝ) (d : E2 → E2),
      H1On (planarCap (unitCircleParameter s) q) h d ∧
      (∫ z in planarCap (unitCircleParameter s) q, ‖d z‖ ^ 2) ≤
        (((2 * Real.pi) ^ 2 + 1) / 2) * ∫ t in Icc a b, deriv f t ^ 2 ∧
      (∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ j : Fin 2,
        IntegrableOn (fun z => h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z)
          (planarCap (unitCircleParameter s) q) ∧
        IntegrableOn (fun t => f t * psi (unitCircleParameter s +
          q • unitCircleParameter (s + Real.pi + t)) * unitCircleParameter (s + Real.pi + t) j)
          (Icc a b) ∧
        (∫ z in planarCap (unitCircleParameter s) q,
          h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) =
          q * ∫ t in Icc a b, f t * psi (unitCircleParameter s +
            q • unitCircleParameter (s + Real.pi + t)) * unitCircleParameter (s + Real.pi + t) j) := by
  classical
  dsimp only
  let a := Real.arcsin (q / 2) - Real.pi / 2
  let b := Real.pi / 2 - Real.arcsin (q / 2)
  let x := unitCircleParameter s
  let R := planeRotation (s + Real.pi)
  obtain ⟨ha, hab, hb, _⟩ := cap_sector_angles q hq hqhalf
  change -Real.pi < a at ha
  change a < b at hab
  change b < Real.pi at hb
  obtain ⟨g, hgc, hgp, hga, hgd, hgf, hge, hgenergy, hgdenergy⟩ :=
    periodic_zero_extension a b ha hab hb f hfa hfleft hfright hfd
  let h : E2 → ℝ := fun z => scalarCone 0 q 0 g (R.symm (z - x))
  let d : E2 → E2 := fun z => R (scalarConeGrad 0 q g (R.symm (z - x)))
  have hrot := rotated_scalar_cone x R q 0 hq g hgp hgc hga hgd
  dsimp only at hrot
  have hzero (z : E2) (hz : z ∈ Metric.ball x q) (hzD : z ∉ disc 1) : h z = 0 ∧ d z = 0 := by
    by_cases hzx : z = x
    · subst z
      simp [h, d, scalarCone, scalarConeGrad]
    let u := R.symm (z - x)
    have hu : u ≠ 0 := by
      intro he
      apply hzx
      have he' := congrArg R he
      simpa only [u, R.apply_symm_apply, map_zero, sub_eq_zero] using he'
    have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hrq : ‖u‖ < q := by
      simpa only [u, R.symm.norm_map, Metric.mem_ball, dist_eq_norm] using hz
    have hrec : x + ‖u‖ • R (unitCircleParameter (polarAngle u)) = z := by
      rw [← map_smul, polarAngle_reconstruct]
      simp [u]
    have hang : polarAngle u ∉ Icc a b := by
      intro ht
      have hi := cap_sector_inside s q ‖u‖ (polarAngle u) hq hqhalf hr hrq ht
      rw [hrec] at hi
      exact hzD hi
    have ho := zero_extension_deriv_off a b ha hab hb f g hfleft hfright hgf
      (polarAngle u) (polarAngle_mem u) hang
    constructor
    · change 0 + (‖u - 0‖ / q) * g (polarAngle (u - 0)) = 0
      simp only [sub_zero, ho.1, mul_zero, zero_add]
    · dsimp [d, scalarConeGrad]
      simp only [sub_zero]
      change R (q⁻¹ • ((g (polarAngle u) / ‖u‖) • u +
        (deriv g (polarAngle u) / ‖u‖) • rotateQuarter u)) = 0
      simp [ho.1, ho.2]
  have hhc : MemLp h 2 (volume.restrict (planarCap x q)) :=
    hrot.1.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have hdc : MemLp d 2 (volume.restrict (planarCap x q)) :=
    hrot.2.1.mono_measure (Measure.restrict_mono inter_subset_right le_rfl)
  have hgreen (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi) (j : Fin 2) :
      IntegrableOn (fun z => h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z)
        (planarCap x q) ∧
      IntegrableOn (fun t => f t * psi (x + q • unitCircleParameter (s + Real.pi + t)) *
        unitCircleParameter (s + Real.pi + t) j) (Icc a b) ∧
      (∫ z in planarCap x q, h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) =
        q * ∫ t in Icc a b, f t * psi (x + q • unitCircleParameter (s + Real.pi + t)) *
          unitCircleParameter (s + Real.pi + t) j := by
    obtain ⟨hi, ht, he⟩ := hrot.2.2.2 psi hs j
    have hc : ContinuousOn f (Icc a b) := by
      have hh : AbsolutelyContinuousOnInterval f a b := hfa
      simpa only [uIcc_of_le hab.le] using hh.continuousOn
    refine ⟨hi.mono_set inter_subset_right, ?_, ?_⟩
    · apply ContinuousOn.integrableOn_compact isCompact_Icc
      have hcc : Continuous (fun t : ℝ => unitCircleParameter (s + Real.pi + t)) :=
        circle_contDiff.continuous.comp (continuous_const.add continuous_id)
      have hcp : Continuous (fun t : ℝ => psi (x + q • unitCircleParameter (s + Real.pi + t))) :=
        hs.continuous.comp (continuous_const.add ((continuous_const : Continuous (fun _ : ℝ => q)).smul hcc))
      have hcj : Continuous (fun t : ℝ => unitCircleParameter (s + Real.pi + t) j) :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp hcc
      exact hc.mul hcp.continuousOn |>.mul hcj.continuousOn
    · change (∫ z in disc 1 ∩ Metric.ball x q, h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) = _
      rw [integral_inter_of_zero_off (Metric.ball x q) (disc 1) measurableSet_ball measurableSet_ball
        (fun z => h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) (by
        intro z hz hzn
        obtain ⟨hz0, hdz0⟩ := hzero z hz hzn
        simp [hz0, hdz0])]
      change (∫ z in Metric.ball x q, h z * fderiv ℝ psi z (coordinateVector 2 j) + d z j * psi z) = _
      rw [he]
      congr 1
      calc
        _ = ∫ t in Icc (-Real.pi) Real.pi,
            (Icc a b).indicator (fun t => f t * psi (x + q • unitCircleParameter (s + Real.pi + t)) *
              unitCircleParameter (s + Real.pi + t) j) t := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht'
          dsimp only
          rw [hgf t ht', show R (unitCircleParameter t) = unitCircleParameter (s + Real.pi + t) from
            planeRotation_circle (s + Real.pi) t]
          by_cases htab : t ∈ Icc a b <;> simp [htab]
        _ = _ := by
          rw [setIntegral_indicator measurableSet_Icc,
            inter_eq_right.mpr (Icc_subset_Icc ha.le hb.le)]
  refine ⟨h, d, ?_, ?_, hgreen⟩
  · letI : IsFiniteMeasure (volume.restrict (planarCap x q)) :=
      isFiniteMeasure_restrict.mpr (lt_of_le_of_lt (measure_mono inter_subset_right) measure_ball_lt_top).ne
    refine ⟨⟨IntegrableOn.locallyIntegrableOn (hhc.integrable (by norm_num)),
      IntegrableOn.locallyIntegrableOn (hdc.integrable (by norm_num)), ?_⟩, hhc, hdc⟩
    intro psi hs hsc hss j
    have he := (hgreen psi hs j).2.2
    have hz (t : ℝ) : psi (x + q • unitCircleParameter (s + Real.pi + t)) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hm := (hss ht).2
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hq, circle_norm, mul_one] at hm
      exact (lt_irrefl q) hm
    simp only [hz, mul_zero, zero_mul, integral_zero] at he
    have htest : MemLp (fun z => fderiv ℝ psi z (coordinateVector 2 j)) 2
        (volume.restrict (planarCap x q)) :=
      ((hs.continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
        (hsc.fderiv_apply ℝ _)).restrict _
    have hpsi : MemLp psi 2 (volume.restrict (planarCap x q)) :=
      (hs.continuous.memLp_of_hasCompactSupport hsc).restrict _
    have hl := hhc.integrable_mul htest
    have hr := (hdc.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)).integrable_mul hpsi
    have hspl := integral_add hl hr
    simp only [Pi.mul_apply, EuclideanSpace.coe_proj] at hspl
    rw [hspl] at he
    linarith
  · have he := hrot.2.2.1
    have hec : (∫ z in planarCap x q, ‖d z‖ ^ 2) = ∫ z in Metric.ball x q, ‖d z‖ ^ 2 :=
      integral_inter_of_zero_off _ _ measurableSet_ball measurableSet_ball _ (by
        intro z hz hzn
        simp [(hzero z hz hzn).2])
    have hgi : IntegrableOn (fun t => g t ^ 2) (Icc (-Real.pi) Real.pi) := (hgc.pow 2).integrableOn_Icc
    rw [hec, he, integral_add hgi hgd.integrable_sq, hgenergy, hgdenergy]
    have hp := ac_interval_poincare a b hab f hfa hfd
    have hfl : f a = 0 := hfleft
    simp only [hfl, sub_zero] at hp
    have hE : 0 ≤ ∫ t in Icc a b, deriv f t ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
    have hlen : 0 ≤ b - a ∧ b - a ≤ 2 * Real.pi := ⟨by linarith, by linarith⟩
    have hslen : (b - a) ^ 2 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.pi_pos]
    have hp' := hp.trans (mul_le_mul_of_nonneg_right hslen hE)
    nlinarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
