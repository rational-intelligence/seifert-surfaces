import B1L1IndependentLower
import DifferentialGeometry.External.DeGiorgi.SobolevPoincare
import DifferentialGeometry.External.DeGiorgi.UnitBallApproximationCore.Rescaling

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
set_option autoImplicit false
set_option maxHeartbeats 0

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

private def native_W1q_of_H1 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) [IsFiniteMeasure (volume.restrict U)] : DeGiorgi.MemW1pWitness (ENNReal.ofReal (4 / 3 : ℝ)) u U := by
  have hq2 : ENNReal.ofReal (4 / 3 : ℝ) ≤ (2 : ℝ≥0∞) := by norm_num
  refine
    { memLp := hu.2.1.mono_exponent hq2
      weakGrad := du
      weakGrad_component_memLp := fun j => (hu.2.2.eval_piLp j).mono_exponent hq2
      isWeakGrad := ?_ }
  intro j φ hφ hc hs
  have hbasis : EuclideanSpace.single j 1 = coordinateVector 2 j := by
    ext k
    simp [coordinateVector, EuclideanSpace.single]
  rw [hbasis]
  exact hu.1.2.2 φ hφ hc hs j

private theorem native_subcritical_unitBall_scalar
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On (disc 1) u du) :
    eLpNorm (fun x => u x - ⨍ y in disc 1, u y ∂volume) 2
        (volume.restrict (disc 1)) ≤
      (eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
        (volume.restrict (disc 1))) *
        (volume (disc 1)) ^ ((1 / (2 : ℝ)) - (1 / (4 : ℝ))) *
        DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) := by
  letI : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr
    (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := (1 : ℝ))).ne
  let hw := native_W1q_of_H1 (U := disc 1) u du hu
  have hq1 : (1 : ℝ) < (4 / 3 : ℝ) := by norm_num
  have hq2 : (4 / 3 : ℝ) < (2 : ℝ) := by norm_num
  have hs := DeGiorgi.sobolev_poincare_unitBall (d := 2) hq1 hq2 hw
  have hmeas : AEStronglyMeasurable
      (fun x => u x - ⨍ y in disc 1, u y ∂volume)
      (volume.restrict (disc 1)) := by
    exact (hu.2.1.aestronglyMeasurable.sub
      (aestronglyMeasurable_const))
  have hμ : volume.restrict (disc 1) Set.univ = volume (disc 1) := by
    simp [Measure.restrict_apply_univ]
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := volume.restrict (disc 1)) (f := fun x => u x - ⨍ y in disc 1, u y ∂volume)
      (p := (2 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (by norm_num) hmeas
  rw [hμ] at hcomp
  have hs' :
      eLpNorm (fun x => u x - ⨍ y in disc 1, u y ∂volume) (ENNReal.ofReal (4 : ℝ))
        (volume.restrict (disc 1)) ≤
      DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) *
        eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
          (volume.restrict (disc 1)) := by
    norm_num at hs ⊢
    exact hs
  calc
    eLpNorm (fun x => u x - ⨍ y in disc 1, u y ∂volume) 2
        (volume.restrict (disc 1))
        ≤ eLpNorm (fun x => u x - ⨍ y in disc 1, u y ∂volume) (ENNReal.ofReal (4 : ℝ))
          (volume.restrict (disc 1)) *
            volume (disc 1) ^ ((1 / (2 : ℝ)) - (1 / (4 : ℝ))) := by simpa using hcomp
    _ ≤ (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) *
          eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
            (volume.restrict (disc 1))) *
          volume (disc 1) ^ ((1 / (2 : ℝ)) - (1 / (4 : ℝ))) := by gcongr
    _ = (eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
        (volume.restrict (disc 1))) *
        volume (disc 1) ^ ((1 / (2 : ℝ)) - (1 / (4 : ℝ))) *
        DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) := by ring


private theorem ball_integral_rescale (a : E2) (r : ℝ) (hr : 0 < r) (f : E2 → ℝ) :
    ∫ z in disc 1, f (a + r • z) = r⁻¹ ^ 2 * ∫ x in Metric.ball a r, f x := by
  open scoped Pointwise in
  have hs := Measure.setIntegral_comp_smul_of_pos volume (fun x => f (a + x))
    (Metric.ball (0 : E2) 1) hr
  open scoped Pointwise in
  rw [show r • Metric.ball (0 : E2) 1 = Metric.ball (0 : E2) r from by
    rw [smul_unitBall hr.ne']; simp [Real.norm_of_nonneg hr.le]] at hs
  change (∫ z in Metric.ball (0 : E2) 1, f (a + r • z)) = _
  rw [hs]
  rw [show Module.finrank ℝ E2 = 2 by simp [E2]]
  simp only [inv_pow, smul_eq_mul]
  congr 1
  rw [show Metric.ball a r = (a + ·) '' Metric.ball (0 : E2) r from by simp]
  exact ((measurePreserving_add_left volume a).setIntegral_image_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding f (Metric.ball (0 : E2) r)).symm

private theorem ball_average_rescale (a : E2) (r : ℝ) (hr : 0 < r) (f : E2 → ℝ) :
    (⨍ z in disc 1, f (a + r • z)) = ⨍ x in Metric.ball a r, f x := by
  rw [setAverage_eq, setAverage_eq, ball_integral_rescale a r hr f]
  have hv : volume.real (Metric.ball a r) = r ^ 2 * Real.pi := by
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have hv1 : volume.real (disc 1) = Real.pi := by
    change volume.real (Metric.ball (0 : E2) 1) = _
    rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
    simp [Real.pi_pos.le]
  rw [hv, hv1]
  simp only [smul_eq_mul, mul_inv_rev, inv_pow]
  ring

private theorem native_subcritical_ball_scalar
    (a : E2) (r : ℝ) (hr : 0 < r) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (Metric.ball a r) u du) :
    eLpNorm (fun x => u x - ⨍ y in Metric.ball a r, u y ∂volume) 2
        (volume.restrict (Metric.ball a r)) ≤
      (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) *
        volume (disc 1) ^ (1 / (4 : ℝ))) * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) *
        eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
          (volume.restrict (Metric.ball a r)) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top (μ := volume) (x := a) (r := r)).ne
  let hw := (native_W1q_of_H1 (Metric.ball a r) u du hu).rescaleToUnitBall hr
  have hs := DeGiorgi.sobolev_poincare_unitBall (d := 2)
    (p := (4 / 3 : ℝ)) (by norm_num) (by norm_num) hw
  norm_num at hs
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict (disc 1))
    (f := fun x => u (a + r • x) - ⨍ y in disc 1, u (a + r • y))
    (p := (2 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (by norm_num)
    (hw.memLp.aestronglyMeasurable.sub aestronglyMeasurable_const)
  have hbound : eLpNorm (fun x => u (a + r • x) - ⨍ y in disc 1, u (a + r • y))
      2 (volume.restrict (disc 1)) ≤
      (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) * volume (disc 1) ^ (1 / (4 : ℝ))) *
        eLpNorm (fun x => ‖r • du (a + r • x)‖) (ENNReal.ofReal (4 / 3 : ℝ))
          (volume.restrict (disc 1)) := by
    calc
      _ ≤ eLpNorm (fun x => u (a + r • x) - ⨍ y in disc 1, u (a + r • y))
          4 (volume.restrict (disc 1)) * volume (disc 1) ^ (1 / (4 : ℝ)) := by
            norm_num at hcomp ⊢; exact hcomp
      _ ≤ (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) *
          eLpNorm (fun x => ‖r • du (a + r • x)‖) (ENNReal.ofReal (4 / 3 : ℝ))
          (volume.restrict (disc 1))) * volume (disc 1) ^ (1 / (4 : ℝ)) := by
            exact mul_le_mul_left hs _
      _ = _ := by ring
  rw [ball_average_rescale a r hr u] at hbound
  have hleft := DeGiorgi.eLpNorm_rescale_to_unitBall (d := 2) (x₀ := a) hr
    (f := fun x => u x - ⨍ y in Metric.ball a r, u y)
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
  have hright := DeGiorgi.eLpNorm_rescale_to_unitBall (d := 2) (x₀ := a) hr
    (f := fun x => ‖du x‖) (p := ENNReal.ofReal (4 / 3 : ℝ)) (by norm_num) (by norm_num)
  have hgrad : eLpNorm (fun x => ‖r • du (a + r • x)‖) (ENNReal.ofReal (4 / 3 : ℝ))
      (volume.restrict (disc 1)) =
      ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ (3 / (2 : ℝ))) *
      eLpNorm (fun x => ‖du x‖) (ENNReal.ofReal (4 / 3 : ℝ))
        (volume.restrict (Metric.ball a r)) := by
    simp_rw [norm_smul, Real.norm_of_nonneg hr.le]
    rw [show (fun x => r * ‖du (a + r • x)‖) = r • (fun x => ‖du (a + r • x)‖) from rfl,
      eLpNorm_const_smul]
    change ‖r‖ₑ * eLpNorm (fun x => ‖du (a + r • x)‖) _
      (volume.restrict (Metric.ball (0 : E2) 1)) = _
    rw [hright]
    norm_num [Real.enorm_of_nonneg hr.le, mul_assoc]
  norm_num at hleft
  rw [hgrad] at hbound
  change eLpNorm _ _ (volume.restrict (Metric.ball (0 : E2) 1)) ≤ _ at hbound
  rw [hleft] at hbound
  have hscale : ENNReal.ofReal r * ENNReal.ofReal (r⁻¹ ^ (3 / (2 : ℝ))) =
      ENNReal.ofReal r⁻¹ * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) := by
    rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)]
    congr 1
    rw [Real.inv_rpow hr.le]
    have hsum : r ^ (3 / (2 : ℝ)) = r * r ^ (1 / (2 : ℝ)) := by
      rw [show (3 / (2 : ℝ)) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hr, Real.rpow_one]
    rw [hsum]
    have hsq : (r ^ (1 / (2 : ℝ))) ^ 2 = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    have hpos : 0 < r ^ (1 / (2 : ℝ)) := Real.rpow_pos_of_pos hr _
    field_simp
    nlinarith
  rw [hscale] at hbound
  apply (ENNReal.mul_le_mul_iff_left
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hr)).ne' ENNReal.ofReal_ne_top).mp
  convert hbound using 1 <;> ring


private theorem native_subcritical_constant_finite :
    DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) * volume (disc 1) ^ (1 / (4 : ℝ)) ≠ ⊤ := by
  apply ENNReal.mul_ne_top
  · change ENNReal.ofReal _ * (1 + DeGiorgi.CUnitBallExtensionGrad 2 (4 / 3 : ℝ) *
      (ENNReal.ofReal (DeGiorgi.CPoincVal 2) + 1)) ≠ ⊤
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.add_ne_top.mpr
    refine ⟨by norm_num, ENNReal.mul_ne_top ?_ (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, by norm_num⟩)⟩
    change ENNReal.ofReal ((2 : ℝ) ^ (2 * 2)) * (2 : ℝ≥0∞) ^ ((4 / 3 : ℝ) - 1) ≠ ⊤
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num)).ne
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := (1 : ℝ))).ne).ne

private theorem planar_norm_le_sum_abs (v : E2) : ‖v‖ ≤ |v 0| + |v 1| := by
  have hsq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq v
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), norm_nonneg v,
    sq_abs (v 0), sq_abs (v 1), mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1))]

private theorem native_jet_norm_le_density (d : Fin 2 → E2 → E2) (i : Fin 2) (x : E2) :
    ‖d i x‖ ≤ Real.sqrt (L1Independent.euclideanJetDensity d x) := by
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg ‖d j x‖))).mpr
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖d j x‖) (Finset.mem_univ i)

private theorem native_subcritical_ball_vector
    (a : E2) (r : ℝ) (hr : 0 < r) (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hu : ∀ i, H1On (Metric.ball a r) (fun x => u x i) (d i)) :
    eLpNorm (fun x => u x - ⨍ y in Metric.ball a r, u y ∂volume) 2
        (volume.restrict (Metric.ball a r)) ≤
      (2 * (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) *
        volume (disc 1) ^ (1 / (4 : ℝ)))) * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) *
        eLpNorm (fun x => Real.sqrt (L1Independent.euclideanJetDensity d x))
          (ENNReal.ofReal (4 / 3 : ℝ)) (volume.restrict (Metric.ball a r)) := by
  let μ := volume.restrict (Metric.ball a r)
  let c : E2 := ⨍ y in Metric.ball a r, u y ∂volume
  let K := DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) * volume (disc 1) ^ (1 / (4 : ℝ))
  let g : E2 → ℝ := fun x => Real.sqrt (L1Independent.euclideanJetDensity d x)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top (μ := volume) (x := a) (r := r)).ne
  have hui : ∀ i, Integrable (fun x => u x i) μ := fun i => (hu i).2.1.integrable (by norm_num)
  have humeas : AEStronglyMeasurable u μ := (MemLp.of_eval_piLp (fun i => (hu i).2.1)).aestronglyMeasurable
  have hc (i : Fin 2) : c i = ⨍ y in Metric.ball a r, u y i ∂volume := by
    dsimp only [c]
    simp only [setAverage_eq, PiLp.smul_apply, smul_eq_mul]
    rw [eval_integral_piLp hui]
  have hcoord (i : Fin 2) : eLpNorm (fun x => u x i - c i) 2 μ ≤
      K * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) *
        eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
    rw [hc]
    refine (native_subcritical_ball_scalar a r hr (fun x => u x i) (d i) (hu i)).trans ?_
    apply mul_le_mul_right
    apply eLpNorm_mono_ae (hu i).2.2.aestronglyMeasurable.norm
    exact Eventually.of_forall (fun x => by
      change ‖‖d i x‖‖ ≤ ‖Real.sqrt (L1Independent.euclideanJetDensity d x)‖
      rw [norm_norm, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact native_jet_norm_le_density d i x)
  have hn : eLpNorm (fun x => u x - c) 2 μ ≤
      eLpNorm (fun x => |u x 0 - c 0| + |u x 1 - c 1|) 2 μ := by
    apply eLpNorm_mono_ae (humeas.sub aestronglyMeasurable_const)
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
      exact planar_norm_le_sum_abs (u x - c))
  have hsum : eLpNorm (fun x => |u x 0 - c 0| + |u x 1 - c 1|) 2 μ ≤
      eLpNorm (fun x => u x 0 - c 0) 2 μ + eLpNorm (fun x => u x 1 - c 1) 2 μ := by
    have hh := eLpNorm_add_le (μ := μ) (p := (2 : ℝ≥0∞))
      (f := fun x => |u x 0 - c 0|) (g := fun x => |u x 1 - c 1|) (by norm_num)
    change eLpNorm (fun x => ‖u x 0 - c 0‖ + ‖u x 1 - c 1‖) 2 μ ≤
      eLpNorm (fun x => ‖u x 0 - c 0‖) 2 μ + eLpNorm (fun x => ‖u x 1 - c 1‖) 2 μ at hh
    rw [eLpNorm_norm (μ := μ) (p := (2 : ℝ≥0∞)) (fun x => u x 0 - c 0) ((hu 0).2.1.aestronglyMeasurable.sub aestronglyMeasurable_const),
      eLpNorm_norm (μ := μ) (p := (2 : ℝ≥0∞)) (fun x => u x 1 - c 1) ((hu 1).2.1.aestronglyMeasurable.sub aestronglyMeasurable_const)] at hh
    exact hh
  calc
    _ ≤ eLpNorm (fun x => u x 0 - c 0) 2 μ + eLpNorm (fun x => u x 1 - c 1) 2 μ := hn.trans hsum
    _ ≤ K * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) * eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ +
        K * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) * eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ :=
      add_le_add (hcoord 0) (hcoord 1)
    _ = _ := by dsimp only [K, g, μ]; ring


private theorem native_integral_norm_rpow {F : Type*} [NormedAddCommGroup F]
    {μ : Measure E2} (f : E2 → F) (hf : AEStronglyMeasurable f μ)
    (p : ℝ) (hp : 0 < p) :
    (∫ x, ‖f x‖ ^ p ∂μ) = (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    ((hf.norm.aemeasurable.pow_const p).aestronglyMeasurable)]
  simp_rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [DeGiorgi.lintegral_rpow_norm_eq_eLpNorm_pow hp hf, ENNReal.toReal_rpow]

private theorem native_jet_density_sqrt_memLp (a : E2) (r : ℝ)
    (d : Fin 2 → E2 → E2)
    (hd : ∀ i, MemLp (d i) 2 (volume.restrict (Metric.ball a r))) :
    MemLp (fun x => Real.sqrt (L1Independent.euclideanJetDensity d x)) 2
      (volume.restrict (Metric.ball a r)) := by
  have he : Integrable (L1Independent.euclideanJetDensity d) (volume.restrict (Metric.ball a r)) :=
    integrable_finsetSum _ (fun i _ => (hd i).norm.integrable_sq)
  have hm := (he.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  convert he using 1
  ext x
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖d i x‖))

private theorem native_subcritical_ball_integral :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : E2) (r : ℝ), 0 < r →
      ∀ (u : E2 → E2) (d : Fin 2 → E2 → E2),
      (∀ i, H1On (Metric.ball a r) (fun x => u x i) (d i)) →
      (∫ x in Metric.ball a r, ‖u x - ⨍ y in Metric.ball a r, u y ∂volume‖ ^ 2) ≤
        C * r * (∫ x in Metric.ball a r,
          (Real.sqrt (L1Independent.euclideanJetDensity d x)) ^ (4 / (3 : ℝ))) ^ (3 / (2 : ℝ)) := by
  let K : ℝ≥0∞ := 2 * (DeGiorgi.CSobolevPoincare 2 (4 / 3 : ℝ) * volume (disc 1) ^ (1 / (4 : ℝ)))
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) native_subcritical_constant_finite
  refine ⟨K.toReal ^ 2 + 1, by positivity, ?_⟩
  intro a r hr u d hu
  let μ := volume.restrict (Metric.ball a r)
  let c : E2 := ⨍ y in Metric.ball a r, u y ∂volume
  let g : E2 → ℝ := fun x => Real.sqrt (L1Independent.euclideanJetDensity d x)
  letI : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (measure_ball_lt_top (μ := volume) (x := a) (r := r)).ne
  have hg2 : MemLp g 2 μ := native_jet_density_sqrt_memLp a r d (fun i => (hu i).2.2)
  have hgq : MemLp g (ENNReal.ofReal (4 / 3 : ℝ)) μ := hg2.mono_exponent (by norm_num)
  have hosc : MemLp (fun x => u x - c) 2 μ :=
    (MemLp.of_eval_piLp (fun i => (hu i).2.1)).sub (memLp_const c)
  have hbd := native_subcritical_ball_vector a r hr u d hu
  have hfin : K * ENNReal.ofReal (r ^ (1 / (2 : ℝ))) *
      eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) hgq.eLpNorm_lt_top.ne
  have hreal := ENNReal.toReal_mono hfin hbd
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hr.le _)] at hreal
  have hpow := sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hr.le _)) ENNReal.toReal_nonneg) |>.mpr hreal
  have hosceq : (∫ x, ‖u x - c‖ ^ 2 ∂μ) = (eLpNorm (fun x => u x - c) 2 μ).toReal ^ 2 := by
    simpa using native_integral_norm_rpow (fun x => u x - c) hosc.aestronglyMeasurable 2 (by norm_num)
  have hgqeq : (∫ x, g x ^ (4 / (3 : ℝ)) ∂μ) =
      (eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ).toReal ^ (4 / (3 : ℝ)) := by
    simpa only [g, Real.norm_of_nonneg (Real.sqrt_nonneg _)] using
      native_integral_norm_rpow g hgq.aestronglyMeasurable (4 / (3 : ℝ)) (by norm_num)
  have hrad : (r ^ (1 / (2 : ℝ))) ^ 2 = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
  have hgrad : ((eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ).toReal ^ (4 / (3 : ℝ))) ^
      (3 / (2 : ℝ)) = (eLpNorm g (ENNReal.ofReal (4 / 3 : ℝ)) μ).toReal ^ 2 := by
    rw [← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  change (∫ x, ‖u x - c‖ ^ 2 ∂μ) ≤
    (K.toReal ^ 2 + 1) * r * (∫ x, g x ^ (4 / (3 : ℝ)) ∂μ) ^ (3 / (2 : ℝ))
  rw [hosceq, hgqeq, hgrad]
  simp only [mul_pow, hrad] at hpow
  exact hpow.trans (by gcongr; linarith)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
