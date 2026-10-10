import NativeScalarCone

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

 theorem scalarCone_green (x : E2) (q k : ℝ) (hq : 0 < q) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g)
    (hga : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi)
    (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi) (j : Fin 2) :
    IntegrableOn (fun z => scalarCone x q k g z * fderiv ℝ psi z (coordinateVector 2 j) +
      scalarConeGrad x q g z j * psi z) (Metric.ball x q) ∧
    IntegrableOn (fun t => (k + g t) * psi (x + q • unitCircleParameter t) *
      unitCircleParameter t j) (Icc (-Real.pi) Real.pi) ∧
    (∫ z in Metric.ball x q,
      scalarCone x q k g z * fderiv ℝ psi z (coordinateVector 2 j) +
        scalarConeGrad x q g z j * psi z) =
      q * ∫ t in Icc (-Real.pi) Real.pi,
        (k + g t) * psi (x + q • unitCircleParameter t) * unitCircleParameter t j := by
  let H : ℝ → ℝ → ℝ := fun t r =>
    r * ((k + r / q * g t) * fderiv ℝ psi (x + r • unitCircleParameter t) (coordinateVector 2 j) +
      (1 / q) * (g t * unitCircleParameter t j + deriv g t * rotateQuarter (unitCircleParameter t) j) *
        psi (x + r • unitCircleParameter t))
  have hc := circle_contDiff.continuous
  have hv := continuous_rotateQuarter.comp hc
  have hD : Continuous (fderiv ℝ psi) := hs.continuous_fderiv (by simp)
  have hp : Continuous (fun tr : ℝ × ℝ => x + tr.2 • unitCircleParameter tr.1) :=
    continuous_const.add (continuous_snd.smul (hc.comp continuous_fst))
  have hcj : Continuous (fun tr : ℝ × ℝ => unitCircleParameter tr.1 j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (hc.comp continuous_fst)
  have hvj : Continuous (fun tr : ℝ × ℝ => rotateQuarter (unitCircleParameter tr.1) j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp (hv.comp continuous_fst)
  have hcont : Continuous (fun tr : ℝ × ℝ =>
      tr.2 * (k + tr.2 / q * g tr.1) *
        fderiv ℝ psi (x + tr.2 • unitCircleParameter tr.1) (coordinateVector 2 j) +
      tr.2 / q * g tr.1 * unitCircleParameter tr.1 j *
        psi (x + tr.2 • unitCircleParameter tr.1)) := by fun_prop
  have hw : Continuous (fun tr : ℝ × ℝ =>
      tr.2 / q * rotateQuarter (unitCircleParameter tr.1) j *
        psi (x + tr.2 • unitCircleParameter tr.1)) :=
    ((continuous_snd.div_const q).mul hvj).mul (hs.continuous.comp hp)
  have hgp : IntegrableOn (deriv g) (Icc (-Real.pi) Real.pi) :=
    hga.intervalIntegrable_deriv.1.congr_set_ae Ioc_ae_eq_Icc.symm
  have hi := integral_mul_continuousOn_rectangle (-Real.pi) Real.pi 0 q (deriv g) hgp _ hw.continuousOn
  have hHi : IntegrableOn (uncurry H) (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) q) := by
    convert (hcont.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).add hi using 1
    ext tr
    dsimp [H, Function.uncurry]
    ring
  have hswap : IntegrableOn (fun rt : ℝ × ℝ => H rt.2 rt.1)
      (Icc (0 : ℝ) q ×ˢ Icc (-Real.pi) Real.pi) := by
    exact hHi.swap
  have hpolar := polar_integral_ball x q hq
    (fun z => scalarCone x q k g z * fderiv ℝ psi z (coordinateVector 2 j) +
      scalarConeGrad x q g z j * psi z) H hswap (by
      intro r hr t ht
      obtain ⟨hf, hd⟩ := scalarCone_polar x q k g hg r t hr.1
      rw [hf, hd]
      dsimp [H]
      simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, one_div])
  refine ⟨hpolar.1, ?_, hpolar.2.trans ?_⟩
  · apply Continuous.integrableOn_Icc
    fun_prop
  · have hperiod : g (-Real.pi) = g Real.pi := by
      have he := hg (-Real.pi)
      rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at he
      exact he.symm
    exact scalar_polar_parameter_green x q hq k g hgc hga hperiod psi hs j

 theorem scalarCone_H1 (x : E2) (q k : ℝ) (hq : 0 < q) (g : ℝ → ℝ)
    (hg : Periodic g (2 * Real.pi)) (hgc : Continuous g)
    (hga : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi)
    (hgp : MemLp (deriv g) 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    H1On (Metric.ball x q) (scalarCone x q k g) (scalarConeGrad x q g) := by
  letI : IsFiniteMeasure (volume.restrict (Metric.ball x q)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hf := scalarCone_memLp x q k hq g hg hgc
  have hd := (scalarConeGrad_energy x q hq g hg hgc hgp).1
  refine ⟨⟨IntegrableOn.locallyIntegrableOn (hf.integrable (by norm_num)),
    IntegrableOn.locallyIntegrableOn (hd.integrable (by norm_num)), ?_⟩, hf, hd⟩
  intro psi hs hsc hss j
  have hgreen := (scalarCone_green x q k hq g hg hgc hga psi hs j).2.2
  have hzero (t : ℝ) : psi (x + q • unitCircleParameter t) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hball := hss ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hq, circle_norm, mul_one] at hball
    exact (lt_irrefl q) hball
  simp_rw [hzero, mul_zero] at hgreen
  simp only [zero_mul, integral_zero, mul_zero] at hgreen
  have htest : MemLp (fun z => fderiv ℝ psi z (coordinateVector 2 j)) 2
      (volume.restrict (Metric.ball x q)) :=
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      (hsc.fderiv_apply ℝ _)).restrict _
  have hpsi : MemLp psi 2 (volume.restrict (Metric.ball x q)) :=
    (hs.continuous.memLp_of_hasCompactSupport hsc).restrict _
  have hl := hf.integrable_mul htest
  have hr := (hd.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)).integrable_mul hpsi
  have he := integral_add hl hr
  simp only [Pi.mul_apply, EuclideanSpace.coe_proj] at he
  rw [he] at hgreen
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
