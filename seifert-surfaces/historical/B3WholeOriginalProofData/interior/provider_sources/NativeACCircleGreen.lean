import NativePolarIntegration

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
open SeifertSurfaces.AppendixACoordinates L1Independent
set_option maxRecDepth 10000
set_option maxHeartbeats 0

 theorem integral_mul_continuousOn_rectangle (a b c d : ℝ) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Icc a b)) (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G (Icc a b ×ˢ Icc c d)) :
    IntegrableOn (fun z : ℝ × ℝ => f z.1 * G z) (Icc a b ×ˢ Icc c d) := by
  have hi := hf.comp_fst (volume.restrict (Icc c d))
  rw [Measure.prod_restrict] at hi
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hG
  apply hi.mul_bdd (hG.aestronglyMeasurable (measurableSet_Icc.prod measurableSet_Icc))
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with z hz
  exact hK z hz

 theorem circle_hasDerivAt (t : ℝ) :
    HasDerivAt unitCircleParameter
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]) t := by
  have hh : HasDerivAt (fun t : ℝ => ![Real.cos t, Real.sin t]) ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · simpa using Real.hasDerivAt_cos t
    · simpa using Real.hasDerivAt_sin t
  exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hh

 theorem scalar_polar_parameter_green (x : E2) (q : ℝ) (hq : 0 < q)
    (k : ℝ) (g : ℝ → ℝ) (hgc : Continuous g)
    (hg : AbsolutelyContinuousOnInterval g (-Real.pi) Real.pi)
    (hgper : g (-Real.pi) = g Real.pi)
    (psi : E2 → ℝ) (hs : ContDiff ℝ ∞ psi) (j : Fin 2) :
    (∫ t in Icc (-Real.pi) Real.pi, ∫ r in Icc (0 : ℝ) q,
      r * ((k + (r / q) * g t) *
        fderiv ℝ psi (x + r • unitCircleParameter t) (coordinateVector 2 j) +
        (1 / q) * (g t * unitCircleParameter t j +
          deriv g t * ((EuclideanSpace.equiv (Fin 2) ℝ).symm
            ![-unitCircleParameter t 1, unitCircleParameter t 0]) j) *
          psi (x + r • unitCircleParameter t))) =
      q * ∫ t in Icc (-Real.pi) Real.pi,
        (k + g t) * psi (x + q • unitCircleParameter t) * unitCircleParameter t j := by
  classical
  let c : ℝ → E2 := unitCircleParameter
  let v : ℝ → E2 := fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-Real.sin t, Real.cos t]
  let p : ℝ → ℝ → E2 := fun t r => x + r • c t
  let A : ℝ → ℝ → ℝ := fun t r =>
    (k + 2 * r / q * g t) * c t j * psi (p t r) +
      (r * k + r ^ 2 / q * g t) * c t j * fderiv ℝ psi (p t r) (c t)
  let B : ℝ → ℝ → ℝ := fun t r =>
    (r / q * deriv g t * v t j - (k + r / q * g t) * c t j) * psi (p t r) +
      r * (k + r / q * g t) * v t j * fderiv ℝ psi (p t r) (v t)
  have hc : ContDiff ℝ ∞ c := circle_contDiff
  have hv : ContDiff ℝ ∞ v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hcd (t : ℝ) : HasDerivAt c (v t) t := circle_hasDerivAt t
  have hvd (t : ℝ) : HasDerivAt v (-c t) t := by
    have hh : HasDerivAt (fun t : ℝ => ![-Real.sin t, Real.cos t]) ![-Real.cos t, -Real.sin t] t := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · convert (Real.hasDerivAt_sin t).neg using 1 <;> rfl
      · simpa using Real.hasDerivAt_cos t
    convert ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hh using 1
    · rfl
    · ext i
      fin_cases i <;> rfl
  have hp : ContDiff ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) :=
    contDiff_const.add (contDiff_snd.smul (hc.comp contDiff_fst))
  have hD : Continuous (fderiv ℝ psi) := hs.continuous_fderiv (by simp)
  have hcj : Continuous (fun z : ℝ × ℝ => c z.1 j) := by fun_prop
  have hvj : Continuous (fun z : ℝ × ℝ => v z.1 j) := by fun_prop
  have hpsir (t r : ℝ) : HasDerivAt (fun r => psi (p t r))
      (fderiv ℝ psi (p t r) (c t)) r := by
    have hpr : HasDerivAt (fun r : ℝ => x + r • c t) (c t) r := by
      simpa using ((hasDerivAt_id r).smul_const (c t)).const_add x
    exact (hs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r hpr
  have hpsit (t r : ℝ) : HasDerivAt (fun t => psi (p t r))
      (r * fderiv ℝ psi (p t r) (v t)) t := by
    have hh := (hs.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
      (((hcd t).const_smul r).const_add x)
    convert hh using 1
    · rfl
    · rw [map_smul]
      rfl
  have hAr (t r : ℝ) : HasDerivAt
      (fun r => (r * k + r ^ 2 / q * g t) * c t j * psi (p t r)) (A t r) r := by
    have hh := ((((hasDerivAt_id r).mul_const k).add
      ((((hasDerivAt_id r).pow 2).div_const q).mul_const (g t))).mul_const (c t j)).mul (hpsir t r)
    convert hh using 1
    · rfl
    · dsimp [A]
      ring
  have hBt (t r : ℝ) (hdg : DifferentiableAt ℝ g t) : HasDerivAt
      (fun t => (k + r / q * g t) * v t j * psi (p t r)) (B t r) t := by
    have hj : HasDerivAt (fun t => v t j) (-c t j) t :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.comp_hasDerivAt t (hvd t)
    have hh := (((hdg.hasDerivAt.const_mul (r / q)).const_add k).mul hj).mul (hpsit t r)
    convert hh using 1 <;> dsimp [B] <;> ring
  have hAc : Continuous (uncurry A) := by
    dsimp [A]
    fun_prop
  have hBi : IntegrableOn (uncurry B) (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) q) := by
    let G : ℝ × ℝ → ℝ := fun z => z.2 / q * v z.1 j * psi (p z.1 z.2)
    have hG : Continuous G := by dsimp [G]; fun_prop
    have h1 := integral_mul_continuousOn_rectangle (-Real.pi) Real.pi 0 q
      (deriv g) (hg.intervalIntegrable_deriv.1.congr_set_ae Ioc_ae_eq_Icc.symm)
      G hG.continuousOn
    have h2 : Continuous (fun z : ℝ × ℝ =>
        -(k + z.2 / q * g z.1) * c z.1 j * psi (p z.1 z.2) +
        z.2 * (k + z.2 / q * g z.1) * v z.1 j * fderiv ℝ psi (p z.1 z.2) (v z.1)) := by
      fun_prop
    convert h1.add (h2.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)) using 1
    ext z
    dsimp [B, G, Function.uncurry]
    ring
  have hAi : IntegrableOn (uncurry A) (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) q) :=
    hAc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hradial (t : ℝ) : (∫ r in Icc (0 : ℝ) q, A t r) =
      q * (k + g t) * c t j * psi (p t q) := by
    have hi : IntervalIntegrable (A t) volume 0 q :=
      (hAc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 q
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hAr t r) hi
    rw [intervalIntegral.integral_of_le hq.le, ← integral_Icc_eq_integral_Ioc] at he
    rw [he]
    simp only [zero_mul, zero_pow (by decide : 2 ≠ 0), zero_div, zero_add, sub_zero]
    field_simp
  have hangular (r : ℝ) : (∫ t in Icc (-Real.pi) Real.pi, B t r) = 0 := by
    have hsmooth : ContDiff ℝ ∞ (fun t => v t j * psi (p t r)) := by
      have hpj : ContDiff ℝ ∞ (fun t => p t r) := by
        simpa [p] using contDiff_const.add (hc.const_smul r)
      exact ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).mul (hs.comp hpj)
    have hac : AbsolutelyContinuousOnInterval
        (fun t => (k + r / q * g t) * v t j * psi (p t r)) (-Real.pi) Real.pi := by
      have hkg := (hg.const_mul (r / q)).add ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => k)).contDiffOn.absolutelyContinuousOnInterval)
      have hsm1 : ContDiff ℝ 1 (fun t => v t j * psi (p t r)) := hsmooth.of_le (by simp)
      have ht := hkg.mul hsm1.contDiffOn.absolutelyContinuousOnInterval
      convert ht using 1
      ext t
      simp only [Pi.add_apply, Pi.mul_apply]
      ring
    have he := hac.integral_deriv_eq_sub
    have hder : (∫ t in (-Real.pi)..Real.pi,
        deriv (fun t => (k + r / q * g t) * v t j * psi (p t r)) t) =
        ∫ t in (-Real.pi)..Real.pi, B t r := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hg.ae_differentiableAt] with t ht hmem
      exact (hBt t r (ht (uIoc_subset_uIcc hmem))).deriv
    rw [hder, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      ← integral_Icc_eq_integral_Ioc] at he
    have hec : c (-Real.pi) = c Real.pi := by ext i; fin_cases i <;> simp [c, unitCircleParameter]
    have hev : v (-Real.pi) = v Real.pi := by ext i; fin_cases i <;> simp [v]
    simpa [p, hec, hev, hgper] using he
  have hframe (t : ℝ) : c t j • c t + v t j • v t = coordinateVector 2 j := by
    ext i
    fin_cases j <;> fin_cases i <;> dsimp [c, v, unitCircleParameter, coordinateVector] <;> simp
    all_goals nlinarith [Real.cos_sq_add_sin_sq t]
  have hDj (t r : ℝ) : fderiv ℝ psi (p t r) (coordinateVector 2 j) =
      c t j * fderiv ℝ psi (p t r) (c t) + v t j * fderiv ℝ psi (p t r) (v t) := by
    rw [← hframe t, map_add, map_smul, map_smul]
    rfl
  have hsplit (t r : ℝ) :
      r * ((k + (r / q) * g t) * fderiv ℝ psi (p t r) (coordinateVector 2 j) +
        (1 / q) * (g t * c t j + deriv g t * v t j) * psi (p t r)) = A t r + B t r := by
    rw [hDj]
    dsimp [A, B]
    ring
  change (∫ t in Icc (-Real.pi) Real.pi, ∫ r in Icc (0 : ℝ) q,
    r * ((k + (r / q) * g t) * fderiv ℝ psi (p t r) (coordinateVector 2 j) +
      (1 / q) * (g t * c t j + deriv g t * v t j) * psi (p t r))) = _
  simp_rw [hsplit]
  change Integrable (uncurry A) ((volume.prod volume).restrict (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) q)) at hAi
  change Integrable (uncurry B) ((volume.prod volume).restrict (Icc (-Real.pi) Real.pi ×ˢ Icc (0 : ℝ) q)) at hBi
  rw [← Measure.prod_restrict] at hAi hBi
  have hAdd := integral_integral_add hAi hBi
  simp only [Function.uncurry] at hAdd
  rw [hAdd, integral_integral_swap hBi]
  simp_rw [hradial, hangular]
  simp only [integral_zero, add_zero]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.NativeBallCapExtension
