import VM02aDirectMethod
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantAnnularBoundaryA
open SeifertSurfaces.AppendixACoordinates

theorem native_green_divergence_free_pairing
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (green : HasGreenBoundaryTrace f d b)
    (chi : Fin 2 → E2 → ℝ) (smooth : ∀ j, ContDiff ℝ ∞ (chi j))
    (divergence_zero : ∀ x : E2,
      fderiv ℝ (chi 0) x (coordinateVector 2 0) +
        fderiv ℝ (chi 1) x (coordinateVector 2 1) = 0) :
    ∀ i : Fin 2,
      IntegrableOn (fun x => d i x 0 * chi 0 x + d i x 1 * chi 1 x) (disc 1) ∧
      IntegrableOn (fun t => b t i *
        (chi 0 (unitCircleParameter t) * unitCircleParameter t 0 +
          chi 1 (unitCircleParameter t) * unitCircleParameter t 1))
        (Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∫ x in disc 1, d i x 0 * chi 0 x + d i x 1 * chi 1 x) =
        ∫ t in Icc (0 : ℝ) (2 * Real.pi), b t i *
          (chi 0 (unitCircleParameter t) * unitCircleParameter t 0 +
            chi 1 (unitCircleParameter t) * unitCircleParameter t 1) := by intro i; let F : Fin 2 → E2 → ℝ := fun j x => f x i * fderiv ℝ (chi j) x (coordinateVector 2 j) + d i x j * chi j x; let G : Fin 2 → ℝ → ℝ := fun j t => b t i * chi j (unitCircleParameter t) * unitCircleParameter t j; have h0 := green (chi 0) (smooth 0) i 0; have h1 := green (chi 1) (smooth 1) i 1; have hF : F 0 + F 1 = (fun x => d i x 0 * chi 0 x + d i x 1 * chi 1 x) := by { funext x; dsimp [F]; linear_combination f x i * divergence_zero x }; have hG : G 0 + G 1 = (fun t => b t i * (chi 0 (unitCircleParameter t) * unitCircleParameter t 0 + chi 1 (unitCircleParameter t) * unitCircleParameter t 1)) := by { funext t; dsimp [G]; ring }; have hFI : IntegrableOn (F 0 + F 1) (disc 1) := h0.1.add h1.1; have hGI : IntegrableOn (G 0 + G 1) (Icc (0 : ℝ) (2 * Real.pi)) := h0.2.1.add h1.2.1; rw [← hF, ← hG]; refine ⟨hFI, hGI, ?_⟩; change (∫ x in disc 1, F 0 x + F 1 x) = ∫ t in Icc (0 : ℝ) (2 * Real.pi), G 0 t + G 1 t; rw [integral_add h0.1 h1.1, integral_add h0.2.1 h1.2.1]; exact congrArg₂ (fun x y : ℝ => x + y) h0.2.2 h1.2.2

theorem smooth_squared_radius_rotation_field
    (p : E2) (h : ℝ → ℝ) (smooth_h : ContDiff ℝ ∞ h) :
    let rho2 : E2 → ℝ := fun x => (x 0 - p 0)^2 + (x 1 - p 1)^2
    let chi : Fin 2 → E2 → ℝ := fun j x =>
      ![-(x 1 - p 1) * h (rho2 x), (x 0 - p 0) * h (rho2 x)] j
    let J : E2 → E2 := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    (∀ j, ContDiff ℝ ∞ (chi j)) ∧
    (∀ x : E2, fderiv ℝ (chi 0) x (coordinateVector 2 0) +
      fderiv ℝ (chi 1) x (coordinateVector 2 1) = 0) ∧
    (∀ x : E2, rho2 x = ‖x - p‖^2) ∧
    (∀ x : E2, (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j => chi j x) =
      h (‖x - p‖^2) • J (x - p)) ∧
    (∀ s : ℝ, p = unitCircleParameter s → ∀ t : ℝ,
      chi 0 (unitCircleParameter t) * unitCircleParameter t 0 +
        chi 1 (unitCircleParameter t) * unitCircleParameter t 1 =
      -Real.sin (t - s) * h (‖unitCircleParameter t - unitCircleParameter s‖^2)) := by dsimp only; let rho : E2 → ℝ := fun x => (x 0 - p 0)^2 + (x 1 - p 1)^2; have coord_smooth (i : Fin 2) : ContDiff ℝ ∞ (fun x : E2 => x i - p i) := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).contDiff.sub contDiff_const; have rho_smooth : ContDiff ℝ ∞ rho := ((coord_smooth 0).pow 2).add ((coord_smooth 1).pow 2); have rho_norm (x : E2) : rho x = ‖x - p‖ ^ 2 := (by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; rfl); exact ⟨(by intro j; fin_cases j <;> first | exact (coord_smooth 1).neg.mul (smooth_h.comp rho_smooth) | exact (coord_smooth 0).mul (smooth_h.comp rho_smooth)), (by intro x; have dc (i : Fin 2) : HasFDerivAt (fun y : E2 => y i - p i) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i) x := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) i).hasFDerivAt).sub_const (p i); have drho := ((dc 0).pow 2).add ((dc 1).pow 2); have dh := ((smooth_h.differentiable (by simp) (rho x)).hasDerivAt).comp_hasFDerivAt x drho; have d0 := ((dc 1).neg.mul dh).fderiv; have d1 := ((dc 0).mul dh).fderiv; change fderiv ℝ (fun y : E2 => -(y 1 - p 1) * h (rho y)) x (coordinateVector 2 0) + fderiv ℝ (fun y : E2 => (y 0 - p 0) * h (rho y)) x (coordinateVector 2 1) = 0; simp only [Pi.mul_def, Pi.neg_apply, Function.comp_def] at d0 d1; rw [d0, d1]; simp [PiLp.proj_apply, coordinateVector, EuclideanSpace.single, smul_eq_mul]; ring), rho_norm, (by intro x; rw [← rho_norm x]; ext j; fin_cases j <;> simp [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply] <;> ring), (by intro s hp t; change -(unitCircleParameter t 1 - p 1) * h (rho (unitCircleParameter t)) * unitCircleParameter t 0 + (unitCircleParameter t 0 - p 0) * h (rho (unitCircleParameter t)) * unitCircleParameter t 1 = _; rw [rho_norm, hp]; change -(Real.sin t - Real.sin s) * h (‖unitCircleParameter t - unitCircleParameter s‖ ^ 2) * Real.cos t + (Real.cos t - Real.cos s) * h (‖unitCircleParameter t - unitCircleParameter s‖ ^ 2) * Real.sin t = _; rw [Real.sin_sub]; ring)⟩

theorem circle_cap_radius_geometry (s : ℝ) :
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    ∀ r ∈ Ioo (0 : ℝ) 1,
      0 < alpha r ∧ r ≤ alpha r ∧ 2 * alpha r < (2 * Real.pi) / 3 ∧
      ‖unitCircleParameter (s - alpha r) - unitCircleParameter s‖ = r ∧
      ‖unitCircleParameter (s + alpha r) - unitCircleParameter s‖ = r := by { dsimp only; intro r hr; have hr0 : 0 < r := hr.1; have hr1 : r < 1 := hr.2; have harg : r / 2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩; have hpos : 0 < Real.arcsin (r / 2) := Real.arcsin_pos.mpr (by linarith); have hsin : Real.sin (Real.arcsin (r / 2)) = r / 2 := Real.sin_arcsin' harg; have hle : r / 2 ≤ Real.arcsin (r / 2) := by { simpa only [hsin] using Real.sin_le hpos.le }; have hlt : Real.arcsin (r / 2) < Real.pi / 6 := by { apply (Real.arcsin_lt_iff_lt_sin harg ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).mpr; rw [Real.sin_pi_div_six]; linarith }; have hcos : Real.cos (2 * Real.arcsin (r / 2)) = 1 - r ^ 2 / 2 := by { rw [Real.cos_two_mul]; have hunit := Real.sin_sq_add_cos_sq (Real.arcsin (r / 2)); rw [hsin] at hunit; nlinarith }; have hnorm (t : ℝ) : ‖unitCircleParameter t - unitCircleParameter s‖ ^ 2 = 2 - 2 * Real.cos (t - s) := by { rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]; change (Real.cos t - Real.cos s) ^ 2 + (Real.sin t - Real.sin s) ^ 2 = _; rw [Real.cos_sub]; nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq s] }; exact ⟨by linarith, by linarith, by linarith, by { have hn := hnorm (s - 2 * Real.arcsin (r / 2)); rw [sub_sub_cancel_left, Real.cos_neg, hcos] at hn; nlinarith [norm_nonneg (unitCircleParameter (s - 2 * Real.arcsin (r / 2)) - unitCircleParameter s)] }, by { have hn := hnorm (s + 2 * Real.arcsin (r / 2)); rw [add_sub_cancel_left, hcos] at hn; nlinarith [norm_nonneg (unitCircleParameter (s + 2 * Real.arcsin (r / 2)) - unitCircleParameter s)] }⟩ }

theorem actual_continuous_annular_boundary_substitution
    (b : ℝ → E2) (continuous_b : Continuous b)
    (periodic_b : Function.Periodic b (2 * Real.pi))
    (s a z : ℝ) (a_positive : 0 < a) (a_lt_z : a < z) (z_lt_one : z < 1)
    (h : ℝ → ℝ) (smooth_h : ContDiff ℝ ∞ h)
    (compact_h : HasCompactSupport h) (support_h : tsupport h ⊆ Ioo (a^2) (z^2)) :
    let p : E2 := unitCircleParameter s
    let rho2 : E2 → ℝ := fun x => (x 0 - p 0)^2 + (x 1 - p 1)^2
    let chi : Fin 2 → E2 → ℝ := fun j x =>
      ![-(x 1 - p 1) * h (rho2 x), (x 0 - p 0) * h (rho2 x)] j
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    let chord : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
    ∀ i : Fin 2,
      IntegrableOn (fun t => b t i *
        (chi 0 (unitCircleParameter t) * unitCircleParameter t 0 +
          chi 1 (unitCircleParameter t) * unitCircleParameter t 1))
        (Icc (0 : ℝ) (2 * Real.pi)) ∧
      IntegrableOn (fun r => r * h (r^2) * chord r i) (Ioo a z) ∧
      (∫ t in Icc (0 : ℝ) (2 * Real.pi), b t i *
        (chi 0 (unitCircleParameter t) * unitCircleParameter t 0 +
          chi 1 (unitCircleParameter t) * unitCircleParameter t 1)) =
        ∫ r in Ioo a z, r * h (r^2) * chord r i := by
  classical
  dsimp only
  intro i
  let B : ℝ → ℝ := fun t => b t i
  let A : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
  let F : ℝ → ℝ := fun t => B t * (-Real.sin (t - s) * h (2 - 2 * Real.cos (t - s)))
  let gm : ℝ → ℝ := fun r => r * h (r ^ 2) * B (s - A r)
  let gp : ℝ → ℝ := fun r => r * h (r ^ 2) * B (s + A r)
  have cB : Continuous B := (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_b
  have cA : Continuous A := by fun_prop
  have ch : Continuous h := smooth_h.continuous
  have cF : Continuous F := by dsimp [F]; fun_prop
  have cgm : Continuous gm := by dsimp [gm]; fun_prop
  have cgp : Continuous gp := by dsimp [gp]; fun_prop
  have hnorm (t : ℝ) : ‖unitCircleParameter t - unitCircleParameter s‖ ^ 2 =
      2 - 2 * Real.cos (t - s) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos t - Real.cos s) ^ 2 + (Real.sin t - Real.sin s) ^ 2 = _
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq s]
  have flux (t : ℝ) : b t i *
      ((fun j x => ![-(x 1 - unitCircleParameter s 1) * h ((x 0 - unitCircleParameter s 0)^2 + (x 1 - unitCircleParameter s 1)^2),
        (x 0 - unitCircleParameter s 0) * h ((x 0 - unitCircleParameter s 0)^2 + (x 1 - unitCircleParameter s 1)^2)] j)
        0 (unitCircleParameter t) * unitCircleParameter t 0 +
       (fun j x => ![-(x 1 - unitCircleParameter s 1) * h ((x 0 - unitCircleParameter s 0)^2 + (x 1 - unitCircleParameter s 1)^2),
        (x 0 - unitCircleParameter s 0) * h ((x 0 - unitCircleParameter s 0)^2 + (x 1 - unitCircleParameter s 1)^2)] j)
        1 (unitCircleParameter t) * unitCircleParameter t 1) = F t := by
    have hh := (smooth_squared_radius_rotation_field (unitCircleParameter s) h smooth_h).2.2.2.2 s rfl t
    rw [hnorm] at hh
    exact congrArg (fun x => b t i * x) hh
  have pF : Function.Periodic F (2 * Real.pi) := by
    intro t
    dsimp [F, B]
    rw [periodic_b t]
    have ht : t + 2 * Real.pi - s = (t - s) + 2 * Real.pi := by ring
    rw [ht, Real.sin_add_two_pi, Real.cos_add_two_pi]
  let q : ℝ → ℝ := fun t => 2 * Real.sin (t / 2)
  have dq (t : ℝ) : HasDerivAt q (Real.cos (t / 2)) t := by
    convert (((hasDerivAt_id t).div_const 2).sin).const_mul 2 using 1 <;> dsimp [q] <;> ring
  have cq' : Continuous (fun t : ℝ => Real.cos (t / 2)) := by fun_prop
  have invq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Real.pi) : A (q t) = t := by
    dsimp [A, q]
    rw [show 2 * Real.sin (t / 2) / 2 = Real.sin (t / 2) by ring,
      Real.arcsin_sin (by linarith [Real.pi_pos, ht.1]) (by linarith [ht.2])]
    ring
  have qsq (t : ℝ) : (q t) ^ 2 = 2 - 2 * Real.cos t := by
    have hc := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at hc
    dsimp [q]
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  have qsin (t : ℝ) : q t * Real.cos (t / 2) = Real.sin t := by
    simpa [q, show 2 * (t / 2) = t by ring] using (Real.sin_two_mul (t / 2)).symm
  have sm : (∫ t in (0 : ℝ)..Real.pi,
      B (s - t) * Real.sin t * h (2 - 2 * Real.cos t)) = ∫ r in (0 : ℝ)..2, gm r := by
    have hs := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi) (f := q) (f' := fun t => Real.cos (t / 2))
      (g := gm) (fun t _ => dq t) cq'.continuousOn cgm
    simp only [q, zero_div, Real.sin_zero, mul_zero, Real.sin_pi_div_two,
      mul_one] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Real.pi := by simpa [uIcc_of_le Real.pi_pos.le] using ht
    change _ = gm (q t) * Real.cos (t / 2)
    dsimp [gm]
    rw [invq t ht', qsq]
    rw [← qsin t]
    ring
  have sp : (∫ t in (0 : ℝ)..Real.pi,
      B (s + t) * Real.sin t * h (2 - 2 * Real.cos t)) = ∫ r in (0 : ℝ)..2, gp r := by
    have hs := intervalIntegral.integral_comp_mul_deriv
      (a := (0 : ℝ)) (b := Real.pi) (f := q) (f' := fun t => Real.cos (t / 2))
      (g := gp) (fun t _ => dq t) cq'.continuousOn cgp
    simp only [q, zero_div, Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hs
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) Real.pi := by simpa [uIcc_of_le Real.pi_pos.le] using ht
    change _ = gp (q t) * Real.cos (t / 2)
    dsimp [gp]
    rw [invq t ht', qsq]
    rw [← qsin t]
    ring
  have halfm : (∫ t in (s - Real.pi)..s, F t) = ∫ r in (0 : ℝ)..2, gm r := by
    have ht := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi) F s
    simp only [sub_zero] at ht
    rw [← ht]
    rw [← sm]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F]
    rw [sub_sub_cancel_left, Real.sin_neg, Real.cos_neg]
    ring
  have halfp : (∫ t in s..(s + Real.pi), F t) = -(∫ r in (0 : ℝ)..2, gp r) := by
    have ht := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := Real.pi) F s
    simp only [add_zero] at ht
    rw [← ht]
    rw [← sp, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [F]
    rw [add_sub_cancel_left]
    ring
  have full : (∫ t in (0 : ℝ)..(2 * Real.pi), F t) = ∫ r in (0 : ℝ)..2, gm r - gp r := by
    have hp := pF.intervalIntegral_add_eq 0 (s - Real.pi)
    rw [zero_add, show s - Real.pi + 2 * Real.pi = s + Real.pi by ring] at hp
    rw [hp, ← intervalIntegral.integral_add_adjacent_intervals
      (cF.intervalIntegrable (s - Real.pi) s) (cF.intervalIntegrable s (s + Real.pi)),
      halfm, halfp, intervalIntegral.integral_sub (cgm.intervalIntegrable 0 2) (cgp.intervalIntegrable 0 2)]
    ring
  have cz : Continuous (fun r => r * h (r^2) * (b (s - A r) - b (s + A r)) i) := by
    change Continuous (fun r => r * h (r^2) * (B (s - A r) - B (s + A r)))
    fun_prop
  refine ⟨?_, cz.integrableOn_Icc.mono_set Ioo_subset_Icc_self, ?_⟩
  · simp_rw [flux]
    exact cF.integrableOn_Icc
  · simp_rw [flux]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), full,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2), integral_Ioc_eq_integral_Ioo]
    have hz : ∫ r in Ioo a z, (gm r - gp r) = ∫ r in Ioo (0 : ℝ) 2, (gm r - gp r) := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      · intro r hr
        exact ⟨a_positive.trans hr.1, hr.2.trans (by linarith)⟩
      · intro r hr
        have hh : h (r ^ 2) = 0 := by
          by_contra hh
          have hs := support_h (subset_tsupport h (mem_support.mpr hh))
          have rr : r ∈ Ioo a z := by
            constructor <;> nlinarith [hr.1.1, hr.1.2, a_positive, a_lt_z, hs.1, hs.2]
          exact hr.2 rr
        simp [gm, gp, hh]
    rw [← hz]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r _
    change r * h (r^2) * B (s - A r) - r * h (r^2) * B (s + A r) =
      r * h (r^2) * (B (s - A r) - B (s + A r))
    ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantAnnularBoundaryA
