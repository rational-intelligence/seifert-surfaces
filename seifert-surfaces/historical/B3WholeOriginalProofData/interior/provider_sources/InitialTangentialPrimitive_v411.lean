import InitialBoundaryReplacementData_v411
import InitialCapTraceRadius_v411
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

private theorem original_circle_tangential_L2_v411
    (d : Fin 2 → E2 → E2) (x : E2) (q : ℝ)
    (rows : ∀ i, MemLp (fun t => d i (x + q • unitCircleParameter t)) 2
      (volume.restrict (Ioo (-Real.pi) Real.pi))) :
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let a : ℝ → E2 := fun t =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun i => q * inner ℝ (d i (x + q • unitCircleParameter t))
          (J (unitCircleParameter t)))
    MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi)) ∧
      (∀ t, ‖a t‖ ^ 2 ≤ q ^ 2 * euclideanJetDensity d (x + q • unitCircleParameter t)) ∧
      (∫ t in Ioo (-Real.pi) Real.pi, ‖a t‖ ^ 2) ≤
        q ^ 2 * ∫ t in Ioo (-Real.pi) Real.pi,
          euclideanJetDensity d (x + q • unitCircleParameter t) := by
  classical
  dsimp only
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let μ : Measure ℝ := volume.restrict angles
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let v : ℝ → E2 := fun t => J (unitCircleParameter t)
  let g : Fin 2 → ℝ → ℝ := fun i t =>
    inner ℝ (d i (x + q • unitCircleParameter t)) (v t)
  let a : ℝ → E2 := fun t =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => q * g i t)
  have hv : Continuous v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    exact continuous_pi fun i : Fin 2 => by fin_cases i <;> simp [v, J, unitCircleParameter] <;> fun_prop
  have hvnorm (t : ℝ) : ‖v t‖ = 1 := by
    have hsq : ‖v t‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      change (-Real.sin t) ^ 2 + Real.cos t ^ 2 = 1
      nlinarith [Real.sin_sq_add_cos_sq t]
    nlinarith [norm_nonneg (v t)]
  have hg (i : Fin 2) : MemLp (g i) 2 μ := by
    refine (rows i).of_le ((rows i).aestronglyMeasurable.inner hv.aestronglyMeasurable) ?_
    filter_upwards [] with t
    simpa [g, hvnorm] using norm_inner_le_norm (𝕜 := ℝ)
      (d i (x + q • unitCircleParameter t)) (v t)
  let L (i : Fin 2) : ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 i)
  have ha : MemLp a 2 μ := by
    have h0 := ((hg 0).const_mul q).continuousLinearMap_comp (L 0)
    have h1 := ((hg 1).const_mul q).continuousLinearMap_comp (L 1)
    have he : (fun t => L 0 (q * g 0 t) + L 1 (q * g 1 t)) = a := by
      funext t
      ext i
      fin_cases i <;> simp [L, coordinateVector, EuclideanSpace.single, a]
    exact he ▸ h0.add h1
  have hg_sq (i : Fin 2) (t : ℝ) : (g i t) ^ 2 ≤ ‖d i (x + q • unitCircleParameter t)‖ ^ 2 := by
    have hi := norm_inner_le_norm (𝕜 := ℝ) (d i (x + q • unitCircleParameter t)) (v t)
    rw [hvnorm, mul_one, Real.norm_eq_abs] at hi
    have hs := pow_le_pow_left₀ (abs_nonneg (g i t)) hi 2
    simpa [g, sq_abs] using hs
  have hapoint (t : ℝ) : ‖a t‖ ^ 2 ≤ q ^ 2 * euclideanJetDensity d (x + q • unitCircleParameter t) := by
    rw [EuclideanSpace.real_norm_sq_eq, euclideanJetDensity, Fin.sum_univ_two, Fin.sum_univ_two]
    change (q * g 0 t) ^ 2 + (q * g 1 t) ^ 2 ≤ _
    nlinarith [mul_le_mul_of_nonneg_left (hg_sq 0 t) (sq_nonneg q),
      mul_le_mul_of_nonneg_left (hg_sq 1 t) (sq_nonneg q)]
  have henergy : IntegrableOn (fun t => euclideanJetDensity d (x + q • unitCircleParameter t)) angles := by
    change IntegrableOn (fun t => ∑ i, ‖d i (x + q • unitCircleParameter t)‖ ^ 2) angles
    exact integrable_finsetSum _ fun i _ => (rows i).norm.integrable_sq
  refine ⟨ha, hapoint, ?_⟩
  have hb := integral_mono_ae ha.norm.integrable_sq (henergy.const_mul (q ^ 2))
    (Eventually.of_forall hapoint)
  change (∫ t in angles, ‖a t‖ ^ 2) ≤ q ^ 2 *
    ∫ t in angles, euclideanJetDensity d (x + q • unitCircleParameter t)
  simpa only [integral_const_mul] using hb

private theorem circle_tangent_primitive_v411
    (a : ℝ → E2) (b0 b1 : E2)
    (hL2 : MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (hends : (∫ t in Ioo (-Real.pi) Real.pi, a t) = b1 - b0) :
    let c : ℝ → E2 := fun t => b0 + ∫ u in (-Real.pi)..t, a u
    ContinuousOn c (Icc (-Real.pi) Real.pi) ∧
      c (-Real.pi) = b0 ∧ c Real.pi = b1 ∧
      (∀ᵐ t ∂volume.restrict (Ioo (-Real.pi) Real.pi), HasDerivAt c (a t) t) ∧
      MemLp (deriv c) 2 (volume.restrict (Ioo (-Real.pi) Real.pi)) ∧
      (∫ t in Ioo (-Real.pi) Real.pi, ‖deriv c t‖ ^ 2) =
        ∫ t in Ioo (-Real.pi) Real.pi, ‖a t‖ ^ 2 := by
  classical
  dsimp only
  let c : ℝ → E2 := fun t => b0 + ∫ u in (-Real.pi)..t, a u
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let : IsFiniteMeasure (volume.restrict angles) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hint0 : IntegrableOn a (Ioo (-Real.pi) Real.pi) := hL2.integrable (by norm_num)
  have hint : IntegrableOn a (Icc (-Real.pi) Real.pi) :=
    hint0.congr_set_ae Ioo_ae_eq_Icc.symm
  have hi : IntervalIntegrable a volume (-Real.pi) Real.pi := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    exact hint.mono_set Ioc_subset_Icc_self
  have hc : ContinuousOn c (Icc (-Real.pi) Real.pi) := by
    apply continuousOn_const.add
    simpa [uIcc_of_le hab] using intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn a (uIcc (-Real.pi) Real.pi) from by rwa [uIcc_of_le hab])
  have hder : ∀ᵐ t ∂volume.restrict angles, HasDerivAt c (a t) t := by
    have hraw := hi.ae_hasDerivAt_integral
    have hraw' := hraw.filter_mono (ae_restrict_le (μ := volume) (s := angles))
    filter_upwards [hraw', ae_restrict_mem measurableSet_Ioo] with t ht htm
    have hp := ht (by rw [uIcc_of_le hab]; exact ⟨htm.1.le, htm.2.le⟩) (-Real.pi)
      (by rw [uIcc_of_le hab]; exact ⟨le_rfl, hab⟩)
    exact hp.const_add b0
  have hdeq : deriv c =ᵐ[volume.restrict angles] a := hder.mono fun t ht => ht.deriv
  refine ⟨hc, by simp [c], ?_, hder, hL2.ae_eq hdeq.symm, ?_⟩
  · rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, hends]
    abel
  · change (∫ t in angles, ‖deriv c t‖ ^ 2) = ∫ t in angles, ‖a t‖ ^ 2
    exact integral_congr_ae (hdeq.mono fun t ht => congrArg (fun v : E2 => ‖v‖ ^ 2) ht)

/- The path is the literal integral of the original tangential rows. This
unconditional producer retains the original f slice and fixes both endpoint
values with the actual original Green trace. Its identification with f on the
artificial circle remains the separate local Sobolev trace obligation. -/
private theorem original_cap_tangential_path_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let f0 : E2 → E2 := (disc 1).indicator f
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let shell : ℝ :=
      (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
        (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
    ∃ q ∈ Ioo (r / 2) r,
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      let a : ℝ → E2 := fun t =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun i => q * inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t)))
      let c : ℝ → E2 := fun t =>
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2)) +
          ∫ u in (-Real.pi)..t, a u
      ContinuousOn c (Icc (-Real.pi) Real.pi) ∧
        c (-Real.pi) = liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2)) ∧
        c Real.pi = liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) ∧
        (∀ᵐ t ∂volume.restrict angles, HasDerivAt c (a t) t) ∧
        MemLp (deriv c) 2 (volume.restrict angles) ∧
        (∫ t in angles, ‖deriv c t‖ ^ 2) ≤ 2 * shell := by
  classical
  dsimp only
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let f0 : E2 → E2 := (disc 1).indicator f
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  have hselected : ∃ q ∈ Ioo (r / 2) r,
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      (∀ i, (liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
          liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
        q * ∫ t in angles,
          inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t))) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
          (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialCapTraceRadius_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_trace_radius_v411") |
          throwError "checked original f/d/Green radius producer missing"
      let args ← ([`R, `Ω, `M, `f, `d, `minimum, `theta, `sigma, `lift, `trace,
        `s, `r, `hr, `hrhalf].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      Lean.Elab.Tactic.closeMainGoal `actual_tangential_radius (Lean.mkAppN (Lean.mkConst name) args)
  obtain ⟨q, hq, hqf, hqd, hqflux, hqenergy⟩ := hselected
  let a : ℝ → E2 := fun t =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => q * inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
        (J (unitCircleParameter t)))
  let b0 := liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))
  let b1 := liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2))
  let c : ℝ → E2 := fun t => b0 + ∫ u in (-Real.pi)..t, a u
  have htangent := original_circle_tangential_L2_v411 d0 (unitCircleParameter s) q hqd
  dsimp only at htangent
  change MemLp a 2 (volume.restrict angles) ∧
    (∀ t, ‖a t‖ ^ 2 ≤ q ^ 2 * euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ∧
    (∫ t in angles, ‖a t‖ ^ 2) ≤ q ^ 2 * ∫ t in angles,
      euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t) at htangent
  let : IsFiniteMeasure (volume.restrict angles) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have haI : IntegrableOn a angles := htangent.1.integrable (by norm_num)
  have hends : (∫ t in angles, a t) = b1 - b0 := by
    ext i
    have heval := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm haI
    change (∫ t in angles, a t i) = (∫ t in angles, a t) i at heval
    rw [← heval]
    change (∫ t in angles, q * inner ℝ
      (d0 i (unitCircleParameter s + q • unitCircleParameter t)) (J (unitCircleParameter t))) = _
    rw [integral_const_mul]
    exact (hqflux i).symm
  have hprimitive := circle_tangent_primitive_v411 a b0 b1 htangent.1 hends
  dsimp only at hprimitive
  change ContinuousOn c (Icc (-Real.pi) Real.pi) ∧
    c (-Real.pi) = b0 ∧ c Real.pi = b1 ∧
    (∀ᵐ t ∂volume.restrict angles, HasDerivAt c (a t) t) ∧
    MemLp (deriv c) 2 (volume.restrict angles) ∧
    (∫ t in angles, ‖deriv c t‖ ^ 2) = ∫ t in angles, ‖a t‖ ^ 2 at hprimitive
  refine ⟨q, hq, hqf, hqd, hprimitive.1, hprimitive.2.1,
    hprimitive.2.2.1, hprimitive.2.2.2.1, hprimitive.2.2.2.2.1, ?_⟩
  exact hprimitive.2.2.2.2.2.trans_le (htangent.2.2.trans hqenergy)

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
