import VM02aDirectMethod
import CourantGreenChordFlux
set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
open SeifertSurfaces.AppendixACoordinates

theorem actual_green_weighted_squared_chord_energy
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (hrows : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)))
    (hgreen : HasGreenBoundaryTrace f d b)
    (hb : Continuous b) (hperiod : Function.Periodic b (2 * Real.pi))
    (s a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1)
    (henergy : IntegrableOn (fun x => ‖d 0 x‖ ^ 2 + ‖d 1 x‖ ^ 2) (disc 1)) :
    let c : ℝ → E2 := unitCircleParameter
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    let g : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
    let Q : E2 → ℝ := fun x => ‖d 0 x‖ ^ 2 + ‖d 1 x‖ ^ 2
    let Ann : Set E2 := {x | x ∈ disc 1 ∧ a < ‖x - c s‖ ∧ ‖x - c s‖ < z}
    IntegrableOn (fun r => ‖g r‖ ^ 2 / r) (Ioo a z) ∧
      (∫ r in Ioo a z, ‖g r‖ ^ 2 / r) ≤
        (2 * Real.pi) * ∫ x in Ann, Q x := by
  classical
  dsimp only
  let c : ℝ → E2 := unitCircleParameter
  let J : E2 → E2 := fun v => (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
  let g : ℝ → E2 := fun r => b (s - alpha r) - b (s + alpha r)
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let T : Set ℝ := Ioo (-Real.pi) Real.pi
  let U : Set ℝ := Ioo a z
  let angular : Fin 2 → ℝ → ℝ → E2 := fun i r t => d0 i (c s + r • c t)
  let pair : Fin 2 → ℝ → ℝ → ℝ := fun i r t => inner ℝ (angular i r t) (J (c t))
  let energy : ℝ → ℝ := fun r => ∫ t in T, ‖angular 0 r t‖ ^ 2 + ‖angular 1 r t‖ ^ 2
  let Ann : Set E2 := {x | x ∈ disc 1 ∧ a < ‖x - c s‖ ∧ ‖x - c s‖ < z}
  change IntegrableOn (fun r => ‖g r‖ ^ 2 / r) U ∧
    (∫ r in U, ‖g r‖ ^ 2 / r) ≤ (2 * Real.pi) * ∫ x in Ann, ‖d 0 x‖ ^ 2 + ‖d 1 x‖ ^ 2
  obtain ⟨_, _, hangular, _, hweighted, _, hpolar, _, _⟩ :=
    CourantAnalyticB.native_translated_polar_rows d
      (fun i => (hrows i).aestronglyMeasurable) hrows (c s) a z ha haz hz
  have hflux := actual_green_chord_flux_ae f d b hrows hgreen hb hperiod s a z ha haz hz
  have hJn (t : ℝ) : ‖J (c t)‖ = 1 := by
    have hs : ‖J (c t)‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      change (-Real.sin t) ^ 2 + Real.cos t ^ 2 = 1
      nlinarith [Real.sin_sq_add_cos_sq t]
    nlinarith [norm_nonneg (J (c t))]
  have cg : Continuous g := by
    have ca : Continuous alpha := by dsimp only [alpha]; fun_prop
    exact (hb.comp (continuous_const.sub ca)).sub (hb.comp (continuous_const.add ca))
  have hquot : ContinuousOn (fun r => ‖g r‖ ^ 2 / r) (Icc a z) :=
    (cg.norm.pow 2).continuousOn.div continuousOn_id
      (fun r hr => ne_of_gt (lt_of_lt_of_le ha hr.1))
  have hint : IntegrableOn (fun r => ‖g r‖ ^ 2 / r) U :=
    hquot.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hm : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  let : IsFiniteMeasure (volume.restrict T) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hmass : (volume.restrict T).real univ = 2 * Real.pi := by
    rw [Measure.real, Measure.restrict_apply_univ]
    dsimp only [T]
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hbound : ∀ᵐ r ∂volume.restrict U,
      ‖g r‖ ^ 2 / r ≤ (2 * Real.pi) * (r * energy r) := by
    filter_upwards [hangular, hflux, ae_restrict_mem measurableSet_Ioo] with r har hfr hr
    have hrpos : 0 < r := lt_trans ha hr.1
    have hrow (i : Fin 2) : (∫ t in T, pair i r t) ^ 2 ≤
        (2 * Real.pi) * ∫ t in T, ‖angular i r t‖ ^ 2 := by
      let avg : ℝ := (∫ t in T, pair i r t) / (2 * Real.pi)
      have hq : IntegrableOn (pair i r) T := (har.1 i).2.2.2
      have hn : IntegrableOn (fun t => ‖angular i r t‖ ^ 2) T := (har.1 i).2.2.1
      have heach (t : ℝ) : 2 * avg * pair i r t - avg ^ 2 ≤ ‖angular i r t‖ ^ 2 := by
        have hp : |pair i r t| ≤ ‖angular i r t‖ := by
          simpa only [pair, hJn, mul_one] using abs_real_inner_le_norm (angular i r t) (J (c t))
        have hs : (pair i r t) ^ 2 ≤ ‖angular i r t‖ ^ 2 := (sq_le_sq).mpr (by simpa only [abs_norm] using hp)
        nlinarith [sq_nonneg (pair i r t - avg)]
      have hi := integral_mono ((hq.const_mul (2 * avg)).sub (integrable_const (avg ^ 2))) hn heach
      change (∫ t in T, 2 * avg * pair i r t - avg ^ 2) ≤ ∫ t in T, ‖angular i r t‖ ^ 2 at hi
      rw [integral_sub (hq.const_mul (2 * avg)) (integrable_const (avg ^ 2)),
        integral_const_mul, integral_const, hmass, smul_eq_mul] at hi
      calc
        (∫ t in T, pair i r t) ^ 2 =
            (2 * Real.pi) * (2 * avg * (∫ t in T, pair i r t) - (2 * Real.pi) * avg ^ 2) := by
          have havg : avg * (2 * Real.pi) = (∫ t in T, pair i r t) :=
            div_mul_cancel₀ _ hm.ne'
          rw [← havg]
          ring
        _ ≤ (2 * Real.pi) * ∫ t in T, ‖angular i r t‖ ^ 2 := mul_le_mul_of_nonneg_left hi hm.le
    have hsum : (∫ t in T, ‖angular 0 r t‖ ^ 2) + (∫ t in T, ‖angular 1 r t‖ ^ 2) = energy r :=
      (integral_add (har.1 0).2.2.1 (har.1 1).2.2.1).symm
    have hg : ‖g r‖ ^ 2 = r ^ 2 * ((∫ t in T, pair 0 r t) ^ 2 + (∫ t in T, pair 1 r t) ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, hfr 0, hfr 1]
      change (r * ∫ t in T, pair 0 r t) ^ 2 + (r * ∫ t in T, pair 1 r t) ^ 2 = _
      ring
    have hh := add_le_add (hrow 0) (hrow 1)
    have hs : ‖g r‖ ^ 2 ≤ r ^ 2 * ((2 * Real.pi) * energy r) := by
      rw [hg]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
      rw [← mul_add, hsum] at hh
      exact hh
    apply (div_le_iff₀ hrpos).mpr
    nlinarith [hs]
  refine ⟨hint, ?_⟩
  calc
    (∫ r in U, ‖g r‖ ^ 2 / r) ≤ ∫ r in U, (2 * Real.pi) * (r * energy r) :=
      integral_mono_ae hint (hweighted.const_mul (2 * Real.pi)) hbound
    _ = (2 * Real.pi) * ∫ x in Ann, ‖d 0 x‖ ^ 2 + ‖d 1 x‖ ^ 2 := by
      rw [integral_const_mul]
      exact congrArg (fun x : ℝ => (2 * Real.pi) * x) hpolar

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectMethod.CourantTraceFluxAssembly
