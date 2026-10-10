import InitialPrimitiveGreen_v411
import InitialPeriodicTangential_v411
import InitialArtificialCircleGeometry_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

/- A periodic L2 field supported on the actual interior arc has a literal
primitive on that arc, with its endpoint increment and energy measured on
the original full-period slice. The arbitrary source angle is preserved. -/
private theorem circle_supported_arc_primitive_v411
    (a : ℝ → E2) (period : Periodic a (2 * Real.pi))
    (hL2 : MemLp a 2 (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (u v : ℝ) (huv : u ≤ v) (hvp : v ≤ u + 2 * Real.pi)
    (outside : ∀ t ∈ Icc v (u + 2 * Real.pi), a t = 0)
    (b0 b1 : E2) (ends : (∫ t in Ioo (-Real.pi) Real.pi, a t) = b1 - b0) :
    let c : ℝ → E2 := fun t => b0 + ∫ x in u..t, a x
    ContinuousOn c (Icc u v) ∧ c u = b0 ∧ c v = b1 ∧
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) u v) ∧
      (∀ᵐ t ∂volume.restrict (Icc u v), HasDerivAt c (a t) t) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc u v)) ∧
      (∫ t in Icc u v, ‖deriv c t‖ ^ 2) ≤
        ∫ t in Ioo (-Real.pi) Real.pi, ‖a t‖ ^ 2 ∧
      (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
        (∫ t in Icc u v, a t i * psi t + c t i * deriv psi t) =
          b1 i * psi v - b0 i * psi u) := by
  classical
  dsimp only
  let c : ℝ → E2 := fun t => b0 + ∫ x in u..t, a x
  have hperiods :
      (∀ u v : ℝ, MemLp a 2 (volume.restrict (Icc u v))) ∧
      (∀ u : ℝ, (∫ t in Icc u (u + 2 * Real.pi), a t) =
        ∫ t in Ioo (-Real.pi) Real.pi, a t) ∧
      (∀ u : ℝ, (∫ t in Icc u (u + 2 * Real.pi), ‖a t‖ ^ 2) =
        ∫ t in Ioo (-Real.pi) Real.pi, ‖a t‖ ^ 2) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".periodic_tangent_all_intervals_v411") | throwError "periodic L2 transport receipt missing"
      let args ← ([`a, `period, `hL2].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      Lean.Elab.Tactic.closeMainGoal `periodic_arc_transport (Lean.mkAppN (Lean.mkConst name) args)
  let : IsFiniteMeasure (volume.restrict (Icc u v)) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (Icc u (u + 2 * Real.pi))) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (Icc v (u + 2 * Real.pi))) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have huvL2 := hperiods.1 u v
  have huvp : IntegrableOn a (Icc u (u + 2 * Real.pi)) :=
    (hperiods.1 u (u + 2 * Real.pi)).integrable (by norm_num)
  have hi : IntegrableOn a (Icc u v) := huvL2.integrable (by norm_num)
  have hup : u ≤ u + 2 * Real.pi := by linarith [Real.pi_pos]
  have hI : IntervalIntegrable a volume u v := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le huv]
    exact hi.mono_set Ioc_subset_Icc_self
  have hO : IntervalIntegrable a volume v (u + 2 * Real.pi) := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hvp]
    have hoI : IntegrableOn a (Icc v (u + 2 * Real.pi)) :=
      (hperiods.1 v (u + 2 * Real.pi)).integrable (by norm_num)
    exact hoI.mono_set Ioc_subset_Icc_self
  have hzero : (∫ t in v..(u + 2 * Real.pi), a t) = 0 := by
    rw [intervalIntegral.integral_of_le hvp]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    exact outside t ⟨ht.1.le, ht.2⟩
  have hends : (∫ t in u..v, a t) = b1 - b0 := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hI hO
    rw [hzero, add_zero, intervalIntegral.integral_of_le hup,
      ← integral_Icc_eq_integral_Ioc, hperiods.2.1 u, ends] at hsplit
    exact hsplit
  have hcu : c u = b0 := by simp [c]
  have hcv : c v = b1 := by dsimp only [c]; rw [hends]; abel
  have hc : ContinuousOn c (Icc u v) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le huv] using intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn a (uIcc u v) from by rwa [uIcc_of_le huv])
  have hder : ∀ᵐ t ∂volume.restrict (Icc u v), HasDerivAt c (a t) t := by
    have hraw := hI.ae_hasDerivAt_integral
    have hraw' := hraw.filter_mono (ae_restrict_le (μ := volume) (s := Icc u v))
    filter_upwards [hraw', ae_restrict_mem measurableSet_Icc] with t ht htm
    exact (ht (by rwa [uIcc_of_le huv]) u (by simp)).const_add b0
  have hdeq : deriv c =ᵐ[volume.restrict (Icc u v)] a := hder.mono fun _ ht => ht.deriv
  have hgreen :
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) u v) ∧
      (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
        (∫ t in Icc u v, a t i * psi t + c t i * deriv psi t) =
          c v i * psi v - c u i * psi u) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".L2_primitive_green_identity_v411") | throwError "primitive Green receipt missing"
      let args ← ([`a, `b0, `u, `v, `huv, `huvL2].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      Lean.Elab.Tactic.closeMainGoal `actual_arc_green (Lean.mkAppN (Lean.mkConst name) args)
  refine ⟨hc, hcu, hcv, hgreen.1, hder, huvL2.ae_eq hdeq.symm, ?_, ?_⟩
  · have heq : (∫ t in Icc u v, ‖deriv c t‖ ^ 2) = ∫ t in Icc u v, ‖a t‖ ^ 2 :=
      integral_congr_ae (hdeq.mono fun _ ht => congrArg (fun w : E2 => ‖w‖ ^ 2) ht)
    rw [heq, ← hperiods.2.2 u]
    exact setIntegral_mono_set ((hperiods.1 u (u + 2 * Real.pi)).norm.integrable_sq)
      (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans hvp⟩)
  · intro psi hpsi i
    simpa only [hcu, hcv] using hgreen.2 psi hpsi i

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
