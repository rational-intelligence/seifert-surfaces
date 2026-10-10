import InitialActualBoundaryLift_v411
import InitialCapJointRadius_v411

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

/-! Complete quantitative boundary data for the actual original minimizer:
one uniform radius and cost, one selected actual cap, original weak rows,
a SAME-sign/degree lift unchanged outside that actual cap, and a smooth target
arc whose scaled energy is paid together with the circle energy by one shell.
The local H1 extension and relative-cap Green equation remain distinct work. -/
private theorem original_boundary_cap_replacement_data_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta)) :
    ∃ K rho : ℝ, 0 < K ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
        let angles : Set ℝ := Ioo (-Real.pi) Real.pi
        let shell : ℝ :=
          (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
            (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
        ∃ q ∈ Ioo (r / 2) r, ∃ theta' eta : ℝ → ℝ,
          (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
            (volume.restrict angles)) ∧
          WeakMonotoneBoundaryLift Ω theta' sigma ∧
          (∀ t ∈ Icc (s - 2 * Real.arcsin (q / 2)) (s + 2 * Real.arcsin (q / 2)),
            theta' t = eta t) ∧
          (∀ t : ℝ, unitCircleParameter t ∉ Metric.ball (unitCircleParameter s) q →
            liftedBoundaryValue Ω theta' t = liftedBoundaryValue Ω theta t) ∧
          ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ (fun t => Ω.boundary.gamma (eta t)) ∧
          q ^ 2 * (∫ t in angles,
            euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) +
            q * (∫ t in Icc (s - 2 * Real.arcsin (q / 2)) (s + 2 * Real.arcsin (q / 2)),
              ‖deriv (fun t => Ω.boundary.gamma (eta t)) t‖ ^ 2) ≤ K * shell := by
  classical
  have hboundary : ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let a : ℝ := 2 * Real.arcsin (r / 2)
        ∃ theta' eta : ℝ → ℝ,
          WeakMonotoneBoundaryLift Ω theta' sigma ∧
          (∀ t ∈ Icc (s - a) (s + a), theta' t = eta t) ∧
          (∀ t : ℝ, unitCircleParameter t ∉ Metric.ball (unitCircleParameter s) r →
            liftedBoundaryValue Ω theta' t = liftedBoundaryValue Ω theta t) ∧
          ContDiff ℝ ∞ eta ∧ ContDiff ℝ ∞ (fun t => Ω.boundary.gamma (eta t)) ∧
          r * (∫ t in Icc (s - a) (s + a),
            ‖deriv (fun t => Ω.boundary.gamma (eta t)) t‖ ^ 2) ≤
            C * dist (liftedBoundaryValue Ω theta (s - a))
              (liftedBoundaryValue Ω theta (s + a)) ^ 2 := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialActualBoundaryLift_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_actual_boundary_lift_replacement_v411") |
          throwError "checked actual boundary-lift producer missing"
      let args ← ([`R, `Ω, `theta, `sigma, `lift].toArray.mapM fun name =>
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      Lean.Elab.Tactic.closeMainGoal `actual_boundary_lift (Lean.mkAppN (Lean.mkConst name) args)
  have hjoint : ∀ s r : ℝ, 0 < r → r ≤ 1 / 2 →
      let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
      let angles : Set ℝ := Ioo (-Real.pi) Real.pi
      ∃ q ∈ Ioo (r / 2) r,
        (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
          (volume.restrict angles)) ∧
        q ^ 2 * (∫ t in angles,
          euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) +
          ‖liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
            liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))‖ ^ 2 ≤
          2 * (1 + 2 * Real.pi) *
            ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
              (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialCapJointRadius_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_joint_good_radius_v411") |
          throwError "checked actual joint-radius producer missing"
      let args ← ([`R, `Ω, `M, `f, `d, `minimum, `theta, `sigma, `lift, `trace].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      Lean.Elab.Tactic.closeMainGoal `actual_joint_radius (Lean.mkAppN (Lean.mkConst name) args)
  obtain ⟨C, rho, hC, hrho, hrhohalf, hboundary⟩ := hboundary
  let B : ℝ := 2 * (1 + 2 * Real.pi)
  let K : ℝ := (C + 1) * B
  have hK : 0 < K := by dsimp [K, B]; positivity
  refine ⟨K, rho, hK, hrho, hrhohalf, ?_⟩
  intro s r hr hrr
  dsimp only
  obtain ⟨q, hq, hslice, hbudget⟩ := hjoint s r hr (hrr.trans hrhohalf)
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqrho : q ≤ rho := hq.2.le.trans hrr
  obtain ⟨theta', eta, hnewlift, hnewarc, hoff, heta, hcurve, henergy⟩ :=
    hboundary s q hqpos hqrho
  refine ⟨q, hq, theta', eta, hslice, hnewlift, hnewarc, hoff, heta, hcurve, ?_⟩
  let e : ℝ := q ^ 2 * (∫ t in Ioo (-Real.pi) Real.pi,
    euclideanJetDensity (fun i => (disc 1).indicator (d i))
      (unitCircleParameter s + q • unitCircleParameter t))
  let c : ℝ := dist (liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)))
    (liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) ^ 2
  let aenergy : ℝ := q * (∫ t in Icc (s - 2 * Real.arcsin (q / 2))
    (s + 2 * Real.arcsin (q / 2)), ‖deriv (fun t => Ω.boundary.gamma (eta t)) t‖ ^ 2)
  let shell : ℝ :=
    (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
      (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
  have he : 0 ≤ e := by
    dsimp [e]
    apply mul_nonneg (sq_nonneg _)
    exact integral_nonneg (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hc : 0 ≤ c := sq_nonneg _
  have haenergy : aenergy ≤ C * c := henergy
  rw [← dist_eq_norm] at hbudget
  change e + c ≤ B * shell at hbudget
  change e + aenergy ≤ K * shell
  calc
    _ ≤ e + C * c := add_le_add le_rfl haenergy
    _ ≤ (C + 1) * (e + c) := by nlinarith [mul_nonneg hC.le he]
    _ ≤ (C + 1) * (B * shell) := mul_le_mul_of_nonneg_left hbudget (by linarith)
    _ = K * shell := by dsimp [K]; ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
