import InitialBoundaryAffineArc_v411
import InitialPeriodicLiftPatch_v411

noncomputable section
open Set Topology Function
open scoped ContDiff NNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates DirectMethod.CourantAnnularBoundaryA

private theorem original_source_arc_inside_actual_cap_v411
    (s r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (t : ℝ) (ht : t ∈ Ioo (s - 2 * Real.arcsin (r / 2))
      (s + 2 * Real.arcsin (r / 2))) :
    unitCircleParameter t ∈ Metric.ball (unitCircleParameter s) r := by
  let a : ℝ := 2 * Real.arcsin (r / 2)
  have hg := circle_cap_radius_geometry s
  dsimp only at hg
  have hg := hg r ⟨hr, hr1⟩
  have ha : 0 < a := hg.1
  have hapi : a ≤ Real.pi := by
    have hh : 2 * a < 2 * Real.pi / 3 := hg.2.2.1
    linarith [Real.pi_pos]
  have habs : |t - s| < a := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (t - s)) hapi habs
  rw [Real.cos_abs] at hcos
  have hnorm (u : ℝ) : ‖unitCircleParameter u - unitCircleParameter s‖ ^ 2 =
      2 - 2 * Real.cos (u - s) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    change (Real.cos u - Real.cos s) ^ 2 + (Real.sin u - Real.sin s) ^ 2 = _
    rw [Real.cos_sub]
    nlinarith [Real.sin_sq_add_cos_sq u, Real.sin_sq_add_cos_sq s]
  have hend : ‖unitCircleParameter (s + a) - unitCircleParameter s‖ = r := hg.2.2.2.2
  have hcircle := hnorm (s + a)
  rw [hend, add_sub_cancel_left] at hcircle
  have hnormlt : ‖unitCircleParameter t - unitCircleParameter s‖ < r := by
    nlinarith [hnorm t, norm_nonneg (unitCircleParameter t - unitCircleParameter s)]
  simpa only [Metric.mem_ball, dist_eq_norm] using hnormlt

/-! This is the actual original cap boundary producer.  One uniform small
radius gives a SAME-sign genuine weakly monotone lift, equal to an explicitly
smooth affine target arc on the patch and equal to the original Green trace at
every real parameter outside the ACTUAL source cap. -/
private theorem original_actual_boundary_lift_replacement_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let a : ℝ := 2 * Real.arcsin (r / 2)
        ∃ theta' eta : ℝ → ℝ,
          WeakMonotoneBoundaryLift Ω theta' sigma ∧
          (∀ t ∈ Icc (s - a) (s + a), theta' t = eta t) ∧
          (∀ t : ℝ, unitCircleParameter t ∉ Metric.ball (unitCircleParameter s) r →
            liftedBoundaryValue Ω theta' t = liftedBoundaryValue Ω theta t) ∧
          ContDiff ℝ ∞ eta ∧
          ContDiff ℝ ∞ (fun t => Ω.boundary.gamma (eta t)) ∧
          r * (∫ t in Icc (s - a) (s + a),
            ‖deriv (fun t => Ω.boundary.gamma (eta t)) t‖ ^ 2) ≤
            C * dist (liftedBoundaryValue Ω theta (s - a))
              (liftedBoundaryValue Ω theta (s + a)) ^ 2 := by
  classical
  have haffine : ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let a : ℝ := 2 * Real.arcsin (r / 2)
        ∃ eta : ℝ → ℝ,
          ContDiff ℝ ∞ eta ∧ Monotone (fun t => sigma * eta t) ∧
          eta (s - a) = theta (s - a) ∧ eta (s + a) = theta (s + a) ∧
          (∀ t ∈ Icc (s - a) (s + a),
            eta t ∈ uIcc (theta (s - a)) (theta (s + a))) ∧
          ContDiff ℝ ∞ (fun t => Ω.boundary.gamma (eta t)) ∧
          r * (∫ t in Icc (s - a) (s + a),
            ‖deriv (fun t => Ω.boundary.gamma (eta t)) t‖ ^ 2) ≤
            C * dist (liftedBoundaryValue Ω theta (s - a))
              (liftedBoundaryValue Ω theta (s + a)) ^ 2 := by
    run_tac do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialBoundaryAffineArc_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_boundary_affine_arc_v411") |
          throwError "checked original affine arc proof missing"
      let args ← ([`R, `Ω, `theta, `sigma, `lift].toArray.mapM fun name =>
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let proof := Lean.mkAppN (Lean.mkConst name) args
      Lean.Meta.checkWithKernel proof
      Lean.Elab.Tactic.closeMainGoal `original_affine_arc proof
  obtain ⟨C, rho, hC, hrho, hrhohalf, haffine⟩ := haffine
  refine ⟨C, rho, hC, hrho, hrhohalf, ?_⟩
  intro s r hr hrr
  dsimp only
  let a : ℝ := 2 * Real.arcsin (r / 2)
  have hr1 : r < 1 := (hrr.trans hrhohalf).trans_lt (by norm_num)
  have hg := circle_cap_radius_geometry s
  dsimp only at hg
  have hg := hg r ⟨hr, hr1⟩
  have ha : 0 < a := hg.1
  have haT : 2 * a < 2 * Real.pi := by
    have hh : 2 * a < 2 * Real.pi / 3 := hg.2.2.1
    linarith [Real.pi_pos]
  obtain ⟨eta, heta, hmono, hleft, hright, _, hcurve, henergy⟩ := haffine s r hr hrr
  have hetaC : Continuous eta := heta.continuous
  have hpatch : ∃ theta' : ℝ → ℝ,
      WeakMonotoneBoundaryLift Ω theta' sigma ∧
      (∀ t ∈ Icc (s - a) (s + a), theta' t = eta t) ∧
      (∀ t ∈ Icc (s + a) (s - a + 2 * Real.pi), theta' t = theta t) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialPeriodicLiftPatch_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_periodic_lift_patch_v411") |
          throwError "checked original periodic patch proof missing"
      let args ← ([`R, `Ω, `theta, `sigma, `lift, `s, `a, `ha, `haT, `eta,
        `hetaC, `hmono, `hleft, `hright].toArray.mapM fun name =>
          Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let proof ← Lean.instantiateMVars (Lean.mkAppN (Lean.mkConst name) args)
      Lean.Elab.Tactic.closeMainGoal `original_periodic_patch proof
  obtain ⟨theta', hlift', hnew, hold⟩ := hpatch
  have hperiod (psi : ℝ → ℝ) (hpsi : WeakMonotoneBoundaryLift Ω psi sigma) :
      Periodic (liftedBoundaryValue Ω psi) (2 * Real.pi) := by
    intro t
    change Ω.boundary.gamma (psi (t + 2 * Real.pi)) = Ω.boundary.gamma (psi t)
    rw [hpsi.2.2.2]
    rcases hpsi.1 with hσ | hσ
    · simpa only [hσ, one_mul] using Ω.boundary.periodic (psi t)
    · simpa only [hσ, neg_one_mul, sub_eq_add_neg] using Ω.boundary.periodic.sub_eq (psi t)
  have hcircleperiod : Periodic unitCircleParameter (2 * Real.pi) := by
    intro t
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [unitCircleParameter, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hunchanged : ∀ t : ℝ,
      unitCircleParameter t ∉ Metric.ball (unitCircleParameter s) r →
        liftedBoundaryValue Ω theta' t = liftedBoundaryValue Ω theta t := by
    intro t ht
    have hT : 0 < 2 * Real.pi := by positivity
    let n : ℤ := toIcoDiv hT (s - a) t
    let q : ℝ := t - (n : ℝ) * (2 * Real.pi)
    have hq : q ∈ Ico (s - a) (s - a + 2 * Real.pi) := by
      simpa only [q, n, zsmul_eq_mul] using sub_toIcoDiv_zsmul_mem_Ico hT (s - a) t
    have hcircle : unitCircleParameter q = unitCircleParameter t :=
      (hcircleperiod.int_mul n).sub_eq t
    have hqoff : unitCircleParameter q ∉ Metric.ball (unitCircleParameter s) r := by
      rwa [hcircle]
    have hraw : theta' q = theta q := by
      by_cases hqu : q = s - a
      · rw [hqu]
        have hh := hnew (s - a) ⟨le_rfl, by linarith⟩
        simpa only [a] using hh.trans hleft
      · have hqv : s + a ≤ q := by
          by_contra hnv
          have hqarc : q ∈ Ioo (s - a) (s + a) :=
            ⟨lt_of_le_of_ne hq.1 (Ne.symm hqu), lt_of_not_ge hnv⟩
          exact hqoff (original_source_arc_inside_actual_cap_v411 s r hr hr1 q hqarc)
        exact hold q ⟨hqv, hq.2.le⟩
    have heq : liftedBoundaryValue Ω theta' q = liftedBoundaryValue Ω theta q := by
      dsimp only [liftedBoundaryValue]
      rw [hraw]
    have hp' := ((hperiod theta' hlift').int_mul n).sub_eq t
    have hp := ((hperiod theta lift).int_mul n).sub_eq t
    exact hp'.symm.trans (heq.trans hp)
  exact ⟨theta', eta, hlift', hnew, hunchanged, heta, hcurve, henergy⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
