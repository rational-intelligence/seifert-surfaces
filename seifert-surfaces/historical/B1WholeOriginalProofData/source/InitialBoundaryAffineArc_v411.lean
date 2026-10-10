import InitialBoundaryShortArc_v411
import CourantAnnularBoundaryA

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates
open DirectMethod.CourantAnnularBoundaryA

/-! Construct the literal affine interpolation in the original TARGET lift
coordinate.  Its sign, endpoints, target interval and scaled energy are proved
before the separate global periodic-pasting and H1 cap extension steps. -/
private theorem original_boundary_affine_arc_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma) :
    ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
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
  classical
  have hbounds : ∃ m L δ : ℝ, 0 < m ∧ 0 < L ∧ 0 < δ ∧
      (∀ s t : ℝ, dist (Ω.boundary.gamma s) (Ω.boundary.gamma t) ≤ L * dist s t) ∧
      (∀ s t : ℝ, dist s t ≤ δ →
        m * dist s t ≤ dist (Ω.boundary.gamma s) (Ω.boundary.gamma t)) := by
    run_tac do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialBoundaryShortArc_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_boundary_chord_bounds_v411") |
          throwError "checked original curve chord proof missing"
      let args ← ([`R, `Ω].toArray.mapM fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let proof := Lean.mkAppN (Lean.mkConst name) args
      Lean.Meta.checkWithKernel proof
      Lean.Elab.Tactic.closeMainGoal `original_curve_chord proof
  obtain ⟨m, L, δ, hm, hL, hδ, hupper, hlower⟩ := hbounds
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧
      ∀ s t : ℝ, dist s t ≤ a → dist (theta s) (theta t) < ε := by
    run_tac do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialBoundaryShortArc_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_target_arc_uniform_smallness_v411") |
          throwError "checked original lift modulus proof missing"
      let args ← ([`R, `Ω, `theta, `sigma, `lift].toArray.mapM fun name =>
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let proof := Lean.mkAppN (Lean.mkConst name) args
      Lean.Meta.checkWithKernel proof
      Lean.Elab.Tactic.closeMainGoal `original_lift_modulus proof
  obtain ⟨a0, ha0, hshort⟩ := hmod δ hδ
  have hc : Continuous (fun r : ℝ => 4 * Real.arcsin (r / 2)) := by fun_prop
  have hz : 4 * Real.arcsin ((0 : ℝ) / 2) < a0 := by simpa using ha0
  obtain ⟨b, hb, hsmall⟩ := Metric.eventually_nhds_iff.mp
    ((hc.tendsto 0).eventually (eventually_lt_nhds hz))
  let rho : ℝ := min (1 / 2) (b / 2)
  let C : ℝ := L ^ 2 / m ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, rho, hC, lt_min (by norm_num) (by positivity), min_le_left _ _, ?_⟩
  intro s r hr hrr
  dsimp only
  let a : ℝ := 2 * Real.arcsin (r / 2)
  have hrhalf : r ≤ 1 / 2 := hrr.trans (min_le_left _ _)
  have hgeometry := circle_cap_radius_geometry s
  dsimp only at hgeometry
  have hgeometry := hgeometry r ⟨hr, lt_of_le_of_lt hrhalf (by norm_num)⟩
  have ha : 0 < a := hgeometry.1
  have hra : r ≤ a := hgeometry.2.1
  have hdist : dist (s - a) (s + a) ≤ a0 := by
    have hrb : dist r 0 < b := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hr]
      exact (hrr.trans (min_le_right _ _)).trans_lt (by linarith)
    have hlen := hsmall hrb
    rw [Real.dist_eq, abs_of_nonpos (by linarith : (s - a) - (s + a) ≤ 0)]
    dsimp [a] at *
    linarith
  have htshort : dist (theta (s - a)) (theta (s + a)) ≤ δ := (hshort _ _ hdist).le
  let D : ℝ := theta (s + a) - theta (s - a)
  let k : ℝ := D / (2 * a)
  let eta : ℝ → ℝ := fun t => theta (s - a) + (t - (s - a)) * k
  have heta : ContDiff ℝ ∞ eta := by dsimp [eta]; fun_prop
  have hk : 0 ≤ sigma * k := by
    have hmon := lift.2.2.1 (show s - a ≤ s + a by linarith)
    have hn : 0 ≤ sigma * D := by dsimp [D]; nlinarith
    dsimp [k]
    rw [← mul_div_assoc]
    exact div_nonneg hn (by positivity)
  have hmono : Monotone (fun t => sigma * eta t) := by
    intro t u htu
    have h := mul_nonneg (sub_nonneg.mpr htu) hk
    dsimp [eta]
    nlinarith
  have hleft : eta (s - a) = theta (s - a) := by simp [eta]
  have hright : eta (s + a) = theta (s + a) := by
    dsimp [eta, k, D]
    field_simp
    <;> ring
  have hinside : ∀ t ∈ Icc (s - a) (s + a),
      eta t ∈ uIcc (theta (s - a)) (theta (s + a)) := by
    intro t ht
    have hm0 := hmono ht.1
    have hm1 := hmono ht.2
    dsimp only at hm0 hm1
    rw [hleft] at hm0
    rw [hright] at hm1
    rcases lift.1 with hσ | hσ
    · simp only [hσ, one_mul] at hm0 hm1
      exact ⟨(min_le_left _ _).trans hm0, hm1.trans (le_max_right _ _)⟩
    · simp only [hσ, neg_one_mul] at hm0 hm1
      exact ⟨(min_le_right _ _).trans (by linarith), (by linarith : eta t ≤ theta (s - a)).trans (le_max_left _ _)⟩
  let B : ℝ → E2 := fun t => Ω.boundary.gamma (eta t)
  have hB : ContDiff ℝ ∞ B := Ω.boundary.smooth.comp heta
  have hLip : LipschitzWith (⟨L, hL.le⟩ : ℝ≥0) Ω.boundary.gamma :=
    LipschitzWith.of_dist_le_mul hupper
  have hderiv (t : ℝ) : deriv B t = k • deriv Ω.boundary.gamma (eta t) := by
    have hkderiv : HasDerivAt eta k t := by
      simpa only [id_eq, one_mul, eta] using
        ((((hasDerivAt_id t).sub_const (s - a)).mul_const k).const_add (theta (s - a)))
    exact (((Ω.boundary.smooth.differentiable (by simp) (eta t)).hasDerivAt).scomp t hkderiv).deriv
  have hpoint (t : ℝ) : ‖deriv B t‖ ^ 2 ≤ L ^ 2 * k ^ 2 := by
    rw [hderiv, norm_smul, Real.norm_eq_abs]
    have hn : ‖deriv Ω.boundary.gamma (eta t)‖ ≤ L := norm_deriv_le_of_lipschitz hLip
    have hs := (sq_le_sq₀ (norm_nonneg _) hL.le).mpr hn
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg k), sq_abs k]
  have hint : IntegrableOn (fun t => ‖deriv B t‖ ^ 2) (Icc (s - a) (s + a)) :=
    ((hB.continuous_deriv (by simp)).norm.pow 2).integrableOn_Icc
  let : IsFiniteMeasure (volume.restrict (Icc (s - a) (s + a))) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hI : (∫ t in Icc (s - a) (s + a), ‖deriv B t‖ ^ 2) ≤
      (2 * a) * (L ^ 2 * k ^ 2) := by
    have h := integral_mono hint (integrable_const (L ^ 2 * k ^ 2)) hpoint
    rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at h
    convert h using 1 <;> ring
  have hscaled : r * (∫ t in Icc (s - a) (s + a), ‖deriv B t‖ ^ 2) ≤ L ^ 2 * D ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hI hr.le
    have htwo : r ≤ 2 * a := by linarith
    have halg : (2 * a) ^ 2 * k ^ 2 = D ^ 2 := by dsimp [k]; field_simp
    have hcoef : r * (2 * a) ≤ (2 * a) ^ 2 := by nlinarith
    have hc := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (sq_nonneg L) (sq_nonneg k))
    nlinarith [h, hc]
  have hl := hlower (theta (s - a)) (theta (s + a)) htshort
  have hl2 := (sq_le_sq₀ (mul_nonneg hm.le dist_nonneg) dist_nonneg).mpr hl
  have hD : D ^ 2 = dist (theta (s - a)) (theta (s + a)) ^ 2 := by
    rw [Real.dist_eq, sq_abs]
    dsimp [D]
    ring
  have hcost : L ^ 2 * D ^ 2 ≤ C *
      dist (liftedBoundaryValue Ω theta (s - a)) (liftedBoundaryValue Ω theta (s + a)) ^ 2 := by
    dsimp only [liftedBoundaryValue]
    rw [hD]
    dsimp [C]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hm)).mpr
    have h := mul_le_mul_of_nonneg_left hl2 (sq_nonneg L)
    rw [mul_pow] at h
    nlinarith
  exact ⟨eta, heta, hmono, hleft, hright, hinside, hB, hscaled.trans hcost⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
