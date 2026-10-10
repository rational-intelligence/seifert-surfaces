import InitialBoundaryChordShell_v411
import InitialBoundaryShortArc_v411
import Mathlib.MeasureTheory.Integral.Average

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
open DirectMethod.CourantTraceFluxAssembly

/-! One ACTUAL radius simultaneously carries the original polar H1 rows and
controls the circle derivative cost and the Green endpoint chord.  All costs
are paid from one original shell, without a competitor premise. -/
private theorem original_cap_joint_good_radius_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
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
  classical
  dsimp only
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let U : Set ℝ := Ioo (r / 2) r
  let ann : Set E2 := {z | z ∈ disc 1 ∧ r / 2 < ‖z - unitCircleParameter s‖ ∧
    ‖z - unitCircleParameter s‖ < r}
  let Q : (Fin 2 → E2 → E2) → E2 → ℝ := fun rows z =>
    ‖rows 0 z‖ ^ 2 + ‖rows 1 z‖ ^ 2
  let energy : ℝ → ℝ := fun q =>
    ∫ t in angles, Q d0 (unitCircleParameter s + q • unitCircleParameter t)
  let chord : ℝ → E2 := fun q =>
    liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
      liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))
  let cost : ℝ → ℝ := fun q => q * energy q + ‖chord q‖ ^ 2 / q
  let good : ℝ → Prop := fun q => ∀ i,
    MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
      (volume.restrict angles)
  let shell : ℝ :=
    (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
      (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
  have hrows : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)) :=
    fun i => (minimum.admissible.1 i).2.2
  have hpolar := CourantAnalyticB.native_translated_polar_rows d
    (fun i => (hrows i).aestronglyMeasurable) hrows (unitCircleParameter s)
    (r / 2) r (by positivity) (by linarith) (by linarith)
  dsimp only at hpolar
  rcases hpolar with ⟨_, _, hslices, _, hweighted, _, hidentity, _, _⟩
  have hb : Continuous (liftedBoundaryValue Ω theta) :=
    Ω.boundary.smooth.continuous.comp lift.2.1
  have hp : Periodic (liftedBoundaryValue Ω theta) (2 * Real.pi) := by
    intro t
    change Ω.boundary.gamma (theta (t + 2 * Real.pi)) = Ω.boundary.gamma (theta t)
    rw [lift.2.2.2]
    rcases lift.1 with hσ | hσ
    · simpa only [hσ, one_mul] using Ω.boundary.periodic (theta t)
    · simpa only [hσ, neg_one_mul, sub_eq_add_neg] using
        Ω.boundary.periodic.sub_eq (theta t)
  have henergy : IntegrableOn (Q d) (disc 1) :=
    ((hrows 0).norm.integrable_sq).add ((hrows 1).norm.integrable_sq)
  have hchord := actual_green_weighted_squared_chord_energy f d
    (liftedBoundaryValue Ω theta) hrows trace hb hp s (r / 2) r
    (by positivity) (by linarith) (by linarith) henergy
  dsimp only at hchord
  have hcost : IntegrableOn cost U := hweighted.add hchord.1
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (hrows i).norm.integrable_sq
  have hdiff : planarCap (unitCircleParameter s) (r / 2) ⊆
      planarCap (unitCircleParameter s) r :=
    inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith))
  have hsub : ann ⊆ planarCap (unitCircleParameter s) r \
      planarCap (unitCircleParameter s) (r / 2) := by
    intro z hz
    refine ⟨⟨hz.1, ?_⟩, ?_⟩
    · simpa only [Metric.mem_ball, dist_eq_norm] using hz.2.2
    · intro hzinner
      have hnorm : ‖z - unitCircleParameter s‖ < r / 2 := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hzinner.2
      exact (not_lt_of_ge hz.2.1.le) hnorm
  have hann : (∫ z in ann, Q d z) ≤ shell := by
    have hQ (rows : Fin 2 → E2 → E2) : euclideanJetDensity rows = Q rows := by
      funext z
      exact Fin.sum_univ_two _
    rw [← hQ d]
    have hm := setIntegral_mono_set
      ((hi.mono_set inter_subset_left).mono_set sdiff_subset)
      (Eventually.of_forall fun z => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Eventually.of_forall fun z hz => hsub hz)
    change (∫ z in ann, euclideanJetDensity d z) ≤
      ∫ z in planarCap (unitCircleParameter s) r \
        planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z at hm
    have heq := setIntegral_sdiff (measurableSet_ball.inter measurableSet_ball)
      (hi.mono_set inter_subset_left) hdiff
    exact hm.trans_eq heq
  have hbudget : (∫ q in U, cost q) ≤ (1 + 2 * Real.pi) * shell := by
    dsimp only [cost]
    rw [integral_add hweighted hchord.1]
    rw [hidentity]
    calc
      _ ≤ (∫ z in ann, Q d z) + (2 * Real.pi) * (∫ z in ann, Q d z) :=
        add_le_add le_rfl hchord.2
      _ = (1 + 2 * Real.pi) * ∫ z in ann, Q d z := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hann (by positivity)
  have hgood : ∀ᵐ q ∂volume.restrict U, q ∈ U ∧ good q := by
    filter_upwards [hslices, ae_restrict_mem measurableSet_Ioo] with q hq hqu
    exact ⟨hqu, fun i => (hq.1 i).2.1⟩
  let μ : Measure ℝ := volume.restrict U
  have hvolume : volume U = ENNReal.ofReal (r / 2) := by
    dsimp only [U]
    rw [Real.volume_Ioo]
    congr 1
    ring
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by rw [hvolume]; simp)
  have hμ : μ ≠ 0 := by
    apply Measure.measure_univ_ne_zero.mp
    rw [Measure.restrict_apply_univ, hvolume]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  let N : Set ℝ := {q | ¬(q ∈ U ∧ good q)}
  have hN : μ N = 0 := ae_iff.mp hgood
  obtain ⟨q, hqN, hqavg⟩ := exists_notMem_null_le_average hμ hcost hN
  have hq : q ∈ U ∧ good q := Classical.not_not.mp hqN
  have havg : (⨍ a, cost a ∂μ) ≤
      (2 / r) * ((1 + 2 * Real.pi) * shell) := by
    rw [average_eq, Measure.real]
    dsimp only [μ]
    rw [Measure.restrict_apply_univ, hvolume, ENNReal.toReal_ofReal (by positivity),
      smul_eq_mul]
    have hinv : (r / 2)⁻¹ = 2 / r := by field_simp
    rw [hinv]
    exact mul_le_mul_of_nonneg_left hbudget (by positivity)
  have hqbound := hqavg.trans havg
  have hqpos : 0 < q := lt_trans (by positivity) hq.1.1
  have henergy0 : 0 ≤ energy q := integral_nonneg (fun t => by dsimp [Q]; positivity)
  have hcost0 : 0 ≤ cost q := by dsimp [cost]; positivity
  have hscale : q * cost q ≤ r * cost q :=
    mul_le_mul_of_nonneg_right hq.1.2.le hcost0
  have htotal : q ^ 2 * energy q + ‖chord q‖ ^ 2 = q * cost q := by
    dsimp [cost]
    field_simp [hqpos.ne']
    <;> ring
  have hrbound := mul_le_mul_of_nonneg_left hqbound hr.le
  have heq : r * ((2 / r) * ((1 + 2 * Real.pi) * shell)) =
      2 * (1 + 2 * Real.pi) * shell := by field_simp
  rw [heq] at hrbound
  refine ⟨q, hq.1, hq.2, ?_⟩
  have hQ (rows : Fin 2 → E2 → E2) : euclideanJetDensity rows = Q rows := by
    funext z
    exact Fin.sum_univ_two _
  rw [hQ d0]
  change q ^ 2 * energy q + ‖chord q‖ ^ 2 ≤ 2 * (1 + 2 * Real.pi) * shell
  exact htotal.trans_le (hscale.trans hrbound)

/-! The same selected radius also controls every point of the actual short
boundary arc.  The imported private short-arc proof is applied with its exact
original telescope; no new mathematical provider or boundary premise is used. -/
private theorem original_cap_joint_arc_budget_v411
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
        ∃ q ∈ Ioo (r / 2) r,
          (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
            (volume.restrict angles)) ∧
          q ^ 2 * (∫ t in angles,
            euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
              K * shell ∧
          (∀ u ∈ Icc (s - 2 * Real.arcsin (q / 2)) (s + 2 * Real.arcsin (q / 2)),
            ∀ v ∈ Icc (s - 2 * Real.arcsin (q / 2)) (s + 2 * Real.arcsin (q / 2)),
              dist (liftedBoundaryValue Ω theta u) (liftedBoundaryValue Ω theta v) ^ 2 ≤
                K * shell) := by
  classical
  have harc : ∃ C rho : ℝ, 0 < C ∧ 0 < rho ∧ rho ≤ 1 / 2 ∧
      ∀ s r : ℝ, 0 < r → r ≤ rho →
        let a : ℝ := 2 * Real.arcsin (r / 2)
        ∀ u ∈ Icc (s - a) (s + a), ∀ v ∈ Icc (s - a) (s + a),
          dist (liftedBoundaryValue Ω theta u) (liftedBoundaryValue Ω theta v) ≤
            C * dist (liftedBoundaryValue Ω theta (s - a))
              (liftedBoundaryValue Ω theta (s + a)) := by
    run_tac do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialBoundaryShortArc_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_boundary_cap_arc_chord_control_v411") |
          throwError "checked original short-arc proof missing"
      let args ← ([`R, `Ω, `theta, `sigma, `lift].toArray.mapM fun name =>
        Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let proof := Lean.mkAppN (Lean.mkConst name) args
      Lean.Meta.checkWithKernel proof
      Lean.Elab.Tactic.closeMainGoal `original_short_arc proof
  obtain ⟨C, rho, hC, hrho, hrhohalf, hcontrol⟩ := harc
  let B : ℝ := 2 * (1 + 2 * Real.pi)
  let K : ℝ := B * (C ^ 2 + 1)
  have hB : 0 < B := by dsimp [B]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, rho, hK, hrho, hrhohalf, ?_⟩
  intro s r hr hrr
  dsimp only
  obtain ⟨q, hq, hslice, hbudget⟩ := original_cap_joint_good_radius_v411
    minimum theta sigma lift trace s r hr (hrr.trans hrhohalf)
  let shell : ℝ :=
    (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
      (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
  let e : ℝ := q ^ 2 * (∫ t in Ioo (-Real.pi) Real.pi,
    euclideanJetDensity (fun i => (disc 1).indicator (d i))
      (unitCircleParameter s + q • unitCircleParameter t))
  let c : ℝ := ‖liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
    liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))‖ ^ 2
  have he : 0 ≤ e := by
    dsimp [e]
    apply mul_nonneg (sq_nonneg _)
    exact integral_nonneg (fun t => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hc : 0 ≤ c := sq_nonneg _
  change e + c ≤ B * shell at hbudget
  have hs : 0 ≤ shell := by
    exact nonneg_of_mul_nonneg_right ((add_nonneg he hc).trans hbudget) hB
  have heB : e ≤ B * shell := le_trans (by linarith) hbudget
  have hcB : c ≤ B * shell := le_trans (by linarith) hbudget
  have hBK : B ≤ K := by dsimp [K]; nlinarith [sq_nonneg C]
  have heK : e ≤ K * shell := heB.trans (mul_le_mul_of_nonneg_right hBK hs)
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqrho : q ≤ rho := hq.2.le.trans hrr
  refine ⟨q, hq, hslice, heK, ?_⟩
  intro u hu v hv
  have hd := hcontrol s q hqpos hqrho u hu v hv
  have hd2 : dist (liftedBoundaryValue Ω theta u) (liftedBoundaryValue Ω theta v) ^ 2 ≤
      C ^ 2 * c := by
    have h := (sq_le_sq₀ (dist_nonneg) (mul_nonneg hC.le (dist_nonneg))).mpr hd
    simpa only [mul_pow, dist_eq_norm, c] using h
  have hCK : C ^ 2 * B ≤ K := by dsimp [K]; nlinarith
  calc
    _ ≤ C ^ 2 * c := hd2
    _ ≤ C ^ 2 * (B * shell) := mul_le_mul_of_nonneg_left hcB (sq_nonneg _)
    _ = (C ^ 2 * B) * shell := by ring
    _ ≤ K * shell := mul_le_mul_of_nonneg_right hCK hs

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
