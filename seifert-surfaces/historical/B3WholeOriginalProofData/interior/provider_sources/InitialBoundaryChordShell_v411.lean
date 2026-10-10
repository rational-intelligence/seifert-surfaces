import VM02aDirectMethod
import B1L1IndependentLower
import CourantWeightedChordEnergy
import CourantLogarithmicRadius

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
open DirectMethod
open DirectMethod.CourantTraceFluxAssembly

/-! The original Green trace gives the exact weighted chord cost on every
annular family of boundary caps.  This is an independent boundary-energy
receipt: it does not choose a competitor or import a cap-pasting theorem. -/
private theorem original_cap_trace_chord_shell_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    let alpha : ℝ → ℝ := fun r => 2 * Real.arcsin (r / 2)
    let g : ℝ → E2 := fun r =>
      liftedBoundaryValue Ω theta (s - alpha r) -
        liftedBoundaryValue Ω theta (s + alpha r)
    ∫ r in Ioo a z, ‖g r‖ ^ 2 / r ≤
      (2 * Real.pi) *
        ∫ x in {x | x ∈ disc 1 ∧ a < ‖x - unitCircleParameter s‖ ∧
          ‖x - unitCircleParameter s‖ < z},
          euclideanJetDensity d x := by
  classical
  have hrows : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)) := by
    intro i
    exact (minimum.admissible.1 i).2.2
  have henergy : IntegrableOn
      (fun x => ‖d 0 x‖ ^ 2 + ‖d 1 x‖ ^ 2) (disc 1) := by
    exact ((hrows 0).norm.integrable_sq).add ((hrows 1).norm.integrable_sq)
  have hb : Continuous (liftedBoundaryValue Ω theta) :=
    Ω.boundary.smooth.continuous.comp lift.2.1
  have hperiod : Function.Periodic (liftedBoundaryValue Ω theta) (2 * Real.pi) := by
    intro t
    change Ω.boundary.gamma (theta (t + 2 * Real.pi)) = Ω.boundary.gamma (theta t)
    rw [lift.2.2.2]
    rcases lift.1 with hσ | hσ
    · simpa only [hσ, one_mul] using Ω.boundary.periodic (theta t)
    · simpa only [hσ, neg_one_mul, sub_eq_add_neg] using
        Ω.boundary.periodic.sub_eq (theta t)
  have h := actual_green_weighted_squared_chord_energy
    f d (liftedBoundaryValue Ω theta) hrows trace hb hperiod s a z ha haz hz henergy
  simpa only [euclideanJetDensity, Fin.sum_univ_two] using h.2

/-! At the actual boundary scale, the abstract annulus in the chord receipt
is literally the shell between two planar caps. -/
private theorem original_boundary_cap_trace_shell_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    let alpha : ℝ → ℝ := fun q => 2 * Real.arcsin (q / 2)
    ∫ q in Ioo (r / 2) r,
        ‖liftedBoundaryValue Ω theta (s - alpha q) -
          liftedBoundaryValue Ω theta (s + alpha q)‖ ^ 2 / q ≤
      (2 * Real.pi) *
        ((∫ x in planarCap (unitCircleParameter s) r, euclideanJetDensity d x) -
          (∫ x in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d x)) := by
  classical
  dsimp only
  have hz : r < 1 := lt_of_le_of_lt hrhalf (by norm_num)
  have h := original_cap_trace_chord_shell_v411 minimum theta sigma lift trace s
    (r / 2) r (by positivity) (by linarith) hz
  have hdiff : planarCap (unitCircleParameter s) (r / 2) ⊆
      planarCap (unitCircleParameter s) r := by
    exact inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith))
  have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hshell :
      (∫ x in {x | x ∈ disc 1 ∧ r / 2 < ‖x - unitCircleParameter s‖ ∧
        ‖x - unitCircleParameter s‖ < r}, euclideanJetDensity d x) ≤
        (∫ x in planarCap (unitCircleParameter s) r, euclideanJetDensity d x) -
          (∫ x in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d x) := by
    let ann : Set E2 := {x | x ∈ disc 1 ∧ r / 2 < ‖x - unitCircleParameter s‖ ∧
      ‖x - unitCircleParameter s‖ < r}
    have hsub : ann ⊆ planarCap (unitCircleParameter s) r \
        planarCap (unitCircleParameter s) (r / 2) := by
      intro x hx
      refine ⟨⟨hx.1, ?_⟩, ?_⟩
      · simpa only [Metric.mem_ball, dist_eq_norm] using hx.2.2
      · intro hxinner
        have hnorm : ‖x - unitCircleParameter s‖ < r / 2 := by
          simpa only [Metric.mem_ball, dist_eq_norm] using hxinner.2
        exact (not_lt_of_ge hx.2.1.le) hnorm
    have hm := setIntegral_mono_set
      ((hi.mono_set inter_subset_left).mono_set sdiff_subset)
      (Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
      (Eventually.of_forall fun x hx => hsub hx)
    change (∫ x in ann, euclideanJetDensity d x) ≤
      ∫ x in planarCap (unitCircleParameter s) r \
        planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d x at hm
    have heq := setIntegral_sdiff (measurableSet_ball.inter measurableSet_ball)
      (hi.mono_set inter_subset_left) hdiff
    exact hm.trans_eq heq
  exact h.trans (mul_le_mul_of_nonneg_left hshell (by positivity))

/-! A strict small-shell budget therefore supplies a genuine boundary radius
with a small endpoint chord.  The auxiliary positive slack in `K` handles the
zero-shell case while retaining the exact original annular quantifiers. -/
private theorem original_boundary_cap_good_chord_radius_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r lambda : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hlambda : 0 < lambda)
    (hbudget : 2 * Real.pi *
        ((∫ x in planarCap (unitCircleParameter s) r, euclideanJetDensity d x) -
          (∫ x in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d x)) <
        lambda ^ 2 * Real.log 2) :
    ∃ q ∈ Ioo (r / 2) r,
      dist (liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)))
        (liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) < lambda := by
  classical
  let shell : ℝ :=
    (∫ x in planarCap (unitCircleParameter s) r, euclideanJetDensity d x) -
      (∫ x in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d x)
  have hshell : 0 ≤ shell := by
    dsimp [shell]
    apply sub_nonneg.mpr
    apply setIntegral_mono_set
    · have hi : IntegrableOn (euclideanJetDensity d) (disc 1) := by
        apply integrable_finsetSum
        intro i _
        exact (minimum.admissible.1 i).2.2.norm.integrable_sq
      exact hi.mono_set inter_subset_left
    · exact Eventually.of_forall (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    · exact Eventually.of_forall (fun x hx =>
        ⟨hx.1, Metric.ball_subset_ball (by linarith) hx.2⟩)
  have hmargin : 0 < lambda ^ 2 * Real.log 2 - 2 * Real.pi * shell := by
    dsimp [shell] at hbudget ⊢
    linarith
  let slack : ℝ :=
    (lambda ^ 2 * Real.log 2 - 2 * Real.pi * shell) / (4 * Real.pi)
  have hslack : 0 < slack := by
    dsimp [slack]
    positivity
  let K : ℝ := shell + slack
  have hK : 0 < K := by dsimp [K]; linarith
  have hbound : 2 * Real.pi * K < lambda ^ 2 * Real.log 2 := by
    dsimp [K, slack]
    field_simp
    nlinarith
  have hweighted := original_boundary_cap_trace_shell_v411 minimum theta sigma lift trace s r
    hr hrhalf
  have hKbound : (∫ q in Ioo (r / 2) r,
      ‖liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))‖ ^ 2 / q) ≤
      (2 * Real.pi) * K := by
    have hle : shell ≤ K := by dsimp [K]; linarith
    exact hweighted.trans (mul_le_mul_of_nonneg_left hle (by positivity))
  have hb : Continuous (liftedBoundaryValue Ω theta) :=
    Ω.boundary.smooth.continuous.comp lift.2.1
  have hc : Continuous (fun q : ℝ =>
      liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) := by
    fun_prop
  have hint : IntegrableOn (fun q : ℝ =>
      ‖liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))‖ ^ 2 / q)
      (Ioo (r / 2) r) := by
    exact ((hc.norm.pow 2).continuousOn.div continuousOn_id
      (fun q hq => ne_of_gt (lt_of_lt_of_le (by positivity) hq.1))).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
  obtain ⟨q, hq, hqsmall⟩ := actual_chord_logarithmic_radius_selection
    (liftedBoundaryValue Ω theta) hb s (r / 2) r K lambda
    (by positivity) (by linarith) (by linarith) hK hlambda
    hint hKbound (by
      have hratio : r / (r / 2) = (2 : ℝ) := by field_simp
      rw [hratio]
      exact hbound)
  exact ⟨q, hq, hqsmall⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
