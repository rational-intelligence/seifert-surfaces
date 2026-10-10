import NativeAnnularEnergy
import NativeAnnularCutoff
import NativeHoleFilling

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_original_Caccioppoli
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (P : SameHolderRepresentative Ω f d theta sigma beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E2) (r : ℝ), 0 < r →
      Metric.closedBall a (2 * r) ⊆ disc 1 → ∀ c : E2,
      (∫ z in Metric.ball a r, euclideanJetDensity d z) ≤
        C / r ^ 2 * ∫ z in Metric.ball a (2 * r), ‖P.u z - c‖ ^ 2 := by
  classical
  have elliptic0 := elliptic
  obtain ⟨ell, Lambda, hell, hLambda, hbound⟩ := elliptic
  let k : ℝ := Lambda / ell
  have hk : 0 < k := div_pos hLambda hell
  let q : ℝ := (2 * k - 1) / (2 * k)
  have hk1 : 1 ≤ k := by
    let p : E2 := coordinateVector 2 0
    have hn : ‖p‖ ^ 2 = 1 := by simp [p, coordinateVector, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have h := hbound 0 (mem_univ _) p
    rw [hn] at h
    exact (le_div_iff₀ hell).mpr (by linarith)
  have hq : 0 ≤ q := by dsimp [q]; exact div_nonneg (by linarith) (by positivity)
  have hq1 : q < 1 := by
    dsimp [q]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * k)).mpr
    linarith
  have hcutoff : ∃ D : ℝ, 0 ≤ D ∧ ∀ (a : E2) (s t : ℝ), 0 < s → s < t →
      ∃ chi : E2 → ℝ, ContDiff ℝ ∞ chi ∧ HasCompactSupport chi ∧
        tsupport chi ⊆ Metric.ball a t ∧
        (∀ z, 0 ≤ chi z ∧ chi z ≤ 1) ∧
        (∀ z ∈ Metric.ball a s, chi z = 1 ∧ planarGradient chi z = 0) ∧
        (∀ z, ‖planarGradient chi z‖ ≤ D / (t - s)) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeAnnularCutoff 0).str "native_annular_cutoff_uniform"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn)))
  obtain ⟨D, hD, hcutoff⟩ := hcutoff
  have hiter : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : ℝ → ℝ) (K I r R T : ℝ),
      0 ≤ K → 0 ≤ I → 0 < r → r < R → 0 ≤ T →
      (∀ t, r ≤ t → t < R → E t ≤ T) →
      (∀ s t, r ≤ s → s < t → t < R →
        E s ≤ q * E t + K * I / (t - s)^2) →
      E r ≤ C * K * I / (R - r)^2 := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeHoleFilling 0).str "native_hole_filling_radii"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `q) $(Lean.mkIdent `hq) $(Lean.mkIdent `hq1)))
  obtain ⟨C0, hC0, hiter⟩ := hiter
  refine ⟨C0 * D^2, by positivity, ?_⟩
  intro a r hr hinside c
  let E : ℝ → ℝ := fun t => ∫ z in Metric.ball a t, euclideanJetDensity d z
  let I : ℝ := ∫ z in Metric.ball a (2 * r), ‖P.u z - c‖ ^ 2
  let T : ℝ := ∫ z in disc 1, euclideanJetDensity d z
  have he : IntegrableOn (euclideanJetDensity d) (disc 1) :=
    integrable_finsetSum _ (fun i _ => (P.same_H1 i).2.2.norm.integrable_sq)
  have hen : ∀ z, 0 ≤ euclideanJetDensity d z := fun z =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT : 0 ≤ T := integral_nonneg hen
  have hI : 0 ≤ I := integral_nonneg (fun z => sq_nonneg _)
  have hBsub : Metric.ball a (2 * r) ⊆ disc 1 := Metric.ball_subset_closedBall.trans hinside
  letI : IsFiniteMeasure (volume.restrict (Metric.ball a (2 * r))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have huLp : MemLp P.u 2 (volume.restrict (Metric.ball a (2 * r))) :=
    memLp_piLp_iff.mpr (fun i =>
      (P.same_H1 i).2.1.mono_measure (Measure.restrict_mono hBsub le_rfl))
  have hv : IntegrableOn (fun z => ‖P.u z - c‖ ^ 2) (Metric.ball a (2 * r)) :=
    (huLp.sub (memLp_const c)).norm.integrable_sq
  have hEt : ∀ t, r ≤ t → t < 2 * r → E t ≤ T := by
    intro t _ ht
    have htSub : Metric.ball a t ⊆ disc 1 := (Metric.ball_subset_ball ht.le).trans hBsub
    exact setIntegral_mono_set he (Filter.Eventually.of_forall hen) htSub.eventuallyLE
  have hstep : ∀ s t, r ≤ s → s < t → t < 2 * r →
      E s ≤ q * E t + D^2 * I / (t - s)^2 := by
    intro s t hrs hst ht
    have hs : 0 < s := hr.trans_le hrs
    have htPos : 0 < t := hs.trans hst
    have htInside : Metric.closedBall a t ⊆ disc 1 :=
      (Metric.closedBall_subset_closedBall ht.le).trans hinside
    obtain ⟨chi, hc, hkc, hks, h01, hone, hg⟩ := hcutoff a s t hs hst
    have hcomp : (∀ i, H10On (Metric.ball a t)
        (fun z => (P.u z - chi z • (P.u z - c)) i - P.u z i)
        (fun z => ((1 - chi z) • d i z - (P.u z i - c i) • planarGradient chi z) - d i z)) ∧
        E t ≤ k * ∫ z in Metric.ball a t,
          euclideanJetDensity (fun i z => (1 - chi z) • d i z -
            (P.u z i - c i) • planarGradient chi z) z := by
      run_tac do
        let pn := (Lean.Name.num `_private.NativeCutoffMinimum 0).str
          "native_original_compact_perturbation_energy"
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact $(Lean.mkIdent pn) $(Lean.mkIdent `R) $(Lean.mkIdent `A)
            $(Lean.mkIdent `G) $(Lean.mkIdent `Ω) $(Lean.mkIdent `M)
            $(Lean.mkIdent `agreement) $(Lean.mkIdent `symmetric) $(Lean.mkIdent `elliptic0)
            $(Lean.mkIdent `holder) $(Lean.mkIdent `identity_at_infinity)
            $(Lean.mkIdent `f) $(Lean.mkIdent `d) $(Lean.mkIdent `minimum)
            $(Lean.mkIdent `theta) $(Lean.mkIdent `sigma) $(Lean.mkIdent `beta) $(Lean.mkIdent `P)
            $(Lean.mkIdent `a) $(Lean.mkIdent `t) $(Lean.mkIdent `htPos) $(Lean.mkIdent `htInside)
            $(Lean.mkIdent `chi) $(Lean.mkIdent `hc) $(Lean.mkIdent `hkc) $(Lean.mkIdent `hks)
            $(Lean.mkIdent `c) $(Lean.mkIdent `ell) $(Lean.mkIdent `Lambda)
            $(Lean.mkIdent `hell) $(Lean.mkIdent `hLambda) (fun y p => $(Lean.mkIdent `hbound) y (mem_univ y) p)))
    have hann : (∫ z in Metric.ball a t,
        euclideanJetDensity (fun i z => (1 - chi z) • d i z -
          (P.u z i - c i) • planarGradient chi z) z) ≤
        2 * (E t - E s) +
        2 * (D / (t - s)) ^ 2 * ∫ z in Metric.ball a t, ‖P.u z - c‖ ^ 2 := by
      run_tac do
        let pn := (Lean.Name.num `_private.NativeAnnularEnergy 0).str
          "native_annular_competitor_integral_bound"
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          exact $(Lean.mkIdent pn) $(Lean.mkIdent `P).u $(Lean.mkIdent `d)
            $(Lean.mkIdent `a) $(Lean.mkIdent `s) $(Lean.mkIdent `t) $(Lean.mkIdent `D)
            $(Lean.mkIdent `hs) $(Lean.mkIdent `hst) $(Lean.mkIdent `hD)
            (Metric.ball_subset_closedBall.trans $(Lean.mkIdent `htInside))
            $(Lean.mkIdent `P).same_H1 $(Lean.mkIdent `chi) $(Lean.mkIdent `hc)
            $(Lean.mkIdent `c) $(Lean.mkIdent `h01) $(Lean.mkIdent `hone)
            $(Lean.mkIdent `hg) $(Lean.mkIdent `hcomp).1))
    have hvI : (∫ z in Metric.ball a t, ‖P.u z - c‖ ^ 2) ≤ I :=
      setIntegral_mono_set hv (Filter.Eventually.of_forall fun z => sq_nonneg _)
        (Metric.ball_subset_ball ht.le).eventuallyLE
    have hall := hcomp.2.trans (mul_le_mul_of_nonneg_left hann hk.le)
    have hfinal : E t ≤ k * (2 * (E t - E s) + 2 * (D / (t - s))^2 * I) :=
      hall.trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvI (by positivity))) hk.le)
    have hgap : 0 < t - s := sub_pos.mpr hst
    dsimp [q]
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * k)).mp
    have heq : (2 * k) * ((2 * k - 1) / (2 * k) * E t + D ^ 2 * I / (t - s)^2) =
        (2 * k - 1) * E t + 2 * k * (D / (t - s))^2 * I := by
      field_simp
    rw [heq]
    nlinarith [hfinal]
  have hout := hiter E (D^2) I r (2*r) T (sq_nonneg D) hI hr (by linarith) hT hEt hstep
  have hgap : (2*r-r)^2 = r^2 := by ring
  rw [hgap] at hout
  simpa only [E, I, div_mul_eq_mul_div, mul_assoc] using hout

#print axioms native_original_Caccioppoli
