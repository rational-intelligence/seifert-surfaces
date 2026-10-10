import NativeH10SupportedBridge
import NativeMinimumTransfer

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

private theorem native_H1_of_W12
    (U : Set E2) [IsFiniteMeasure (volume.restrict U)] (u : E2 → ℝ)
    (w : DeGiorgi.MemW1pWitness 2 u U) : H1On U u w.weakGrad := by
  have hd : MemLp w.weakGrad 2 (volume.restrict U) :=
    memLp_piLp_iff.mpr w.weakGrad_component_memLp
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (w.memLp.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hd.locallyIntegrable (by norm_num)), ?_⟩, w.memLp, hd⟩
  intro phi hp hc hs i
  have hbasis : EuclideanSpace.single i 1 = coordinateVector 2 i := by
    ext j
    simp [coordinateVector, EuclideanSpace.single]
  simpa only [hbasis] using w.isWeakGrad i phi hp hc hs

private theorem native_cutoff_difference_H10
    (a : E2) (r : ℝ) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (disc 1) u du) (hinside : Metric.ball a r ⊆ disc 1)
    (chi : E2 → ℝ) (hc : ContDiff ℝ ∞ chi)
    (hk : HasCompactSupport chi) (hs : tsupport chi ⊆ Metric.ball a r)
    (c : ℝ) :
    H10On (Metric.ball a r) (fun z => -(chi z * (u z - c)))
      (fun z => -(chi z • du z + (u z - c) • planarGradient chi z)) := by
  classical
  let U := Metric.ball a r
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let wu : DeGiorgi.MemW1pWitness 2 u (disc 1) :=
    { memLp := hu.2.1
      weakGrad := du
      weakGrad_component_memLp := fun i => hu.2.2.eval_piLp i
      isWeakGrad := by
        intro i phi hp hcp hsp
        have hb : EuclideanSpace.single i 1 = coordinateVector 2 i := by
          ext j
          simp [coordinateVector, EuclideanSpace.single]
        simpa only [hb] using hu.1.2.2 phi hp hcp hsp i }
  let wconst : DeGiorgi.MemW1pWitness 2 (fun _ : E2 => -c) U :=
    { memLp := memLp_const _
      weakGrad := 0
      weakGrad_component_memLp := fun _ => MemLp.zero
      isWeakGrad := by
        intro i
        convert (DeGiorgi.HasWeakPartialDeriv.of_contDiff (Ω := U) (i := i)
            Metric.isOpen_ball (f := fun _ : E2 => -c) contDiff_const) using 1 <;>
          ext x <;> simp [coordinateVector] }
  let w := (wu.restrict Metric.isOpen_ball hinside).add wconst
  obtain ⟨C0, hC0⟩ := hk.exists_bound_of_continuous hc.continuous
  obtain ⟨C1, hC1⟩ := (hk.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv (by simp))
  have hC0n : 0 ≤ C0 := (norm_nonneg (chi a)).trans (hC0 a)
  have hC1n : 0 ≤ C1 := (norm_nonneg (fderiv ℝ chi a)).trans (hC1 a)
  have hchi : ∀ z, |chi z| ≤ C0 := fun z => by simpa only [Real.norm_eq_abs] using hC0 z
  let wp := w.mulSmoothBoundedP (by norm_num) Metric.isOpen_ball hc hC0n hC1n hchi hC1
  let wn := wp.smul (-1)
  have hgrad (z : E2) : wn.weakGrad z =
      -(chi z • du z + (u z - c) • planarGradient chi z) := by
    ext i
    simp only [wn, wp, w, wu, wconst, DeGiorgi.MemW1pWitness.smul,
      DeGiorgi.MemW1pWitness.add, DeGiorgi.MemW1pWitness.restrict,
      DeGiorgi.MemW1pWitness.mulSmoothBoundedP, PiLp.toLp_apply,
      PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, smul_eq_mul]
    have hg : planarGradient chi z i = fderiv ℝ chi z (EuclideanSpace.single i 1) := by
      fin_cases i <;> simp [planarGradient, Fin.sum_univ_two, coordinateVector, EuclideanSpace.single]
    rw [hg]
    simp only [Pi.zero_apply, PiLp.zero_apply, add_zero]
    ring
  have hH : H1On U (fun z => -(chi z * (u z - c)))
      (fun z => -(chi z • du z + (u z - c) • planarGradient chi z)) := by
    have hh := native_H1_of_W12 U _ wn
    have hgfun : wn.weakGrad = fun z => -(chi z • du z + (u z - c) • planarGradient chi z) :=
      funext hgrad
    rw [hgfun] at hh
    simpa only [wn, wp, w, wu, wconst, DeGiorgi.MemW1pWitness.smul,
      neg_one_mul, sub_eq_add_neg] using hh
  have hsv : tsupport (fun z => -(chi z * (u z - c))) ⊆ tsupport chi := by
    apply closure_minimal _ (isClosed_tsupport chi)
    intro z hz
    by_contra hn
    have hcz : chi z = 0 := image_eq_zero_of_notMem_tsupport hn
    exact hz (by simp [hcz])
  have hsd : ∀ i, tsupport (fun z =>
      (-(chi z • du z + (u z - c) • planarGradient chi z)) i) ⊆ tsupport chi := by
    intro i
    apply closure_minimal _ (isClosed_tsupport chi)
    intro z hz
    by_contra hn
    have hcz : chi z = 0 := image_eq_zero_of_notMem_tsupport hn
    have hgz : planarGradient chi z = 0 := planarGradient_eq_zero_off_support chi hn
    exact hz (by simp only [hcz, hgz, zero_smul, smul_zero, add_zero, neg_zero, PiLp.zero_apply])
  run_tac do
    let pn := (Lean.Name.num `_private.NativeH10SupportedBridge 0).str
      "native_H1_supported_is_H10"
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      exact $(Lean.mkIdent pn) $(Lean.mkIdent `U) (tsupport $(Lean.mkIdent `chi))
        Metric.isOpen_ball $(Lean.mkIdent `hk) $(Lean.mkIdent `hs)
        _ _ $(Lean.mkIdent `hH) $(Lean.mkIdent `hsv) $(Lean.mkIdent `hsd)))

#print axioms native_cutoff_difference_H10

private theorem native_original_compact_perturbation_energy
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (a : E2) (r : ℝ) (hr : 0 < r) (hinside : Metric.closedBall a r ⊆ disc 1)
    (chi : E2 → ℝ) (hc : ContDiff ℝ ∞ chi)
    (hk : HasCompactSupport chi) (hs : tsupport chi ⊆ Metric.ball a r)
    (c : E2)
    (ell Lambda : ℝ) (hell : 0 < ell) (hLambda : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (M y) p) ∧
      inner ℝ p (matrixAction (M y) p) ≤ Lambda * ‖p‖ ^ 2) :
    (∀ i, H10On (Metric.ball a r)
      (fun z => (P.u z - chi z • (P.u z - c)) i - P.u z i)
      (fun z => ((1 - chi z) • d i z - (P.u z i - c i) • planarGradient chi z) - d i z)) ∧
    (∫ z in Metric.ball a r, euclideanJetDensity d z) ≤
      (Lambda / ell) * ∫ z in Metric.ball a r,
        euclideanJetDensity (fun i z => (1 - chi z) • d i z -
          (P.u z i - c i) • planarGradient chi z) z := by
  let h : E2 → E2 := fun z => P.u z - chi z • (P.u z - c)
  let dh : Fin 2 → E2 → E2 := fun i z => (1 - chi z) • d i z -
    (P.u z i - c i) • planarGradient chi z
  have hsub : Metric.ball a r ⊆ disc 1 := Metric.ball_subset_closedBall.trans hinside
  have hseam : ∀ i, H10On (Metric.ball a r) (fun z => h z i - P.u z i)
      (fun z => dh i z - d i z) := by
    intro i
    have ht := native_cutoff_difference_H10 a r (fun z => P.u z i) (d i)
      (P.same_H1 i) hsub chi hc hk hs (c i)
    convert ht using 1
    · funext z
      simp only [h, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    · funext z
      ext j
      simp only [dh, PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, PiLp.add_apply, smul_eq_mul]
      ring
  have hmin : SimultaneousMetricMinimum Ω M P.u d := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeMinimumTransfer 0).str "same_holder_minimum_transfer"
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        exact $(Lean.mkIdent pn) $(Lean.mkIdent `Ω) $(Lean.mkIdent `M)
          $(Lean.mkIdent `f) $(Lean.mkIdent `d) $(Lean.mkIdent `minimum)
          $(Lean.mkIdent `theta) $(Lean.mkIdent `sigma) $(Lean.mkIdent `beta) $(Lean.mkIdent `P)))
  have hpaste := interior_disc_paste Ω P.u h d dh P.same_H1 theta sigma
    P.original_lift P.same_Green a r hr hinside hseam
  have he := same_minimizer_local_energy R A G Ω M agreement symmetric elliptic holder
    identity_at_infinity P.u d hmin (Metric.ball a r) Metric.isOpen_ball.measurableSet
    hsub h dh hpaste.2.2 ell Lambda hell hLambda bounds
  exact ⟨hseam, he.2.2.2.2.2.2⟩

#print axioms native_original_compact_perturbation_energy
