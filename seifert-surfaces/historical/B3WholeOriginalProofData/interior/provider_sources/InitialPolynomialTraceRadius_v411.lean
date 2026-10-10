import InitialWeightedTrace_v411
set_option maxHeartbeats 0

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

/- The actual minimizer, its original rows, and every polynomial Green test
are retained at ONE radius carrying the original shell-energy bound. -/
private theorem original_cap_polynomial_trace_radius_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    let f0 : E2 → E2 := (disc 1).indicator f
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let phi : ℕ → ℕ → E2 → ℝ := fun m n x => x 0 ^ m * x 1 ^ n
    let grad : ℕ → ℕ → E2 → E2 := fun m n x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ (phi m n) x (coordinateVector 2 j))
    let dp : ℕ → ℕ → Fin 2 → E2 → E2 :=
      fun m n i x => phi m n x • d i x + f x i • grad m n x
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    ∃ q ∈ Ioo (r / 2) r,
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      (∀ m n : ℕ, ∀ i : Fin 2,
        (phi m n (unitCircleParameter (s - 2 * Real.arcsin (q / 2))) •
            liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
          phi m n (unitCircleParameter (s + 2 * Real.arcsin (q / 2))) •
            liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
        q * ∫ t in angles,
          inner ℝ ((disc 1).indicator (dp m n i)
            (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t))) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
          (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
  classical
  dsimp only
  let f0 : E2 → E2 := (disc 1).indicator f
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let phi : ℕ → ℕ → E2 → ℝ := fun m n x => x 0 ^ m * x 1 ^ n
  let grad : ℕ → ℕ → E2 → E2 := fun m n x =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j => fderiv ℝ (phi m n) x (coordinateVector 2 j))
  let dp : ℕ → ℕ → Fin 2 → E2 → E2 :=
    fun m n i x => phi m n x • d i x + f x i • grad m n x
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let B : ℝ → Prop := fun q => ∀ m n : ℕ, ∀ i : Fin 2,
    (phi m n (unitCircleParameter (s - 2 * Real.arcsin (q / 2))) •
        liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
      phi m n (unitCircleParameter (s + 2 * Real.arcsin (q / 2))) •
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
    q * ∫ t in angles,
      inner ℝ ((disc 1).indicator (dp m n i)
        (unitCircleParameter s + q • unitCircleParameter t)) (J (unitCircleParameter t))
  have hb : Continuous (liftedBoundaryValue Ω theta) :=
    Ω.boundary.smooth.continuous.comp lift.2.1
  have hp : Periodic (liftedBoundaryValue Ω theta) (2 * Real.pi) := by
    intro t
    change Ω.boundary.gamma (theta (t + 2 * Real.pi)) = Ω.boundary.gamma (theta t)
    rw [lift.2.2.2]
    rcases lift.1 with hσ | hσ
    · simpa only [hσ, one_mul] using Ω.boundary.periodic (theta t)
    · simpa only [hσ, neg_one_mul, sub_eq_add_neg] using Ω.boundary.periodic.sub_eq (theta t)
  have hH1 := minimum.admissible.1
  have hra : 0 < r / 2 := by positivity
  have hrab : r / 2 < r := by linarith
  have hr1 : r < 1 := by linarith
  let boundary := liftedBoundaryValue Ω theta
  let radiusLow := r / 2
  let center := unitCircleParameter s
  have hBm : ∀ m n : ℕ, ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r),
      ∀ i : Fin 2,
        (phi m n (unitCircleParameter (s - 2 * Real.arcsin (q / 2))) •
            liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
          phi m n (unitCircleParameter (s + 2 * Real.arcsin (q / 2))) •
            liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
        q * ∫ t in angles,
          inner ℝ ((disc 1).indicator (dp m n i)
            (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t)) := by
    intro m n
    let poly := phi m n
    have hpoly : ContDiff ℝ ∞ poly := by dsimp [poly, phi]; fun_prop
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".original_weighted_circle_flux_ae_v411") | throwError "polynomial Green flux receipt missing"
      let names := [`f, `d, `boundary, `hH1, `trace, `hb, `hp, `poly, `hpoly,
        `s, `radiusLow, `r, `hra, `hrab, `hr1]
      let args ← names.toArray.mapM fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none
      Lean.Elab.Tactic.closeMainGoal `original_polynomial_flux (Lean.mkAppN (Lean.mkConst name) args)
  have hB : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), B q := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro n
    exact hBm m n
  let L (i : Fin 2) : ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 i)
  have hF : MemLp f 2 (volume.restrict (disc 1)) := by
    have h0 := ((hH1 0).2.1).continuousLinearMap_comp (L 0)
    have h1 := ((hH1 1).2.1).continuousLinearMap_comp (L 1)
    have he : (fun z => L 0 (f z 0) + L 1 (f z 1)) = f := by
      funext z
      ext i
      fin_cases i <;> simp [L, coordinateVector, EuclideanSpace.single]
    exact he ▸ h0.add h1
  have hpolarF := CourantAnalyticB.native_translated_polar_rows (fun _ => f)
    (fun _ => hF.aestronglyMeasurable) (fun _ => hF) (unitCircleParameter s)
    (r / 2) r (by positivity) (by linarith) (by linarith)
  dsimp only at hpolarF
  let P : ℝ → Prop := fun q =>
    MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
      (volume.restrict angles) ∧ B q
  have hP : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), P q := by
    filter_upwards [hpolarF.2.2.1, hB] with q hq hqb
    exact ⟨(hq.1 0).2.1, hqb⟩
  have hselected : ∃ q ∈ Ioo (r / 2) r, P q ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
          (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".original_cap_good_shell_radius_with_ae_v411") | throwError "shell radius receipt missing"
      let args ← ([`R, `Ω, `M, `f, `d, `minimum].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      let center ← Lean.Elab.Term.elabTerm (Lean.mkIdent `center) none
      let tail ← ([`r, `hr, `hrhalf, `P, `hP].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      Lean.Elab.Tactic.closeMainGoal `original_selected_polynomial_trace
        (Lean.mkAppN (Lean.mkConst name) (args ++ #[center] ++ tail))
  obtain ⟨q, hq, hqp, hqd, hqe⟩ := hselected
  exact ⟨q, hq, hqp.1, hqd, hqp.2, hqe⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
