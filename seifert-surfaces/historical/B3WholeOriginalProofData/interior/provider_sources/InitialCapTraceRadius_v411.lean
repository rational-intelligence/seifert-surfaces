import InitialCapAERadius_v411
import CourantGreenChordFlux
set_option maxHeartbeats 0

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
open DirectMethod.CourantTraceFluxAssembly

/- This radius retains the literal original f and d slices, their L2 classes,
and the exact Green tangential flux. No representative or cap seam is assumed. -/
private theorem original_cap_trace_radius_v411
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2) :
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let f0 : E2 → E2 := (disc 1).indicator f
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    ∃ q ∈ Ioo (r / 2) r,
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      (∀ i, (liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
          liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
        q * ∫ t in angles,
          inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t))) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
          (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
  classical
  dsimp only
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let f0 : E2 → E2 := (disc 1).indicator f
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let U : Set ℝ := Ioo (r / 2) r
  let L (i : Fin 2) : ℝ →L[ℝ] E2 :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (coordinateVector 2 i)
  have hF : MemLp f 2 (volume.restrict (disc 1)) := by
    have h0 := ((minimum.admissible.1 0).2.1).continuousLinearMap_comp (L 0)
    have h1 := ((minimum.admissible.1 1).2.1).continuousLinearMap_comp (L 1)
    have he : (fun z => L 0 (f z 0) + L 1 (f z 1)) = f := by
      funext z
      ext i
      fin_cases i <;> simp [L, coordinateVector, EuclideanSpace.single]
    exact he ▸ h0.add h1
  have hpolarF := CourantAnalyticB.native_translated_polar_rows (fun _ => f)
    (fun _ => hF.aestronglyMeasurable) (fun _ => hF) (unitCircleParameter s)
    (r / 2) r (by positivity) (by linarith) (by linarith)
  dsimp only at hpolarF
  have hFslices : ∀ᵐ q ∂volume.restrict U,
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) := by
    filter_upwards [hpolarF.2.2.1] with q hq
    exact (hq.1 0).2.1
  have hrows : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1)) :=
    fun i => (minimum.admissible.1 i).2.2
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
  have hflux := actual_green_chord_flux_ae f d (liftedBoundaryValue Ω theta)
    hrows trace hb hp s (r / 2) r (by positivity) (by linarith) (by linarith)
  dsimp only at hflux
  let P : ℝ → Prop := fun q =>
    MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
      (volume.restrict angles) ∧
    ∀ i, (liftedBoundaryValue Ω theta (s - 2 * Real.arcsin (q / 2)) -
        liftedBoundaryValue Ω theta (s + 2 * Real.arcsin (q / 2))) i =
      q * ∫ t in angles,
        inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
          (J (unitCircleParameter t))
  have hP : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), P q := by
    filter_upwards [hFslices, hflux] with q hq hqflux
    exact ⟨hq, hqflux⟩
  have hselected : ∃ q ∈ Ioo (r / 2) r, P q ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
          (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString ==
        "_private.InitialCapAERadius_v411.0.SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_good_shell_radius_with_ae_v411") |
          throwError "checked original shell-radius selector missing"
      let args ← ([`R, `Ω, `M, `f, `d, `minimum, `s].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let circle ← Lean.Elab.Term.elabTerm (Lean.mkIdent `unitCircleParameter) none
      let center := Lean.mkApp circle args[6]!
      let tail ← ([`r, `hr, `hrhalf, `P, `hP].toArray.mapM
        fun name => Lean.Elab.Term.elabTerm (Lean.mkIdent name) none)
      let base := args.extract 0 6
      Lean.Elab.Tactic.closeMainGoal `actual_trace_radius
        (Lean.mkAppN (Lean.mkConst name) (base ++ #[center] ++ tail))
  obtain ⟨q, hq, hqp, hqd, hqenergy⟩ := hselected
  exact ⟨q, hq, hqp.1, hqd, hqp.2, hqenergy⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
