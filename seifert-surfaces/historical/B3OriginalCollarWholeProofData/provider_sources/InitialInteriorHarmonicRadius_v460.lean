import InitialInteriorTangentialFlux_v460
import InitialLocalAllTestGreen_v460
import InitialHarmonicTests_v445
set_option maxHeartbeats 1000000

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_interior_zero" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorTangentialFlux_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_interior_weighted_tangential_flux_ae_v460)⟩

local macro "paid_all_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialLocalAllTestGreen_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_local_cap_green_all_tests_ae_v460)⟩

/- The actual minimizer, its original rows, and every centered harmonic Green test
are retained at ONE radius carrying the original shell-energy bound. -/
private theorem original_interior_harmonic_shell_radius_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (x:E2) (r:ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (inside : Metric.closedBall x r ⊆ disc 1) :
    let f0 : E2 → E2 := (disc 1).indicator f
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
      ![((((z 0 - x 0 : ℝ) : ℂ) +
          ((z 1 - x 1 : ℝ) : ℂ) * Complex.I) ^ n).re,
        ((((z 0 - x 0 : ℝ) : ℂ) +
          ((z 1 - x 1 : ℝ) : ℂ) * Complex.I) ^ n).im] k
    let grad : ℕ → Fin 2 → E2 → E2 := fun n k x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ (phi n k) x (coordinateVector 2 j))
    let dp : ℕ → Fin 2 → Fin 2 → E2 → E2 :=
      fun n k i x => phi n k x • d i x + f x i • grad n k x
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    ∃ q ∈ Ioo (r / 2) r,
      (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
        (∫ y in planarCap x q,f y i*fderiv ℝ psi y (coordinateVector 2 j)+d i y j*psi y)=
          (q*∫ t in angles,(disc 1).indicator (fun y=>f y i*psi y)
            (x+q•unitCircleParameter t)*unitCircleParameter t j)+
          ∫ t in circlePatch x q,liftedBoundaryValue Ω theta t i*psi (unitCircleParameter t)*unitCircleParameter t j) ∧
      MemLp (fun t => f0 (x + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (x + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      (∀ (n : ℕ) (k : Fin 2), ∀ i : Fin 2,
        0 =
        q * ∫ t in angles,
          inner ℝ ((disc 1).indicator (dp n k i)
            (x + q • unitCircleParameter t))
            (J (unitCircleParameter t))) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (x + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (x) r, euclideanJetDensity d z) -
          (∫ z in planarCap (x) (r / 2), euclideanJetDensity d z)) := by
  classical
  dsimp only
  let f0 : E2 → E2 := (disc 1).indicator f
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
      ![((((z 0 - x 0 : ℝ) : ℂ) +
          ((z 1 - x 1 : ℝ) : ℂ) * Complex.I) ^ n).re,
        ((((z 0 - x 0 : ℝ) : ℂ) +
          ((z 1 - x 1 : ℝ) : ℂ) * Complex.I) ^ n).im] k
  let grad : ℕ → Fin 2 → E2 → E2 := fun n k x =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j => fderiv ℝ (phi n k) x (coordinateVector 2 j))
  let dp : ℕ → Fin 2 → Fin 2 → E2 → E2 :=
    fun n k i x => phi n k x • d i x + f x i • grad n k x
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  let B : ℝ → Prop := fun q => ∀ (n : ℕ) (k : Fin 2), ∀ i : Fin 2,
    0 =
    q * ∫ t in angles,
      inner ℝ ((disc 1).indicator (dp n k i)
        (x + q • unitCircleParameter t)) (J (unitCircleParameter t))
  have hH1 := minimum.admissible.1
  have hra : 0 < r / 2 := by positivity
  have hrab : r / 2 < r := by linarith
  have hr1 : r < 1 := by linarith
  let boundary := liftedBoundaryValue Ω theta
  let radiusLow := r / 2
  let center := x
  have hBm : ∀ (n : ℕ) (k : Fin 2), ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r),
      ∀ i : Fin 2,
        0 =
        q * ∫ t in angles,
          inner ℝ ((disc 1).indicator (dp n k i)
            (x + q • unitCircleParameter t))
            (J (unitCircleParameter t)) := by
    intro n k
    let poly := phi n k
    have hpoly : ContDiff ℝ ∞ poly := by
      run_tac Lean.Elab.Tactic.withMainContext do
        let name := (Lean.Name.num `_private.InitialHarmonicTests_v445 0) ++
          `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.centered_complex_circle_power_tests_v445
        let xx ← Lean.Elab.Term.elabTerm (Lean.mkIdent `center) none
        let nn ← Lean.Elab.Term.elabTerm (Lean.mkIdent `n) none
        let kk ← Lean.Elab.Term.elabTerm (Lean.mkIdent `k) none
        let hp := Lean.mkAppN (Lean.mkConst name) #[xx, nn]
        let left ← Lean.Meta.mkAppM ``And.left #[hp]
        Lean.Elab.Tactic.closeMainGoal `harmonic_smooth (Lean.mkApp left kk)
    have hzflux := paid_interior_zero f d boundary hH1 trace center radiusLow r hra hrab hr1 inside poly hpoly
    filter_upwards [hzflux] with q hq
    intro i
    exact (hq i).symm
  have hB : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), B q := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro k
    exact hBm n k
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
    (fun _ => hF.aestronglyMeasurable) (fun _ => hF) (x)
    (r / 2) r (by positivity) (by linarith) (by linarith)
  dsimp only at hpolarF
  let Extra : ℝ → Prop := fun q=>∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
    (∫ y in planarCap x q,f y i*fderiv ℝ psi y (coordinateVector 2 j)+d i y j*psi y)=
      (q*∫ t in angles,(disc 1).indicator (fun y=>f y i*psi y)
        (x+q•unitCircleParameter t)*unitCircleParameter t j)+
      ∫ t in circlePatch x q,boundary t i*psi (unitCircleParameter t)*unitCircleParameter t j
  have hExtra : ∀ᵐ q ∂volume.restrict (Ioo (r/2) r),Extra q :=
    paid_all_green f d boundary hH1 trace (Ω.boundary.smooth.continuous.comp lift.2.1)
      x (r/2) r hra hrab hr1
  let P : ℝ → Prop := fun q =>
    MemLp (fun t => f0 (x + q • unitCircleParameter t)) 2
      (volume.restrict angles) ∧ B q ∧ Extra q
  have hP : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r), P q := by
    filter_upwards [hpolarF.2.2.1, hB,hExtra] with q hq hqb hqx
    exact ⟨(hq.1 0).2.1, hqb,hqx⟩
  have hselected : ∃ q ∈ Ioo (r / 2) r, P q ∧
      (∀ i, MemLp (fun t => d0 i (x + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      q ^ 2 * (∫ t in angles,
        euclideanJetDensity d0 (x + q • unitCircleParameter t)) ≤
        2 * ((∫ z in planarCap (x) r, euclideanJetDensity d z) -
          (∫ z in planarCap (x) (r / 2), euclideanJetDensity d z)) := by
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
  exact ⟨q, hq,hqp.2.2, hqp.1, hqd, hqp.2.1, hqe⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
