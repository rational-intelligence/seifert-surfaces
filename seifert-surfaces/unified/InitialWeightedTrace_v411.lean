import InitialGreenProduct_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
open DirectMethod.CourantTraceFluxAssembly

/- Smooth multiplication turns the actual Green identity into a weighted
tangential slice identity. This retains the f term needed to identify the
artificial-circle trace, rather than only its total endpoint increment. -/
private theorem original_weighted_circle_flux_ae_v411
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun z => f z i) (d i))
    (green : HasGreenBoundaryTrace f d b)
    (hb : Continuous b) (period : Periodic b (2 * Real.pi))
    (phi : E2 → ℝ) (hphi : ContDiff ℝ ∞ phi)
    (s a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    let grad : E2 → E2 := fun x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ phi x (coordinateVector 2 j))
    let dp : Fin 2 → E2 → E2 := fun i x => phi x • d i x + f x i • grad x
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    ∀ᵐ q ∂volume.restrict (Ioo a z), ∀ i : Fin 2,
      (phi (unitCircleParameter (s - 2 * Real.arcsin (q / 2))) •
          b (s - 2 * Real.arcsin (q / 2)) -
        phi (unitCircleParameter (s + 2 * Real.arcsin (q / 2))) •
          b (s + 2 * Real.arcsin (q / 2))) i =
      q * ∫ t in Ioo (-Real.pi) Real.pi,
        inner ℝ ((disc 1).indicator (dp i)
          (unitCircleParameter s + q • unitCircleParameter t))
          (J (unitCircleParameter t)) := by
  classical
  dsimp only
  let grad : E2 → E2 := fun x =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun j => fderiv ℝ phi x (coordinateVector 2 j))
  let dp : Fin 2 → E2 → E2 := fun i x => phi x • d i x + f x i • grad x
  let bp : ℝ → E2 := fun t => phi (unitCircleParameter t) • b t
  have hrows : ∀ i, MemLp (dp i) 2 (volume.restrict (disc 1)) := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".native_H1_smooth_product_rows_L2_v411") | throwError "smooth product L2 receipt missing"
      let args ← ([`f, `d, `hH1, `phi, `hphi].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      Lean.Elab.Tactic.closeMainGoal `smooth_product_rows (Lean.mkAppN (Lean.mkConst name) args)
  have hgreen : HasGreenBoundaryTrace (fun x => phi x • f x) dp bp := by
    run_tac Lean.Elab.Tactic.withMainContext do
      let env ← Lean.getEnv
      let some (name, _) := env.constants.toList.find? (fun p => p.1.toString.endsWith
        ".native_green_smooth_product_v411") | throwError "smooth product Green receipt missing"
      let args ← ([`f, `d, `b, `green, `phi, `hphi].toArray.mapM
        fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
      Lean.Elab.Tactic.closeMainGoal `smooth_product_green (Lean.mkAppN (Lean.mkConst name) args)
  have hc : Continuous unitCircleParameter := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
    exact continuous_pi fun i : Fin 2 => by
      fin_cases i <;> simp [unitCircleParameter] <;> fun_prop
  have hbp : Continuous bp := (hphi.continuous.comp hc).smul hb
  have hperiod : Periodic bp (2 * Real.pi) := by
    intro t
    have hc : unitCircleParameter (t + 2 * Real.pi) = unitCircleParameter t := by
      ext i
      fin_cases i <;> simp [unitCircleParameter, Real.cos_add_two_pi, Real.sin_add_two_pi]
    simp only [bp, hc, period t]
  exact actual_green_chord_flux_ae (fun x => phi x • f x) dp bp
    hrows hgreen hbp hperiod s a z ha haz hz

/- The countable family is simultaneous at almost every radius, enabling
radius selection without any uncountable intersection of null sets. -/
private theorem original_polynomial_circle_flux_ae_v411
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun z => f z i) (d i))
    (green : HasGreenBoundaryTrace f d b)
    (hb : Continuous b) (period : Periodic b (2 * Real.pi))
    (s a z : ℝ) (ha : 0 < a) (haz : a < z) (hz : z < 1) :
    let phi : ℕ → ℕ → E2 → ℝ := fun m n x => x 0 ^ m * x 1 ^ n
    let grad : ℕ → ℕ → E2 → E2 := fun m n x =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => fderiv ℝ (phi m n) x (coordinateVector 2 j))
    let dp : ℕ → ℕ → Fin 2 → E2 → E2 :=
      fun m n i x => phi m n x • d i x + f x i • grad m n x
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    ∀ᵐ q ∂volume.restrict (Ioo a z), ∀ m n : ℕ, ∀ i : Fin 2,
      (phi m n (unitCircleParameter (s - 2 * Real.arcsin (q / 2))) •
          b (s - 2 * Real.arcsin (q / 2)) -
        phi m n (unitCircleParameter (s + 2 * Real.arcsin (q / 2))) •
          b (s + 2 * Real.arcsin (q / 2))) i =
      q * ∫ t in Ioo (-Real.pi) Real.pi,
        inner ℝ ((disc 1).indicator (dp m n i)
          (unitCircleParameter s + q • unitCircleParameter t))
          (J (unitCircleParameter t)) := by
  dsimp only
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro n
  exact original_weighted_circle_flux_ae_v411 f d b hH1 green hb period
    (fun x : E2 => x 0 ^ m * x 1 ^ n) (by fun_prop) s a z ha haz hz

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
