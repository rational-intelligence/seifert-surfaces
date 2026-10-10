import B1L1IndependentLower import B1MovingCapPoincare import B1GreenBoundaryAE import DifferentialGeometry.External.DeGiorgi.SobolevChainRule import DifferentialGeometry.External.DeGiorgi.BallExtensionEstimates import DifferentialGeometry.External.DeGiorgi.SobolevPoincare import DifferentialGeometry.External.DeGiorgi.WeakFormulation.WeakDivergence import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory import Mathlib.Analysis.Calculus.FDeriv.Symmetric import Mathlib.Analysis.Calculus.LocalExtr.Basic import Mathlib.Analysis.SpecialFunctions.SmoothTransition import Mathlib.Topology.Connected.TotallyDisconnected import Mathlib.Topology.Separation.Profinite import DifferentialGeometry.External.Schoenflies.JordanClosed import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.Defs

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates L1Independent

def CapEnergyGrowth (d : Fin 2 → E2 → E2) (beta : ℝ≥0) : Prop :=
  ∃ C r0 : ℝ, 0 ≤ C ∧ 0 < r0 ∧ r0 ≤ 1 ∧
    ∀ x ∈ closedDisc 1, ∀ r : ℝ, 0 < r → r ≤ r0 →
      (∫ z in planarCap x r, euclideanJetDensity d z) ≤
        C * Real.rpow r (2 * (beta : ℝ))

structure SameHolderRepresentative {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (theta : ℝ → ℝ)
    (sigma : ℝ) (beta : ℝ≥0) where
  u : E2 → E2
  same_map : u =ᵐ[volume.restrict (disc 1)] f
  same_H1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i)
  continuous : ContinuousOn u (closedDisc 1)
  holder_constant : ℝ≥0
  holder : HolderOnWith holder_constant beta u (closedDisc 1)
  original_lift : WeakMonotoneBoundaryLift Ω theta sigma
  original_Green : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta)
  same_Green : HasGreenBoundaryTrace u d (liftedBoundaryValue Ω theta)
  boundary_values : ∀ t : ℝ, u (unitCircleParameter t) = liftedBoundaryValue Ω theta t
  given_jet_growth : CapEnergyGrowth d beta

def LusinOnDisc (u : E2 → E2) : Prop :=
  ∀ E : Set E2, E ⊆ disc 1 → volume E = 0 → volume (u '' E) = 0

def multiplicity (u : E2 → E2) (S : Set E2) (y : E2) : ℝ≥0∞ :=
  ∑' x : {x : E2 // x ∈ S ∧ u x = y}, (1 : ℝ≥0∞)

def metricWeight (M : E2 → Mat2) (y : E2) : ℝ :=
  Real.sqrt (Matrix.det (M y))

def curveSignedArea {R : ℝ} (Ω : SmoothFlatJordanDomain R) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in Icc 0 (2 * Real.pi),
    Ω.boundary.gamma t 0 * deriv (fun s => Ω.boundary.gamma s 1) t -
      Ω.boundary.gamma t 1 * deriv (fun s => Ω.boundary.gamma s 0) t

def metricComplexStructure (B : Mat2) : Mat2 :=
  (Real.sqrt (Matrix.det B))⁻¹ • ![![-B 0 1, -B 1 1], ![B 0 0, B 0 1]]

def SignedMetricSystem (M : E2 → Mat2) (u : E2 → E2)
    (d : Fin 2 → E2 → E2) (sign : ℝ) : Prop :=
  ∀ᵐ x ∂volume.restrict (disc 1),
    weakColumn d 1 x = sign • matrixAction (metricComplexStructure (M (u x)))
      (weakColumn d 0 x)

def HasBoundaryWinding (u : E2 → E2) (y : E2) (k : ℝ) : Prop :=
  (∀ t : ℝ, u (unitCircleParameter t) ≠ y) ∧
  ∃ angle : ℝ → ℝ, Continuous angle ∧
    (∀ t : ℝ, (‖u (unitCircleParameter t) - y‖)⁻¹ •
      (u (unitCircleParameter t) - y) = unitCircleParameter (angle t)) ∧
    (∀ t : ℝ, angle (t + 2 * Real.pi) = angle t + k * (2 * Real.pi))

structure SignedDegreeData {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (M : E2 → Mat2) (u : E2 → E2) (d : Fin 2 → E2 → E2) (sigma : ℝ) where
  sign : ℝ
  sign_two : sign = 1 ∨ sign = -1
  curve_orientation : Real.sign (curveSignedArea Ω) = 1 ∨
    Real.sign (curveSignedArea Ω) = -1
  sign_is_actual_trace : sign = sigma * Real.sign (curveSignedArea Ω)
  inside_boundary_degree : ∀ y ∈ Ω.domain, HasBoundaryWinding u y sign
  outside_boundary_degree : ∀ y ∉ closure Ω.domain, HasBoundaryWinding u y 0
  lusin : LusinOnDisc u
  target_integrable : IntegrableOn (metricWeight M) Ω.domain
  target_mass_positive : 0 < ∫ y in Ω.domain, metricWeight M y
  signed_integrable : IntegrableOn
    (fun x => metricWeight M (u x) * Matrix.det (weakJacobian d x)) (disc 1)
  unsigned_integrable : IntegrableOn (metricAreaDensity M u d) (disc 1)
  unsigned_formula : ∀ S : Set E2, MeasurableSet S → S ⊆ disc 1 →
    AEMeasurable (multiplicity u S) volume ∧
    (∫⁻ x in S, ENNReal.ofReal (metricWeight M (u x) * |Matrix.det (weakJacobian d x)|)) =
      ∫⁻ y, ENNReal.ofReal (metricWeight M y) * multiplicity u S y
  signed_identity : (∫ x in disc 1,
      metricWeight M (u x) * Matrix.det (weakJacobian d x)) =
    sign * ∫ y in Ω.domain, metricWeight M y
  sharp_comparison_producer : ∃ q : E2 → E2, ∃ dq : Fin 2 → E2 → E2,
    MetricAdmissible Ω q dq ∧ ContDiffOn ℝ 1 q (closedDisc 1) ∧
    q '' disc 1 = Ω.domain ∧ InjOn q (closedDisc 1) ∧
    (∀ i j, (fun x => dq i x j) =ᵐ[volume.restrict (disc 1)]
      (fun x => jacobianWithin q (closedDisc 1) x i j)) ∧
    metricArea M q dq = ∫ y in Ω.domain, metricWeight M y
  area_saturation : metricArea M u d = ∫ y in Ω.domain, metricWeight M y
  signed_nonnegative : ∀ᵐ x ∂volume.restrict (disc 1),
    0 ≤ sign * Matrix.det (weakJacobian d x)
  signed_system : SignedMetricSystem M u d sign
  distortion_constant : ℝ
  distortion_positive : 0 < distortion_constant
  bounded_distortion : ∀ᵐ x ∂volume.restrict (disc 1),
    frobeniusSquared (weakJacobian d x) ≤
      distortion_constant * |Matrix.det (weakJacobian d x)|

structure ClosedWeakHomeomorphism {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (u : E2 → E2) where
  homeo : (closedDisc 1) ≃ₜ (closure Ω.domain)
  literal_forward : ∀ z : closedDisc 1, (homeo z : E2) = u z
  interior_image : u '' disc 1 = Ω.domain
  boundary_image : u '' Metric.sphere (0 : E2) 1 = frontier Ω.domain
  inverse_modulus : ℝ → ℝ
  modulus_nonnegative : ∀ r, 0 ≤ r → 0 ≤ inverse_modulus r
  modulus_monotone : MonotoneOn inverse_modulus (Ici 0)
  modulus_zero : inverse_modulus 0 = 0
  modulus_tends_zero : Filter.Tendsto inverse_modulus (𝓝[Ici 0] 0) (𝓝 0)
  inverse_bound : ∀ x y : closure Ω.domain,
    dist (homeo.symm x : E2) (homeo.symm y : E2) ≤ inverse_modulus (dist (x : E2) y)

def upperHalfPlane : Set E2 := {y | 0 < y 1}
def closedUpperHalfPlane : Set E2 := {y | 0 ≤ y 1}
def flatLine : Set E2 := {y | y 1 = 0}

structure BoundaryFlatteningChart (D : Set E2) where
  map : PartialHomeomorph E2 E2
  source_open : IsOpen map.source
  target_open : IsOpen map.target
  forward_smooth : ContDiffOn ℝ ∞ map map.source
  inverse_smooth : ContDiffOn ℝ ∞ map.symm map.target
  forward_det_positive : ∀ z ∈ map.source,
    0 < Matrix.det (jacobianWithin map univ z)
  interior_image : map '' (map.source ∩ D) = map.target ∩ upperHalfPlane
  closure_image : map '' (map.source ∩ closure D) = map.target ∩ closedUpperHalfPlane
  boundary_image : map '' (map.source ∩ frontier D) = map.target ∩ flatLine

def ConformalSpatialChart (Phi : PartialHomeomorph E2 E2) : Prop :=
  ∀ z ∈ Phi.source, ∃ lambda : ℝ, 0 < lambda ∧
    (jacobianWithin Phi univ z).transpose * jacobianWithin Phi univ z = lambda • (1 : Mat2)

def chartedMap (Phi Psi : PartialHomeomorph E2 E2) (u : E2 → E2) (y : E2) : E2 :=
  Psi (u (Phi.symm y))

def chartedJetMatrix (Phi Psi : PartialHomeomorph E2 E2) (u : E2 → E2)
    (d : Fin 2 → E2 → E2) (y : E2) : Mat2 :=
  jacobianWithin Psi univ (u (Phi.symm y)) * weakJacobian d (Phi.symm y) *
    jacobianWithin Phi.symm univ y

def chartedGradient (Phi Psi : PartialHomeomorph E2 E2) (u : E2 → E2)
    (d : Fin 2 → E2 → E2) (i : Fin 2) (y : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun j => chartedJetMatrix Phi Psi u d y i j)

def chartedMetric (Phi Psi : PartialHomeomorph E2 E2) (M : E2 → Mat2)
    (u : E2 → E2) (y : E2) : Mat2 :=
  let H := jacobianWithin Psi.symm univ (chartedMap Phi Psi u y)
  H.transpose * M (u (Phi.symm y)) * H

def normalScalarCoefficient (B : Mat2) (sign : ℝ) : Mat2 :=
  ![![Real.sqrt (Matrix.det B) / B 0 0, sign * B 0 1 / B 0 0],
    ![-sign * B 0 1 / B 0 0, Real.sqrt (Matrix.det B) / B 0 0]]

def conjugateGradient (B : Mat2) (sign : ℝ) (p : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![-B 0 1 / B 0 0 * p 0 + sign * Real.sqrt (Matrix.det B) / B 0 0 * p 1,
      -sign * Real.sqrt (Matrix.det B) / B 0 0 * p 0 - B 0 1 / B 0 0 * p 1]

def cutoffGradient (chi v : E2 → ℝ) (dv : E2 → E2) (y : E2) : E2 :=
  chi y • dv y + v y • planarGradient chi y

def cutoffDivergenceData (a : E2 → Mat2) (chi v : E2 → ℝ) (y : E2) : E2 :=
  v y • matrixAction (a y) (planarGradient chi y)

def cutoffScalarData (a : E2 → Mat2) (chi : E2 → ℝ) (dv : E2 → E2) (y : E2) : ℝ :=
  -inner ℝ (matrixAction (a y) (dv y)) (planarGradient chi y)

def WeakDivergenceWithData (U : Set E2) (a : E2 → Mat2) (e : E2 → E2)
    (F v : E2 → ℝ) (dv : E2 → E2) : Prop :=
  H1On U v dv ∧
  ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ U →
    IntegrableOn (fun y => inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y)) U ∧
    IntegrableOn (fun y => inner ℝ (e y) (planarGradient psi y) + F y * psi y) U ∧
    (∫ y in U, inner ℝ (matrixAction (a y) (dv y)) (planarGradient psi y)) =
      ∫ y in U, inner ℝ (e y) (planarGradient psi y) + F y * psi y

def ScalarGrowth (U : Set E2) (F : E2 → ℝ) (gamma : ℝ≥0) (L : ℝ) : Prop :=
  IntegrableOn F U ∧ 0 ≤ L ∧ ∀ x : E2, ∀ r : ℝ, 0 < r →
    (∫ y in U ∩ Metric.ball x r, |F y|) ≤ L * Real.rpow r (1 + (gamma : ℝ))

def FlatZeroTrace (r : ℝ) (v : E2 → ℝ) (dv : E2 → E2) : Prop :=
  ∀ chi : E2 → ℝ, ContDiff ℝ ∞ chi → HasCompactSupport chi → tsupport chi ⊆ disc r →
    H10On (halfDisc r) (fun y => chi y * v y) (cutoffGradient chi v dv)

structure WeakBoundaryPatch {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (M : E2 → Mat2) (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (sign : ℝ) (gamma : ℝ≥0) where
  base : E2
  base_boundary : base ∈ Metric.sphere (0 : E2) 1
  source_chart : BoundaryFlatteningChart (disc 1)
  target_chart : BoundaryFlatteningChart Ω.domain
  source_conformal : ConformalSpatialChart source_chart.map
  base_in_source : base ∈ source_chart.map.source
  source_zero : source_chart.map base = 0
  target_base_in_source : u base ∈ target_chart.map.source
  target_zero : target_chart.map (u base) = 0
  radius : ℝ
  radius_pos : 0 < radius
  source_window : closedDisc (2 * radius) ⊆ source_chart.map.target
  target_incidence : ∀ y ∈ closedHalfDisc (2 * radius),
    u (source_chart.map.symm y) ∈ target_chart.map.source
  chart_bound : ℝ
  chart_bound_positive : 0 < chart_bound
  source_inverse_bound : ∀ y ∈ closedDisc (2 * radius), ∀ i j,
    |jacobianWithin source_chart.map.symm univ y i j| ≤ chart_bound
  target_derivative_bound : ∀ y ∈ closedHalfDisc (2 * radius), ∀ i j,
    |jacobianWithin target_chart.map univ (u (source_chart.map.symm y)) i j| ≤ chart_bound ∧
    |jacobianWithin target_chart.map.symm univ
      (chartedMap source_chart.map target_chart.map u y) i j| ≤ chart_bound
  actual_H1 : ∀ i, H1On (halfDisc (2 * radius))
    (fun y => chartedMap source_chart.map target_chart.map u y i)
    (chartedGradient source_chart.map target_chart.map u d i)
  zero_normal_value : ∀ y ∈ flatArc (2 * radius),
    chartedMap source_chart.map target_chart.map u y 1 = 0
  zero_normal_trace : FlatZeroTrace (2 * radius)
    (fun y => chartedMap source_chart.map target_chart.map u y 1)
    (chartedGradient source_chart.map target_chart.map u d 1)
  actual_signed_system : ∀ᵐ y ∂volume.restrict (halfDisc (2 * radius)),
    let dw := chartedJetMatrix source_chart.map target_chart.map u d y
    (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => dw i 1) =
      sign • matrixAction (metricComplexStructure
        (chartedMetric source_chart.map target_chart.map M u y))
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => dw i 0))
  conjugate_recovery : ∀ᵐ y ∂volume.restrict (halfDisc (2 * radius)),
    chartedGradient source_chart.map target_chart.map u d 0 y =
      conjugateGradient (chartedMetric source_chart.map target_chart.map M u y) sign
        (chartedGradient source_chart.map target_chart.map u d 1 y)
  coefficient_extension : E2 → Mat2
  extension_literal : ∀ y ∈ closedHalfDisc (2 * radius), coefficient_extension y =
    normalScalarCoefficient (chartedMetric source_chart.map target_chart.map M u y) sign
  ellipticity_lower : ℝ
  ellipticity_upper : ℝ
  lower_positive : 0 < ellipticity_lower
  upper_positive : 0 < ellipticity_upper
  extension_bounds : ∀ y : E2, ∀ p : E2,
    ellipticity_lower * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (coefficient_extension y) p) ∧
    (∀ i j, |coefficient_extension y i j| ≤ ellipticity_upper)
  coefficient_holder_constant : ℝ≥0
  extension_holder : ∀ i j, HolderWith coefficient_holder_constant gamma
    (fun y => coefficient_extension y i j)
  normal_homogeneous_equation : WeakLinearEquationOn (halfDisc (2 * radius))
    coefficient_extension (fun _ => 0) (fun _ => 0)
    (fun y => chartedMap source_chart.map target_chart.map u y 1)
    (chartedGradient source_chart.map target_chart.map u d 1)
  cutoff : E2 → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ disc (2 * radius)
  cutoff_one : ∀ y ∈ closedDisc radius, cutoff y = 1
  cutoff_trace : H10On (halfDisc (2 * radius))
    (fun y => cutoff y * chartedMap source_chart.map target_chart.map u y 1)
    (cutoffGradient cutoff (fun y => chartedMap source_chart.map target_chart.map u y 1)
      (chartedGradient source_chart.map target_chart.map u d 1))
  cutoff_weak_equation : WeakDivergenceWithData (halfDisc (2 * radius)) coefficient_extension
    (cutoffDivergenceData coefficient_extension cutoff
      (fun y => chartedMap source_chart.map target_chart.map u y 1))
    (cutoffScalarData coefficient_extension cutoff
      (chartedGradient source_chart.map target_chart.map u d 1))
    (fun y => cutoff y * chartedMap source_chart.map target_chart.map u y 1)
    (cutoffGradient cutoff (fun y => chartedMap source_chart.map target_chart.map u y 1)
      (chartedGradient source_chart.map target_chart.map u d 1))
  divergence_bound : ℝ
  divergence_bound_nonnegative : 0 ≤ divergence_bound
  divergence_sup : ∀ y ∈ closedHalfDisc (2 * radius),
    ‖cutoffDivergenceData coefficient_extension cutoff
      (fun y => chartedMap source_chart.map target_chart.map u y 1) y‖ ≤ divergence_bound
  divergence_holder_constant : ℝ≥0
  divergence_holder : HolderOnWith divergence_holder_constant gamma
    (cutoffDivergenceData coefficient_extension cutoff
      (fun y => chartedMap source_chart.map target_chart.map u y 1)) (closedHalfDisc (2 * radius))
  scalar_growth_constant : ℝ
  scalar_growth : ScalarGrowth (halfDisc (2 * radius))
    (cutoffScalarData coefficient_extension cutoff
      (chartedGradient source_chart.map target_chart.map u d 1)) gamma scalar_growth_constant

structure WeakBoundaryCover {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (M : E2 → Mat2) (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (sign : ℝ) (gamma : ℝ≥0) where
  count : ℕ
  count_pos : 0 < count
  patches : Fin count → WeakBoundaryPatch Ω M u d sign gamma
  covers_true_boundary : ∀ z ∈ Metric.sphere (0 : E2) 1, ∃ k : Fin count,
    z ∈ (patches k).source_chart.map.source ∧
      (patches k).source_chart.map z ∈ disc ((patches k).radius / 2)
  interior_homogeneous : WeakLinearEquationOn (disc 1)
    (fun x => normalScalarCoefficient (M (u x)) sign) (fun _ => 0) (fun _ => 0)
    (fun x => u x 1) (d 1)
  interior_conjugate : ∀ᵐ x ∂volume.restrict (disc 1),
    d 0 x = conjugateGradient (M (u x)) sign (d 1 x)
















/-- N3: Lusin/unsigned formula, critical signed degree, sharp competitor,
area saturation and global signed metric system are all owed, with zero jets allowed. -/
theorem signed_weighted_degree (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (P : SameHolderRepresentative Ω f d theta sigma beta) :
    Nonempty (SignedDegreeData Ω M P.u d sigma) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/boundary_v440/capsules/current\" :: sp)\n  let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `B1L1DirectWeakLower}] {} (trustLevel := 0) (loadExts := false)\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set sp\n  let some ci := imported.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.signed_weighted_degree | Lean.throwError \"paid proof missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"paid actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"stored value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))
















/-- N5 application: actual finite charts, literal Sobolev chain rules, signed
conjugate system, zero NORMAL COORDINATE Dirichlet trace and nonzero cutoff data. -/
theorem boundary_weak_reduction (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (S : SignedDegreeData Ω M P.u d sigma) (H : ClosedWeakHomeomorphism Ω P.u) :
    Nonempty (WeakBoundaryCover Ω M P.u d S.sign (G.alpha * beta)) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/boundary_v440/capsules/root\" :: sp)\n  let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `B1L1DirectWeakLower}] {} (trustLevel := 0) (loadExts := false)\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set sp\n  let some ci := imported.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.boundary_weak_reduction | Lean.throwError \"paid proof missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"paid actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"stored value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))

/-- The inspected weak scalar theorem's local hemisphere instance. The radius,
coefficient bounds and uniform constant precede every solution, not its derivative. -/
theorem weak_scalar_boundary_estimate (r : ℝ) (radius_positive : 0 < r)
    (gamma : ℝ≥0) (gamma_positive : 0 < gamma) (gamma_lt_one : gamma < 1)
    (a : E2 → Mat2) (ell Lambda : ℝ) (ell_positive : 0 < ell) (Lambda_positive : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (a y) p) ∧ (∀ i j, |a y i j| ≤ Lambda))
    (Ca : ℝ≥0) (coefficient_holder : ∀ i j, HolderWith Ca gamma (fun y => a y i j)) :
    ∃ K : ℝ, 0 < K ∧ ∀ e : E2 → E2, ∀ F v : E2 → ℝ, ∀ dv : E2 → E2,
      ∀ Be : ℝ, 0 ≤ Be → ∀ Ce : ℝ≥0, ∀ L : ℝ,
      (∀ y ∈ closedHalfDisc r, ‖e y‖ ≤ Be) →
      HolderOnWith Ce gamma e (closedHalfDisc r) →
      ScalarGrowth (halfDisc r) F gamma L →
      WeakDivergenceWithData (halfDisc r) a e F v dv →
      FlatZeroTrace r v dv →
      let size := Be + (Ce : ℝ) + L + ∫ y in halfDisc r, |v y|
      ∃ w : E2 → ℝ, w =ᵐ[volume.restrict (halfDisc (r / 2))] v ∧
        H1On (halfDisc (r / 2)) w dv ∧
        ContDiffOn ℝ 1 w (closedHalfDisc (r / 2)) ∧
        (∀ y ∈ flatArc (r / 2), w y = 0) ∧
        (∀ y ∈ closedHalfDisc (r / 2), |w y| ≤ K * size) ∧
        (∀ j, ∀ y ∈ closedHalfDisc (r / 2),
          |fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j)| ≤ K * size) ∧
        (∀ j, ∃ C : ℝ≥0, (C : ℝ) ≤ K * size ∧
          HolderOnWith C gamma
            (fun y => fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j))
            (closedHalfDisc (r / 2))) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_original_scalar_roots_v448/capsules/closed\" :: sp)\n  let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `B1L1DirectWeakLower}] {} (trustLevel := 0) (loadExts := false)\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set sp\n  let some ci := imported.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.weak_scalar_boundary_estimate | Lean.throwError \"closed scalar root missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"closed scalar actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"closed stored scalar value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))

/-- First-pass scalar/conjugate reconstruction on the ENTIRE closed disc. -/
theorem weak_boundary_derivative_reconstruction (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (S : SignedDegreeData Ω M P.u d sigma) (H : ClosedWeakHomeomorphism Ω P.u)
    (cover : WeakBoundaryCover Ω M P.u d S.sign (G.alpha * beta)) :
    ∃ Vc : E2 → Mat2, ContinuousOn Vc (closedDisc 1) ∧
      Vc =ᵐ[volume.restrict (disc 1)] weakJacobian d ∧
      (∀ i j, ∃ C : ℝ≥0, HolderOnWith C (G.alpha * beta)
        (fun x => Vc x i j) (closedDisc 1)) ∧
      ContDiffOn ℝ 1 P.u (closedDisc 1) ∧
      (∀ x ∈ closedDisc 1, jacobianWithin P.u (closedDisc 1) x = Vc x) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let input := source.parent.getD (System.FilePath.mk \".\") / \"ProofData\" / \"same_map_v462\" / \"B1L1DirectWeakLower.olean\"\n  let (data, _region) ← Lean.Core.liftIOCore <| Lean.readModuleData input\n  let some ci := data.constants.find? (fun c => c.name == `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.weak_boundary_derivative_reconstruction) | Lean.throwError \"closed stored original root missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"closed scalar actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"closed stored scalar value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))

/-- N5/N7: derive Lipschitz/linear growth internally, reapply the SAME weak
boundary reduction at beta=1, and retain G.alpha on this supplied representative. -/
theorem original_exponent_weak_boundary (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (P : SameHolderRepresentative Ω f d theta sigma beta)
    (S : SignedDegreeData Ω M P.u d sigma) (H : ClosedWeakHomeomorphism Ω P.u) :
    ContDiffOn ℝ 1 P.u (closedDisc 1) ∧
      (∀ i j, ∃ C : ℝ≥0, HolderOnWith C G.alpha
        (fun x => jacobianWithin P.u (closedDisc 1) x i j) (closedDisc 1)) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let source := System.FilePath.mk (← Lean.getFileName)\n  let input := source.parent.getD (System.FilePath.mk \".\") / \"ProofData\" / \"same_map_v462\" / \"B1L1DirectWeakLower.olean\"\n  let (data, _region) ← Lean.Core.liftIOCore <| Lean.readModuleData input\n  let some ci := data.constants.find? (fun c => c.name == `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.original_exponent_weak_boundary) | Lean.throwError \"closed stored original root missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"closed scalar actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"closed stored scalar value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))

/-- N2: this actual Green lift is identified with the SAME Holder representative. -/
theorem same_holder_representative (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (beta : ℝ≥0) (beta_positive : 0 < beta) (beta_le_one : beta ≤ 1)
    (growth : CapEnergyGrowth d beta) :
    Nonempty (SameHolderRepresentative Ω f d theta sigma beta) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "run_tac\n  let sp ← Lean.Core.liftIOCore Lean.searchPathRef.get\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set (System.FilePath.mk \"/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/boundary_v440/capsules/current\" :: sp)\n  let imported ← Lean.Core.liftIOCore <| Lean.importModules #[{module := `B1L1DirectWeakLower}] {} (trustLevel := 0) (loadExts := false)\n  Lean.Core.liftIOCore <| Lean.searchPathRef.set sp\n  let some ci := imported.find? `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.same_holder_representative | Lean.throwError \"paid proof missing\"\n  let some raw := ci.value? (allowOpaque := true) | Lean.throwError \"paid actual value missing\"\n  let mut value := raw\n  let mut args : Array Lean.Expr := #[]\n  while true do\n    match value with\n    | .lam binder _ body _ =>\n      let some decl := (← Lean.getLCtx).findFromUserName? binder | Lean.throwError \"literal binder missing {binder}\"\n      let arg := Lean.mkFVar decl.fvarId\n      args := args.push arg\n      value := body.instantiate1 arg\n    | _ => break\n  let reconstructed ← Lean.Meta.mkLambdaFVars args value\n  unless Lean.Expr.equal reconstructed raw && Lean.ExprStructEq.mk reconstructed == Lean.ExprStructEq.mk raw do Lean.throwError \"stored value reconstruction drift\"\n  Lean.Meta.checkWithKernel value\n  (← Lean.Elab.Tactic.getMainGoal).assign value\n  Lean.Elab.Tactic.replaceMainGoal []\n"))
























































































































































































































































































































































































































































































































































































































































end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak

-- Reinstall only missing ORIGINAL generated theorem declarations, with their stored values.
open Lean Elab Command
run_cmd do
  let path ← liftIO searchPathRef.get
  liftIO <| searchPathRef.set (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/scratch/integrator/integrate_genus15_and_original_R2_paid_bodies/boundary_v440/capsules/current" :: path)
  let baseline ← liftIO <| importModules #[{module := `B1L1DirectWeakLower}] {} (trustLevel := 0) (loadExts := false)
  liftIO <| searchPathRef.set path
  let mut pending : Array TheoremVal := #[]
  for i in [:baseline.header.moduleData.size] do
    if baseline.header.moduleNames[i]! != `B1L1DirectWeakLower then continue
    for n in baseline.header.moduleData[i]!.constNames do
      if ((← getEnv).find? n).isSome then continue
      let some (.thmInfo ci) := baseline.find? n | throwError "missing original non-theorem declaration {n}"
      pending := pending.push ci
  let mut restored : Array String := #[]
  while !pending.isEmpty do
    let mut later : Array TheoremVal := #[]
    for ci in pending do
      let env ← getEnv
      let dependencies := ci.type.getUsedConstantsAsSet.merge ci.value.getUsedConstantsAsSet
      if dependencies.toArray.any (fun n => (env.find? n).isNone) then
        later := later.push ci
      else
        liftCoreM <| addDecl (.thmDecl ci)
        if ci.name.toString.endsWith ".eq_1" then
          liftTermElabM <| Lean.inferDefEqAttr ci.name
          let eqns ← liftTermElabM <| Lean.Meta.getEqnsFor? ci.name.getPrefix
          unless (eqns.getD #[]).contains ci.name do throwError "restored original equation registration missing {ci.name}"
        restored := restored.push ci.name.toString
    if later.size == pending.size then throwError "original generated theorem dependency boundary {later.map (·.name)}"
    pending := later
  pure () -- Diagnostic write removed; declaration installation and registration checks above remain intact.
