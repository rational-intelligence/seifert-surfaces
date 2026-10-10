import B1GlobalInverseMetric

noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

/-- Literal weak Jacobian: row i is the supplied weak gradient of coordinate i. -/
def weakJacobian (d : Fin 2 → E2 → E2) (x : E2) : Mat2 := fun i j => d i x j

def weakColumn (d : Fin 2 → E2 → E2) (j : Fin 2) (x : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i => d i x j)

/-- Unit circle, outward normal and unit-speed boundary parameter. -/
def unitCircleParameter (t : ℝ) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos t, Real.sin t]

/-- A degree +1 or -1 continuous weakly monotone lift; no pointwise condition on f. -/
def WeakMonotoneBoundaryLift {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (theta : ℝ → ℝ) (orientation : ℝ) : Prop :=
  (orientation = 1 ∨ orientation = -1) ∧ Continuous theta ∧
  Monotone (fun t => orientation * theta t) ∧
  (∀ t, theta (t + 2 * Real.pi) = theta t + orientation * (2 * Real.pi))

def liftedBoundaryValue {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (theta : ℝ → ℝ) (t : ℝ) : E2 := Ω.boundary.gamma (theta t)

/-- Coordinatewise Green identity for the Sobolev trace on the unit disc.
Globally smooth scalar tests need not have support in the disc. -/
def HasGreenBoundaryTrace (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (b : ℝ → E2) : Prop :=
  ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
    IntegrableOn (fun x => f x i * fderiv ℝ psi x (coordinateVector 2 j) +
      d i x j * psi x) (disc 1) ∧
    IntegrableOn (fun t => b t i * psi (unitCircleParameter t) *
      (unitCircleParameter t) j) (Icc 0 (2 * Real.pi)) ∧
    (∫ x in disc 1, f x i * fderiv ℝ psi x (coordinateVector 2 j) +
      d i x j * psi x) =
      ∫ t in Icc 0 (2 * Real.pi), b t i * psi (unitCircleParameter t) *
        (unitCircleParameter t) j

/-- Full C(Gamma) class: H1 coordinates and continuous weakly monotone Sobolev
trace. No continuity, C1, radial representative, conformality or chart field. -/
def MetricAdmissible {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (f : E2 → E2) (d : Fin 2 → E2 → E2) : Prop :=
  (∀ i, H1On (disc 1) (fun x => f x i) (d i)) ∧
  ∃ theta : ℝ → ℝ, ∃ orientation : ℝ,
    WeakMonotoneBoundaryLift Ω theta orientation ∧
    HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta)

def metricE (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (x : E2) : ℝ :=
  inner ℝ (weakColumn d 0 x) (matrixAction (M (f x)) (weakColumn d 0 x))
def metricF (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (x : E2) : ℝ :=
  inner ℝ (weakColumn d 0 x) (matrixAction (M (f x)) (weakColumn d 1 x))
def metricH (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (x : E2) : ℝ :=
  inner ℝ (weakColumn d 1 x) (matrixAction (M (f x)) (weakColumn d 1 x))

def metricAreaDensity (M : E2 → Mat2) (f : E2 → E2)
    (d : Fin 2 → E2 → E2) (x : E2) : ℝ :=
  Real.sqrt (Matrix.det (M (f x))) * |Matrix.det (weakJacobian d x)|
def metricDirichletDensity (M : E2 → Mat2) (f : E2 → E2)
    (d : Fin 2 → E2 → E2) (x : E2) : ℝ := metricE M f d x + metricH M f d x

def metricArea (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2) : ℝ :=
  ∫ x in disc 1, metricAreaDensity M f d x
def metricDirichlet (M : E2 → Mat2) (f : E2 → E2)
    (d : Fin 2 → E2 → E2) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in disc 1, metricDirichletDensity M f d x

/-- Same-map simultaneous minimum and weak metric conformality; no regularity premise. -/
structure SimultaneousMetricMinimum {R : ℝ} (Ω : SmoothFlatJordanDomain R)
    (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2) : Prop where
  admissible : MetricAdmissible Ω f d
  area_integrable : IntegrableOn (metricAreaDensity M f d) (disc 1)
  dirichlet_integrable : IntegrableOn (metricDirichletDensity M f d) (disc 1)
  area_minimum : ∀ f' d', MetricAdmissible Ω f' d' →
    metricArea M f d ≤ metricArea M f' d'
  dirichlet_minimum : ∀ f' d', MetricAdmissible Ω f' d' →
    metricDirichlet M f d ≤ metricDirichlet M f' d'
  weak_conformality : ∀ᵐ x ∂volume.restrict (disc 1),
    metricE M f d x = metricH M f d x ∧ metricF M f d x = 0

/-- F0's energy finiteness bridge on the full admissible H1 class. -/
theorem metric_energy_densities_integrable (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (admissible : MetricAdmissible Ω f d) :
    IntegrableOn (metricAreaDensity M f d) (disc 1) ∧
    IntegrableOn (metricDirichletDensity M f d) (disc 1) := by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  have vector_measurable {μ : Measure E2} (f : E2 → E2)\n      (h : ∀ i : Fin 2, AEStronglyMeasurable (fun x => f x i) μ) :\n      AEStronglyMeasurable f μ := by\n    have hp : AEMeasurable (fun x => fun i : Fin 2 => f x i) μ :=\n      aemeasurable_pi_iff.mpr (fun i => (h i).aemeasurable)\n    have hv := (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_aestronglyMeasurable\n      hp.aestronglyMeasurable\n    exact hv\n  have global_bound (ψ : E2 → ℝ) (hc : Continuous ψ) (L c : ℝ)\n      (hfar : ∀ x, L ≤ ‖x‖ → ψ x = c) : ∃ C, ∀ x, ‖ψ x‖ ≤ C := by\n    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E2) L).exists_bound_of_continuousOn hc.continuousOn\n    refine ⟨max C ‖c‖, fun x => ?_⟩\n    by_cases hx : ‖x‖ ≤ L\n    · exact (hC x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)\n    · rw [hfar x (le_of_lt (lt_of_not_ge hx))]\n      exact le_max_right _ _\n  have quadratic_expansion (M : E2 → Mat2) (f : E2 → E2)\n      (d : Fin 2 → E2 → E2) (j : Fin 2) (x : E2) :\n      inner ℝ (weakColumn d j x) (matrixAction (M (f x)) (weakColumn d j x)) =\n        ∑ i : Fin 2, ∑ k : Fin 2, M (f x) i k * (d i x j * d k x j) := by\n    delta weakColumn matrixAction\n    rw [EuclideanSpace.inner_eq_star_dotProduct]\n    simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]\n    change ((M (f x) 0 0 * d 0 x j + M (f x) 0 1 * d 1 x j) * d 0 x j +\n      (M (f x) 1 0 * d 0 x j + M (f x) 1 1 * d 1 x j) * d 1 x j) = _\n    ring\n  have energy_integrable (M : E2 → Mat2) (f : E2 → E2)\n      (d : Fin 2 → E2 → E2) (hM : ∀ i j, Continuous (fun x => M x i j))\n      (hfar : ∃ L : ℝ, ∀ x : E2, L ≤ ‖x‖ → M x = 1)\n      (hf : ∀ i : Fin 2, MemLp (fun x => f x i) 2 (volume.restrict (disc 1)))\n      (hd : ∀ i : Fin 2, MemLp (d i) 2 (volume.restrict (disc 1))) :\n      IntegrableOn (metricAreaDensity M f d) (disc 1) ∧\n      IntegrableOn (metricDirichletDensity M f d) (disc 1) := by\n    let μ : Measure E2 := volume.restrict (disc 1)\n    have hfs : AEStronglyMeasurable f μ := vector_measurable f (fun i => (hf i).aestronglyMeasurable)\n    have hdc (i j : Fin 2) : MemLp (fun x => d i x j) 2 μ := by\n      change MemLp (fun x => (EuclideanSpace.proj (𝕜 := ℝ) j) (d i x)) 2\n        (volume.restrict (disc 1))\n      exact (hd i).continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)\n    have hprod (i j k l : Fin 2) : Integrable (fun x => d i x j * d k x l) μ :=\n      (hdc i j).integrable_mul (hdc k l)\n    obtain ⟨L, hfar⟩ := hfar\n    have hb (i j : Fin 2) : ∃ C, ∀ x, ‖M x i j‖ ≤ C :=\n      global_bound (fun x => M x i j) (hM i j) L ((1 : Mat2) i j)\n        (fun x hx => by rw [hfar x hx])\n    have hint (i j k : Fin 2) :\n        Integrable (fun x => M (f x) i k * (d i x j * d k x j)) μ := by\n      obtain ⟨C, hC⟩ := hb i k\n      exact (hprod i j k j).bdd_mul ((hM i k).comp_aestronglyMeasurable hfs)\n        (Filter.Eventually.of_forall fun x => hC (f x))\n    have hquadratic (j : Fin 2) : Integrable (fun x =>\n        inner ℝ (weakColumn d j x) (matrixAction (M (f x)) (weakColumn d j x))) μ := by\n      have hs : Integrable (fun x => ∑ i : Fin 2, ∑ k : Fin 2,\n          M (f x) i k * (d i x j * d k x j)) μ := by\n        apply integrable_finsetSum\n        intro i hi\n        apply integrable_finsetSum\n        intro k hk\n        exact hint i j k\n      exact hs.congr (Filter.Eventually.of_forall fun x => (quadratic_expansion M f d j x).symm)\n    have hdet : Integrable (fun x => Matrix.det (weakJacobian d x)) μ := by\n      have hh := (hprod 0 0 1 1).sub (hprod 0 1 1 0)\n      convert hh using 1\n      funext x\n      exact Matrix.det_fin_two (weakJacobian d x)\n    have hMc : Continuous M := continuous_pi_iff.mpr fun i =>\n      continuous_pi_iff.mpr fun j => hM i j\n    have hsqrt : Continuous (fun x => Real.sqrt (Matrix.det (M x))) := hMc.matrix_det.sqrt\n    obtain ⟨C, hC⟩ := global_bound (fun x => Real.sqrt (Matrix.det (M x))) hsqrt L 1\n      (fun x hx => by rw [hfar x hx, Matrix.det_one, Real.sqrt_one])\n    constructor\n    · exact hdet.abs.bdd_mul (hsqrt.comp_aestronglyMeasurable hfs)\n        (Filter.Eventually.of_forall fun x => hC (f x))\n    · exact (hquadratic 0).add (hquadratic 1)\n  have hM (i j : Fin 2) : Continuous (fun x => M x i j) := by\n    obtain ⟨C, hC⟩ := holder i j\n    exact hC.continuous G.alpha_pos\n  exact energy_integrable M f d hM\n    (by obtain ⟨L, hL, hfar⟩ := identity_at_infinity; exact ⟨L, hfar⟩)\n    (fun i => (admissible.1 i).2.1) (fun i => (admissible.1 i).2.2)\n\n)"))

/- F1: source (4.12)--(4.15). The epsilon-Cartan and inner-variation steps
remain internal proof obligations, with no new original H02 premise. -/
-- simultaneous_metric_minimizer has its sole declaration in downstream B1SimultaneousMetricMinimizer.








/-- Source-faithful closed-disc representative of the SAME variational map.
The pinned PartialHomeomorph has within-set continuity, with no openness field. -/
structure ClosedMetricRepresentative {R : ℝ} {A : E2 → Mat2}
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R)
    (f : E2 → E2) (d : Fin 2 → E2 → E2) where
  tau : PartialHomeomorph E2 E2
  source_eq : tau.source = closedDisc 1
  target_eq : tau.target = closure Ω.domain
  interior_image : tau '' disc 1 = Ω.domain
  boundary_image : tau '' Metric.sphere (0 : E2) 1 = frontier Ω.domain
  forward_C1 : ContDiffOn ℝ 1 tau (closedDisc 1)
  inverse_C1 : ContDiffOn ℝ 1 tau.symm (closure Ω.domain)
  forward_det : ∀ z ∈ closedDisc 1,
    Matrix.det (jacobianWithin tau (closedDisc 1) z) ≠ 0
  inverse_det : ∀ x ∈ closure Ω.domain,
    Matrix.det (jacobianWithin tau.symm (closure Ω.domain) x) ≠ 0
  forward_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C G.alpha (fun z => jacobianWithin tau (closedDisc 1) z i j)
      (closedDisc 1)
  inverse_holder : ∀ i j, ∃ C : ℝ≥0,
    HolderOnWith C G.alpha (fun x => jacobianWithin tau.symm (closure Ω.domain) x i j)
      (closure Ω.domain)
  same_map : tau =ᵐ[volume.restrict (disc 1)] f
  same_weak_jets : ∀ i j,
    (fun z => jacobianWithin tau (closedDisc 1) z i j) =ᵐ[volume.restrict (disc 1)]
      (fun z => d i z j)


/-- Identity for orientation +1, actual disc reflection (u,v) -> (u,-v) for -1. -/
def discOrientationMap (orientation : ℝ) (z : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z 0, orientation * z 1]

/-- Literal weak-gradient transformation of f composed with that same reflection. -/
def orientedWeakGradient (d : Fin 2 → E2 → E2) (orientation : ℝ)
    (i : Fin 2) (z : E2) : E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![d i (discOrientationMap orientation z) 0,
      orientation * d i (discOrientationMap orientation z) 1]

/-- F2 orientation tail: source (4.7),(4.8) and the actual reflection there.
The representative, its inverse, and weak jets remain tied to this same minimizer.
The paid metric transfer/caller packaging bridges are not reproved. -/
theorem positive_system_of_same_regular_minimizer (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (Q : ClosedMetricRepresentative G Ω f d) :
    ∃ orientation : ℝ, (orientation = 1 ∨ orientation = -1) ∧
    ∃ P : ClosedMetricRepresentative G Ω
      (fun z => f (discOrientationMap orientation z)) (orientedWeakGradient d orientation),
      (∀ z ∈ closedDisc 1, P.tau z = Q.tau (discOrientationMap orientation z)) ∧
      (∀ x ∈ closure Ω.domain,
        P.tau.symm x = discOrientationMap orientation (Q.tau.symm x)) ∧
      (∀ᵐ z ∂volume.restrict (disc 1),
        let D := jacobianWithin P.tau (closedDisc 1) z
        Real.sqrt (Matrix.det (M (P.tau z))) * D 0 1 =
          -(M (P.tau z) 0 1 * D 0 0 + M (P.tau z) 1 1 * D 1 0) ∧
        Real.sqrt (Matrix.det (M (P.tau z))) * D 1 1 =
          M (P.tau z) 0 0 * D 0 0 + M (P.tau z) 0 1 * D 1 0) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option maxHeartbeats 3000000 in
  exact (by
    classical
    have orient_apply (e : ℝ) (z : E2) (i : Fin 2) :
        discOrientationMap e z i = if i = 0 then z 0 else e * z 1 := by
      fin_cases i <;> simp [discOrientationMap]
    have orient_involutive (e : ℝ) (he : e = 1 ∨ e = -1) :
        Function.Involutive (discOrientationMap e) := by
      intro z
      ext i
      rcases he with rfl | rfl <;> fin_cases i <;> simp [discOrientationMap]
    
    let orientIsometry (e : ℝ) (he : e = 1 ∨ e = -1) : E2 ≃ₗᵢ[ℝ] E2 := {
      toFun := discOrientationMap e
      invFun := discOrientationMap e
      left_inv := orient_involutive e he
      right_inv := orient_involutive e he
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [discOrientationMap, mul_add]
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [discOrientationMap, mul_left_comm]
      norm_map' := by
        intro x
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        change ‖discOrientationMap e x‖ ^ 2 = ‖x‖ ^ 2
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        rcases he with rfl | rfl <;> simp [discOrientationMap, Fin.sum_univ_two] }
    
    have orient_closed (e : ℝ) (he : e = 1 ∨ e = -1) (z : E2) :
        discOrientationMap e z ∈ closedDisc 1 ↔ z ∈ closedDisc 1 := by
      change discOrientationMap e z ∈ Metric.closedBall 0 1 ↔ z ∈ Metric.closedBall 0 1
      simpa only [mem_closedBall_zero_iff] using
        (show ‖discOrientationMap e z‖ ≤ 1 ↔ ‖z‖ ≤ 1 by change ‖(orientIsometry e he) z‖ ≤ 1 ↔ ‖z‖ ≤ 1; rw [(orientIsometry e he).norm_map])
    have orient_disc (e : ℝ) (he : e = 1 ∨ e = -1) (z : E2) :
        discOrientationMap e z ∈ disc 1 ↔ z ∈ disc 1 := by
      change discOrientationMap e z ∈ Metric.ball 0 1 ↔ z ∈ Metric.ball 0 1
      simpa only [mem_ball_zero_iff] using
        (show ‖discOrientationMap e z‖ < 1 ↔ ‖z‖ < 1 by change ‖(orientIsometry e he) z‖ < 1 ↔ ‖z‖ < 1; rw [(orientIsometry e he).norm_map])
    have orient_sphere (e : ℝ) (he : e = 1 ∨ e = -1) (z : E2) :
        discOrientationMap e z ∈ Metric.sphere (0 : E2) 1 ↔ z ∈ Metric.sphere (0 : E2) 1 := by
      simp only [Metric.mem_sphere, dist_zero_right]
      change ‖(orientIsometry e he) z‖ = 1 ↔ ‖z‖ = 1
      rw [(orientIsometry e he).norm_map]
    
    have closed_unique : UniqueDiffOn ℝ (closedDisc 1) := by
      apply uniqueDiffOn_convex (convex_closedBall (0 : E2) 1)
      exact ⟨0, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self (by norm_num))⟩
    
    have expansion (L : E2 →L[ℝ] E2) (v : E2) :
        L v = v 0 • L (coordinateVector 2 0) + v 1 • L (coordinateVector 2 1) := by
      have hv : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector]
      conv_lhs => rw [hv]
      simp
    
    have jac_dense (L : E2 →L[ℝ] E2)
        (h : Matrix.det (fun i j : Fin 2 => L (coordinateVector 2 j) i) ≠ 0) :
        DenseRange L := by
      rw [_root_.Matrix.det_fin_two] at h
      dsimp only at h
      apply Function.Surjective.denseRange
      apply LinearMap.surjective_of_injective (f := L.toLinearMap)
      intro x y hxy
      have hn : L (x-y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hxy
      have h0 := congrArg (fun z : E2 => z 0) hn
      have h1 := congrArg (fun z : E2 => z 1) hn
      rw [expansion] at h0 h1
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at h0 h1
      have hz0 : (x-y) 0 = 0 := by
        apply (mul_eq_zero.mp (show
          (L (coordinateVector 2 0) 0 * L (coordinateVector 2 1) 1 -
           L (coordinateVector 2 1) 0 * L (coordinateVector 2 0) 1) * (x-y) 0 = 0 by
            linear_combination L (coordinateVector 2 1) 1 * h0 - L (coordinateVector 2 1) 0 * h1)).resolve_left h
      have hz1 : (x-y) 1 = 0 := by
        apply (mul_eq_zero.mp (show
          (L (coordinateVector 2 0) 0 * L (coordinateVector 2 1) 1 -
           L (coordinateVector 2 1) 0 * L (coordinateVector 2 0) 1) * (x-y) 1 = 0 by
            linear_combination L (coordinateVector 2 0) 0 * h1 - L (coordinateVector 2 0) 1 * h0)).resolve_left h
      apply sub_eq_zero.mp
      ext i
      fin_cases i
      · exact hz0
      · exact hz1
    
    have target_unique {R : ℝ} {A : E2 → Mat2} {G : InverseMetricData R A}
        {Ω : SmoothFlatJordanDomain R} {f : E2 → E2} {d : Fin 2 → E2 → E2}
        (Q : ClosedMetricRepresentative G Ω f d) : UniqueDiffOn ℝ (closure Ω.domain) := by
      rw [← Q.target_eq, ← Q.tau.image_source_eq_target, Q.source_eq]
      apply closed_unique.image
      · intro z hz
        exact (Q.forward_C1.differentiableOn (by norm_num) z hz).hasFDerivWithinAt
      · intro z hz
        exact jac_dense _ (Q.forward_det z hz)
    
    have orient_basis (e : ℝ) (j : Fin 2) : discOrientationMap e (coordinateVector 2 j) =
        (if j = 0 then (1 : ℝ) else e) • coordinateVector 2 j := by
      ext i
      fin_cases i <;> fin_cases j <;> simp [discOrientationMap, coordinateVector]
    
    have pre_jac (e : ℝ) (he : e = 1 ∨ e = -1) (T : E2 → E2)
        (hT : ContDiffOn ℝ 1 T (closedDisc 1)) (z : E2) (hz : z ∈ closedDisc 1)
        (i j : Fin 2) :
        jacobianWithin (fun x => T (discOrientationMap e x)) (closedDisc 1) z i j =
          (if j = 0 then (1 : ℝ) else e) * jacobianWithin T (closedDisc 1)
            (discOrientationMap e z) i j := by
      let L := (orientIsometry e he).toContinuousLinearEquiv.toContinuousLinearMap
      have hL : (L : E2 → E2) = discOrientationMap e := rfl
      have hd := fderivWithin_comp (s := closedDisc 1) (t := closedDisc 1) z
        (hT.differentiableOn (by norm_num) _ ((orient_closed e he z).mpr hz))
        (L.differentiable z).differentiableWithinAt
        (fun x hx => (orient_closed e he x).mpr hx) (closed_unique z hz)
      change (fderivWithin ℝ (T ∘ L) (closedDisc 1) z (coordinateVector 2 j)) i = _
      rw [hL, hd]
      change (fderivWithin ℝ T (closedDisc 1) (discOrientationMap e z)
        (fderivWithin ℝ (L : E2 → E2) (closedDisc 1) z (coordinateVector 2 j))) i = _
      rw [L.fderivWithin (closed_unique z hz)]
      simp only [ContinuousLinearMap.comp_apply]
      change (fderivWithin ℝ T (closedDisc 1) (discOrientationMap e z)
        (discOrientationMap e (coordinateVector 2 j))) i = _
      rw [orient_basis, map_smul]
      rfl
    
    have post_jac (e : ℝ) (he : e = 1 ∨ e = -1) (T : E2 → E2) (S : Set E2)
        (hS : UniqueDiffOn ℝ S) (hT : ContDiffOn ℝ 1 T S) (z : E2) (hz : z ∈ S)
        (i j : Fin 2) :
        jacobianWithin (fun x => discOrientationMap e (T x)) S z i j =
          (if i = 0 then (1 : ℝ) else e) * jacobianWithin T S z i j := by
      let L := (orientIsometry e he).toContinuousLinearEquiv.toContinuousLinearMap
      have hd := fderivWithin_comp (s := S) (t := univ) z
        (L.differentiable (T z)).differentiableWithinAt
        (hT.differentiableOn (by norm_num) z hz) (mapsTo_univ _ _) (hS z hz)
      change (fderivWithin ℝ (L ∘ T) S z (coordinateVector 2 j)) i = _
      rw [hd, L.fderivWithin uniqueDiffWithinAt_univ]
      simp only [ContinuousLinearMap.comp_apply]
      fin_cases i <;> simp [L, orientIsometry, discOrientationMap, jacobianWithin]
    
    have choose_orientation (F : E2 → ℝ) (hc : ContinuousOn F (closedDisc 1))
        (hn : ∀ z ∈ closedDisc 1, F z ≠ 0) :
        ∃ e : ℝ, (e = 1 ∨ e = -1) ∧ ∀ z ∈ closedDisc 1, 0 < e * F z := by
      have hzero : (0 : E2) ∈ closedDisc 1 := Metric.mem_closedBall_self (by norm_num)
      have hs := (convex_closedBall (0 : E2) (1 : ℝ)).isPreconnected
      by_cases h : 0 < F 0
      · refine ⟨1, Or.inl rfl, ?_⟩
        intro z hz
        simp only [one_mul]
        by_contra hh
        have hle : F z ≤ 0 := le_of_not_gt hh
        obtain ⟨w, hw, hFw⟩ := hs.intermediate_value hz hzero hc ⟨hle, h.le⟩
        exact hn w hw hFw
      · have hneg : F 0 < 0 := lt_of_le_of_ne (le_of_not_gt h) (hn 0 hzero)
        refine ⟨-1, Or.inr rfl, ?_⟩
        intro z hz
        have hnegz : F z < 0 := by
          by_contra hh
          have hle : 0 ≤ F z := le_of_not_gt hh
          obtain ⟨w, hw, hFw⟩ := hs.intermediate_value hzero hz hc ⟨hneg.le, hle⟩
          exact hn w hw hFw
        simpa using neg_pos.mpr hnegz
    
    
    have orient_image (e : ℝ) (he : e = 1 ∨ e = -1) (S : Set E2)
        (hS : ∀ z, discOrientationMap e z ∈ S ↔ z ∈ S) : discOrientationMap e '' S = S := by
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        exact (hS z).mpr hz
      · intro z hz
        exact ⟨discOrientationMap e z, (hS z).mpr hz, orient_involutive e he z⟩
    
    have orient_ae (e : ℝ) (he : e = 1 ∨ e = -1) :
        _root_.MeasureTheory.Measure.QuasiMeasurePreserving (discOrientationMap e) (volume.restrict (disc 1))
          (volume.restrict (disc 1)) := by
      have hpre : (orientIsometry e he) ⁻¹' disc 1 = disc 1 := by
        ext z
        exact orient_disc e he z
      have h := (orientIsometry e he).measurePreserving.restrict_preimage
        (show MeasurableSet (disc 1) from measurableSet_ball)
      rw [hpre] at h
      exact h.quasiMeasurePreserving
    
    have factor_edist (e : ℝ) (he : e = 1 ∨ e = -1) (i : Fin 2) (x y : ℝ) :
        edist ((if i = 0 then (1 : ℝ) else e) * x)
          ((if i = 0 then (1 : ℝ) else e) * y) = edist x y := by
      rcases he with rfl | rfl <;> fin_cases i <;> simp
    
    have pre_det (e : ℝ) (he : e = 1 ∨ e = -1) (T : E2 → E2)
        (hT : ContDiffOn ℝ 1 T (closedDisc 1)) (z : E2) (hz : z ∈ closedDisc 1) :
        Matrix.det (jacobianWithin (fun x => T (discOrientationMap e x)) (closedDisc 1) z) =
          e * Matrix.det (jacobianWithin T (closedDisc 1) (discOrientationMap e z)) := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [pre_jac e he T hT z hz]
      norm_num
      ring
    
    have post_det (e : ℝ) (he : e = 1 ∨ e = -1) (T : E2 → E2) (S : Set E2)
        (hS : UniqueDiffOn ℝ S) (hT : ContDiffOn ℝ 1 T S) (z : E2) (hz : z ∈ S) :
        Matrix.det (jacobianWithin (fun x => discOrientationMap e (T x)) S z) =
          e * Matrix.det (jacobianWithin T S z) := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [post_jac e he T S hS hT z hz]
      norm_num
      ring
    
    let orientRepresentative {R : ℝ} {A : E2 → Mat2} {G : InverseMetricData R A}
        {Ω : SmoothFlatJordanDomain R} {f : E2 → E2} {d : Fin 2 → E2 → E2}
        (e : ℝ) (he : e = 1 ∨ e = -1) (Q : ClosedMetricRepresentative G Ω f d) :
        ClosedMetricRepresentative G Ω (fun z => f (discOrientationMap e z))
          (orientedWeakGradient d e) := by
      classical
      let L := (orientIsometry e he).toContinuousLinearEquiv.toContinuousLinearMap
      have hL : (L : E2 → E2) = discOrientationMap e := rfl
      have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
      let tau : PartialHomeomorph E2 E2 :=
        { toFun := fun z => Q.tau (discOrientationMap e z)
          invFun := fun x => discOrientationMap e (Q.tau.symm x)
          source := closedDisc 1
          target := closure Ω.domain
          map_source' := by
            intro z hz
            rw [← Q.target_eq]
            apply Q.tau.map_source
            rw [Q.source_eq]
            exact (orient_closed e he z).mpr hz
          map_target' := by
            intro x hx
            apply (orient_closed e he _).mpr
            rw [← Q.source_eq]
            apply Q.tau.map_target
            rwa [Q.target_eq]
          left_inv' := by
            intro z hz
            have hq : discOrientationMap e z ∈ Q.tau.source := by
              rw [Q.source_eq]
              exact (orient_closed e he z).mpr hz
            rw [Q.tau.left_inv hq, orient_involutive e he z]
          right_inv' := by
            intro x hx
            rw [orient_involutive e he]
            apply Q.tau.right_inv
            rwa [Q.target_eq]
          continuousOn_toFun := by
            exact (Q.forward_C1.continuousOn).comp L.continuous.continuousOn
              (fun z hz => (orient_closed e he z).mpr hz)
          continuousOn_invFun := by
            exact L.continuous.continuousOn.comp Q.inverse_C1.continuousOn (mapsTo_univ _ _) }
      refine
        { tau := tau
          source_eq := rfl
          target_eq := rfl
          interior_image := ?_
          boundary_image := ?_
          forward_C1 := ?_
          inverse_C1 := ?_
          forward_det := ?_
          inverse_det := ?_
          forward_holder := ?_
          inverse_holder := ?_
          same_map := ?_
          same_weak_jets := ?_ }
      · change (Q.tau ∘ discOrientationMap e) '' disc 1 = Ω.domain
        rw [Set.image_comp, orient_image e he _ (orient_disc e he), Q.interior_image]
      · change (Q.tau ∘ discOrientationMap e) '' Metric.sphere (0 : E2) 1 = frontier Ω.domain
        rw [Set.image_comp, orient_image e he _ (orient_sphere e he), Q.boundary_image]
      · exact Q.forward_C1.comp L.contDiff.contDiffOn
          (fun z hz => (orient_closed e he z).mpr hz)
      · exact L.contDiff.contDiffOn.comp Q.inverse_C1 (mapsTo_univ _ _)
      · intro z hz
        change Matrix.det (jacobianWithin (fun x => Q.tau (discOrientationMap e x))
          (closedDisc 1) z) ≠ 0
        rw [pre_det e he Q.tau Q.forward_C1 z hz]
        exact mul_ne_zero he0 (Q.forward_det _ ((orient_closed e he z).mpr hz))
      · intro x hx
        change Matrix.det (jacobianWithin (fun x => discOrientationMap e (Q.tau.symm x))
          (closure Ω.domain) x) ≠ 0
        rw [post_det e he Q.tau.symm _ (target_unique Q) Q.inverse_C1 x hx]
        exact mul_ne_zero he0 (Q.inverse_det x hx)
      · intro i j
        obtain ⟨C, hC⟩ := Q.forward_holder i j
        refine ⟨C, ?_⟩
        intro x hx y hy
        change edist (jacobianWithin (fun z => Q.tau (discOrientationMap e z)) (closedDisc 1) x i j)
          (jacobianWithin (fun z => Q.tau (discOrientationMap e z)) (closedDisc 1) y i j) ≤ _
        rw [pre_jac e he _ Q.forward_C1 x hx, pre_jac e he _ Q.forward_C1 y hy,
          factor_edist e he]
        have h := hC _ ((orient_closed e he x).mpr hx) _ ((orient_closed e he y).mpr hy)
        change edist _ _ ≤ _ * edist ((orientIsometry e he) x) ((orientIsometry e he) y) ^ _ at h
        rwa [(orientIsometry e he).isometry.edist_eq] at h
      · intro i j
        obtain ⟨C, hC⟩ := Q.inverse_holder i j
        refine ⟨C, ?_⟩
        intro x hx y hy
        change edist (jacobianWithin (fun z => discOrientationMap e (Q.tau.symm z))
          (closure Ω.domain) x i j) (jacobianWithin (fun z => discOrientationMap e (Q.tau.symm z))
          (closure Ω.domain) y i j) ≤ _
        rw [post_jac e he _ _ (target_unique Q) Q.inverse_C1 x hx,
          post_jac e he _ _ (target_unique Q) Q.inverse_C1 y hy, factor_edist e he]
        exact hC x hx y hy
      · exact (orient_ae e he).ae Q.same_map
      · intro i j
        have hj := (orient_ae e he).ae (Q.same_weak_jets i j)
        filter_upwards [hj, ae_restrict_mem (show MeasurableSet (disc 1) from measurableSet_ball)]
          with z hz hmem
        change jacobianWithin (fun x => Q.tau (discOrientationMap e x)) (closedDisc 1) z i j = _
        rw [pre_jac e he _ Q.forward_C1 z (Metric.ball_subset_closedBall hmem), hz]
        fin_cases j <;> simp [orientedWeakGradient]
    
    have cr_algebra (p q r u v b c : ℝ)
        (hmetric : p*r-q^2 = 1) (hdet : 0 < u*c-b*v)
        (hE : 0 < p*u^2+2*q*u*v+r*v^2)
        (hconf : p*u^2+2*q*u*v+r*v^2 = p*b^2+2*q*b*c+r*c^2)
        (hort : p*u*b+q*(u*c+v*b)+r*v*c = 0) :
        b = -(q*u+r*v) ∧ c = p*u+q*v := by
      let E := p*u^2+2*q*u*v+r*v^2
      let H := p*b^2+2*q*b*c+r*c^2
      let F := p*u*b+q*(u*c+v*b)+r*v*c
      let K := u*c-b*v
      have hidentity : E*H-F^2 = (p*r-q^2)*K^2 := by dsimp [E,H,F,K]; ring
      have hsame : E = H := hconf
      have hF : F = 0 := hort
      have hsq : E^2 = K^2 := by rw [← hsame, hF, hmetric] at hidentity; nlinarith
      have hEK : E = K := by nlinarith
      have hb : E*(b+q*u+r*v) = 0 := by
        calc
          E*(b+q*u+r*v) = E*b+(q*u+r*v)*K := by rw [← hEK]; ring
          _ = u*F := by dsimp [E,K,F]; ring
          _ = 0 := by rw [hF]; ring
      have hc : E*(c-(p*u+q*v)) = 0 := by
        calc
          E*(c-(p*u+q*v)) = E*c-(p*u+q*v)*K := by rw [← hEK]; ring
          _ = v*F := by dsimp [E,K,F]; ring
          _ = 0 := by rw [hF]; ring
      have hb0 := (mul_eq_zero.mp hb).resolve_left (ne_of_gt hE)
      have hc0 := (mul_eq_zero.mp hc).resolve_left (ne_of_gt hE)
      constructor <;> linarith
    
    have metric_expand (B : Mat2) (x y : E2) :
        inner ℝ x (matrixAction B y) =
          x 0 * (B 0 0*y 0+B 0 1*y 1) + x 1*(B 1 0*y 0+B 1 1*y 1) := by
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
        matrixAction, star_trivial]
      change (B 0 0*y 0+B 0 1*y 1)*x 0 + (B 1 0*y 0+B 1 1*y 1)*x 1 = _
      ring
    classical
    have hc (i j : Fin 2) : ContinuousOn
        (fun z => jacobianWithin Q.tau (closedDisc 1) z i j) (closedDisc 1) := by
      obtain ⟨C,hC⟩ := Q.forward_holder i j
      exact hC.continuousOn G.alpha_pos
    have hdc : ContinuousOn (fun z => Matrix.det (jacobianWithin Q.tau (closedDisc 1) z))
        (closedDisc 1) := by
      apply (((hc 0 0).mul (hc 1 1)).sub ((hc 0 1).mul (hc 1 0))).congr
      intro z hz
      exact Matrix.det_fin_two _
    obtain ⟨e,he,hpos⟩ := choose_orientation _ hdc Q.forward_det
    let P := orientRepresentative e he Q
    have hPpos (z : E2) (hz : z ∈ closedDisc 1) :
        0 < Matrix.det (jacobianWithin P.tau (closedDisc 1) z) := by
      change 0 < Matrix.det (jacobianWithin (fun x => Q.tau (discOrientationMap e x))
        (closedDisc 1) z)
      rw [pre_det e he _ Q.forward_C1 z hz]
      exact hpos _ ((orient_closed e he z).mpr hz)
    refine ⟨e,he,P,?_,?_,?_⟩
    · intro z hz
      rfl
    · intro x hx
      rfl
    · have hconf := (orient_ae e he).ae minimum.weak_conformality
      have hmap := (orient_ae e he).ae Q.same_map
      have h00 := (orient_ae e he).ae (Q.same_weak_jets 0 0)
      have h01 := (orient_ae e he).ae (Q.same_weak_jets 0 1)
      have h10 := (orient_ae e he).ae (Q.same_weak_jets 1 0)
      have h11 := (orient_ae e he).ae (Q.same_weak_jets 1 1)
      filter_upwards [hconf,hmap,h00,h01,h10,h11,
        ae_restrict_mem (show MeasurableSet (disc 1) from measurableSet_ball)]
        with z hconf hmap h00 h01 h10 h11 hz
      let y := discOrientationMap e z
      have hzc : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz
      have hym : P.tau z = f y := hmap
      have htarget : P.tau z ∈ closure Ω.domain := by
        rw [← P.target_eq]
        apply P.tau.map_source
        rwa [P.source_eq]
      have hD00 : jacobianWithin P.tau (closedDisc 1) z 0 0 = d 0 y 0 := by
        change jacobianWithin (fun x => Q.tau (discOrientationMap e x)) (closedDisc 1) z 0 0 = _
        rw [pre_jac e he _ Q.forward_C1 z hzc, h00]
        simp [y]
      have hD01 : jacobianWithin P.tau (closedDisc 1) z 0 1 = e*d 0 y 1 := by
        change jacobianWithin (fun x => Q.tau (discOrientationMap e x)) (closedDisc 1) z 0 1 = _
        rw [pre_jac e he _ Q.forward_C1 z hzc, h01]
        norm_num [y]
      have hD10 : jacobianWithin P.tau (closedDisc 1) z 1 0 = d 1 y 0 := by
        change jacobianWithin (fun x => Q.tau (discOrientationMap e x)) (closedDisc 1) z 1 0 = _
        rw [pre_jac e he _ Q.forward_C1 z hzc, h10]
        simp [y]
      have hD11 : jacobianWithin P.tau (closedDisc 1) z 1 1 = e*d 1 y 1 := by
        change jacobianWithin (fun x => Q.tau (discOrientationMap e x)) (closedDisc 1) z 1 1 = _
        rw [pre_jac e he _ Q.forward_C1 z hzc, h11]
        norm_num [y]
      have hdet : 0 < d 0 y 0*(e*d 1 y 1)-(e*d 0 y 1)*d 1 y 0 := by
        have h := hPpos z hzc
        rwa [Matrix.det_fin_two,hD00,hD01,hD10,hD11] at h
      have hcol : weakColumn d 0 y ≠ 0 := by
        intro hh
        have h0 := congrArg (fun x : E2 => x 0) hh
        have h1 := congrArg (fun x : E2 => x 1) hh
        have hz0 : d 0 y 0 = 0 := by simpa [weakColumn] using h0
        have hz1 : d 1 y 0 = 0 := by simpa [weakColumn] using h1
        rw [hz0,hz1] at hdet
        norm_num at hdet
      have hE : 0 < metricE M f d y := by
        have hm : f y ∈ closure Ω.domain := hym ▸ htarget
        have hh := G.positive_definite (f y) (Ω.closure_inside hm) (weakColumn d 0 y) hcol
        simpa only [metricE,agreement (f y) hm] using hh
      have hsym : M (f y) 1 0 = M (f y) 0 1 := symmetric _ (mem_univ _) 1 0
      have hMdet : Matrix.det (M (f y)) = 1 := by
        rw [agreement _ (hym ▸ htarget)]
        exact G.det_one _ (Ω.closure_inside (hym ▸ htarget))
      have hmetric : M (f y) 0 0*M (f y) 1 1-M (f y) 0 1^2 = 1 := by
        rw [Matrix.det_fin_two,hsym] at hMdet
        nlinarith
      have henergy : 0 < M (f y) 0 0*(d 0 y 0)^2 +
          2*M (f y) 0 1*d 0 y 0*d 1 y 0+M (f y) 1 1*(d 1 y 0)^2 := by
        dsimp only [metricE] at hE
        rw [metric_expand,hsym] at hE
        change 0 < d 0 y 0*(M (f y) 0 0*d 0 y 0+M (f y) 0 1*d 1 y 0)+
          d 1 y 0*(M (f y) 0 1*d 0 y 0+M (f y) 1 1*d 1 y 0) at hE
        nlinarith
      have hconformal : M (f y) 0 0*(d 0 y 0)^2 +
          2*M (f y) 0 1*d 0 y 0*d 1 y 0+M (f y) 1 1*(d 1 y 0)^2 =
          M (f y) 0 0*(e*d 0 y 1)^2 +
          2*M (f y) 0 1*(e*d 0 y 1)*(e*d 1 y 1)+M (f y) 1 1*(e*d 1 y 1)^2 := by
        have hh := hconf.1
        dsimp only [metricE,metricH] at hh
        rw [metric_expand,metric_expand,hsym] at hh
        rcases he with rfl | rfl <;> simp [weakColumn] at hh ⊢ <;> nlinarith [hh]
      have horthogonal : M (f y) 0 0*d 0 y 0*(e*d 0 y 1) +
          M (f y) 0 1*(d 0 y 0*(e*d 1 y 1)+d 1 y 0*(e*d 0 y 1))+
          M (f y) 1 1*d 1 y 0*(e*d 1 y 1) = 0 := by
        have hh := hconf.2
        dsimp only [metricF] at hh
        rw [metric_expand,hsym] at hh
        rcases he with rfl | rfl <;> simp [weakColumn] at hh ⊢ <;> nlinarith [hh]
      have hresult := cr_algebra _ _ _ _ _ _ _ hmetric hdet henergy hconformal horthogonal
      dsimp only
      rw [hD00,hD01,hD10,hD11,hym,hMdet,Real.sqrt_one]
      simpa only [one_mul] using hresult
  )

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
