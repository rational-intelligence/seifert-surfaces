import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Concrete R4 data. All newly asserted bridges are proof obligations.
Only the selected qinz1yang DifferentialGeometry.External.DeGiorgi provider is used.
The ball solution has no prescribed zero boundary trace. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.WeakSchauder

abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
abbrev H1Witness (v : V → ℝ) (Ω : Set V) := DeGiorgi.MemW1pWitness 2 v Ω

/-- A pointwise coercive, operator-bounded, possibly nonsymmetric field.
Measurability is restricted to the domain, with no global extension requirement. -/
structure CoefficientBounds (a : V → Mat) (Ω : Set V) (κ Λ : ℝ) : Prop where
  measurable : ∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict Ω)
  coercive : ∀ x ∈ Ω, ∀ ξ : V, κ * ‖ξ‖ ^ 2 ≤ inner ℝ ξ (DeGiorgi.matMulE (a x) ξ)
  mixed : ∀ x ∈ Ω, ∀ ξ η : V,
    |inner ℝ (DeGiorgi.matMulE (a x) ξ) η| ≤ Λ * ‖ξ‖ * ‖η‖

/-- The ordinary componentwise Hölder condition, retaining the finite exponent. -/
def CoefficientHolder (a : V → Mat) (Ω : Set V) (H α : NNReal) : Prop :=
  ∀ i j, HolderOnWith H α (fun x => a x i j) Ω

/-- All-H₀¹-test homogeneous divergence equation for the displayed actual weak
Sobolev gradient. Integrability precedes the totalized Bochner equality. -/
def WeakEquation (a : V → Mat) {v : V → ℝ} {Ω : Set V}
    (hv : H1Witness v Ω) : Prop :=
  ∀ (φ : V → ℝ), DeGiorgi.MemH01 φ Ω → ∀ hφ : H1Witness φ Ω,
    IntegrableOn (fun x => inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x))
      (hφ.weakGrad x)) Ω ∧
    (∫ x in Ω, inner ℝ (DeGiorgi.matMulE (a x) (hv.weakGrad x)) (hφ.weakGrad x)) = 0

/-- Distributional equation against genuine compactly supported smooth tests. -/
def SmoothWeakEquation (a : V → Mat) (G : V → V) (Ω : Set V) : Prop :=
  ∀ (φ : V → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    IntegrableOn (fun x => ∑ i : Fin 3,
      DeGiorgi.matMulE (a x) (G x) i * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) Ω ∧
    (∫ x in Ω, ∑ i : Fin 3,
      DeGiorgi.matMulE (a x) (G x) i * (fderiv ℝ φ x) (EuclideanSpace.single i 1)) = 0

def energy (G : V → V) (x : V) (r : ℝ) : ℝ :=
  ∫ y in Metric.ball x r, ‖G y‖ ^ 2

def ballMean (G : V → V) (x : V) (r : ℝ) : V :=
  (volume (Metric.ball x r)).toReal⁻¹ • ∫ y in Metric.ball x r, G y

def excess (G : V → V) (x : V) (r : ℝ) : ℝ :=
  ∫ y in Metric.ball x r, ‖G y - ballMean G x r‖ ^ 2

/-- An actual mean-square Campanato estimate, not a regularity label.
The maximal radius and all permitted centers are explicit. -/
def CampanatoBound (G : V → V) (centers : Set V) (rmax : ℝ) (β : NNReal) (M : ℝ) : Prop :=
  ∀ x ∈ centers, ∀ r : ℝ, 0 < r → r ≤ rmax →
    excess G x r ≤ M * r ^ (3 + 2 * (β : ℝ))

def symmetricPart (A : Mat) : Mat := (1 / 2 : ℝ) • (A + A.transpose)

/-- Exact boundary-value characterization by H₀¹ difference; no classical
boundary continuity or gradient decay is part of the replacement data. -/
def IsHarmonicReplacement (A : Mat) {v h : V → ℝ} {Ω : Set V}
    (_hv : H1Witness v Ω) (hh : H1Witness h Ω) : Prop :=
  DeGiorgi.MemH01 (fun x => v x - h x) Ω ∧ WeakEquation (fun _ => A) hh

/-- The coefficient oscillation is relative to one frozen value. -/
def OscillationBound (a : V → Mat) (A : Mat) (Ω : Set V) (δ : ℝ) : Prop :=
  ∀ x ∈ Ω, ∀ ξ η : V,
    |inner ℝ (DeGiorgi.matMulE (a x - A) ξ) η| ≤ δ * ‖ξ‖ * ‖η‖

/-- A weak-gradient field is genuinely square integrable as a vector. -/
theorem weak_gradient_memLp (Ω : Set V) (v : V → ℝ) (hv : H1Witness v Ω) :
    MemLp hv.weakGrad 2 (volume.restrict Ω) := by
  exact MemLp.of_eval_piLp hv.weakGrad_component_memLp

private lemma sum_abs_sq_le (ξ : V) :
    (∑ i : Fin 3, |ξ i|) ^ 2 ≤ 3 * ‖ξ‖ ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun i : Fin 3 => |ξ i|) (g := fun _ => (1 : ℝ))
  simpa [EuclideanSpace.real_norm_sq_eq, mul_comm] using h

private lemma sum_abs_mul_le (ξ η : V) :
    (∑ i : Fin 3, |ξ i|) * (∑ i : Fin 3, |η i|) ≤ 3 * ‖ξ‖ * ‖η‖ := by
  have hξ := sum_abs_sq_le ξ
  have hη := sum_abs_sq_le η
  have hprod := mul_le_mul hξ hη (sq_nonneg _) (by positivity)
  have hξ0 : 0 ≤ ∑ i : Fin 3, |ξ i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hη0 : 0 ≤ ∑ i : Fin 3, |η i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hξ0 hη0) (by positivity)).mp
  nlinarith only [hprod]

private lemma matrix_mixed_bound (A : Mat) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ∀ i j, |A i j| ≤ δ) (ξ η : V) :
    |inner ℝ (DeGiorgi.matMulE A ξ) η| ≤ 3 * δ * ‖ξ‖ * ‖η‖ := by
  have hexp : inner ℝ (DeGiorgi.matMulE A ξ) η =
      ∑ i : Fin 3, ∑ j : Fin 3, A i j * ξ j * η i := by
    simp only [PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec,
      dotProduct, RCLike.inner_apply, conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hexp]
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, A i j * ξ j * η i|
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, |A i j * ξ j * η i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, δ * |ξ j| * |η i| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      gcongr
      exact hA i j
    _ = δ * ((∑ j : Fin 3, |ξ j|) * (∑ i : Fin 3, |η i|)) := by
      rw [Finset.mul_sum]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    _ ≤ δ * (3 * ‖ξ‖ * ‖η‖) := mul_le_mul_of_nonneg_left (sum_abs_mul_le ξ η) hδ
    _ = 3 * δ * ‖ξ‖ * ‖η‖ := by ring

/-- Coefficients satisfying the declared Hölder bound yield the operator
oscillation needed for energy comparison. The factor 3 is the dimension. -/
theorem holder_frozen_oscillation (a : V → Mat) (center : V) (R : ℝ)
    (hR : 0 < R) (H α : NNReal)
    (hholder : CoefficientHolder a (Metric.ball center R) H α) :
    OscillationBound a (a center) (Metric.ball center R) (3 * (H : ℝ) * R ^ (α : ℝ)) := by
  intro x hx ξ η
  have hcenter : center ∈ Metric.ball center R := Metric.mem_ball_self hR
  have hentries : ∀ i j, |(a x - a center) i j| ≤ (H : ℝ) * R ^ (α : ℝ) := by
    intro i j
    simpa [Real.dist_eq] using
      (hholder i j).dist_le_of_le hx hcenter (Metric.mem_ball.mp hx).le
  simpa [mul_assoc] using matrix_mixed_bound (a x - a center)
    ((H : ℝ) * R ^ (α : ℝ)) (by positivity) hentries ξ η

end SeifertSurfaces.WeakSchauder
