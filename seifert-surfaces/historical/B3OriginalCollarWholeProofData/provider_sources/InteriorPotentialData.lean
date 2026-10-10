import GradientEstimateRescalingData
import Mathlib.Topology.MetricSpace.HolderNorm

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
open SeifertSurfaces.AppendixACoordinates

/-- Exactly the native unit-ball input context, with no regularity of the scalar added. -/
structure InteriorData (alpha : ℝ≥0) (lam Lambda : ℝ) (HN : ℝ≥0) where
  N : E2 → Mat2
  symmetric : SymmetricOn N (Metric.ball (0 : E2) 1)
  elliptic_bound : ∀ z ∈ Metric.ball (0 : E2) 1, ∀ t : E2,
    lam * ‖t‖ ^ 2 ≤ inner ℝ t (matrixAction (N z) t) ∧
      ‖matrixAction (N z) t‖ ≤ Lambda * ‖t‖
  holder_N : ∀ i j, HolderOnWith HN alpha (fun z => N z i j) (Metric.ball (0 : E2) 1)
  F : E2 → E2
  BF : ℝ
  HF : ℝ≥0
  BF_nonneg : 0 ≤ BF
  bounded_F : ∀ z ∈ Metric.ball (0 : E2) 1, ‖F z‖ ≤ BF
  holder_F : HolderOnWith HF alpha F (Metric.ball (0 : E2) 1)
  v : E2 → ℝ
  dv : E2 → E2
  weak : DirectWeak.WeakDivergenceWithData (Metric.ball (0 : E2) 1) N F (fun _ => 0) v dv

def bootstrapExponent (alpha : ℝ≥0) : ℝ := 4 / (1 - (alpha : ℝ))

def scalarExponent (alpha : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (1 - 2 / bootstrapExponent alpha)

def dataSize {alpha : ℝ≥0} {lam Lambda : ℝ} {HN : ℝ≥0}
    (d : InteriorData alpha lam Lambda HN) : ℝ :=
  Real.sqrt (∫ z in Metric.ball (0 : E2) 1, ‖d.dv z‖ ^ 2) + d.BF + (d.HF : ℝ)

def normalizedScalar {alpha : ℝ≥0} {lam Lambda : ℝ} {HN : ℝ≥0}
    (d : InteriorData alpha lam Lambda HN) (z : E2) : ℝ :=
  d.v z - ⨍ t in Metric.ball (0 : E2) 1, d.v t

def localizedScalar (chi w : E2 → ℝ) (z : E2) : ℝ := chi z * w z

def localizedGradient (chi w : E2 → ℝ) (dv : E2 → E2) (z : E2) : E2 :=
  chi z • dv z + w z • planarGradient chi z

def localizedVectorData (N : E2 → Mat2) (F : E2 → E2)
    (chi w : E2 → ℝ) (z : E2) : E2 :=
  chi z • F z + w z • matrixAction (N z) (planarGradient chi z)

def localizedScalarData (N : E2 → Mat2) (F dv : E2 → E2)
    (chi : E2 → ℝ) (z : E2) : ℝ :=
  inner ℝ (F z - matrixAction (N z) (dv z)) (planarGradient chi z)

def extendedCoefficient (N : E2 → Mat2) (x : E2) (eta : E2 → ℝ) (z : E2) : Mat2 :=
  eta z • N z + (1 - eta z) • N x

/-- Fundamental solution of minus divergence of the constant positive definite matrix. -/
def frozenKernel (A : Mat2) (z : E2) : ℝ :=
  -(Real.log (Real.sqrt (inner ℝ z (matrixAction A⁻¹ z)))) /
    (2 * Real.pi * Real.sqrt (Matrix.det A))

def frozenKernelGradient (A : Mat2) (z : E2) : E2 :=
  (-(2 * Real.pi * Real.sqrt (Matrix.det A) *
      inner ℝ z (matrixAction A⁻¹ z))⁻¹) • matrixAction A⁻¹ z

def frozenQ (A : Mat2) (e : E2 → E2) (z : E2) : ℝ :=
  -(∫ t, inner ℝ (frozenKernelGradient A (z - t)) (e t))

def rawFrozenP (A : Mat2) (f : E2 → ℝ) (z : E2) : ℝ :=
  ∫ t, frozenKernel A (z - t) * f t

def frozenP (A : Mat2) (x : E2) (R : ℝ) (f : E2 → ℝ) (z : E2) : ℝ :=
  rawFrozenP A f z - ⨍ t in Metric.ball x (2 * R), rawFrozenP A f t

def CompatibleScalarForcing (x : E2) (R : ℝ) (f : E2 → ℝ) : Prop :=
  Function.support f ⊆ Metric.closedBall x R ∧ Integrable f ∧ (∫ z, f z) = 0

/-- Global native distributional identity; scalar L² is required only on bounded balls. -/
def FrozenWeakPotential (A : Mat2) (e : E2 → E2) (f u : E2 → ℝ)
    (du : E2 → E2) : Prop :=
  WeakGradientOn Set.univ u du ∧
  (∀ (z : E2) (s : ℝ), 0 < s → H1On (Metric.ball z s) u du) ∧
  ∀ psi : E2 → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
    Integrable (fun z => inner ℝ (matrixAction A (du z)) (planarGradient psi z)) ∧
    Integrable (fun z => inner ℝ (e z) (planarGradient psi z) + f z * psi z) ∧
    (∫ z, inner ℝ (matrixAction A (du z)) (planarGradient psi z)) =
      ∫ z, inner ℝ (e z) (planarGradient psi z) + f z * psi z

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
