import B1TangencyReflection

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

structure SimilarityFactorization (R : ℝ) (w : ℂ → ℂ) where
  Phi : ℂ → ℂ
  holomorphic : DifferentiableOn ℂ Phi (Metric.ball 0 R)
  omega : ℂ → ℂ
  omega_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball (0 : ℂ) R, ‖omega z‖ ≤ C
  alpha : ℝ≥0
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1
  omega_holder : ∃ C : ℝ≥0, HolderOnWith C alpha omega (Metric.ball (0 : ℂ) R)
  same_w : ∀ z ∈ Metric.ball (0 : ℂ) R, w z = Phi z * Complex.exp (omega z)

/- The usable weak similarity theorem cited at [18, Ch III, §4.1]. Its
analytic proof is owed; no external axiom or final tangency premise is inserted. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
