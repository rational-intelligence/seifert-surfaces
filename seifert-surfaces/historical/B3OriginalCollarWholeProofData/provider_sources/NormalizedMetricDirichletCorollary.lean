import NormalizedMetricLocalBounds

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
open SeifertSurfaces.AppendixACoordinates
open IsothermalPDELower

/-- Full-ball measurability and coercive/operator bounds for native Dirichlet D4. -/
theorem normalizedInverse_dirichlet_bounds
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (M : E2 → Mat2) (y : E2) (r : ℝ) (hr : 0 < r)
    (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r)) :
    (∀ i j, AEStronglyMeasurable (fun x => normalizedInverse M x i j)
      (volume.restrict (Metric.ball y r))) ∧
    ∃ lam K : ℝ, 0 < lam ∧ 0 < K ∧
      ∀ x ∈ Metric.ball y r, ∀ v : E2,
        lam * ‖v‖ ^ 2 ≤ inner ℝ (matrixAction (normalizedInverse M x) v) v ∧
        ‖matrixAction (normalizedInverse M x) v‖ ≤ K * ‖v‖ := by
  obtain ⟨lam, K, HN, hlam, hK, hbounds, hholder⟩ :=
    normalizedInverse_local_bounds R A G M y r hr symmetric elliptic holder
  refine ⟨?_, lam, K, hlam, hK, hbounds⟩
  intro i j
  exact ((hholder i j).continuousOn G.alpha_pos).aestronglyMeasurable measurableSet_ball

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
