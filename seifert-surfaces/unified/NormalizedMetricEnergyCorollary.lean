import NormalizedMetricLocalBounds

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
open SeifertSurfaces.AppendixACoordinates
open IsothermalPDELower

/-- The exact local normalization residual required by the affine-energy caller. -/
theorem normalizedInverse_energy_local_bounds
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (M : E2 → Mat2) (y : E2) (r : ℝ) (hr : 0 < r)
    (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r)) :
    ∃ r1 lam Lambda : ℝ, ∃ HN : ℝ≥0,
      0 < r1 ∧ r1 ≤ r ∧ r1 ≤ 1 ∧ 0 < lam ∧
      (∀ x ∈ Metric.ball y r1, ∀ v : E2,
        lam * ‖v‖ ^ 2 ≤ inner ℝ v (matrixAction (normalizedInverse M x) v) ∧
        ‖matrixAction (normalizedInverse M x) v‖ ≤ Lambda * ‖v‖) ∧
      (∀ i j, HolderOnWith HN G.alpha (fun x => normalizedInverse M x i j)
        (Metric.ball y r1)) := by
  obtain ⟨lam, K, HN, hlam, hK, hb, hH⟩ :=
    normalizedInverse_local_bounds R A G M y r hr symmetric elliptic holder
  have hsub : Metric.ball y (min r 1) ⊆ Metric.ball y r :=
    Metric.ball_subset_ball (min_le_left r 1)
  refine ⟨min r 1, lam, K, HN, lt_min hr zero_lt_one,
    min_le_left r 1, min_le_right r 1, hlam, ?_, ?_⟩
  · intro x hx v
    obtain ⟨hc, ho⟩ := hb x (hsub hx) v
    exact ⟨by simpa only [real_inner_comm] using hc, ho⟩
  · intro i j
    exact (hH i j).mono hsub


end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.MetricNormalization
