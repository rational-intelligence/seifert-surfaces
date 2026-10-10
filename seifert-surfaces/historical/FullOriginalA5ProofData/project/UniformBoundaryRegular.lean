import B1L1DirectWeakLower
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.AppendixACoordinates

theorem uniform_zero_scalar_boundary_regular (r : ℝ) (radius_positive : 0 < r)
    (gamma : ℝ≥0) (gamma_positive : 0 < gamma) (gamma_lt_one : gamma < 1)
    (a : E2 → Mat2) (ell Lambda : ℝ) (ell_positive : 0 < ell) (Lambda_positive : 0 < Lambda)
    (bounds : ∀ y : E2, ∀ p : E2,
      ell * ‖p‖ ^ 2 ≤ inner ℝ p (matrixAction (a y) p) ∧ (∀ i j, |a y i j| ≤ Lambda))
    (Ca : ℝ≥0) (coefficient_holder : ∀ i j, HolderWith Ca gamma (fun y => a y i j)) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (e : E2 → E2) (v : E2 → ℝ) (dv : E2 → E2)
        (Be : ℝ), 0 ≤ Be → ∀ Ce : ℝ≥0,
      (∀ y ∈ closedHalfDisc r, ‖e y‖ ≤ Be) →
      HolderOnWith Ce gamma e (closedHalfDisc r) →
      WeakDivergenceWithData (halfDisc r) a e (fun _ => 0) v dv →
      FlatZeroTrace r v dv →
      let size := Be + (Ce : ℝ) + ∫ y in halfDisc r, |v y|
      ∃ w : E2 → ℝ, w =ᵐ[volume.restrict (halfDisc (r / 2))] v ∧
        ContDiffOn ℝ 1 w (closedHalfDisc (r / 2)) ∧
        (∀ y ∈ flatArc (r / 2), w y = 0) ∧
        (∀ y ∈ closedHalfDisc (r / 2), |w y| ≤ A * size) ∧
        (∀ j, ∀ y ∈ closedHalfDisc (r / 2),
          |fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j)| ≤ A * size) ∧
        (∀ j, ∃ C : ℝ≥0, (C : ℝ) ≤ A * size ∧
          HolderOnWith C gamma
            (fun y => fderivWithin ℝ w (closedHalfDisc (r / 2)) y (coordinateVector 2 j))
            (closedHalfDisc (r / 2))) := by sorry

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
