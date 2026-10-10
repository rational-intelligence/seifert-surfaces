import OriginalB1_v468
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations SeifertSurfaces.AppendixB
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem canonical_original_prop57_tangencies_consumer {g : SmoothMetric E.Carrier}
    {J : LongitudeFoliation.{v} E} (D : B1OriginalData g J) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ D.r0 ∧
      (∀ s : Circle, ∀ r ∈ Ioo (0 : ℝ) rho,
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, r) ≠ 0) ∧
      Set.Finite {s : Circle |
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0} := by
  exact original_prop57_tangencies D

theorem canonical_B1_original_consumer {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
    (D : B1OriginalData g J) :
    BddAbove {l : ℝ | ∃ s : Circle, ∃ r ∈ Icc (0 : ℝ) D.r0,
      l = |deriv (deriv (D.f s)) r|} ∧
    (∃ s : Circle, B1NormalDerivative D s ≠ 0) ∧
    (∃ ς : ℝ, (ς = 1 ∨ ς = -1) ∧
      ∃ I : ClosedLeafArc J D.boundaryLabel D.leafParameter,
      ∃ a0 r1 : ℝ, 0 < a0 ∧ 0 < r1 ∧ r1 ≤ D.r0 ∧
        ∀ s ∈ I.parameterSet, ∀ r : ℝ, 0 < r → r ≤ r1 →
          (1 / 2 : ℝ) * a0 * r ≤ ς * D.f s r ∧ 0 < (1 / 2 : ℝ) * a0 * r) := by
  exact B1_original D

end SeifertSurfaces.OriginalEndpoints
