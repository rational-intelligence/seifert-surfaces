import B1LocalIsolation_v468
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
theorem original_prop57_tangencies {g : SmoothMetric E.Carrier}
    {J : LongitudeFoliation.{v} E} (D : B1OriginalData g J) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ D.r0 ∧
      (∀ s : Circle, ∀ r ∈ Ioo (0 : ℝ) rho,
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, r) ≠ 0) ∧
      Set.Finite {s : Circle |
        mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ)
          (fun p : Circle × ℝ => D.f p.1 p.2) (s, 0) = 0} := by
  exact B1Tangency.same_circle_compact_globalization D (B1Tangency.actual_boundary_local_isolation D)

end SeifertSurfaces.OriginalEndpoints

#print axioms SeifertSurfaces.OriginalEndpoints.original_prop57_tangencies
