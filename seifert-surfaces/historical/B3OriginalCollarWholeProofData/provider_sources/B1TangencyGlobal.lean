import B1TangencyFiniteOrder

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

def LocalBoundaryIsolation (D : B1OriginalData g J) (s : Circle) : Prop :=
  ∃ U : Set (Circle × ℝ), IsOpen U ∧ (s, 0) ∈ U ∧
    ∀ p ∈ U ∩ radialCylinder D.r0, p ≠ (s, 0) →
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) p ≠ 0

/- Combine the chain at a critical boundary point and continuity at a
noncritical point, in the actual original manifold coordinates. -/
end SeifertSurfaces.OriginalEndpoints.B1Tangency
