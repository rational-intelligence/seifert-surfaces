import B1ActualCollarInverse_v475
import EndpointGeometry

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000

/-- The actual collar, restricted to an open interior tube, is one smooth
ambient chart with its literal coordinate inverse. -/
theorem actual_interior_collar_ambient_chart_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (O : Set E3) (hO : IsOpen O) (hOC : O ⊆ collarDomain D W.R) :
    ∃ c : SmoothAmbientChart ThreeSphere,
      c.chart.source = (E.toSphere ∘ localCollar D s) '' O ∧
      c.chart.target = O ∧
      (∀ y ∈ O, c.chart (E.toSphere (localCollar D s y)) = y) ∧
      (∀ y ∈ O, c.chart.symm y = E.toSphere (localCollar D s y)) := by
  obtain ⟨Φ,hsource,htarget,hfun⟩ :=
    actual_interior_collar_global_partialDiffeomorph_v475 D s W O hO hOC
  let c : SmoothAmbientChart ThreeSphere := {
    chart := Φ.symm.toOpenPartialHomeomorph
    smooth := Φ.symm.contMDiffOn
    inverse_smooth := Φ.contMDiffOn }
  refine ⟨c,htarget,hsource,?_,?_⟩
  · intro y hy
    change Φ.symm (E.toSphere (localCollar D s y)) = y
    have hFy : Φ y = E.toSphere (localCollar D s y) := congrFun hfun y
    rw [← hFy]
    exact Φ.toPartialEquiv.left_inv (hsource.symm ▸ hy)
  · intro y hy
    change Φ y = E.toSphere (localCollar D s y)
    exact congrFun hfun y

#print axioms actual_interior_collar_ambient_chart_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
