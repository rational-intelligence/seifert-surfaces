import OriginalA4
import GeometricCategory

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A7

universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Standing Appendix A metric geometry, expressed in the actual two-sided
sphere extension of the actual exterior. This is the collar of source (2),
not transversality or a graph chart for any surface. -/
structure SourceGeometry where
  metric : SmoothMetric E.Carrier
  extension : AmbientMetric ThreeSphere
  metric_restriction : ∀ p : E.Carrier, ∀ v w : TangentSpace (𝓡∂ 3) p,
    metric.inner p v w = extension.inner (E.toSphere p)
      (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere p v)
      (mfderiv (𝓡∂ 3) (𝓡 3) E.toSphere p w)
  boundary_exact : ∀ p : E.Carrier,
    E.toSphere p ∈ frontier (Set.range E.toSphere) ↔ p ∈ (𝓡∂ 3).boundary E.Carrier
  collars : ∀ p ∈ (𝓡∂ 3).boundary E.Carrier,
    ∃ C : WarpedBoundaryCollar extension (Set.range E.toSphere),
      E.toSphere p ∈ C.coordinates.chart.source

/-- The actual source A.6 minimizer supplied to A.7. The competitor category
is the whole geometric piecewise category, with free intermediate boundary
motion and leaf-labelled endpoints. No neatness or boundary graph is a field. -/
structure A6Minimizer (G : SourceGeometry E) (J : LongitudeFoliation.{u} E) where
  source : CompactOrientedSurface.{u}
  connected : ConnectedSpace source
  initial : GeometricPiecewiseSurface source E.Carrier
  initial_incompressible : initial.Incompressible
  initial_boundary : J.BoundaryIn initial.map
  embedding : ProperSmoothEmbedding source E.Carrier
  representative : GeometricPiecewiseSurface source E.Carrier
  representative_map : representative.map = embedding.continuousMap
  properly_isotopic : GeometricImageIsotopic initial representative
  boundary_leaf : J.BoundaryIn embedding.toFun
  area_attainment : area G.metric embedding.toFun =
    sInf {a : ℝ | ∃ R : CompactOrientedSurface.{u},
      ∃ C : GeometricPiecewiseSurface R E.Carrier,
        J.BoundaryIn C.map ∧ GeometricImageIsotopic initial C ∧
          a = geometricArea G.metric C}
  minimal_interior : ∀ p : source,
    IsMinimalPatch G.extension
      (E.toSphere ∘ embedding.toFun ∘ (extChartAt (𝓡∂ 2) p).symm)
      ((extChartAt (𝓡∂ 2) p).target ∩ {y : E2 | 0 < y 0})
  stable_fixed_boundary : ∀ H : ℝ → ProperSmoothEmbedding source E.Carrier,
    (H 0).toFun = embedding.toFun →
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
      (fun p : ℝ × source => (H p.1).toFun p.2) →
    (∀ t x, x ∈ source.boundary → (H t).toFun x = embedding.toFun x) →
    ContDiffAt ℝ 2 (fun t => area G.metric (H t).toFun) 0 →
    0 ≤ deriv (deriv (fun t => area G.metric (H t).toFun)) 0


end SeifertSurfaces.OriginalEndpoints.A7
