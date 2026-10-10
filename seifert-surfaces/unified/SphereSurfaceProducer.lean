import DiskBandProducers
import ShellLongitudeProducers

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
universe u
noncomputable section

open Module Filter OpenPartialHomeomorph Manifold IsManifold

structure RoundingPrism where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanQuadrant 3) carrier]
  [smooth : IsManifold (modelWithCornersEuclideanQuadrant 3) ∞ carrier]
  [compact : CompactSpace carrier]
  [hausdorff : T2Space carrier]
attribute [instance] RoundingPrism.topology RoundingPrism.charted
  RoundingPrism.smooth RoundingPrism.compact RoundingPrism.hausdorff
instance : CoeSort RoundingPrism Type := ⟨RoundingPrism.carrier⟩

structure GeometricRoundingTrack {X : Type} [TopologicalSpace X]
    (initial : X → Euc 3) (track : Time × X → Euc 3) where
  count : ℕ
  prism : Fin count → RoundingPrism
  coordinate : ∀ i, C(prism i, Time × X)
  embedding : ∀ i, IsEmbedding (coordinate i)
  covers : (⋃ i, Set.range (coordinate i)) = univ
  source_c1 : ∀ i, ContMDiff (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) 1
      (fun q => ((coordinate i q).1, initial (coordinate i q).2))
  source_rank : ∀ i q, Function.Injective
    (mfderiv (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
      (fun q => ((coordinate i q).1, initial (coordinate i q).2)) q)
  target_c1 : ∀ i, ContMDiff (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) 1
      (fun q => ((coordinate i q).1, track (coordinate i q)))
  target_rank : ∀ i q, Function.Injective
    (mfderiv (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
      (fun q => ((coordinate i q).1, track (coordinate i q))) q)
  smooth_interiors : ∀ i, ContMDiffOn (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ∞
      (fun q => ((coordinate i q).1, track (coordinate i q)))
      ((modelWithCornersEuclideanQuadrant 3).interior (prism i))

def diskBandSeams {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandData R) : Set (Euc 3) :=
  (⋃ k, ⋃ e : Fin 2, Set.range
    (fun t => (B.disk (B.incident k e)).lifted (B.height (B.incident k e)) (B.attaching k e t))) ∪
  (⋃ i, ⋃ j, {(!₂[(B.disk i).vertex j 0, (B.disk i).vertex j 1, B.height i] : Euc 3)})

structure DiskBandRounding {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandPresentation R) (δ : ℝ) where
  surface : CompactOrientedSurface.{0}
  [connected : ConnectedSpace surface]
  embedding : surface → Euc 3
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, Euc 3) ∞ embedding
  boundary : surface.OrientedBoundaryCircle
  boundary_covers : Set.range boundary.toFun = surface.boundary
  identification : B.data.Carrier ≃ₜ surface
  boundary_parameter : ∀ z, identification (B.boundary.boundary z) = boundary.toFun z
  stage : Time → C(B.data.Carrier, Euc 3)
  stage_embedding : ∀ t, IsEmbedding (stage t)
  continuous_family : Continuous (fun p : Time × B.data.Carrier => stage p.1 p.2)
  initial : (stage 0 : B.data.Carrier → Euc 3) = B.data.map
  terminal : (stage 1 : B.data.Carrier → Euc 3) = embedding ∘ identification
  regularity : GeometricRoundingTrack B.data.map (fun p => stage p.1 p.2)
  supported : ∀ t x, B.data.map x ∉ Metric.thickening δ (diskBandSeams B.data) →
    stage t x = B.data.map x
attribute [instance] DiskBandRounding.connected

structure SphereSpanningSurface (K : OrientedKnot) where
  surface : CompactOrientedSurface.{u}
  [connected : ConnectedSpace surface]
  embedding : surface → ThreeSphere
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡 3) ∞ embedding
  boundary : surface.OrientedBoundaryCircle
  boundary_covers : Set.range boundary.toFun = surface.boundary
  boundary_eq : ∀ z, embedding (boundary.toFun z) = K.component 0 z
attribute [instance] SphereSpanningSurface.connected


end
end SeifertSurfaces.LongitudeProducers
