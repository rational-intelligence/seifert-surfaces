import BoundaryFoliation
import SectorPieces
import Mathlib.Topology.Connected.LocallyConnected

open scoped Manifold ContDiff
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section

abbrev CornerModel := modelWithCornersEuclideanQuadrant 2

/-- Smooth abstract pieces with a genuine quadrant model. The embedding of
each piece is C1 up to its boundary and smooth on its interior. -/
structure CompactCornerPiece where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanQuadrant 2) carrier]
  [smooth : IsManifold CornerModel ∞ carrier]
  [compact : CompactSpace carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]
attribute [instance] CompactCornerPiece.topology CompactCornerPiece.charted
  CompactCornerPiece.smooth CompactCornerPiece.compact CompactCornerPiece.hausdorff
  CompactCornerPiece.secondCountable
instance : CoeSort CompactCornerPiece (Type u) := ⟨CompactCornerPiece.carrier⟩
instance cornerMeasurable (P : CompactCornerPiece.{u}) : MeasurableSpace P := borel P

structure CornerChartPartition (P : CompactCornerPiece.{u}) where
  count : ℕ
  center : Fin count → P
  piece : Fin count → Set P
  measurable : ∀ i, MeasurableSet (piece i)
  subordinate : ∀ i, piece i ⊆ (extChartAt CornerModel (center i)).source
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  covers : (⋃ i, piece i) = univ

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Finite graph in the surface and in its embedded image, with smooth arcs
and circles; arc interiors are disjoint and lie off the surface boundary.
Circle components can be split into arcs at incident vertices. -/
structure SeamGraph (S : CompactOrientedSurface.{u}) (f : S → M) where
  arcCount : ℕ
  circleCount : ℕ
  arc : Fin arcCount → C(Time, S)
  circle : Fin circleCount → C(Circle, S)
  arc_embedding : ∀ i, IsEmbedding (arc i)
  circle_embedding : ∀ i, IsEmbedding (circle i)
  arc_smooth_image : ∀ i, ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞
    (f ∘ arc i)
  arc_differential_injective : ∀ i x,
    Function.Injective (mfderiv (𝓡∂ 1) (𝓡∂ 3) (f ∘ arc i) x)
  circle_smooth_image : ∀ i, ContMDiff (𝓡 1) (𝓡∂ 3) ∞
    (f ∘ circle i)
  circle_differential_injective : ∀ i x,
    Function.Injective (mfderiv (𝓡 1) (𝓡∂ 3) (f ∘ circle i) x)
  arc_boundary : ∀ i, (arc i) ⁻¹' S.boundary ⊆ {0, 1}
  circle_off_boundary : ∀ i, Disjoint (Set.range (circle i)) S.boundary
  arc_intersections : ∀ i j, i ≠ j →
    Set.range (arc i) ∩ Set.range (arc j) ⊆
      {arc i 0, arc i 1} ∩ {arc j 0, arc j 1}
  circle_intersections : Pairwise (fun i j =>
    Disjoint (Set.range (circle i)) (Set.range (circle j)))
  arc_circle_disjoint : ∀ i j, Disjoint (Set.range (arc i)) (Set.range (circle j))

def SeamGraph.carrier {S : CompactOrientedSurface.{u}} {f : S → M}
    (G : SeamGraph S f) : Set S :=
  (⋃ i, Set.range (G.arc i)) ∪ (⋃ i, Set.range (G.circle i))

/-- Reference presentations in a fixed smooth source category. This bundle
is deliberately NOT the literal whole-piece category of Definition A.1:
its source-coordinate conditions can require subdivision at reflex corners.
GeometricCategory and SourceReferenceComparison state the actual source
category and its explicit representation and isotopy comparison obligations. -/
structure PiecewiseSurface (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] where
  map : C(S, M)
  embedding : IsEmbedding map
  boundary_preimage : map ⁻¹' ((𝓡∂ 3).boundary M) = S.boundary
  seam : SeamGraph S map
  smooth_off_seam : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ map (seam.carrier)ᶜ
  pieceCount : ℕ
  domain : Fin pieceCount → CompactSectorPiece.{u}
  parametrization : ∀ i, C(domain i, S)
  parametrization_embedding : ∀ i, IsEmbedding (parametrization i)
  parametrization_c1 : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) 1
    (parametrization i ∘ ((domain i).chart j).map.symm) ((domain i).chart j).map.target
  parametrization_differential_injective : ∀ i j y,
    y ∈ ((domain i).chart j).map.target → Function.Injective
      (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
        (parametrization i ∘ ((domain i).chart j).map.symm)
          ((domain i).chart j).map.target y)
  piece_c1 : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) 1
    (sectorCoordinateMap (map ∘ parametrization i) j) ((domain i).chart j).map.target
  piece_topological_embedding : ∀ i, IsEmbedding (map ∘ parametrization i)
  piece_differential_injective : ∀ i j y, y ∈ ((domain i).chart j).map.target →
    Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (sectorCoordinateMap (map ∘ parametrization i) j) ((domain i).chart j).map.target y)
  piece_smooth_interior : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 3) ∞
    (sectorCoordinateMap (map ∘ parametrization i) j)
      (interior ((domain i).chart j).map.target)
  piece_edges_smooth : ∀ i j t,
    t = 0 ∨ t = ((domain i).chart j).model.angle →
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 3) ∞
      (fun r => sectorCoordinateMap (map ∘ parametrization i) j (r • sectorUnit t))
      (Ico (0 : ℝ) ((domain i).chart j).model.radius)
  piece_interior_component : ∀ i, ∃ x ∈ (seam.carrier ∪ S.boundary)ᶜ,
    (parametrization i) '' (domain i).interior =
      connectedComponentIn (seam.carrier ∪ S.boundary)ᶜ x
  pieces_distinct : Pairwise (fun i j =>
    Disjoint ((parametrization i) '' (domain i).interior)
      ((parametrization j) '' (domain j).interior))
  piece_closure : ∀ i, Set.range (parametrization i) =
    closure ((parametrization i) '' (domain i).interior)
  covers : (⋃ i, Set.range (parametrization i)) = univ
  piece_boundary : ∀ i,
    (parametrization i) '' (domain i).boundary ⊆ seam.carrier ∪ S.boundary

namespace PiecewiseSurface
variable {S : CompactOrientedSurface.{u}}
def image (F : PiecewiseSurface S M) : Set M := Set.range F.map
def Incompressible (F : PiecewiseSurface S M) : Prop :=
  ∀ x, Function.Injective (FundamentalGroup.map F.map x)
end PiecewiseSurface

def cornerCoordinateGram (g : SmoothMetric M) {P : CompactCornerPiece.{u}}
    (f : P → M) (p : P) (y : Euc 2) : Matrix (Fin 2) (Fin 2) ℝ :=
    let e := extChartAt CornerModel p
    let d := mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 3) (f ∘ e.symm) e.target y
    fun j k =>
      g.inner (f (e.symm y))
        (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single j 1)))
        (d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single k 1)))

def cornerCoordinateDensity (g : SmoothMetric M) {P : CompactCornerPiece.{u}}
    (f : P → M) (p : P) (y : Euc 2) : ℝ :=
  Real.sqrt (cornerCoordinateGram g f p y).det

def cornerPartitionArea (g : SmoothMetric M) {P : CompactCornerPiece.{u}}
    (f : P → M) (C : CornerChartPartition P) : ℝ :=
  ∑ i, ∫ y in (extChartAt CornerModel (C.center i)) '' (C.piece i),
    cornerCoordinateDensity g f (C.center i) y

def piecewiseArea (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : PiecewiseSurface S M) : ℝ :=
  ∑ i, sectorArea g (F.map ∘ F.parametrization i)

/-- A genuine isotopy of piecewise surfaces: a jointly continuous family of
embeddings, each with its own finite smooth seam/piece data. Pointwise boundary
fixing is an endpoint-independent condition, not a smooth ambient isotopy. -/
structure CompactCornerPrism where
  carrier : Type u
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanQuadrant 3) carrier]
  [smooth : IsManifold (modelWithCornersEuclideanQuadrant 3) ∞ carrier]
  [compact : CompactSpace carrier]
  [hausdorff : T2Space carrier]
attribute [instance] CompactCornerPrism.topology CompactCornerPrism.charted
  CompactCornerPrism.smooth CompactCornerPrism.compact CompactCornerPrism.hausdorff
instance : CoeSort CompactCornerPrism (Type u) := ⟨CompactCornerPrism.carrier⟩

/-- Finite joint regularity in the fixed cylinder category: both the
prism-to-time/source map and the ambient track are C1, with smooth interiors.
The cylinder parametrization has injective differential, so an arbitrary
rough coordinate change cannot supply this regularity. -/
structure PiecewiseTrack (S : CompactOrientedSurface.{u}) (track : Time × S → M) where
  count : ℕ
  prism : Fin count → CompactCornerPrism.{u}
  parametrization : ∀ i, C(prism i, Time × S)
  embedding : ∀ i, IsEmbedding (parametrization i)
  parametrization_c1 : ∀ i,
    ContMDiff (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 2)) 1
      (parametrization i)
  parametrization_smooth_interior : ∀ i,
    ContMDiffOn (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 2)) ∞
      (parametrization i) ((modelWithCornersEuclideanQuadrant 3).interior (prism i))
  parametrization_differential_injective : ∀ i x, Function.Injective
    (mfderiv (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 2))
      (parametrization i) x)
  covers : (⋃ i, Set.range (parametrization i)) = univ
  c1_track : ∀ i, ContMDiff (modelWithCornersEuclideanQuadrant 3) (𝓡∂ 3) 1
    (track ∘ parametrization i)
  smooth_interior : ∀ i, ContMDiffOn (modelWithCornersEuclideanQuadrant 3) (𝓡∂ 3) ∞
    (track ∘ parametrization i)
      ((modelWithCornersEuclideanQuadrant 3).interior (prism i))

structure PiecewiseNormalIsotopy (S : CompactOrientedSurface.{u})
    (F G : PiecewiseSurface S M) where
  stage : Time → PiecewiseSurface S M
  continuous_family : Continuous (fun p : Time × S => (stage p.1).map p.2)
  regularity : PiecewiseTrack S (fun p => (stage p.1).map p.2)
  initial : (stage 0).map = F.map
  terminal : (stage 1).map = G.map

def FixedBoundaryIsotopic {S : CompactOrientedSurface.{u}}
    (F G : PiecewiseSurface S M) : Prop :=
  ∃ H : PiecewiseNormalIsotopy S F G,
    ∀ t x, x ∈ S.boundary → (H.stage t).map x = F.map x

/-- Boundary sliding places no leaf condition on intermediate isotopy stages,
as in proper isotopy classes in the source. End competitors have boundary in J.
The relation is in the piecewise category, not invented smooth equivalence. -/
def PiecewiseIsotopic {S : CompactOrientedSurface.{u}}
    (F G : PiecewiseSurface S M) : Prop := Nonempty (PiecewiseNormalIsotopy S F G)

/-- Finite source-coordinate sector presentations make the endpoint map a
piecewise smooth morphism of the actual source smooth structures. -/
structure PiecewiseSourceMap (S R : CompactOrientedSurface.{u}) (f : S → R) where
  count : ℕ
  domain : Fin count → CompactSectorPiece.{u}
  parametrization : ∀ i, C(domain i, S)
  embedding : ∀ i, IsEmbedding (parametrization i)
  covers : (⋃ i, Set.range (parametrization i)) = univ
  source_c1 : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) 1
    (parametrization i ∘ ((domain i).chart j).map.symm) ((domain i).chart j).map.target
  source_injective : ∀ i j y, y ∈ ((domain i).chart j).map.target →
    Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (parametrization i ∘ ((domain i).chart j).map.symm) ((domain i).chart j).map.target y)
  image_c1 : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) 1
    (f ∘ parametrization i ∘ ((domain i).chart j).map.symm)
      ((domain i).chart j).map.target
  image_injective : ∀ i j y, y ∈ ((domain i).chart j).map.target →
    Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2)
      (f ∘ parametrization i ∘ ((domain i).chart j).map.symm)
        ((domain i).chart j).map.target y)
  source_smooth_interior : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞
    (parametrization i ∘ ((domain i).chart j).map.symm)
      (interior ((domain i).chart j).map.target)
  image_smooth_interior : ∀ i j, ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞
    (f ∘ parametrization i ∘ ((domain i).chart j).map.symm)
      (interior ((domain i).chart j).map.target)

structure PiecewiseSourceHomeomorph (S R : CompactOrientedSurface.{u}) where
  homeomorph : S ≃ₜ R
  forward : PiecewiseSourceMap S R homeomorph
  backward : PiecewiseSourceMap R S homeomorph.symm
  boundary_image : homeomorph '' S.boundary = R.boundary

end
end SeifertSurfaces.MetricFoundations
