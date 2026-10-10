import PiecewiseCompetitors import AcyclicMathlibSupport import ProofTermLoader

open scoped Manifold ContDiff
open Set Topology MeasureTheory
namespace SeifertSurfaces.MetricFoundations
open Foundations
universe u v
noncomputable section
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
attribute [-instance] TopCat.of.chartedSpace CompleteLattice.toCompletePartialOrder
/-- A local smooth chart for the IMAGE off the seam. Its homeomorphism is
topological; no differentiability with respect to the auxiliary source S is
required. Regularity and rank are measured on the actual ambient image. -/
structure SmoothImageChart (S : CompactOrientedSurface.{u}) (f : S → M) where
  chart : PartialHomeomorph S (EuclideanHalfSpace 2)
  source_open : IsOpen chart.source
  target_open : IsOpen chart.target
  cInfinity : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ (f ∘ chart.symm) chart.target
  differential_injective : ∀ y ∈ chart.target, Function.Injective
    (mfderivWithin (𝓡∂ 2) (𝓡∂ 3) (f ∘ chart.symm) chart.target y)
  boundary_image : chart '' (S.boundary ∩ chart.source) =
    ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ chart.target

/-- Literal geometric pieces of Definition A.1. A fixed smooth S supplies
only compact topology, pi1 and a boundary-labelled parameter space. Whole
pieces use polar sectors of every opening in (0,2pi); their parametrizations
into S are only topological. All C1/rank requirements concern the map into M.
In particular, no nondegenerate C1 sector-to-source-halfspace map is required. -/
structure GeometricPiecewiseSurface (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] where
  map : C(S, M)
  embedding : IsEmbedding map
  boundary_preimage : map ⁻¹' ((𝓡∂ 3).boundary M) = S.boundary
  seam : SeamGraph S map
  smooth_off_seam : ∀ x ∈ seam.carrierᶜ,
    ∃ c : SmoothImageChart S map, x ∈ c.chart.source ∧ c.chart.source ⊆ seam.carrierᶜ
  pieceCount : ℕ
  domain : Fin pieceCount → CompactSectorPiece.{u}
  parametrization : ∀ i, C(domain i, S)
  parametrization_embedding : ∀ i, IsEmbedding (parametrization i)
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

namespace GeometricPiecewiseSurface
variable {S : CompactOrientedSurface.{u}}
def image (F : GeometricPiecewiseSurface S M) : Set M := Set.range F.map
def Incompressible (F : GeometricPiecewiseSurface S M) : Prop :=
  ∀ x, Function.Injective (FundamentalGroup.map F.map x)
end GeometricPiecewiseSurface

def geometricArea (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) : ℝ :=
  ∑ i, sectorArea g (F.map ∘ F.parametrization i)

/-- A geometric cylinder subdivision is anchored to the initial embedded
image: the source graph (time,F(x)) and the target graph (time,track(time,x))
are genuine C1 rank-three maps on compact quadrant prisms. No rough cylinder
homeomorphism can create this regularity by itself. No derivative into the
auxiliary source halfspace is requested. -/
structure GeometricTrack {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (track : Time × S → M) where
  count : ℕ
  prism : Fin count → CompactCornerPrism.{u}
  parametrization : ∀ i, C(prism i, Time × S)
  embedding : ∀ i, IsEmbedding (parametrization i)
  covers : (⋃ i, Set.range (parametrization i)) = univ
  source_c1 : ∀ i, ContMDiff (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod (𝓡∂ 3)) 1
      (fun q => ((parametrization i q).1, F.map (parametrization i q).2))
  source_injective : ∀ i q, Function.Injective
    (mfderiv (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 3))
      (fun q => ((parametrization i q).1, F.map (parametrization i q).2)) q)
  source_smooth_interior : ∀ i, ContMDiffOn (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod (𝓡∂ 3)) ∞
      (fun q => ((parametrization i q).1, F.map (parametrization i q).2))
      ((modelWithCornersEuclideanQuadrant 3).interior (prism i))
  target_c1 : ∀ i, ContMDiff (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod (𝓡∂ 3)) 1
      (fun q => ((parametrization i q).1, track (parametrization i q)))
  target_injective : ∀ i q, Function.Injective
    (mfderiv (modelWithCornersEuclideanQuadrant 3) ((𝓡∂ 1).prod (𝓡∂ 3))
      (fun q => ((parametrization i q).1, track (parametrization i q))) q)
  target_smooth_interior : ∀ i, ContMDiffOn (modelWithCornersEuclideanQuadrant 3)
    ((𝓡∂ 1).prod (𝓡∂ 3)) ∞
      (fun q => ((parametrization i q).1, track (parametrization i q)))
      ((modelWithCornersEuclideanQuadrant 3).interior (prism i))

/-- Piecewise morphism measured in the geometric source and target images.
The initial-image anchor supplies both genuine coordinate regularity and rank.
Convex subpieces here are subdivisions for morphisms, not a restriction on
the whole geometric pieces of Definition A.1. -/
structure GeometricSourceMap {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M)
    (f : S → R) where
  count : ℕ
  domain : Fin count → CompactCornerPiece.{u}
  parametrization : ∀ i, C(domain i, S)
  embedding : ∀ i, IsEmbedding (parametrization i)
  covers : (⋃ i, Set.range (parametrization i)) = univ
  source_c1 : ∀ i, ContMDiff CornerModel (𝓡∂ 3) 1 (F.map ∘ parametrization i)
  source_injective : ∀ i x,
    Function.Injective (mfderiv CornerModel (𝓡∂ 3) (F.map ∘ parametrization i) x)
  source_smooth_interior : ∀ i, ContMDiffOn CornerModel (𝓡∂ 3) ∞
    (F.map ∘ parametrization i) (CornerModel.interior (domain i))
  target_c1 : ∀ i, ContMDiff CornerModel (𝓡∂ 3) 1 (G.map ∘ f ∘ parametrization i)
  target_injective : ∀ i x,
    Function.Injective (mfderiv CornerModel (𝓡∂ 3) (G.map ∘ f ∘ parametrization i) x)
  target_smooth_interior : ∀ i, ContMDiffOn CornerModel (𝓡∂ 3) ∞
    (G.map ∘ f ∘ parametrization i) (CornerModel.interior (domain i))

structure GeometricSourceHomeomorph {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M) where
  homeomorph : S ≃ₜ R
  forward : GeometricSourceMap F G homeomorph
  backward : GeometricSourceMap G F homeomorph.symm
  boundary_image : homeomorph '' S.boundary = R.boundary

structure GeometricNormalIsotopy {S : CompactOrientedSurface.{u}}
    (F G : GeometricPiecewiseSurface S M) where
  stage : Time → GeometricPiecewiseSurface S M
  continuous_family : Continuous (fun p : Time × S => (stage p.1).map p.2)
  regularity : GeometricTrack F (fun p => (stage p.1).map p.2)
  initial : (stage 0).map = F.map
  terminal : (stage 1).map = G.map

def GeometricFixedBoundaryIsotopic {S : CompactOrientedSurface.{u}}
    (F G : GeometricPiecewiseSurface S M) : Prop :=
  ∃ H : GeometricNormalIsotopy F G,
    ∀ t x, x ∈ S.boundary → (H.stage t).map x = F.map x

def GeometricIsotopic {S : CompactOrientedSurface.{u}}
    (F G : GeometricPiecewiseSurface S M) : Prop := Nonempty (GeometricNormalIsotopy F G)

def GeometricImageIsotopic {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S M) (G : GeometricPiecewiseSurface R M) : Prop :=
  ∃ e : GeometricSourceHomeomorph F G,
    ∃ stage : Time → GeometricPiecewiseSurface S M,
      Continuous (fun p : Time × S => (stage p.1).map p.2) ∧
      Nonempty (GeometricTrack F (fun p => (stage p.1).map p.2)) ∧
      (stage 0).map = F.map ∧ (stage 1).map =
        G.map.comp ⟨e.homeomorph, e.homeomorph.continuous⟩

theorem piecewiseArea_same_image (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (G : GeometricPiecewiseSurface R M) (h : F.image = G.image) :
    geometricArea g F = geometricArea g G := by
  specialized_category_proof "/home/caoyichuan/test/seifert-surfaces/target/provenance/B1CategoryArea3/SeifertSurfaces.MetricFoundations.piecewiseArea_same_image_SPECIALIZED_TERM.json"
theorem smooth_as_piecewise {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) : ∃ F : GeometricPiecewiseSurface S M,
    F.map = f.continuousMap ∧ F.seam.carrier = ∅ := by
  specialized_category_proof "/home/caoyichuan/test/seifert-surfaces/target/provenance/B1CategoryArea3/SeifertSurfaces.MetricFoundations.smooth_as_piecewise_SPECIALIZED_TERM.json"
theorem smooth_piecewise_area (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (F : GeometricPiecewiseSurface S M) (h : F.map = f.continuousMap) :
    geometricArea g F = area g f.toFun := by
  specialized_category_proof "/home/caoyichuan/test/seifert-surfaces/target/provenance/B1CategoryArea3/SeifertSurfaces.MetricFoundations.smooth_piecewise_area_SPECIALIZED_TERM.json"
end
end SeifertSurfaces.MetricFoundations
