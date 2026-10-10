import A7SourceInputsV463

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology MeasureTheory
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Full native geometric proper image isotopy fixing the initial boundary
pointwise; the endpoint is allowed a geometric source homeomorphism. -/
def FixedBoundaryImageIsotopic {S R : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (G : GeometricPiecewiseSurface R E.Carrier) : Prop :=
  ∃ e : GeometricSourceHomeomorph F G,
    ∃ stage : Time → GeometricPiecewiseSurface S E.Carrier,
      Continuous (fun p : Time × S => (stage p.1).map p.2) ∧
      Nonempty (GeometricTrack F (fun p => (stage p.1).map p.2)) ∧
      (stage 0).map = F.map ∧
      (stage 1).map = G.map.comp ⟨e.homeomorph, e.homeomorph.continuous⟩ ∧
      ∀ t x, x ∈ S.boundary → (stage t).map x = F.map x

/-- Equation (E)(i): infimum of actual induced area over the entire geometric
piecewise proper image isotopy class relative to the fixed boundary. -/
def fixedBoundaryInfimum (g : SmoothMetric E.Carrier)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier) : ℝ :=
  sInf {a : ℝ | ∃ R : CompactOrientedSurface.{u},
    ∃ C : GeometricPiecewiseSurface R E.Carrier,
      FixedBoundaryImageIsotopic E F C ∧ a = geometricArea g C}

/-- Source F' belongs to the full fixed-boundary class and attains its
infimum. This is the premise of A.2/A.5, never the premise of A.6. -/
structure FixedBoundaryMinimizer (g : SmoothMetric E.Carrier)
    {S R : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier) : Prop where
  in_class : FixedBoundaryImageIsotopic E F Fprime
  attainment : geometricArea g Fprime = fixedBoundaryInfimum E g F

/-- Actual minimality of the same smooth embedding in the same two-sided
metric extension, at every genuine interior source chart. -/
def MinimalEmbedding (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S E.Carrier) : Prop :=
  ∀ p : S, IsMinimalPatch G.extension
    (E.toSphere ∘ f.toFun ∘ (extChartAt (𝓡∂ 2) p).symm)
    ((extChartAt (𝓡∂ 2) p).target ∩ {y : E2 | 0 < y 0})

/-- Fixed-boundary stability: actual nonnegative second area variation
for every joint smooth normal deformation fixing the boundary. -/
def StableFixedBoundary (g : SmoothMetric E.Carrier) {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S E.Carrier) : Prop :=
  ∀ H : ℝ → ProperSmoothEmbedding S E.Carrier,
    (H 0).toFun = f.toFun →
    ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
      (fun p : ℝ × S => (H p.1).toFun p.2) →
    (∀ t x, x ∈ S.boundary → (H t).toFun x = f.toFun x) →
    ContDiffAt ℝ 2 (fun t => area g (H t).toFun) 0 →
    0 ≤ deriv (deriv (fun t => area g (H t).toFun)) 0

/-- Complete A.5 image regularity, retaining its actual labelled boundary,
minimality and fixed-boundary stability. The smooth source structure is output. -/
structure SmoothStableMinimalImage (G : A7.SourceGeometry E)
    (image boundary : Set E.Carrier) where
  source : CompactOrientedSurface.{u}
  embedding : ProperSmoothEmbedding source E.Carrier
  image_eq : embedding.image = image
  boundary_eq : embedding.toFun '' source.boundary = boundary
  ambient_boundary_eq : image ∩ (𝓡∂ 3).boundary E.Carrier = boundary
  minimal : MinimalEmbedding E G embedding
  stable : StableFixedBoundary E G.metric embedding

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
