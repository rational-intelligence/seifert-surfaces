import A5PaidA2Compatibility
import A5NativeFiniteSeamConsumer
import A5NativeStabilityConsumer

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The exact paid original A2 root supplies native piece minimality to the
A5 consumer, with all original contexts and definition identities retained. -/
theorem original_minimizer_native_pieces_minimal
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) :
    ∀ i j, IsMinimalPatch G.extension
      (E.toSphere ∘ sectorCoordinateMap (Fprime.map ∘ Fprime.parametrization i) j)
      (interior ((Fprime.domain i).chart j).map.target) := by
  exact (A2_original_stationarity_and_minimality E G J F hF_incompressible hF_boundary Fprime hminimum).2

/-- Native seam/boundary image charts and the exact full original competitor
producer close the original A5 certificate. Piece minimality, finite vertex
removal, global source, labelled boundary, global minimality, actual area
comparison and second variation are all discharged here. -/
theorem original_A5_certificate_of_native_chart_and_competitor_producers
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (hboundary : ∀ x ∈ R.boundary, ∃ C : SmoothImageChart R Fprime.map, x ∈ C.chart.source)
    (harc : ∀ (a : Fin Fprime.seam.arcCount) (s : Time), 0 < s → s < 1 →
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.arc a s ∈ C.chart.source)
    (hcircle : ∀ (a : Fin Fprime.seam.circleCount) (s : Circle),
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.circle a s ∈ C.chart.source)
    (hcompetitors : ∀ (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime)
      (H : ℝ → ProperSmoothEmbedding Q.source E.Carrier),
      (H 0).toFun = Q.embedding.toFun →
      ContMDiff (𝓘(ℝ).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
        (fun p : ℝ × Q.source => (H p.1).toFun p.2) →
      (∀ t x, x ∈ Q.source.boundary → (H t).toFun x = Q.embedding.toFun x) →
      ∀ᶠ t in 𝓝 (0 : ℝ), ∃ C : GeometricPiecewiseSurface Q.source E.Carrier,
        C.map = (H t).continuousMap ∧ FixedBoundaryImageIsotopic E F C) :
    Nonempty (SmoothStableMinimalImage.{u} E G Fprime.image
      (F.map '' S.boundary)) := by
  have hpieces := original_minimizer_native_pieces_minimal E G J F
    hF_incompressible hF_boundary Fprime hminimum
  obtain ⟨Q, hminimal, hbd, hambient⟩ :=
    minimizer_smooth_minimal_source_of_regular_seam_and_boundary_charts E G F Fprime
      hminimum hpieces hboundary harc hcircle
  refine ⟨{
    source := Q.source
    embedding := Q.embedding
    image_eq := Q.image_eq
    boundary_eq := hbd
    ambient_boundary_eq := hambient
    minimal := hminimal
    stable := ?_ }⟩
  intro H hzero hsmooth hfixed harea
  exact reconstructed_second_variation_of_nearby_original_competitors hminimum Q H hzero
    (hcompetitors Q H hzero hsmooth hfixed) harea

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
