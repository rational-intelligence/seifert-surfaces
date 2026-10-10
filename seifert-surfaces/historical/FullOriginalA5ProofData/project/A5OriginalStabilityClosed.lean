import A5OriginalEndpointAssembly
import A5OriginalDeformationContractV471

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- Every actual smooth-source reconstruction of the original geometric
minimizer is stable under all jointly smooth fixed-boundary deformations.
The native competitor and anchored track requirements are proved inputs. -/
theorem original_minimizer_reconstruction_stable
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S R : CompactOrientedSurface.{u}} {g : SmoothMetric E.Carrier}
    {F : GeometricPiecewiseSurface S E.Carrier}
    {Fprime : GeometricPiecewiseSurface R E.Carrier}
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime) :
    StableFixedBoundary E g Q.embedding := by
  intro H hzero hsmooth hboundary harea
  exact reconstructed_second_variation_of_nearby_original_competitors hminimum Q H hzero
    (reconstructed_smooth_family_nearby_original_competitors hminimum Q H hzero hsmooth hboundary)
    harea

/-- The original A5 conclusion now follows from its native seam and boundary
image charts alone. All exact original competitor, stability, minimality,
global-source and finite interior endpoint debts have been discharged. -/
theorem original_A5_certificate_of_native_image_charts
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
      ∃ C : SmoothImageChart R Fprime.map, Fprime.seam.circle a s ∈ C.chart.source) :
    Nonempty (SmoothStableMinimalImage.{u} E G Fprime.image
      (F.map '' S.boundary)) := by
  exact original_A5_certificate_of_native_chart_and_competitor_producers E G J F
    hF_incompressible hF_boundary Fprime hminimum hboundary harc hcircle
    (fun Q H hzero hsmooth hfixed =>
      reconstructed_smooth_family_nearby_original_competitors hminimum Q H hzero hsmooth hfixed)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
