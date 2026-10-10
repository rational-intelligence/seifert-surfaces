import A5PaidSmoothBoundaryConsumerCompatibility

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- The complete original A5 conclusion from the separately owned native
C1 boundary geometry producer. All smooth boundary regularity, metric PDE
transport, smooth-source reconstruction and stability are discharged. -/
theorem original_A5_certificate_of_native_boundary_C1_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (hboundary : ∀ x ∈ R.boundary,
      ∃ C : BoundaryC1ImageChart R E.Carrier Fprime.map, x ∈ C.chart.source) :
    Nonempty (SmoothStableMinimalImage.{u} E G Fprime.image
      (F.map '' S.boundary)) := by
  have hFb : J.BoundaryIn Fprime.map := by
    obtain ⟨a,ha⟩ := hF_boundary
    exact ⟨a,hminimum.in_class.boundary_image_eq.trans ha⟩
  have hcover : ∀ y, y ∉ R.boundary →
      ∃ C : SmoothImageChart R Fprime.map, y ∈ C.chart.source := by
    intro y hy
    obtain ⟨C,hC,_⟩ := original_minimizer_interior_smooth_image_charts
      E G J F hF_incompressible hF_boundary Fprime hminimum y hy
    exact ⟨C,hC⟩
  have hpieces := original_minimizer_native_pieces_minimal
    E G J F hF_incompressible hF_boundary Fprime hminimum
  apply original_A5_certificate_of_native_boundary_image_charts
    E G J F hF_incompressible hF_boundary Fprime hminimum
  intro x hx
  obtain ⟨C,hCx⟩ := hboundary x hx
  exact native_boundary_C1_image_chart_to_smooth
    E J Fprime hFb C x hCx hx G.extension hcover hpieces

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
