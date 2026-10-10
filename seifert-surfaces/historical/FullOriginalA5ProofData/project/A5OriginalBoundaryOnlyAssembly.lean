import A5PaidRegularSeamCompatibility
import A5NativeBoundaryExceptionalSet
import A5NativeEndpointTangentAgreement

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u

/-- All original A5 debts except actual boundary image charts are now proved
under the literal full original minimizer context. -/
theorem original_A5_certificate_of_native_boundary_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (hboundary : ∀ x ∈ R.boundary,
      ∃ C : SmoothImageChart R Fprime.map, x ∈ C.chart.source) :
    Nonempty (SmoothStableMinimalImage.{u} E G Fprime.image
      (F.map '' S.boundary)) := by
  obtain ⟨harc,hcircle⟩ := original_minimizer_regular_seam_image_charts
    E G J F hF_incompressible hF_boundary Fprime hminimum
  exact original_A5_certificate_of_native_image_charts
    E G J F hF_incompressible hF_boundary Fprime hminimum hboundary harc hcircle

/-- Every point of the actual original minimizer has a punctured smooth
image neighborhood, including every exceptional boundary endpoint. -/
theorem original_minimizer_punctured_smooth_image_neighborhood
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime) (x : R) :
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ≠ x → ∃ C : SmoothImageChart R Fprime.map, y ∈ C.chart.source := by
  obtain ⟨harc,hcircle⟩ := original_minimizer_regular_seam_image_charts
    E G J F hF_incompressible hF_boundary Fprime hminimum
  exact native_boundary_endpoint_punctured_image_cover Fprime x harc hcircle

/-- The whole interior image of the original minimizer is smooth. All
ordinary seams and every isolated native vertex have actually been removed. -/
theorem original_minimizer_interior_smooth_image_charts
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) (J : LongitudeFoliation.{u} E)
    {S R : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (F : GeometricPiecewiseSurface S E.Carrier)
    (hF_incompressible : F.Incompressible) (hF_boundary : J.BoundaryIn F.map)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E G.metric F Fprime)
    (x : R) (hx : x ∉ R.boundary) :
    ∃ C : SmoothImageChart R Fprime.map,
      x ∈ C.chart.source ∧ C.chart.source ⊆ R.boundaryᶜ := by
  obtain ⟨U,hU,hxU,hcover⟩ := original_minimizer_punctured_smooth_image_neighborhood
    E G J F hF_incompressible hF_boundary Fprime hminimum x
  let V := U ∩ R.boundaryᶜ
  have hV : IsOpen V := hU.inter
    ((𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by simp)).isOpen_compl
  let c : SmoothAmbientChart ThreeSphere := {
    chart := chartAt E3 (E.toSphere (Fprime.map x))
    smooth := contMDiffOn_chart
    inverse_smooth := contMDiffOn_chart_symm }
  obtain ⟨C,hxC,hC⟩ := native_interior_image_chart_of_punctured_image_cover
    E Fprime G.extension x V hV ⟨hxU,hx⟩ inter_subset_right c (mem_chart_source E3 _)
    (original_minimizer_native_pieces_minimal E G J F hF_incompressible hF_boundary Fprime hminimum)
    (fun y hy hne => hcover y hy.1 hne)
  exact ⟨C,hxC,fun y hy => (hC hy).2⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
