import A5SameImageClassTransport

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- The reconstructed smooth source itself belongs to the original full
fixed-boundary class and attains its original infimum. Neither a new track
nor a weakened image-only competitor relation is assumed. -/
theorem smooth_source_reconstruction_is_original_minimizer
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S R : CompactOrientedSurface.{u}} (g : SmoothMetric E.Carrier)
    (F : GeometricPiecewiseSurface S E.Carrier)
    (Fprime : GeometricPiecewiseSurface R E.Carrier)
    (hminimum : FixedBoundaryMinimizer E g F Fprime)
    (Q : GlobalSmoothSource.SmoothSourceReconstruction E Fprime) :
    ∃ H : GeometricPiecewiseSurface Q.source E.Carrier,
      H.map = Q.embedding.continuousMap ∧ H.seam.carrier = ∅ ∧
      FixedBoundaryMinimizer E g F H ∧
      area g Q.embedding.toFun = geometricArea g Fprime := by
  obtain ⟨H, hHmap, hHseam⟩ := smooth_as_piecewise Q.embedding
  have he (x : R) : H.map (Q.homeomorph.symm x) = Fprime.map x := by
    rw [hHmap]
    change Q.embedding.toFun (Q.homeomorph.symm x) = Fprime.map x
    rw [Q.pointwise_same_map, Q.homeomorph.apply_symm_apply]
  have hb : Q.homeomorph.symm '' R.boundary = Q.source.boundary := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [← Q.boundary_transport] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa only [Q.homeomorph.symm_apply_apply] using hz
    · intro hx
      refine ⟨Q.homeomorph x, ?_, Q.homeomorph.symm_apply_apply x⟩
      rw [← Q.boundary_transport]
      exact ⟨x, hx, rfl⟩
  have hinclass : FixedBoundaryImageIsotopic E F H :=
    hminimum.in_class.same_image_source F Fprime H Q.homeomorph.symm he hb
  have himage : H.image = Fprime.image := by
    change Set.range H.map = Fprime.image
    rw [hHmap]
    exact Q.image_eq
  have ha : geometricArea g H = geometricArea g Fprime := piecewiseArea_same_image g H Fprime himage
  refine ⟨H, hHmap, hHseam, ⟨hinclass, ha.trans hminimum.attainment⟩, ?_⟩
  exact (smooth_piecewise_area g Q.embedding H hHmap).symm.trans ha

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
