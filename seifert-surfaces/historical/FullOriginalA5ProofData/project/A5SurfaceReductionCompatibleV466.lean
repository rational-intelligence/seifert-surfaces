import A5OrientationTransportCompatibleV466
import ExternalTransportContracts
import GeometricCategory

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u

structure CompatibleOrientedSurfaceReduction (S : CompactOrientedSurface.{u}) where
  surface : CompactOrientedSurface.{0}
  diffeomorph : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S surface ∞
  boundary_image : diffeomorph '' S.boundary = surface.boundary

/-- A genuine universe reduction transports the old atlas and its differential form through a diffeomorphism. -/
theorem a5_compatible_oriented_surface_reduction_of_embedding
    (S : CompactOrientedSurface.{u}) {M : Type} [TopologicalSpace M]
    (f : S → M) (hf : IsEmbedding f) : Nonempty (CompatibleOrientedSurfaceReduction S) := by
  classical
  let e : S ≃ₜ Set.range f := hf.toHomeomorph
  letI : ChartedSpace (EuclideanHalfSpace 2) (Set.range f) := e.chartedSpace
  letI : IsManifold (𝓡∂ 2) ∞ (Set.range f) := Transport.homeomorph_atlas_manifold (𝓡∂ 2) ∞ e
  letI : T2Space (Set.range f) := e.t2Space
  letI : CompactSpace (Set.range f) := e.compactSpace
  letI : SecondCountableTopology (Set.range f) := e.symm.isEmbedding.secondCountableTopology
  let D : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S (Set.range f) ∞ := {
    toEquiv := e.toEquiv
    contMDiff_toFun := Transport.homeomorph_atlas_forward (𝓡∂ 2) ∞ e
    contMDiff_invFun := Transport.homeomorph_atlas_inverse (𝓡∂ 2) ∞ e }
  obtain ⟨O,_,_⟩ := a5_smooth_volume_orientation_diffeomorph_transport D S.orientation
  let Q : CompactOrientedSurface.{0} := {carrier := Set.range f, orientation := O}
  exact ⟨{surface := Q, diffeomorph := D, boundary_image := D.image_boundary (by simp)}⟩

#print axioms a5_compatible_oriented_surface_reduction_of_embedding
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
