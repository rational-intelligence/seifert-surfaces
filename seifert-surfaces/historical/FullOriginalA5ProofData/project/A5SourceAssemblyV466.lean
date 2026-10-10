import A5ImageAtlasV466

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

structure NativeImageSourceAssembly {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M) where
  source : CompactOrientedSurface.{u}
  embedding : ProperSmoothEmbedding source M
  homeomorph : source ≃ₜ S
  pointwise_same_map : ∀ z : source, embedding.toFun z = F.map (homeomorph z)
  boundary_transport : homeomorph '' source.boundary = S.boundary
  image_eq : embedding.image = F.image
  boundary_image_eq : embedding.toFun '' source.boundary = F.map '' S.boundary

/-- Once the new atlas has its actual smooth volume form, all original-map transport is exact. -/
theorem native_image_source_assembly_of_orientation
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S M)
    (A : NativeImageSmoothAtlas F)
    (O : letI := A.charted; SmoothVolumeOrientation (𝓡∂ 2) S) :
    Nonempty (NativeImageSourceAssembly F) := by
  letI := A.charted
  letI := A.smooth
  let Q : CompactOrientedSurface.{u} := {carrier := S.carrier, orientation := O}
  let f : ProperSmoothEmbedding Q M := {
    toFun := F.map
    smooth := A.map_smooth
    embedding := F.embedding
    differential_injective := A.map_rank
    boundary_preimage := by
      change F.map ⁻¹' ((𝓡∂ 3).boundary M) = (𝓡∂ 2).boundary S
      rw [A.boundary_eq]
      exact F.boundary_preimage }
  let e : Q ≃ₜ S := Homeomorph.refl S.carrier
  refine ⟨{
    source := Q
    embedding := f
    homeomorph := e
    pointwise_same_map := fun _ => rfl
    boundary_transport := ?_
    image_eq := rfl
    boundary_image_eq := ?_}⟩
  · change id '' ((𝓡∂ 2).boundary S) = _
    rw [image_id,A.boundary_eq]
  · change F.map '' ((𝓡∂ 2).boundary S) = _
    rw [A.boundary_eq]

#print axioms native_image_source_assembly_of_orientation
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
