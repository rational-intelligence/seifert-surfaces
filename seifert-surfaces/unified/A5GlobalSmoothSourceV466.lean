import GeometricCategory
import A5SourceAssemblyV466
import A5SmoothOrientationFromTopologicalV466
import A5SurfaceReductionCompatibleV466

/-!
Global smooth-source reconstruction after the native A5 image charts cover
the entire geometric piecewise surface. This is an independent differential
topology obligation, not an additional premise on the original A5 theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource

universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- Actual smooth, compact, oriented source for the identical geometric image.
The source bundle includes a compatible C∞ half-space atlas and an everywhere
nonzero smooth orientation two-form. Both must be constructed, rather than
supplied as hypotheses or pulled back through a merely topological map. -/
structure SmoothSourceReconstruction {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier) where
  source : CompactOrientedSurface.{u}
  embedding : ProperSmoothEmbedding source E.Carrier
  homeomorph : source ≃ₜ S
  pointwise_same_map : ∀ z : source, embedding.toFun z = F.map (homeomorph z)
  boundary_transport : homeomorph '' source.boundary = S.boundary
  image_eq : embedding.image = F.image
  boundary_image_eq : embedding.toFun '' source.boundary = F.map '' S.boundary

/-- Construct a genuine smooth oriented source at the original universe from
a cover by the native smooth image charts, retaining the original map
pointwise through a source homeomorphism and transporting the exact boundary.

Source: Proposition A.5, extracted lines 1280--1282, p. 26, where the local
smooth structures at every point of compact F′ are assembled globally. The
image-chart cover is produced by the original A5 local regularity owner.
No compatibility atlas, smooth orientation form, smooth representative,
minimality, stability, or geometric isotopy track is assumed here. -/
theorem smooth_source_of_native_image_chart_cover
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (hcover : ∀ x : S, ∃ c : SmoothImageChart S F.map, x ∈ c.chart.source) :
    Nonempty (SmoothSourceReconstruction E F) := by
  classical
  obtain ⟨R⟩ := a5_compatible_oriented_surface_reduction_of_embedding S F.map F.embedding
  obtain ⟨A⟩ := native_image_smooth_atlas_exists F hcover
  let C : A5CompactSmoothCarrier.{u} := {
    carrier := S.carrier
    charted := A.charted
    smooth := A.smooth }
  let h : R.surface ≃ₜ C := R.diffeomorph.symm.toHomeomorph
  obtain ⟨O⟩ := a5_smooth_orientation_from_oriented_topology R.surface C h
  obtain ⟨Q⟩ := native_image_source_assembly_of_orientation F A O
  exact ⟨{
    source := Q.source
    embedding := Q.embedding
    homeomorph := Q.homeomorph
    pointwise_same_map := Q.pointwise_same_map
    boundary_transport := Q.boundary_transport
    image_eq := Q.image_eq
    boundary_image_eq := Q.boundary_image_eq }⟩

#print axioms smooth_source_of_native_image_chart_cover
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
