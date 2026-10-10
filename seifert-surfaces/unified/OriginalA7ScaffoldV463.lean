import A7SourceInputsV463
import OriginalA4
import GeometricCategory
import A7GraphToA4V464
import A7BoundaryTransferV464
import A7CollarPlaneIdentityV464
import A7NativeImmersionCriterionV464

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC

noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A7

universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The tangent plane of the same actual surface map in the actual ambient
extension. This is the range of its differential, not a freely supplied plane. -/
def tangentPlane {G : SourceGeometry E} {J : LongitudeFoliation.{u} E}
    (minimizer : A6Minimizer E G J) (x : minimizer.source) :
    Submodule ℝ (TangentSpace (𝓡 3) (E.toSphere (minimizer.embedding.toFun x))) :=
  LinearMap.range
    (mfderiv (𝓡∂ 2) (𝓡 3) (E.toSphere ∘ minimizer.embedding.toFun) x).toLinearMap

theorem ambient_collared_nonzero (G : SourceGeometry E) (J : LongitudeFoliation.{u} E)
    (minimizer : A6Minimizer E G J) (x : minimizer.source) (hx : x ∈ minimizer.source.boundary)
    (C : WarpedBoundaryCollar G.extension (Set.range E.toSphere))
    (hp : E.toSphere (minimizer.embedding.toFun x) ∈ C.coordinates.chart.source) :
    ((mfderiv 𝓘(ℝ,E3) 𝓘(ℝ) C.radial (E.toSphere (minimizer.embedding.toFun x))).comp
      (tangentPlane E minimizer x).subtypeL ≠ 0) ∧
    tangentPlane E minimizer x ≠
      boundaryTangentPlane C (E.toSphere (minimizer.embedding.toFun x)) hp := by
  have hi : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ,E3) ∞ E.toSphere := E.inclusion
  have hs : ContMDiff (𝓡∂ 2) 𝓘(ℝ,E3) ∞ (E.toSphere ∘ minimizer.embedding.toFun) :=
    hi.isImmersion.contMDiff.comp minimizer.embedding.smooth
  have hd : Function.Injective
      (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (E.toSphere ∘ minimizer.embedding.toFun) x) := by
    rw [mfderiv_comp x (hi.isImmersion.contMDiff.mdifferentiableAt (by simp))
      (minimizer.embedding.smooth.mdifferentiableAt (by simp))]
    exact (hi.isImmersion.mfderiv_injective (by simp) _).comp
      (minimizer.embedding.differential_injective x)
  have hb (y : minimizer.source) :
      E.toSphere (minimizer.embedding.toFun y) ∈ frontier (Set.range E.toSphere) ↔
        y ∈ (𝓡∂ 2).boundary minimizer.source := by
    rw [G.boundary_exact]
    change y ∈ minimizer.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier ↔ _
    rw [minimizer.embedding.boundary_preimage]
    rfl
  obtain ⟨D,hDp,hDplane⟩ := A7Support.halfspace_minimal_graph_data hs x hx hd
    G.extension (Set.range E.toSphere) C hp (fun _ => Set.mem_range_self _) hb
      (minimizer.minimal_interior x)
  have hr := A4_original D
  have hbp := A7Support.boundary_plane_point_congr C D.p
    (E.toSphere (minimizer.embedding.toFun x)) hDp D.p_collar hp
  have hplane := hr.2.1
  rw [hbp,hDplane] at hplane
  have hrad := hr.1
  rw [hDp,hDplane] at hrad
  exact ⟨hrad,hplane⟩

theorem original_inward_transverse (G : SourceGeometry E) (J : LongitudeFoliation.{u} E)
    (minimizer : A6Minimizer E G J) :
    ∀ x ∈ minimizer.source.boundary,
      ∃ w : TangentSpace (𝓡∂ 2) x,
        inwardCoordinate (minimizer.embedding.toFun x)
          (mfderiv (𝓡∂ 2) (𝓡∂ 3) minimizer.embedding.toFun x w) ≠ 0 := by
  intro x hx
  have hi : Manifold.IsSmoothEmbedding (𝓡∂ 3) 𝓘(ℝ,E3) ∞ E.toSphere := E.inclusion
  have hfx : minimizer.embedding.toFun x ∈ (𝓡∂ 3).boundary E.Carrier := by
    change x ∈ minimizer.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier
    rw [minimizer.embedding.boundary_preimage]
    exact hx
  obtain ⟨C,hC⟩ := G.collars _ hfx
  have hdr := (ambient_collared_nonzero E G J minimizer x hx C hC).1
  exact A7Support.collar_differential_forces_native_transversality
    minimizer.embedding.smooth hi.isImmersion.contMDiff G.extension (Set.range E.toSphere) C
    (fun _ => Set.mem_range_self _) G.boundary_exact x hfx hC hdr

/-- Source Lemma A.7 (R2), lines 1326–1335. The full A.6 minimizer is supplied;
the proof must construct its own tangent-plane graph and invoke the paid A.4.
All boundary points are transverse, and the identical parametrized map admits
the native neat embedding structure. A.6 existence is not asserted here. -/
theorem A7_original (G : SourceGeometry E) (J : LongitudeFoliation.{u} E)
    (minimizer : A6Minimizer E G J) :
    (∀ x ∈ minimizer.source.boundary,
      ∀ C : WarpedBoundaryCollar G.extension (Set.range E.toSphere),
      ∀ hp : E.toSphere (minimizer.embedding.toFun x) ∈ C.coordinates.chart.source,
        tangentPlane E minimizer x ≠
          boundaryTangentPlane C (E.toSphere (minimizer.embedding.toFun x)) hp) ∧
    (∀ x ∈ minimizer.source.boundary,
      ∃ w : TangentSpace (𝓡∂ 2) x,
        inwardCoordinate (minimizer.embedding.toFun x)
          (mfderiv (𝓡∂ 2) (𝓡∂ 3) minimizer.embedding.toFun x w) ≠ 0) ∧
    ∃ f : NeatEmbedding minimizer.source E.Carrier, f.toFun = minimizer.embedding.toFun := by
  have htrans := original_inward_transverse E G J minimizer
  refine ⟨?_,htrans,?_⟩
  · intro x hx C hp
    exact (ambient_collared_nonzero E G J minimizer x hx C hp).2
  · have hb (x : minimizer.source) :
        minimizer.embedding.toFun x ∈ (𝓡∂ 3).boundary E.Carrier ↔
          x ∈ (𝓡∂ 2).boundary minimizer.source := by
      change x ∈ minimizer.embedding.toFun ⁻¹' (𝓡∂ 3).boundary E.Carrier ↔ _
      rw [minimizer.embedding.boundary_preimage]
      rfl
    let f : NeatEmbedding minimizer.source E.Carrier := {
      toFun := minimizer.embedding.toFun
      smoothEmbedding := {
        isImmersion := A7Support.native_transverse_isImmersion
          minimizer.embedding.smooth minimizer.embedding.differential_injective hb htrans
        isEmbedding := minimizer.embedding.embedding }
      boundary_preimage := minimizer.embedding.boundary_preimage
      boundary_transverse := htrans }
    exact ⟨f,rfl⟩

end SeifertSurfaces.OriginalEndpoints.A7
