import ActualDiskFixedSupportedPlanarIsotopyV827

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology TopologicalSpace
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualNativeOriginalCollarSupportV838
variable {S : CompactOrientedSurface.{0}} {M : Type}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  {f : NeatEmbedding S M} {D : InteriorCompressingDisk f} (A : CompressionAnnulus D)

lemma edgePoint_continuous (k : Fin 2) : Continuous (A.edgePoint k) := by
  apply Continuous.subtype_mk
  exact A.band.continuous.comp (continuous_id.prodMk
    (continuous_const : Continuous (fun _ : Circle => CompressionAnnulus.sideTime k)))

lemma edgePoint_boundary_compl (k : Fin 2) (z : Circle) :
    (A.edgePoint k z : S) ∈ S.boundaryᶜ :=
  A.interior_surface ⟨(z,CompressionAnnulus.sideTime k),rfl⟩

lemma band_closed : IsClosed (range A.band) := (isCompact_range A.band.continuous).isClosed

lemma exists_band_neighborhood_away_boundary :
    ∃ U : Set S,IsOpen U ∧ range A.band ⊆ U ∧ Disjoint (closure U) S.boundary := by
  have hb := (𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by decide)
  obtain ⟨U,hU,hband,hUb⟩ := normal_exists_closure_subset (band_closed A) hb.isOpen_compl A.interior_surface
  exact ⟨U,hU,hband,disjoint_left.mpr (fun x hx hxb => hUb hx hxb)⟩

#print axioms exists_band_neighborhood_away_boundary
end CompressionActualNativeOriginalCollarSupportV838
