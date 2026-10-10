import A5NativeHalfspaceImageChart

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

theorem model_halfspace_boundary_iff (z : EuclideanHalfSpace 2) :
    z ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) ↔ ((𝓡∂ 2) z) 0 = 0 := by
  change (𝓡∂ 2).IsBoundaryPoint z ↔ _
  rw [ModelWithCorners.isBoundaryPoint_iff,extChartAt_self_apply,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  exact eq_comm

/-- A relative half-space coordinate change preserving the flat boundary
preserves the literal native source-boundary image identity. -/
theorem boundary_image_of_halfspace_chart_comp
    {X : Type*} [TopologicalSpace X] (B : Set X)
    (e : OpenPartialHomeomorph X (EuclideanHalfSpace 2))
    (he : e '' (B ∩ e.source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ e.target)
    (d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2))
    (hd : ∀ z ∈ d.source, ((𝓡∂ 2) (d z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0) :
    (e.trans d) '' (B ∩ (e.trans d).source) =
      ((𝓡∂ 2).boundary (EuclideanHalfSpace 2)) ∩ (e.trans d).target := by
  ext y
  constructor
  · rintro ⟨x,⟨hxB,hx⟩,rfl⟩
    have hb : e x ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
      have hh : e x ∈ e '' (B ∩ e.source) := ⟨x,⟨hxB,hx.1⟩,rfl⟩
      rw [he] at hh
      exact hh.1
    refine ⟨?_,(e.trans d).map_source hx⟩
    rw [model_halfspace_boundary_iff]
    exact (hd (e x) hx.2).mpr ((model_halfspace_boundary_iff _).mp hb)
  · intro hy
    have hdy := d.map_target hy.2.1
    have hdb : d.symm y ∈ (𝓡∂ 2).boundary (EuclideanHalfSpace 2) := by
      rw [model_halfspace_boundary_iff]
      apply (hd (d.symm y) hdy).mp
      rw [d.right_inv hy.2.1]
      exact (model_halfspace_boundary_iff _).mp hy.1
    have hde : d.symm y ∈ e '' (B ∩ e.source) := by rw [he]; exact ⟨hdb,hy.2.2⟩
    obtain ⟨x,⟨hxB,hxe⟩,hx⟩ := hde
    refine ⟨x,⟨hxB,⟨hxe,?_⟩⟩,?_⟩
    · change e x ∈ d.source
      rw [hx]
      exact hdy
    · change d (e x) = y
      rw [hx,d.right_inv hy.2.1]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
