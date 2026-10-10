import ActualPlanarWholeDiskExtensionV756
import ActualPlanarEmbeddingReplacementV758

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
noncomputable section
namespace CompressionActualPlanarWholeEmbeddingExtensionV759

/-- Every prescribed embedded closed disk extends pointwise over the plane.
    This preserves the whole input map, including its disk core. -/
theorem whole_disk_embedding_extension (f : C(Disk,Plane)) (hf : IsEmbedding f) :
    ∃ H : Plane ≃ₜ Plane,∀ x : Disk,H x = f x := by
  classical
  let a : C(Circle,Disk) := ⟨CompressionAnnulus.capEdge,
    CompressionExactQuotientSupport.continuous_capEdge⟩
  have ha : IsEmbedding a := (a.continuous.isClosedEmbedding capEdge_injective).isEmbedding
  let r : C(Circle,Plane) := ⟨fun z => (a z : Plane),continuous_subtype_val.comp a.continuous⟩
  have hr : IsEmbedding r := IsEmbedding.subtypeVal.comp ha
  have hrange : Set.range r = Metric.sphere (0 : Plane) 1 := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact mem_sphere_zero_iff_norm.mpr (circleVector_norm z)
    · intro hx
      let x' : Disk := ⟨x,Metric.sphere_subset_closedBall hx⟩
      obtain ⟨z,hz⟩ := CompressionCapRadialSupport.capEdge_range.symm ▸
        (show x' ∈ closedDiskBoundary from mem_sphere_zero_iff_norm.mp hx)
      exact ⟨z,congrArg Subtype.val hz⟩
  have hmodel : Schoenflies.IsJordanCurve (Metric.sphere (0 : Plane) 1) :=
    hrange ▸ circle_isJordanCurve r hr
  let rf : C(Circle,Plane) := f.comp a
  have hrf : IsEmbedding rf := hf.comp ha
  let C : Set Plane := f '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1}
  have hCeq : Set.range rf = C := by
    change Set.range (f ∘ a) = C
    rw [Set.range_comp]
    change f '' Set.range CompressionAnnulus.capEdge = C
    rw [CompressionCapRadialSupport.capEdge_range]
    simp only [C,closedDiskBoundary,mem_sphere,dist_zero_right]
  have hC : Schoenflies.IsJordanCurve C := hCeq ▸ circle_isJordanCurve rf hrf
  let rSphere : Circle ≃ₜ Metric.sphere (0 : Plane) 1 :=
    hr.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let rCurve : Circle ≃ₜ C :=
    hrf.toHomeomorph.trans (Homeomorph.setCongr hCeq)
  let e : Metric.sphere (0 : Plane) 1 ≃ₜ C := rSphere.symm.trans rCurve
  obtain ⟨H,hH⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hmodel hC e
  have hHboundary (x : Disk) (hx : (x : Plane) ∈ Metric.sphere 0 1) : H x = f x := by
    obtain ⟨z,hz⟩ := CompressionCapRadialSupport.capEdge_range.symm ▸
      (show x ∈ closedDiskBoundary from mem_sphere_zero_iff_norm.mp hx)
    have hh := hH (rSphere z)
    change H (rSphere z : Plane) = (rCurve (rSphere.symm (rSphere z)) : Plane) at hh
    rw [rSphere.symm_apply_apply] at hh
    change H (a z : Plane) = f (a z) at hh
    simpa only [show a z = x from hz] using hh
  have hHrange : H '' Metric.sphere (0 : Plane) 1 = C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hH ⟨x,hx⟩]
      exact (e ⟨x,hx⟩).property
    · intro hy
      let x := e.symm ⟨y,hy⟩
      exact ⟨x.val,x.property,(hH x).trans (congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩))⟩
  let dH : C(Disk,Plane) := ⟨fun x => H x,H.continuous.comp continuous_subtype_val⟩
  have hdH : IsEmbedding dH := H.isEmbedding.comp IsEmbedding.subtypeVal
  have hdHC : dH '' {x : Disk | (x : Plane) ∈ Metric.sphere 0 1} = C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hHrange ▸ Set.mem_image_of_mem H hx
    · intro hy
      obtain ⟨x,hx,he⟩ := hHrange.symm ▸ hy
      exact ⟨⟨x,Metric.sphere_subset_closedBall hx⟩,hx,he⟩
  obtain ⟨hfO,hfK⟩ := embedded_disk_image f hf hC
  obtain ⟨hHO,hHK⟩ := embedded_disk_image dH hdH (hdHC.symm ▸ hC)
  rw [hdHC] at hHO hHK
  have hdHK : Set.range dH = H '' Disk := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  have hdHO : dH '' {x : Disk | (x : Plane) ∈ Metric.ball 0 1} = H '' Metric.ball 0 1 := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,Metric.ball_subset_closedBall hx⟩,hx,rfl⟩
  exact CompressionActualPlanarEmbeddingReplacementV758.whole_region_extension
    Disk (Metric.ball 0 1) Metric.isClosed_closedBall Metric.isOpen_ball
    Metric.ball_subset_closedBall ⟨0,by simp⟩ f hf H
    (hfK.trans (hHK.symm.trans hdHK)) (hfO.trans (hHO.symm.trans hdHO))
    (fun x hx => hHboundary x (mem_sphere_zero_iff_norm.mpr
      (le_antisymm (mem_closedBall_zero_iff.mp x.property)
        (le_of_not_gt (fun h => hx (mem_ball_zero_iff.mpr h)))) ) |>.symm)

end CompressionActualPlanarWholeEmbeddingExtensionV759
