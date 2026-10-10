import ActualBoundaryExactBallImagesV914

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology Metric
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualBoundaryExactAnnularRegionsV919

lemma image_fixed_disk (H : Plane ≃ₜ Plane) (hfix : ∀ x,‖x‖ ≤ 1 → H x = x) :
    H '' closedBall (0 : Plane) 1 = closedBall 0 1 := by
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    rwa [hfix y (mem_closedBall_zero_iff.mp hy)]
  · intro x hx
    exact ⟨x,hx,hfix x (mem_closedBall_zero_iff.mp hx)⟩

/-- Exact whole boundary labels determine both complete annular regions,
    including all inner points that the buffered localization leaves alone. -/
theorem boundary_exact_annular_regions (K H : Plane ≃ₜ Plane)
    (hKfix : ∀ x,‖x‖ ≤ 1 → K x = x)
    (hHfix : ∀ x,‖x‖ ≤ 1 → H x = x)
    (hbound : ∀ x,‖x‖ = 2 → K x = H x) :
    K '' (closedBall (0 : Plane) 2 \ closedBall 0 1) =
      H '' (closedBall (0 : Plane) 2 \ closedBall 0 1) ∧
    K '' (ball (0 : Plane) 2 \ closedBall 0 1) =
      H '' (ball (0 : Plane) 2 \ closedBall 0 1) := by
  have h0 : K 0 = H 0 := by rw [hKfix 0 (by simp),hHfix 0 (by simp)]
  obtain ⟨hc,ho⟩ := CompressionActualBoundaryExactBallImagesV914.boundary_exact_ball_images K H 2 (by norm_num) h0 hbound
  constructor
  · rw [image_diff K.injective,image_diff H.injective,hc,image_fixed_disk K hKfix,image_fixed_disk H hHfix]
  · rw [image_diff K.injective,image_diff H.injective,ho,image_fixed_disk K hKfix,image_fixed_disk H hHfix]

#print axioms boundary_exact_annular_regions
end CompressionActualBoundaryExactAnnularRegionsV919
