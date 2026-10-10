import ActualParametricBoundaryExactLocalizationV894
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualBoundaryExactBallImagesV914

/-- A whole homeomorphism fixing the boundary sphere and origin retains
    the whole closed ball. This follows by the radial path and IVT. -/
theorem maps_closedBall_of_fixed_sphere (g : Plane ≃ₜ Plane)
    (R : ℝ) (hR : 0 < R) (h0 : g 0 = 0)
    (hsphere : ∀ x,‖x‖ = R → g x = x) :
    MapsTo g (closedBall (0 : Plane) R) (closedBall 0 R) := by
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  apply le_of_not_gt
  intro hn
  let f : ℝ → ℝ := fun t => ‖g (t • x)‖
  have hf : Continuous f := (g.continuous.comp (continuous_id.smul continuous_const)).norm
  have hf0 : f 0 = 0 := by simp [f,h0]
  have hf1 : f 1 = ‖g x‖ := by simp [f]
  obtain ⟨s,hs,hse⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hf.continuousOn
    (show R ∈ Icc (f 0) (f 1) from by rw [hf0,hf1]; exact ⟨hR.le,hn.le⟩)
  have hs1 : s < 1 := lt_of_le_of_ne hs.2 (by intro he; rw [he,hf1] at hse; exact hn.ne' hse)
  have hfix : g (g (s • x)) = g (s • x) := hsphere _ hse
  have he : s • x = g (s • x) := g.injective hfix.symm
  have hnorm : ‖s • x‖ = R := (congrArg norm he).trans hse
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1] at hnorm
  have hxn := mem_closedBall_zero_iff.mp hx
  have hmul := mul_le_mul_of_nonneg_left hxn hs.1
  have hsr := mul_lt_mul_of_pos_right hs1 hR
  nlinarith

theorem maps_ball_of_fixed_sphere (g : Plane ≃ₜ Plane)
    (R : ℝ) (hR : 0 < R) (h0 : g 0 = 0)
    (hsphere : ∀ x,‖x‖ = R → g x = x) :
    MapsTo g (ball (0 : Plane) R) (ball 0 R) := by
  intro x hx
  have hn : ‖g x‖ ≤ R := mem_closedBall_zero_iff.mp
    (maps_closedBall_of_fixed_sphere g R hR h0 hsphere (ball_subset_closedBall hx))
  apply mem_ball_zero_iff.mpr
  apply lt_of_le_of_ne hn
  intro he
  have hxg : x = g x := g.injective (hsphere _ he).symm
  have hnx : ‖x‖ = R := (congrArg norm hxg).trans he
  exact (ne_of_lt (mem_ball_zero_iff.mp hx)) hnx

theorem image_balls_of_fixed_sphere (g : Plane ≃ₜ Plane)
    (R : ℝ) (hR : 0 < R) (h0 : g 0 = 0)
    (hsphere : ∀ x,‖x‖ = R → g x = x) :
    g '' closedBall (0 : Plane) R = closedBall 0 R ∧
    g '' ball (0 : Plane) R = ball 0 R := by
  have h0i : g.symm 0 = 0 := g.injective (by rw [g.apply_symm_apply,h0])
  have hsi (x : Plane) (hx : ‖x‖ = R) : g.symm x = x :=
    g.injective (by rw [g.apply_symm_apply,hsphere x hx])
  constructor
  · apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact maps_closedBall_of_fixed_sphere g R hR h0 hsphere hx
    · intro y hy
      exact ⟨g.symm y,maps_closedBall_of_fixed_sphere g.symm R hR h0i hsi hy,g.apply_symm_apply _⟩
  · apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      exact maps_ball_of_fixed_sphere g R hR h0 hsphere hx
    · intro y hy
      exact ⟨g.symm y,maps_ball_of_fixed_sphere g.symm R hR h0i hsi hy,g.apply_symm_apply _⟩

/-- Exact sphere labels and one fixed interior point determine the full
    ball image, allowing the supported replacement to retain both entire
    annular side regions. -/
theorem boundary_exact_ball_images (K H : Plane ≃ₜ Plane)
    (R : ℝ) (hR : 0 < R) (h0 : K 0 = H 0)
    (hsphere : ∀ x,‖x‖ = R → K x = H x) :
    K '' closedBall (0 : Plane) R = H '' closedBall 0 R ∧
    K '' ball (0 : Plane) R = H '' ball 0 R := by
  let g : Plane ≃ₜ Plane := K.trans H.symm
  have h0g : g 0 = 0 := by change H.symm (K 0) = 0; rw [h0,H.symm_apply_apply]
  have hsg (x : Plane) (hx : ‖x‖ = R) : g x = x := by
    change H.symm (K x) = x
    rw [hsphere x hx,H.symm_apply_apply]
  obtain ⟨hc,ho⟩ := image_balls_of_fixed_sphere g R hR h0g hsg
  have hKH : (K : Plane → Plane) = H ∘ g := by funext x; exact (H.apply_symm_apply _).symm
  rw [hKH,image_comp,image_comp,hc,ho]
  exact ⟨rfl,rfl⟩

#print axioms maps_closedBall_of_fixed_sphere
#print axioms boundary_exact_ball_images
end CompressionActualBoundaryExactBallImagesV914
