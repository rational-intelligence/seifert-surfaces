import ActualBoundaryExactDiskSeparatedIsotopyV845
import ActualAnnulusHalfWholeExtensionV762

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualAnnulusHalfSupportedClosedStripV848

/-- Extend the whole prescribed annular embedding first. Localization then
    matches every point of a whole closed outer strip, with support closure
    separated from the entire inner disk. No connector or boundary-label
    matching hypothesis is assumed. -/
theorem annulus_half_supported_closed_strip (q : C(Circle × Time,Plane))
    (hq : IsEmbedding q) (hq0 : ∀ z,q (z,0) = circleVector z)
    (hqout : ∀ z t,t ≠ 0 → 1 < ‖q (z,t)‖)
    (hqbound : ∀ z t,‖q (z,t)‖ ≤ 2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : Time → Plane ≃ₜ Plane,∃ W : Set Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ ball 0 3 ∧
      Disjoint (closure W) (closedBall (0 : Plane) 1) ∧
      (∀ x,K 0 x = x) ∧
      (∀ (z : Circle) (t : Time),ε ≤ (t:ℝ) → K 1 ((1+(t:ℝ)) • circleVector z) = q (z,t)) ∧
      (∀ t x,‖x‖ ≤ 1 → K t x = x) ∧
      ∀ t x,x ∉ W → K t x = x := by
  obtain ⟨H,hHfix,hHq⟩ :=
    CompressionActualAnnulusHalfWholeExtensionV762.annulus_half_whole_extension q hq hq0 hqout
  have hHR : H '' closedBall (0 : Plane) 2 ⊆ ball 0 3 := by
    rintro y ⟨x,hx,rfl⟩
    apply mem_ball_zero_iff.mpr
    by_cases hx1 : ‖x‖ ≤ 1
    · rw [hHfix x hx1]
      linarith
    · have hxn : 1 < ‖x‖ := lt_of_not_ge hx1
      let t : Time := ⟨‖x‖-1,by constructor; linarith; linarith [mem_closedBall_zero_iff.mp hx]⟩
      have hxe : x = (1+(t:ℝ)) • circleVector (angle x) := by
        change x = (1+(‖x‖-1)) • circleVector (angle x)
        rw [show 1+(‖x‖-1) = ‖x‖ by ring]
        exact (polar_reconstruction x (norm_ne_zero_iff.mp (by linarith))).symm
      rw [hxe,hHq]
      exact (hqbound _ _).trans_lt (by norm_num)
  let B : Set Plane := {x | 1+ε ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
  have hBc : IsCompact B := (isCompact_closedBall (0 : Plane) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun _ hx => mem_closedBall_zero_iff.mpr hx.2)
  have hBn : ∀ x ∈ B,1 < ‖x‖ := fun _ hx => (by linarith : (1:ℝ)<1+ε).trans_le hx.1
  obtain ⟨K,W,hK,hW,hWc,hWR,hWD,h0,h1,hfix,hoff⟩ :=
    CompressionActualBoundaryExactDiskSeparatedIsotopyV845.boundary_exact_disk_separated_isotopy
      H hHfix B hBc hBn 2 3 (by norm_num) (by norm_num)
      (fun _ hx => mem_closedBall_zero_iff.mpr hx.2) hHR
  refine ⟨K,W,hK,hW,hWc,hWR,hWD,h0,?_,hfix,hoff⟩
  intro z t ht
  have hn : ‖(1+(t:ℝ)) • circleVector z‖ = 1+(t:ℝ) := by
    rw [norm_smul,circleVector_norm,Real.norm_eq_abs,
      abs_of_pos (by linarith [t.property.1] : 0 < 1+(t:ℝ)),mul_one]
  have hxB : (1+(t:ℝ)) • circleVector z ∈ B := by
    change 1+ε ≤ ‖(1+(t:ℝ)) • circleVector z‖ ∧ ‖(1+(t:ℝ)) • circleVector z‖ ≤ 2
    rw [hn]
    constructor <;> linarith [t.property.2]
  exact (h1 hxB).trans (hHq z t)

#print axioms annulus_half_supported_closed_strip
end CompressionActualAnnulusHalfSupportedClosedStripV848
