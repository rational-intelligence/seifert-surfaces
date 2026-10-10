import ActualBufferedSupportedPlanarIsotopyV844

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualBoundaryExactDiskSeparatedIsotopyV845

/-- A whole-plane homeomorphism fixing the unit disk cannot send a point
    outside that disk into it. -/
theorem image_outside_fixed_disk (H : Plane ≃ₜ Plane)
    (hfix : ∀ x : Plane,‖x‖ ≤ 1 → H x = x) {x : Plane} (hx : 1 < ‖x‖) :
    1 < ‖H x‖ := by
  apply lt_of_not_ge
  intro h
  have he : x = H x := H.injective (hfix (H x) h).symm
  exact (not_le_of_gt hx) (he.symm ▸ h)

/-- Identity outside a smaller disk forces preservation of every larger
    open disk, for both the homeomorphism and its inverse. -/
theorem inverse_preserves_larger_ball (g : Plane ≃ₜ Plane)
    (c R : ℝ) (hcR : c < R) (hoff : ∀ x,c ≤ ‖x‖ → g x = x) :
    MapsTo g.symm (ball (0 : Plane) R) (ball 0 R) := by
  intro x hx
  apply mem_ball_zero_iff.mpr
  apply lt_of_not_ge
  intro h
  have he : g.symm x = x := (hoff _ (hcR.le.trans h)).symm.trans (g.apply_symm_apply x)
  exact (not_le_of_gt (mem_ball_zero_iff.mp hx)) (he ▸ h)

/-- Every label on a compact boundary outside the fixed disk is matched
    by an actual supported isotopy whose support closure misses that whole
    disk. All support and boundary matching data are constructed. -/
theorem boundary_exact_disk_separated_isotopy (H : Plane ≃ₜ Plane)
    (hfix : ∀ x : Plane,‖x‖ ≤ 1 → H x = x)
    (B : Set Plane) (hBc : IsCompact B) (hBn : ∀ x ∈ B,1 < ‖x‖)
    (r R : ℝ) (hr : 1 < r) (hrR : r < R)
    (hBr : B ⊆ closedBall (0 : Plane) r)
    (hHR : H '' closedBall (0 : Plane) r ⊆ ball 0 R) :
    ∃ K : Time → Plane ≃ₜ Plane,∃ W : Set Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ ball 0 R ∧
      Disjoint (closure W) (closedBall (0 : Plane) 1) ∧
      (∀ x,K 0 x = x) ∧ EqOn (K 1) H B ∧
      (∀ t x,‖x‖ ≤ 1 → K t x = x) ∧
      ∀ t x,x ∉ W → K t x = x := by
  obtain ⟨m,hm,hBm⟩ := hBc.exists_forall_le'
    ((continuous_norm.min (continuous_norm.comp H.continuous)).continuousOn)
    (a := (1:ℝ)) (fun x hx => lt_min (hBn x hx) (image_outside_fixed_disk H hfix (hBn x hx)))
  let c : ℝ := (1+min m r)/2
  have hc : 1 < c := by dsimp [c]; have hh := lt_min hm hr; linarith
  have hcm : c ≤ m := by dsimp [c]; have hh := min_le_left m r; have hh' := lt_min hm hr; linarith
  have hcr : c < r := by dsimp [c]; have hh := min_le_right m r; linarith
  let b : ℝ := (1+c)/2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbc : b < c := by dsimp [b]; linarith
  let a : ℝ := 1/(b+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by linarith)).mpr; linarith
  have hab : a*b ≤ 1 := by
    dsimp [a]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by linarith)).mpr
    linarith
  let g : Plane ≃ₜ Plane := compression b c a (by linarith) hbc ha ha1
  have hgout (x : Plane) (hx : c ≤ ‖x‖) : g x = x := radial_fixed_outer b c a hbc x hx
  have hgnorm (x : Plane) : ‖g x‖ ≤ ‖x‖ := by
    change ‖radial b c a x‖ ≤ ‖x‖
    rw [radial_norm b c a ha ha1]
    exact (mul_le_mul_of_nonneg_right (coefficient_bounds b c a ‖x‖ ha ha1).2
      (norm_nonneg x)).trans_eq (one_mul _)
  let H' : Plane ≃ₜ Plane := g.trans (H.trans g.symm)
  have hH'fix (x : Plane) (hx : ‖x‖ ≤ b) : H' x = x := by
    have hgin : ‖g x‖ ≤ 1 := by
      change ‖radial b c a x‖ ≤ 1
      rw [radial_norm b c a ha ha1,coefficient_inner b c a ‖x‖ hbc hx]
      exact (mul_le_mul_of_nonneg_left hx ha.le).trans hab
    change g.symm (H (g x)) = x
    rw [hfix _ hgin,g.symm_apply_apply]
  have hH'B : EqOn H' H B := by
    intro x hx
    have hnx := hcm.trans ((hBm x hx).trans (min_le_left _ _))
    have hnHx := hcm.trans ((hBm x hx).trans (min_le_right _ _))
    change g.symm (H (g x)) = H x
    rw [hgout _ hnx]
    exact g.injective (by rw [g.apply_symm_apply,hgout _ hnHx])
  have hH'R : H' '' closedBall (0 : Plane) r ⊆ ball 0 R := by
    rintro y ⟨x,hx,rfl⟩
    exact inverse_preserves_larger_ball g c R (hcr.trans hrR) hgout
      (hHR ⟨g x,mem_closedBall_zero_iff.mpr ((hgnorm x).trans (mem_closedBall_zero_iff.mp hx)),rfl⟩)
  obtain ⟨K,W,hK,hW,hWc,hWR,hWD,h0,h1,hfixK,hoff⟩ :=
    CompressionActualBufferedSupportedPlanarIsotopyV844.buffered_supported_planar_isotopy
      H' b hb hH'fix r R (by linarith) hrR hH'R
  refine ⟨K,W,hK,hW,hWc,hWR,hWD,h0,?_,?_,hoff⟩
  · intro x hx
    exact (h1 x (mem_closedBall_zero_iff.mp (hBr hx))).trans (hH'B hx)
  · intro t x hx
    exact hfixK t x (hx.trans hb.le)

#print axioms image_outside_fixed_disk
#print axioms inverse_preserves_larger_ball
#print axioms boundary_exact_disk_separated_isotopy
end CompressionActualBoundaryExactDiskSeparatedIsotopyV845
