import ActualClosedBallNeighborhoodV826

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
open CompressionActualSupportedCommutatorV822
open CompressionActualCompactlySupportedContinuousBijectionV823
noncomputable section
namespace CompressionActualDiskFixedSupportedPlanarIsotopyV827

/-- A whole plane homeomorphism fixing the unit disk can be realized on a
    prescribed whole closed ball by an actual supported ambient isotopy.
    Its whole source ball and image fit strictly inside the requested outer ball. -/
theorem disk_fixed_supported_planar_isotopy (H : Plane ≃ₜ Plane)
    (hfix : ∀ x : Plane,‖x‖ ≤ 1 → H x = x)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hHR : H '' closedBall (0 : Plane) r ⊆ ball 0 R) :
    ∃ K : Time → Plane ≃ₜ Plane,∃ W : Set Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ ball 0 R ∧
      (∀ x,K 0 x = x) ∧
      (∀ x,‖x‖ ≤ r → K 1 x = H x) ∧
      (∀ t x,‖x‖ ≤ 1 → K t x = x) ∧
      ∀ t x,x ∉ W → K t x = x := by
  classical
  let U : Set Plane := ball 0 R ∩ H ⁻¹' ball 0 R
  have hU : IsOpen U := isOpen_ball.inter (isOpen_ball.preimage H.continuous)
  have hsub : closedBall (0 : Plane) r ⊆ U := by
    intro x hx
    exact ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hrR),hHR ⟨x,hx,rfl⟩⟩
  obtain ⟨s,hrs,hsU⟩ := CompressionActualClosedBallNeighborhoodV826.exists_larger_closedBall hr hU hsub
  let a : ℝ := 1/(r+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by linarith)).mpr; linarith
  have har : a*r ≤ 1 := by
    dsimp [a]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by linarith)).mpr
    linarith
  let A (t : Time) : ℝ := 1+(t:ℝ)*(a-1)
  have hAb (t : Time) : a ≤ A t ∧ A t ≤ 1 := by
    dsimp [A]
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hAp (t : Time) : 0 < A t := ha.trans_le (hAb t).1
  let g (t : Time) : Plane ≃ₜ Plane := compression r s (A t) hr hrs (hAp t) (hAb t).2
  have hgval (t : Time) (x : Plane) : g t x = radial r s (A t) x := rfl
  have hgcont : Continuous (fun p : Time × Plane => g p.1 p.2) :=
    (radial_joint_continuous r s).comp
      (((continuous_const.add (continuous_fst.subtype_val.mul continuous_const))).prodMk continuous_snd)
  have hgoff (t : Time) : EqOn (g t) id (closedBall (0 : Plane) s)ᶜ := by
    intro x hx
    exact radial_fixed_outer r s (A t) hrs x
      (le_of_not_ge (fun h => hx (mem_closedBall_zero_iff.mpr h)))
  have hgi : Continuous (fun p : Time × Plane => (g p.1).symm p.2) :=
    continuous_family_inverse g hgcont (closedBall 0 s) (isCompact_closedBall _ _) hgoff
  let K (t : Time) : Plane ≃ₜ Plane := localize H (g t)
  let W : Set Plane := ball 0 s ∪ H '' ball 0 s
  let C : Set Plane := closedBall 0 s ∪ H '' closedBall 0 s
  have hC : IsCompact C := (isCompact_closedBall _ _).union ((isCompact_closedBall _ _).image H.continuous)
  have hWsub : W ⊆ C := union_subset_union ball_subset_closedBall (image_mono ball_subset_closedBall)
  have hcl : closure W ⊆ C := closure_minimal hWsub hC.isClosed
  have hCR : C ⊆ ball 0 R := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact (hsU hx).1
    · exact (hsU hy).2
  have hgballoff (t : Time) : EqOn (g t) id (ball (0 : Plane) s)ᶜ := by
    intro x hx
    exact radial_fixed_outer r s (A t) hrs x
      (le_of_not_gt (fun h => hx (mem_ball_zero_iff.mpr h)))
  have hg0 (x : Plane) : g 0 x = x := by
    rw [hgval]
    simp [radial,coefficient,A]
  have hcontract : MapsTo (g 1) (closedBall (0 : Plane) r) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff,hgval,radial_norm r s (A 1) (hAp 1) (hAb 1).2,
      coefficient_inner r s (A 1) ‖x‖ hrs (mem_closedBall_zero_iff.mp hx)]
    have hA1 : A 1 = a := by simp [A]
    rw [hA1]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) ha.le).trans har
  refine ⟨K,W,localize_family H g hgcont hgi,isOpen_ball.union (H.isOpenMap _ isOpen_ball),
    hC.of_isClosed_subset isClosed_closure hcl,hcl.trans hCR,?_,?_,?_,?_⟩
  · intro x
    change H ((g 0).symm (H.symm (g 0 x))) = x
    rw [hg0]
    have hinv : (g 0).symm (H.symm x) = H.symm x := (g 0).injective (by rw [(g 0).apply_symm_apply,hg0])
    rw [hinv,H.apply_symm_apply]
  · intro x hx
    exact localize_eq H (g 1) (fun x hx => hfix x (mem_closedBall_zero_iff.mp hx)) hcontract
      (mem_closedBall_zero_iff.mpr hx)
  · intro t x hx
    have hnorm : ‖g t x‖ ≤ 1 := by
      rw [hgval,radial_norm r s (A t) (hAp t) (hAb t).2]
      exact (mul_le_mul_of_nonneg_right (coefficient_bounds r s (A t) ‖x‖ (hAp t) (hAb t).2).2
        (norm_nonneg x)).trans (by simpa using hx)
    have hf : H.symm (g t x) = g t x := H.injective (by rw [H.apply_symm_apply,hfix _ hnorm])
    change H ((g t).symm (H.symm (g t x))) = x
    rw [hf,(g t).symm_apply_apply,hfix x hx]
  · intro t x hx
    exact localize_fixed_outside H (g t) (hgballoff t) hx

#print axioms disk_fixed_supported_planar_isotopy
end CompressionActualDiskFixedSupportedPlanarIsotopyV827
