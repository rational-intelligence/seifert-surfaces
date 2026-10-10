import ActualTaperedNormalBlockIsotopyV837

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualUniformFixedDiskNeighborhoodV840

/-- The whole compact time family admits a uniform larger disk image bound. -/
theorem uniform_larger_disk (H : Time → Plane ≃ₜ Plane)
    (hH : Continuous (fun p : Time × Plane => H p.1 p.2))
    (hfix : ∀ t x,‖x‖ ≤ 1 → H t x = x)
    (ρ : ℝ) (hρ : 1 < ρ) :
    ∃ s : ℝ,1 < s ∧ ∀ t,H t '' closedBall (0 : Plane) s ⊆ ball 0 ρ := by
  let U : Set (Time × Plane) := {p | H p.1 p.2 ∈ ball 0 ρ}
  have hU : IsOpen U := isOpen_ball.preimage hH
  have hprod : (univ : Set Time) ×ˢ closedBall (0 : Plane) 1 ⊆ U := by
    intro p hp
    change H p.1 p.2 ∈ ball 0 ρ
    rw [hfix _ _ (mem_closedBall_zero_iff.mp hp.2)]
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hp.2).trans_lt hρ)
  obtain ⟨V₁,V₂,hV₁,hV₂,hv₁,hv₂,hVU⟩ :=
    generalized_tube_lemma (isCompact_univ : IsCompact (univ : Set Time))
      (isCompact_closedBall (0 : Plane) 1) hU hprod
  obtain ⟨s,hs,hsub⟩ := CompressionActualClosedBallNeighborhoodV826.exists_larger_closedBall
    (by norm_num : (0:ℝ)<1) hV₂ hv₂
  refine ⟨s,hs,?_⟩
  intro t y hy
  obtain ⟨x,hx,rfl⟩ := hy
  exact @hVU (t,x) ⟨hv₁ (mem_univ t),hsub hx⟩

#print axioms uniform_larger_disk
end CompressionActualUniformFixedDiskNeighborhoodV840
