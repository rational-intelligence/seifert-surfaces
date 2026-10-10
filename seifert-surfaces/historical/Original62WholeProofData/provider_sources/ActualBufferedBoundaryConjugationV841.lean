import ActualTaperedNormalBlockIsotopyV837

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualBufferedBoundaryConjugationV841

/-- Conjugation can enlarge the fixed disk while preserving every supplied
    boundary point label, provided that the boundary and its image lie beyond
    the explicit conjugator support. No cyclic-order or curve-label premise. -/
theorem buffered_boundary_conjugation (H : Plane ≃ₜ Plane)
    (hfix : ∀ x : Plane,‖x‖ ≤ 1 → H x = x)
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (B : Set Plane) (hB : ∀ x ∈ B,c ≤ ‖x‖ ∧ c ≤ ‖H x‖) :
    ∃ H' : Plane ≃ₜ Plane,
      (∀ x,‖x‖ ≤ b → H' x = x) ∧ EqOn H' H B := by
  let a : ℝ := 1/(b+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by linarith)).mpr; linarith
  have hab : a*b ≤ 1 := by
    dsimp [a]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by linarith)).mpr
    linarith
  let g : Plane ≃ₜ Plane := compression b c a hb hbc ha ha1
  have hgin (x : Plane) (hx : ‖x‖ ≤ b) : ‖g x‖ ≤ 1 := by
    change ‖radial b c a x‖ ≤ 1
    rw [radial_norm b c a ha ha1,coefficient_inner b c a ‖x‖ hbc hx]
    exact (mul_le_mul_of_nonneg_left hx ha.le).trans hab
  have hgout (x : Plane) (hx : c ≤ ‖x‖) : g x = x := radial_fixed_outer b c a hbc x hx
  let H' : Plane ≃ₜ Plane := g.trans (H.trans g.symm)
  refine ⟨H',?_,?_⟩
  · intro x hx
    change g.symm (H (g x)) = x
    rw [hfix _ (hgin x hx),g.symm_apply_apply]
  · intro x hx
    change g.symm (H (g x)) = H x
    rw [hgout x (hB x hx).1]
    exact g.injective (by rw [g.apply_symm_apply,hgout _ (hB x hx).2])

/-- Remove a smaller closed disk from the support of an isotopy that fixes
    a strictly larger disk. The resulting support closure misses the whole
    smaller disk, which is stronger than pointwise stationarity. -/
theorem support_away_fixed_disk
    (K : SeifertSurfaces.Foundations.Time → Plane ≃ₜ Plane)
    (W : Set Plane) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hoff : ∀ t x,x ∉ W → K t x = x)
    (b c : ℝ) (hcb : c < b) (hfix : ∀ t x,‖x‖ ≤ b → K t x = x) :
    ∃ V : Set Plane,IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ closure W ∧
      Disjoint (closure V) (ball (0 : Plane) c) ∧
      ∀ t x,x ∉ V → K t x = x := by
  let V : Set Plane := W ∩ (closedBall (0 : Plane) c)ᶜ
  have hVo : IsOpen V := hW.inter isClosed_closedBall.isOpen_compl
  have hVW : closure V ⊆ closure W := closure_mono inter_subset_left
  have hVc : closure V ⊆ (ball (0 : Plane) c)ᶜ :=
    closure_minimal (fun x hx hxb => hx.2 (ball_subset_closedBall hxb)) isOpen_ball.isClosed_compl
  refine ⟨V,hVo,hWc.of_isClosed_subset isClosed_closure hVW,hVW,
    disjoint_left.mpr (fun x hx hc => hVc hx hc),?_⟩
  intro t x hx
  by_cases hxW : x ∈ W
  · have hn : ‖x‖ ≤ c := by
      apply le_of_not_gt
      intro h
      exact hx ⟨hxW,fun hm => (not_le_of_gt h) (mem_closedBall_zero_iff.mp hm)⟩
    exact hfix t x (hn.trans hcb.le)
  · exact hoff t x hxW

#print axioms buffered_boundary_conjugation
#print axioms support_away_fixed_disk
end CompressionActualBufferedBoundaryConjugationV841
