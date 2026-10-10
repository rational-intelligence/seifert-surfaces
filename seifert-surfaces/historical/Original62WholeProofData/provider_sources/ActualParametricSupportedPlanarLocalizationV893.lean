import ActualBufferedSupportedPlanarIsotopyV844
import ActualGlobalConfinedAnnulusFamilyV892

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
open CompressionActualSupportedCommutatorV822
open CompressionActualCompactlySupportedContinuousBijectionV823
noncomputable section
namespace CompressionActualParametricSupportedPlanarLocalizationV893

/-- Localize the whole joint parameter family with one compact support,
    preserving every prescribed closed-ball point at every parameter. -/
theorem parametric_supported_planar_localization
    (H : Time → Plane ≃ₜ Plane)
    (hH : Continuous (fun p : Time × Plane => H p.1 p.2))
    (hHi : Continuous (fun p : Time × Plane => (H p.1).symm p.2))
    (b : ℝ) (hb : 1 < b) (hfix : ∀ t x,‖x‖ ≤ b → H t x = x)
    (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (hHR : ∀ t x,‖x‖ ≤ r → ‖H t x‖ < R) :
    ∃ K : Time → Plane ≃ₜ Plane,∃ V : Set Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      Continuous (fun p : Time × Plane => (K p.1).symm p.2) ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ ball 0 R ∧
      Disjoint (closure V) (closedBall (0 : Plane) 1) ∧
      (∀ t x,‖x‖ ≤ r → K t x = H t x) ∧
      (∀ t x,‖x‖ ≤ b → K t x = x) ∧
      (∀ t x,x ∉ V → K t x = x) ∧
      ∀ t,(∀ x,H t x = x) → ∀ x,K t x = x := by
  classical
  let O : Set (Time × Plane) := {p | ‖p.2‖ < R ∧ ‖H p.1 p.2‖ < R}
  have hO : IsOpen O := (isOpen_lt continuous_snd.norm continuous_const).inter
    (isOpen_lt hH.norm continuous_const)
  have hcontain : (univ : Set Time) ×ˢ closedBall (0 : Plane) r ⊆ O := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have hxr := mem_closedBall_zero_iff.mp hx
    exact ⟨hxr.trans_lt hrR,hHR t x hxr⟩
  obtain ⟨U,B,hU,hB,hall,hCB,hUB⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set Time)) (isCompact_closedBall (0 : Plane) r) hO hcontain
  obtain ⟨s,hrs,hsB⟩ := CompressionActualClosedBallNeighborhoodV826.exists_larger_closedBall hr hB hCB
  have hsR (t : Time) (x : Plane) (hx : x ∈ closedBall (0 : Plane) s) :
      ‖x‖ < R ∧ ‖H t x‖ < R := @hUB (t,x) ⟨hall (mem_univ t),hsB hx⟩
  let a : ℝ := b/(r+b)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; apply (div_le_one (by linarith)).mpr; linarith
  have har : a*r ≤ b := by
    dsimp [a]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0 < r+b)).mpr
    nlinarith
  let g : Plane ≃ₜ Plane := compression r s a hr hrs ha ha1
  have hgoff : EqOn g id (ball (0 : Plane) s)ᶜ := by
    intro x hx
    exact radial_fixed_outer r s a hrs x
      (le_of_not_gt (fun hn => hx (mem_ball_zero_iff.mpr hn)))
  have hcontract : MapsTo g (closedBall (0 : Plane) r) (closedBall 0 b) := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    change ‖radial r s a x‖ ≤ b
    rw [radial_norm r s a ha ha1,coefficient_inner r s a ‖x‖ hrs (mem_closedBall_zero_iff.mp hx)]
    exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) ha.le).trans har
  let K (t : Time) : Plane ≃ₜ Plane := localize (H t) g
  have hK : Continuous (fun p : Time × Plane => K p.1 p.2) :=
    hH.comp (continuous_fst.prodMk (g.symm.continuous.comp
      (hHi.comp (continuous_fst.prodMk (g.continuous.comp continuous_snd)))))
  let W : Set Plane := ball 0 s ∪ ⋃ t : Time,H t '' ball 0 s
  let C : Set Plane := closedBall 0 s ∪
    (fun p : Time × Plane => H p.1 p.2) '' (univ ×ˢ closedBall 0 s)
  have hW : IsOpen W := isOpen_ball.union (isOpen_iUnion (fun t => (H t).isOpenMap _ isOpen_ball))
  have hC : IsCompact C := (isCompact_closedBall _ _).union
    ((isCompact_univ.prod (isCompact_closedBall _ _)).image hH)
  have hWC : W ⊆ C := by
    rintro x (hx | hx)
    · exact Or.inl (ball_subset_closedBall hx)
    · obtain ⟨t,y,hy,he⟩ := mem_iUnion.mp hx
      exact Or.inr ⟨(t,y),⟨mem_univ _,ball_subset_closedBall hy⟩,he⟩
  have hcl : closure W ⊆ C := closure_minimal hWC hC.isClosed
  have hCR : C ⊆ ball 0 R := by
    rintro x (hx | ⟨⟨t,y⟩,⟨ht,hy⟩,rfl⟩)
    · exact mem_ball_zero_iff.mpr (hsR 0 x hx).1
    · exact mem_ball_zero_iff.mpr (hsR t y hy).2
  have hoff : ∀ t x,x ∉ W → K t x = x := by
    intro t x hx
    exact localize_fixed_outside (H t) g hgoff (by
      rintro (hy | hy)
      · exact hx (Or.inl hy)
      · exact hx (Or.inr (mem_iUnion.mpr ⟨t,hy⟩)))
  have hKfix (t : Time) (x : Plane) (hx : ‖x‖ ≤ b) : K t x = x := by
    have hnorm : ‖g x‖ ≤ b := by
      change ‖radial r s a x‖ ≤ b
      rw [radial_norm r s a ha ha1]
      exact (mul_le_mul_of_nonneg_right (coefficient_bounds r s a ‖x‖ ha ha1).2
        (norm_nonneg x)).trans (by simpa using hx)
    have hf : (H t).symm (g x) = g x := (H t).injective
      (by rw [(H t).apply_symm_apply,hfix t _ hnorm])
    change H t (g.symm ((H t).symm (g x))) = x
    rw [hf,g.symm_apply_apply,hfix t x hx]
  let c : ℝ := (1+b)/2
  have hc : 1 < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  obtain ⟨V,hV,hVc,hVW,hVD,hoffV⟩ :=
    CompressionActualBufferedBoundaryConjugationV841.support_away_fixed_disk
      K W hW (hC.of_isClosed_subset isClosed_closure hcl) hoff b c hcb hKfix
  have hKi : Continuous (fun p : Time × Plane => (K p.1).symm p.2) :=
    continuous_family_inverse K hK (closure V) hVc
      (fun t x hx => hoffV t x (fun hv => hx (subset_closure hv)))
  refine ⟨K,V,hK,hKi,hV,hVc,hVW.trans (hcl.trans hCR),?_,?_,hKfix,hoffV,?_⟩
  · exact hVD.mono_right (fun x hx => mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hx).trans_lt hc))
  · intro t x hx
    exact localize_eq (H t) g (fun x hx => hfix t x (mem_closedBall_zero_iff.mp hx)) hcontract
      (mem_closedBall_zero_iff.mpr hx)
  · intro t ht x
    change H t (g.symm ((H t).symm (g x))) = x
    have hi (y : Plane) : (H t).symm y = y := (H t).injective
      (by rw [(H t).apply_symm_apply,ht])
    rw [hi,g.symm_apply_apply,ht]

#print axioms parametric_supported_planar_localization
end CompressionActualParametricSupportedPlanarLocalizationV893
