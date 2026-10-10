import ActualParametricSupportedPlanarLocalizationV893
import ActualBoundaryExactDiskSeparatedIsotopyV845

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Topology Metric
open SeifertSurfaces.Foundations
open CompressionActualRadialCompactCompressionV825
noncomputable section
namespace CompressionActualParametricBoundaryExactLocalizationV894

/-- Every stage of the same whole confined annulus family has one
    jointly continuous supported realization, exact on the whole compact
    outer strip and separated from the entire fixed unit disk. -/
theorem parametric_boundary_exact_localization
    (H : Time → Plane ≃ₜ Plane)
    (hH : Continuous (fun p : Time × Plane => H p.1 p.2))
    (hHi : Continuous (fun p : Time × Plane => (H p.1).symm p.2))
    (hfix : ∀ t x,‖x‖ ≤ 1 → H t x = x)
    (hbound : ∀ t x,‖x‖ ≤ 2 → ‖H t x‖ ≤ 2)
    (B : Set Plane) (hBc : IsCompact B)
    (hBn : ∀ x ∈ B,1 < ‖x‖) (hB2 : ∀ x ∈ B,‖x‖ ≤ 2) :
    ∃ K : Time → Plane ≃ₜ Plane,∃ V : Set Plane,
      Continuous (fun p : Time × Plane => K p.1 p.2) ∧
      Continuous (fun p : Time × Plane => (K p.1).symm p.2) ∧
      IsOpen V ∧ IsCompact (closure V) ∧ closure V ⊆ ball 0 3 ∧
      Disjoint (closure V) (closedBall (0 : Plane) 1) ∧
      (∀ t x,x ∈ B → K t x = H t x) ∧
      (∀ t x,‖x‖ ≤ 1 → K t x = x) ∧
      (∀ t x,x ∉ V → K t x = x) ∧
      ∀ t,(∀ x,H t x = x) → ∀ x,K t x = x := by
  classical
  have hprod : IsCompact ((univ : Set Time) ×ˢ B) := isCompact_univ.prod hBc
  obtain ⟨m,hm,hBm⟩ := hprod.exists_forall_le'
    ((continuous_snd.norm.min hH.norm).continuousOn) (a := (1:ℝ)) (by
      rintro ⟨t,x⟩ ⟨ht,hx⟩
      exact lt_min (hBn x hx)
        (CompressionActualBoundaryExactDiskSeparatedIsotopyV845.image_outside_fixed_disk (H t) (hfix t) (hBn x hx)))
  let c : ℝ := (1+min m 2)/2
  have hc : 1 < c := by dsimp [c]; have hh := lt_min hm (by norm_num : (1:ℝ)<2); linarith
  have hcm : c ≤ m := by dsimp [c]; have hh := min_le_left m 2; have hh' := lt_min hm (by norm_num : (1:ℝ)<2); linarith
  have hc2 : c < 2 := by dsimp [c]; have hh := min_le_right m 2; linarith
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
  let H' (t : Time) : Plane ≃ₜ Plane := g.trans ((H t).trans g.symm)
  have hH' : Continuous (fun p : Time × Plane => H' p.1 p.2) :=
    g.symm.continuous.comp (hH.comp (continuous_fst.prodMk (g.continuous.comp continuous_snd)))
  have hH'i : Continuous (fun p : Time × Plane => (H' p.1).symm p.2) :=
    g.symm.continuous.comp (hHi.comp (continuous_fst.prodMk (g.continuous.comp continuous_snd)))
  have hH'fix (t : Time) (x : Plane) (hx : ‖x‖ ≤ b) : H' t x = x := by
    have hgin : ‖g x‖ ≤ 1 := by
      change ‖radial b c a x‖ ≤ 1
      rw [radial_norm b c a ha ha1,coefficient_inner b c a ‖x‖ hbc hx]
      exact (mul_le_mul_of_nonneg_left hx ha.le).trans hab
    change g.symm (H t (g x)) = x
    rw [hfix t _ hgin,g.symm_apply_apply]
  have hH'B (t : Time) : EqOn (H' t) (H t) B := by
    intro x hx
    have hl := hBm (t,x) ⟨mem_univ _,hx⟩
    have hnx := hcm.trans (hl.trans (min_le_left _ _))
    have hnHx := hcm.trans (hl.trans (min_le_right _ _))
    change g.symm (H t (g x)) = H t x
    rw [hgout _ hnx]
    exact g.injective (by rw [g.apply_symm_apply,hgout _ hnHx])
  have hH'3 (t : Time) (x : Plane) (hx : ‖x‖ ≤ 2) : ‖H' t x‖ < 3 := by
    have hh : H t (g x) ∈ ball (0 : Plane) 3 := mem_ball_zero_iff.mpr
      ((hbound t (g x) ((hgnorm x).trans hx)).trans_lt (by norm_num))
    exact mem_ball_zero_iff.mp (CompressionActualBoundaryExactDiskSeparatedIsotopyV845.inverse_preserves_larger_ball
      g c 3 (by linarith) hgout hh)
  obtain ⟨K,V,hK,hKi,hV,hVc,hVR,hVD,hKV,hKfix,hoff,hid⟩ :=
    CompressionActualParametricSupportedPlanarLocalizationV893.parametric_supported_planar_localization
      H' hH' hH'i b hb hH'fix 2 3 (by norm_num) (by norm_num) hH'3
  refine ⟨K,V,hK,hKi,hV,hVc,hVR,hVD,?_,?_,hoff,?_⟩
  · intro t x hx
    exact (hKV t x (hB2 x hx)).trans (hH'B t hx)
  · intro t x hx
    exact hKfix t x (hx.trans hb.le)
  · intro t ht x
    apply hid t (fun y => ?_) x
    change g.symm (H t (g y)) = y
    rw [ht,g.symm_apply_apply]

#print axioms parametric_boundary_exact_localization
end CompressionActualParametricBoundaryExactLocalizationV894
