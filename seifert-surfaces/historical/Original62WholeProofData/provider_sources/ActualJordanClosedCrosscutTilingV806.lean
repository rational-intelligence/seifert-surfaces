import SchoenfliesNativeCoimportProbeV754

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualJordanClosedCrosscutTilingV806

/-- The two closed Jordan cells of a crosscut exhaust the original closed
    Jordan disk, and overlap on exactly the entire crosscut. -/
theorem closed_crosscut_tiling
    {C P A₁ A₂ : Set Plane} {p q : Plane}
    (h : IsCrosscut C P p q) (hcut : IsCutPair C p q A₁ A₂)
    (hcollars : HasArcCollars (inside C) P) :
    IsJordanCurve (A₁ ∪ P) ∧ IsJordanCurve (A₂ ∪ P) ∧
      closure (inside (A₁ ∪ P)) ∪ closure (inside (A₂ ∪ P)) = closure (inside C) ∧
      closure (inside (A₁ ∪ P)) ∩ closure (inside (A₂ ∪ P)) = P ∧
      closure (inside (A₁ ∪ P)) ∩ C = A₁ ∧
      closure (inside (A₂ ∪ P)) ∩ C = A₂ := by
  have hC := jordan_curve_theorem h.curve
  have hJ₁ := jordan_curve_theorem (h.isJordanCurve_union hcut)
  have hJ₂ := jordan_curve_theorem (h.isJordanCurve_union hcut.symm)
  have hside₁ := h.side_subset (fun _ => jordan_curve_theorem) hcut
  have hside₂ := h.side_subset (fun _ => jordan_curve_theorem) hcut.symm
  have hcover := h.inside_diff_eq (fun _ => jordan_curve_theorem) hcut hcollars
  have hsep := h.disjoint_sides (fun _ => jordan_curve_theorem) hcut
  have hunion : closure (inside (A₁ ∪ P)) ∪ closure (inside (A₂ ∪ P)) =
      closure (inside C) := by
    rw [(IsRegionOf.inside _).closure_eq hJ₁,(IsRegionOf.inside _).closure_eq hJ₂,
      (IsRegionOf.inside _).closure_eq hC]
    apply Subset.antisymm
    · rintro x ((hx | hx) | (hx | hx))
      · exact Or.inl (hside₁ hx).1
      · rcases hx with hx | hx
        · exact Or.inr (hcut.fst_subset hx)
        · by_cases hxC : x ∈ C
          · exact Or.inr hxC
          · exact Or.inl (h.sdiff_subset ⟨hx,by
              simp only [mem_insert_iff,mem_singleton_iff]
              rintro (rfl | rfl)
              · exact hxC h.left_mem
              · exact hxC h.right_mem⟩)
      · exact Or.inl (hside₂ hx).1
      · rcases hx with hx | hx
        · exact Or.inr (hcut.snd_subset hx)
        · by_cases hxC : x ∈ C
          · exact Or.inr hxC
          · exact Or.inl (h.sdiff_subset ⟨hx,by
              simp only [mem_insert_iff,mem_singleton_iff]
              rintro (rfl | rfl)
              · exact hxC h.left_mem
              · exact hxC h.right_mem⟩)
    · rintro x (hx | hx)
      · by_cases hxP : x ∈ P
        · exact Or.inl (Or.inr (Or.inr hxP))
        · rcases (hcover ▸ (show x ∈ inside C \ P from ⟨hx,hxP⟩)) with hx₁ | hx₂
          · exact Or.inl (Or.inl hx₁)
          · exact Or.inr (Or.inl hx₂)
      · rcases hcut.union_eq.symm ▸ hx with hx₁ | hx₂
        · exact Or.inl (Or.inr (Or.inl hx₁))
        · exact Or.inr (Or.inr (Or.inl hx₂))
  have hinter : closure (inside (A₁ ∪ P)) ∩ closure (inside (A₂ ∪ P)) = P := by
    rw [(IsRegionOf.inside _).closure_eq hJ₁,(IsRegionOf.inside _).closure_eq hJ₂]
    apply Subset.antisymm
    · rintro x ⟨hx₁ | hx₁,hx₂ | hx₂⟩
      · exact False.elim (disjoint_left.mp hsep hx₁ hx₂)
      · rcases hx₂ with hx₂ | hx₂
        · exact False.elim ((inside_subset_compl (hside₁ hx₁).1) (hcut.snd_subset hx₂))
        · exact hx₂
      · rcases hx₁ with hx₁ | hx₁
        · exact False.elim ((inside_subset_compl (hside₂ hx₂).1) (hcut.fst_subset hx₁))
        · exact hx₁
      · rcases hx₁ with hx₁ | hx₁
        · rcases hx₂ with hx₂ | hx₂
          · rcases hcut.inter_eq ▸ (show x ∈ A₁ ∩ A₂ from ⟨hx₁,hx₂⟩) with rfl | hxq
            · exact h.arc.left_mem
            · rw [mem_singleton_iff] at hxq
              exact hxq ▸ h.arc.right_mem
          · exact hx₂
        · exact hx₁
    · intro x hx
      exact ⟨Or.inr (Or.inr hx),Or.inr (Or.inr hx)⟩
  exact ⟨h.isJordanCurve_union hcut,h.isJordanCurve_union hcut.symm,hunion,hinter,
    h.closure_side_inter (fun _ => jordan_curve_theorem) hcut,
    h.closure_side_inter (fun _ => jordan_curve_theorem) hcut.symm⟩

#print axioms closed_crosscut_tiling
end CompressionActualJordanClosedCrosscutTilingV806
