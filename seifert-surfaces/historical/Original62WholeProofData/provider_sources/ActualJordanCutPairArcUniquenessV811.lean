import ActualNestedJordanCompatibleCutsV810

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open Schoenflies
noncomputable section
namespace CompressionActualJordanCutPairArcUniquenessV811

/-- A third arc with the same endpoints contained in the curve is one of
    the two complete boundary arcs. Its open interior cannot cross from
    one closed arc to the other through either excluded endpoint. -/
theorem arc_eq_one_of_cut_pair
    {C A B₁ B₂ : Set Plane} {p q : Plane}
    (hcut : IsCutPair C p q B₁ B₂) (hA : IsArcBetween A p q) (hAC : A ⊆ C) :
    A = B₁ ∨ A = B₂ := by
  have hclosed (B : Set Plane) (hB : IsArcBetween B p q) : IsClosed B := by
    obtain ⟨f,hfc,-,hfim,-,-⟩ := hB
    rw [← hfim]
    exact (isCompact_I.image_of_continuousOn hfc).isClosed
  have hcover : A \ {p,q} ⊆ B₁ ∪ B₂ := by
    intro x hx
    exact hcut.union_eq.symm ▸ hAC hx.1
  have hn : ¬ ((A \ {p,q} ∩ B₁).Nonempty ∧ (A \ {p,q} ∩ B₂).Nonempty) := by
    rintro ⟨h₁,h₂⟩
    obtain ⟨x,hx,hmeet⟩ := isPreconnected_closed_iff.mp hA.isPreconnected_diff
      B₁ B₂ (hclosed B₁ hcut.fst) (hclosed B₂ hcut.snd) hcover h₁ h₂
    exact hx.2 (hcut.inter_eq ▸ hmeet)
  have hsub : A ⊆ B₁ ∨ A ⊆ B₂ := by
    by_cases h₁ : (A \ {p,q} ∩ B₁).Nonempty
    · left
      intro x hx
      by_cases hxpq : x ∈ ({p,q} : Set Plane)
      · exact (pair_subset hcut.fst.left_mem hcut.fst.right_mem) hxpq
      · rcases hcover ⟨hx,hxpq⟩ with hx₁ | hx₂
        · exact hx₁
        · exact False.elim (hn ⟨h₁,⟨x,⟨hx,hxpq⟩,hx₂⟩⟩)
    · right
      intro x hx
      by_cases hxpq : x ∈ ({p,q} : Set Plane)
      · exact (pair_subset hcut.snd.left_mem hcut.snd.right_mem) hxpq
      · rcases hcover ⟨hx,hxpq⟩ with hx₁ | hx₂
        · exact False.elim (h₁ ⟨x,⟨hx,hxpq⟩,hx₁⟩)
        · exact hx₂
  rcases hsub with hsub | hsub
  · exact Or.inl (hA.eq_of_subset_arc hcut.fst hcut.fst hsub Subset.rfl)
  · exact Or.inr (hA.eq_of_subset_arc hcut.snd hcut.snd hsub Subset.rfl)

#print axioms arc_eq_one_of_cut_pair
end CompressionActualJordanCutPairArcUniquenessV811
