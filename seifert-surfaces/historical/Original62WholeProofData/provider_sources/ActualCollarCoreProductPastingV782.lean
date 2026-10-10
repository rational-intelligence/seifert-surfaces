import ActualAnnulusWholeFamilyWithSideChoiceV780

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualCollarCoreProductPastingV782

/-- Paste a whole annulus-collar product to the actual whole disk core product.
    Agreement is required only on their literal common collar level. -/
theorem collar_core_product_pasting
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y]
    (c : C(Circle × Time,X)) (hc : IsEmbedding c) (r : Time)
    (ho : IsOpen (c '' {p : Circle × Time | p.2.val < r.val}))
    (out : C((Circle × Time) × Time,Y)) (core : C(X × Time,Y))
    (hmatch : ∀ z t,out ((z,r),t) = core (c (z,r),t)) :
    ∃ J : C(X × Time,Y),
      (∀ z s t,s.val ≤ r.val → J (c (z,s),t) = out ((z,s),t)) ∧
      ∀ p t,p ∉ c '' {p : Circle × Time | p.2.val < r.val} → J (p,t) = core (p,t) := by
  classical
  let K : (Circle × Time) × Time → X × Time := fun p => (c p.1,p.2)
  have hKc : Continuous K := (c.continuous.comp continuous_fst).prodMk continuous_snd
  have hKi : Function.Injective K := by
    intro p q he
    have h₁ := congrArg (fun a : X × Time => a.1) he
    have h₂ := congrArg (fun a : X × Time => a.2) he
    exact Prod.ext (hc.injective h₁) h₂
  have hK : IsEmbedding K := (hKc.isClosedEmbedding hKi).isEmbedding
  let S : Set ((Circle × Time) × Time) := {p | p.1.2.val ≤ r.val}
  let C : Set (X × Time) := K '' S
  let O : Set (X × Time) := (c '' {p : Circle × Time | p.2.val < r.val}) ×ˢ univ
  have hS : IsClosed S := isClosed_le continuous_fst.snd.subtype_val continuous_const
  have hC : IsClosed C := (hS.isCompact.image hKc).isClosed
  have hO : IsOpen O := ho.prod isOpen_univ
  have hOC : O ⊆ C := by
    rintro ⟨p,t⟩ ⟨⟨q,hq,rfl⟩,ht⟩
    refine ⟨(q,t),?_,rfl⟩
    change q.2.val ≤ r.val
    change q.2.val < r.val at hq
    exact hq.le
  let f : X × Time → Y := Function.extend K out core
  have hf (p : (Circle × Time) × Time) : f (K p) = out p := hKi.extend_apply out core p
  let J : X × Time → Y := C.piecewise f core
  have hJout (z : Circle) (s t : Time) (hs : s.val ≤ r.val) :
      J (c (z,s),t) = out ((z,s),t) := by
    have hp : (c (z,s),t) ∈ C := ⟨((z,s),t),hs,rfl⟩
    exact (Set.piecewise_eq_of_mem C f core hp).trans (hf ((z,s),t))
  have hJcore (p : X) (t : Time) (hp : p ∉ c '' {p : Circle × Time | p.2.val < r.val}) :
      J (p,t) = core (p,t) := by
    by_cases hx : (p,t) ∈ C
    · obtain ⟨⟨⟨z,s⟩,u⟩,hs,he⟩ := hx
      have he' : (c (z,s),u) = (p,t) := he
      obtain ⟨hcs,hut⟩ := Prod.mk.inj he'
      subst u
      have hn : ¬ s.val < r.val := by
        intro hlt
        exact hp ⟨(z,s),hlt,hcs⟩
      have hsr : s = r := Subtype.ext (le_antisymm hs (le_of_not_gt hn))
      subst s
      rw [← hcs,hJout _ _ _ le_rfl,hmatch]
    · exact Set.piecewise_eq_of_notMem C f core hx
  have hJfirst : ContinuousOn J C := by
    apply hK.isInducing.continuousOn_image_iff.mpr
    apply out.continuous.continuousOn.congr
    intro p hp
    obtain ⟨⟨z,s⟩,t⟩ := p
    exact hJout z s t hp
  have hJsecond : ContinuousOn J Oᶜ := core.continuous.continuousOn.congr (by
    rintro ⟨p,t⟩ hp
    exact hJcore p t (fun hc' => hp ⟨hc',mem_univ t⟩))
  have hcover : C ∪ Oᶜ = univ := by
    ext p
    simp only [mem_union,mem_compl_iff,mem_univ,iff_true]
    by_cases hp : p ∈ O
    · exact Or.inl (hOC hp)
    · exact Or.inr hp
  have hJc : Continuous J := by
    rw [← continuousOn_univ,← hcover]
    exact hJfirst.union_of_isClosed hJsecond hC hO.isClosed_compl
  exact ⟨⟨J,hJc⟩,hJout,hJcore⟩

end CompressionActualCollarCoreProductPastingV782
