import ActualSupportedCommutatorV822

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
noncomputable section
namespace CompressionActualCompactlySupportedContinuousBijectionV823

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- Continuity and identity off a compact set give a closed map, even
    before injectivity or surjectivity is known. -/
theorem isClosedMap_of_fixed_outside_compact {f : X → X} {K : Set X}
    (hf : Continuous f) (hK : IsCompact K) (hoff : EqOn f id Kᶜ) : IsClosedMap f := by
  intro S hS
  have heq : f '' S = f '' (S ∩ K) ∪ (S ∩ {x | f x = x}) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      by_cases hxK : x ∈ K
      · exact Or.inl ⟨x,⟨hx,hxK⟩,rfl⟩
      · have he : f x = x := hoff hxK
        exact Or.inr ⟨he.symm ▸ hx,by rw [he]; exact he⟩
    · rintro (⟨x,hx,rfl⟩ | ⟨hy,he⟩)
      · exact ⟨x,hx.1,rfl⟩
      · exact ⟨y,hy,he⟩
  rw [heq]
  exact ((hK.inter_left hS).image hf).isClosed.union
    (hS.inter (isClosed_eq hf continuous_id))

/-- A continuous bijection with compact support is a homeomorphism. -/
def homeomorph_of_fixed_outside_compact (f : X → X) (hf : Continuous f)
    (hb : Function.Bijective f) (K : Set X) (hK : IsCompact K)
    (hoff : EqOn f id Kᶜ) : X ≃ₜ X :=
  (Equiv.ofBijective f hb).toHomeomorphOfContinuousClosed hf
    (isClosedMap_of_fixed_outside_compact hf hK hoff)

/-- The inverse of a jointly continuous compactly supported family is
    jointly continuous. This supplies the inverse needed for localization. -/
theorem continuous_family_inverse {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] (g : Y → X ≃ₜ X)
    (hg : Continuous (fun p : Y × X => g p.1 p.2))
    (K : Set X) (hK : IsCompact K) (hoff : ∀ t,EqOn (g t) id Kᶜ) :
    Continuous (fun p : Y × X => (g p.1).symm p.2) := by
  let f (p : Y × X) : Y × X := (p.1,g p.1 p.2)
  have hf : Continuous f := continuous_fst.prodMk hg
  have hbij : Function.Bijective f := by
    constructor
    · intro p q he
      have he' : (p.1,g p.1 p.2) = (q.1,g q.1 q.2) := he
      have ht := congrArg (fun z : Y × X => z.1) he'
      change p.1 = q.1 at ht
      have hx : p.2 = q.2 := by
        apply (g p.1).injective
        have hv := congrArg (fun z : Y × X => z.2) he'
        simpa only [f,ht] using hv
      exact Prod.ext ht hx
    · intro q
      exact ⟨(q.1,(g q.1).symm q.2),Prod.ext rfl ((g q.1).apply_symm_apply q.2)⟩
  have hKp : IsCompact ((univ : Set Y) ×ˢ K) := isCompact_univ.prod hK
  have hfOff : EqOn f id ((univ : Set Y) ×ˢ K)ᶜ := by
    rintro ⟨t,x⟩ hx
    have hxK : x ∉ K := fun h => hx ⟨mem_univ _,h⟩
    exact Prod.ext rfl (hoff t hxK)
  let e := homeomorph_of_fixed_outside_compact f hf hbij _ hKp hfOff
  have hinv (q : Y × X) : e.symm q = (q.1,(g q.1).symm q.2) := by
    apply e.injective
    have he : f (q.1,(g q.1).symm q.2) = q :=
      Prod.ext rfl ((g q.1).apply_symm_apply q.2)
    exact (e.apply_symm_apply q).trans he.symm
  exact (continuous_snd.comp e.symm.continuous).congr (fun q => congrArg Prod.snd (hinv q))

#print axioms isClosedMap_of_fixed_outside_compact
#print axioms continuous_family_inverse
end CompressionActualCompactlySupportedContinuousBijectionV823
