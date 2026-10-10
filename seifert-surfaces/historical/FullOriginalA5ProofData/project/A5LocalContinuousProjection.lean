import A5LocalProjection

set_option autoImplicit false
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- The punctured projection theorem requires continuity only on the actual
coordinate neighborhood. Outside values of the ambient chart play no role. -/
theorem locally_continuous_projection_across_point
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    (f : X → Euc 2) (x : X) (U : Set X) (hU : IsOpen U) (hxU : x ∈ U)
    (hf : ContinuousOn f U)
    (hzero : ∀ z ∈ U, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (U \ {x}))
    (hsourceacc : x ∈ closure ({x}ᶜ : Set X))
    (hpuncture : ∀ O : Set X, IsOpen O → x ∈ O →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPreconnected (W \ {x}))
    (height : X → ℝ) (hheight : ContinuousOn height U)
    (hseparate : InjOn (fun z => (f z, height z)) U) :
    IsLocalHomeomorphOn f {x} := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let xU : U := ⟨x, hxU⟩
  let fU : U → Euc 2 := f ∘ Subtype.val
  have hi : IsLocalHomeomorph (Subtype.val : U → X) :=
    hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hlocalU : IsLocalHomeomorphOn fU (univ \ {xU}) := by
    apply hlocal.comp hi.isLocalHomeomorphOn
    intro z hz
    exact ⟨z.property, fun he => hz.2 (Subtype.ext he)⟩
  have haccU : xU ∈ closure ({xU}ᶜ : Set U) := by
    apply mem_closure_iff_nhds.mpr
    intro O hO
    obtain ⟨O', hO'O, hO', hxO'⟩ := mem_nhds_iff.mp hO
    obtain ⟨A, hA, hAO⟩ := IsInducing.subtypeVal.isOpen_iff.mp hO'
    have hxA : x ∈ A := by rw [← hAO] at hxO'; exact hxO'
    obtain ⟨y, hy, hyx⟩ := mem_closure_iff_nhds.mp hsourceacc _
      ((hA.inter hU).mem_nhds ⟨hxA, hxU⟩)
    refine ⟨⟨y, hy.2⟩, hO'O ?_, ?_⟩
    · rw [← hAO]
      exact hy.1
    · intro he
      exact hyx (congrArg Subtype.val he)
  have hpU : ∀ O : Set U, IsOpen O → xU ∈ O →
      ∃ W : Set U, IsOpen W ∧ xU ∈ W ∧ W ⊆ O ∧ IsPreconnected (W \ {xU}) := by
    intro O hO hxO
    obtain ⟨A, hA, rfl⟩ := IsInducing.subtypeVal.isOpen_iff.mp hO
    obtain ⟨W, hW, hxW, hWA, hpre⟩ := hpuncture (A ∩ U) (hA.inter hU) ⟨hxO, hxU⟩
    refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hxW,
      fun z hz => (hWA hz).1, ?_⟩
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    have he : (Subtype.val : U → X) '' ((Subtype.val ⁻¹' W) \ {xU}) = W \ {x} := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
        exact ⟨hz, fun he => hzx (Subtype.ext he)⟩
      · intro hy
        exact ⟨⟨y, (hWA hy.1).2⟩, ⟨hy.1, fun he => hy.2 (congrArg Subtype.val he)⟩, rfl⟩
    rwa [he]
  have hl := projection_local_homeomorph_across_point fU hf.domRestrict xU univ isOpen_univ
    (mem_univ _) (fun z _ hz => Subtype.ext (hzero z z.property hz)) hlocalU haccU hpU
    (height ∘ Subtype.val) hheight.domRestrict
    (fun a _ b _ hab => Subtype.ext (hseparate a.property b.property hab))
  have hfX : IsLocalHomeomorphOn f ((Subtype.val : U → X) '' {xU}) :=
    hl.of_comp_right hi.isLocalHomeomorphOn
  apply hfX.mono
  intro y hy
  subst y
  exact ⟨xU, mem_singleton _, rfl⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
