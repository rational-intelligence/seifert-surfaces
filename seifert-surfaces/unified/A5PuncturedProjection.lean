import A5OrderedCovering
import Mathlib.Topology.LocalAtTarget

set_option autoImplicit false
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-- A unique exceptional fiber and connected punctured source neighborhoods
force the whole local punctured covering to be connected. -/
theorem punctured_cover_preconnected
    {X B : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace B] [T2Space B]
    (f : X → B) (hf : Continuous f) (x : X)
    (U : Set B) (hU : IsOpen U) (hxU : f x ∈ U)
    (hzero : ∀ z, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (f ⁻¹' (U \ {f x})))
    (hbase : IsPreconnected (U \ {f x}))
    (hacc : f x ∈ closure (U \ {f x}))
    (hpuncture : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x})) :
    IsPreconnected (f ⁻¹' (U \ {f x})) := by
  let D := f ⁻¹' (U \ {f x})
  let T := U \ {f x}
  let p : D → T := T.restrictPreimage f
  have hc : IsCoveringMap p :=
    (IsCoveringMapOn.of_isLocalHomeomorphOn hf hlocal).isCoveringMap_restrictPreimage
  have hclosed : IsClosedMap p := hf.isClosedMap.restrictPreimage T
  let _ : PreconnectedSpace T := Subtype.preconnectedSpace hbase
  apply isPreconnected_iff_preconnectedSpace.mpr
  apply preconnectedSpace_iff_clopen.mpr
  intro A hA
  by_cases hAe : A = ∅
  · exact Or.inl hAe
  right
  apply Set.eq_univ_of_forall
  intro z
  by_contra hz
  have hAcne : Aᶜ.Nonempty := ⟨z, hz⟩
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hAe
  have image_all (C : Set D) (hC : IsClopen C) (hne : C.Nonempty) : p '' C = univ :=
    IsClopen.eq_univ ⟨hclosed C hC.isClosed, hc.isOpenMap C hC.isOpen⟩ (hne.image p)
  have hAi : p '' A = univ := image_all A hA hAne
  have hAci : p '' Aᶜ = univ := image_all Aᶜ hA.compl hAcne
  obtain ⟨W, hW, hxW, hWV, hWconn⟩ := hpuncture (f ⁻¹' U) (hU.preimage hf) hxU
  have hWD : W \ {x} ⊆ D := by
    intro y hy
    refine ⟨hWV hy.1, ?_⟩
    intro he
    exact hy.2 (hzero y he)
  let j : ↥(W \ {x}) → D := fun y => ⟨y, hWD y.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  let _ : PreconnectedSpace ↥(W \ {x}) := Subtype.preconnectedSpace hWconn
  have hsplit : j ⁻¹' A = ∅ ∨ j ⁻¹' A = univ := isClopen_iff.mp (hA.preimage hj)
  have hnot : f x ∉ f '' Wᶜ := by
    rintro ⟨y, hy, he⟩
    exact hy (hzero y he ▸ hxW)
  have hgood : (f '' Wᶜ)ᶜ ∈ 𝓝 (f x) :=
    (hf.isClosedMap _ hW.isClosed_compl).isOpen_compl.mem_nhds hnot
  obtain ⟨b, hbGood, hbT⟩ := mem_closure_iff_nhds.mp hacc _ hgood
  let bT : T := ⟨b, hbT⟩
  have all_fibers_in_W (y : D) (he : p y = bT) : y.val ∈ W := by
    by_contra hy
    exact hbGood ⟨y, hy, congrArg Subtype.val he⟩
  have get (C : Set D) (hCi : p '' C = univ) :
      ∃ y : ↥(W \ {x}), j y ∈ C := by
    have hb : bT ∈ p '' C := hCi.symm ▸ mem_univ bT
    obtain ⟨y, hy, he⟩ := hb
    have hyW : y.val ∈ W := all_fibers_in_W y he
    have hyn : y.val ∉ ({x} : Set X) := by
      intro hyx
      have hyT := y.property.2
      exact hyT (congrArg f hyx)
    exact ⟨⟨y.val, hyW, hyn⟩, hy⟩
  obtain ⟨yA, hyA⟩ := get A hAi
  obtain ⟨yAc, hyAc⟩ := get Aᶜ hAci
  rcases hsplit with he | he
  · have : yA ∈ (∅ : Set ↥(W \ {x})) := he ▸ hyA
    exact this
  · have : yAc ∈ j ⁻¹' A := he.symm ▸ mem_univ yAc
    exact hyAc this

/-- An embedded real height excludes nontrivial branching over the unique
exceptional fiber. The covering and its connectedness are proved here from
compactness and punctured local homeomorphisms. -/
theorem projection_injective_across_exceptional_point
    {X B : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace B] [T2Space B]
    (f : X → B) (hf : Continuous f) (x : X)
    (U : Set B) (hU : IsOpen U) (hxU : f x ∈ U)
    (hzero : ∀ z, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (f ⁻¹' (U \ {f x})))
    (hbase : IsPreconnected (U \ {f x}))
    (hacc : f x ∈ closure (U \ {f x}))
    (hpuncture : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}))
    (height : X → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z))) :
    InjOn f (f ⁻¹' U) := by
  let T := U \ {f x}
  let D := f ⁻¹' T
  let p : D → T := T.restrictPreimage f
  have hcOn := IsCoveringMapOn.of_isLocalHomeomorphOn hf hlocal
  have hc : IsCoveringMap p := hcOn.isCoveringMap_restrictPreimage
  let _ : PreconnectedSpace D := Subtype.preconnectedSpace
    (punctured_cover_preconnected f hf x U hU hxU hzero hlocal hbase hacc hpuncture)
  have hfinite (b : T) : (p ⁻¹' {b}).Finite := by
    have hd : DiscreteTopology (f ⁻¹' {b.val}) := (hcOn b.val b.property).1
    have hfib : (f ⁻¹' {b.val}).Finite :=
      (isClosed_singleton.preimage hf).isCompact.finite ⟨hd⟩
    let _ : Finite (f ⁻¹' {b.val}) := hfib.to_subtype
    let J : (p ⁻¹' {b}) → (f ⁻¹' {b.val}) := fun y =>
      ⟨y.val.val, congrArg Subtype.val y.property⟩
    have hJ : Function.Injective J := by
      intro a c he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : f ⁻¹' {b.val} => y.val) he
    let _ : Finite (p ⁻¹' {b}) := Finite.of_injective J hJ
    exact Set.toFinite _
  have hsep : Function.Injective (fun z : D => (p z, height z)) := by
    intro a b he
    apply Subtype.ext
    apply hseparate
    have hfst : f a.val = f b.val :=
      congrArg (fun q : T × ℝ => q.1.val) he
    have hsnd : height a.val = height b.val :=
      congrArg (fun q : T × ℝ => q.2) he
    exact Prod.ext hfst hsnd
  have hi := finite_covering_injective_of_ordered_heights p hc hfinite
    (fun z : D => height z) (hheight.comp continuous_subtype_val) hsep
  intro a ha b hb hab
  by_cases haz : f a = f x
  · exact (hzero a haz).trans (hzero b (hab.symm.trans haz)).symm
  · have haD : a ∈ D := ⟨ha, haz⟩
    have hbD : b ∈ D := ⟨hb, fun h => haz (hab.trans h)⟩
    exact congrArg Subtype.val (hi (show p ⟨a, haD⟩ = p ⟨b, hbD⟩ from Subtype.ext hab))

/-- The single-sheet projection extends to a genuine local homeomorphism
across the exceptional point, with target exactly the supplied neighborhood. -/
theorem projection_homeomorph_across_exceptional_point
    {X B : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace B] [T2Space B]
    (f : X → B) (hf : Continuous f) (x : X)
    (U : Set B) (hU : IsOpen U) (hxU : f x ∈ U)
    (hzero : ∀ z, f z = f x → z = x)
    (hlocal : IsLocalHomeomorphOn f (f ⁻¹' (U \ {f x})))
    (hbase : IsPreconnected (U \ {f x}))
    (hacc : f x ∈ closure (U \ {f x}))
    (hsourceacc : x ∈ closure ({x}ᶜ : Set X))
    (hpuncture : ∀ V : Set X, IsOpen V → x ∈ V →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧ IsPreconnected (W \ {x}))
    (height : X → ℝ) (hheight : Continuous height)
    (hseparate : Function.Injective (fun z => (f z, height z))) :
    IsHomeomorph (U.restrictPreimage f) := by
  let T := U \ {f x}
  let D := f ⁻¹' T
  let p : D → T := T.restrictPreimage f
  have hc : IsCoveringMap p :=
    (IsCoveringMapOn.of_isLocalHomeomorphOn hf hlocal).isCoveringMap_restrictPreimage
  have hclosed : IsClosedMap p := hf.isClosedMap.restrictPreimage T
  let _ : PreconnectedSpace T := Subtype.preconnectedSpace hbase
  have hrange : IsClopen (range p) :=
    ⟨hclosed.isClosed_range, hc.isOpenMap.isOpen_range⟩
  obtain ⟨y, hyU, hyx⟩ := mem_closure_iff_nhds.mp hsourceacc _
    ((hU.preimage hf).mem_nhds hxU)
  have hyT : y ∈ D := ⟨hyU, fun he => hyx (hzero y he)⟩
  have hall : range p = univ := hrange.eq_univ ⟨p ⟨y, hyT⟩, ⟨⟨y, hyT⟩, rfl⟩⟩
  have hsurj : Function.Surjective (U.restrictPreimage f) := by
    intro b
    by_cases hb : b.val = f x
    · refine ⟨⟨x, hxU⟩, Subtype.ext hb.symm⟩
    · have hbT : b.val ∈ T := ⟨b.property, hb⟩
      have hbR : (⟨b.val, hbT⟩ : T) ∈ range p := hall.symm ▸ mem_univ _
      obtain ⟨z, hz⟩ := hbR
      refine ⟨⟨z.val, z.property.1⟩, ?_⟩
      exact Subtype.ext (congrArg (fun q : T => q.val) hz)
  have hinj := projection_injective_across_exceptional_point f hf x U hU hxU hzero
    hlocal hbase hacc hpuncture height hheight hseparate
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨hf.restrictPreimage, hf.isClosedMap.restrictPreimage U, ?_, hsurj⟩
  intro a b hab
  exact Subtype.ext (hinj a.property b.property (congrArg Subtype.val hab))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
