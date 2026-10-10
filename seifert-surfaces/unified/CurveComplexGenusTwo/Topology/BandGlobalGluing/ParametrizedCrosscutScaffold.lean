import CurveComplexGenusTwo.Topology.PrescribedCrosscut

open Set Topology unitInterval
namespace CurveComplex
open Schoenflies

/-- Build the actual prescribed crosscut extension from the two parametrized
embeddings, retaining every transverse parameter rather than only the image. -/
theorem parametrized_relative_crosscut_replacement
    (f g : I → Plane) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (ha : f 0 ∈ modelCurve) (hb : f 1 ∈ modelCurve)
    (hfi : ∀ t : I, 0 < t → t < 1 → f t ∈ Plane.openSquare 0 1)
    (hgi : ∀ t : I, 0 < t → t < 1 → g t ∈ Plane.openSquare 0 1) :
    ∃ F : Plane ≃ₜ Plane,
      (∀ t : I, F (f t) = g t) ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) := by
  classical
  let fc : ℝ → Plane := f ∘ projIcc 0 1 zero_le_one
  let gc : ℝ → Plane := g ∘ projIcc 0 1 zero_le_one
  have hfc : ContinuousOn fc I := (hf.continuous.comp continuous_projIcc).continuousOn
  have hgc : ContinuousOn gc I := (hg.continuous.comp continuous_projIcc).continuousOn
  have hfval (t : ℝ) (ht : t ∈ I) : fc t = f ⟨t,ht⟩ := by
    simp [fc,projIcc_of_mem zero_le_one ht]
  have hgval (t : ℝ) (ht : t ∈ I) : gc t = g ⟨t,ht⟩ := by
    simp [gc,projIcc_of_mem zero_le_one ht]
  have hfci : InjOn fc I := by
    intro r hr s hs he
    rw [hfval r hr,hfval s hs] at he
    exact congrArg Subtype.val (hf.injective he)
  have hgci : InjOn gc I := by
    intro r hr s hs he
    rw [hgval r hr,hgval s hs] at he
    exact congrArg Subtype.val (hg.injective he)
  have hfimage : fc '' I = Set.range f := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(hfval t ht).symm⟩
    · rintro ⟨t,rfl⟩; exact ⟨t,t.property,hfval t t.property⟩
  have hgimage : gc '' I = Set.range g := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,(hgval t ht).symm⟩
    · rintro ⟨t,rfl⟩; exact ⟨t,t.property,hgval t t.property⟩
  have hA : IsArcBetween (Set.range f) (f 0) (f 1) :=
    ⟨fc,hfc,hfci,hfimage,hfval 0 zero_mem_I,hfval 1 one_mem_I⟩
  have hB : IsArcBetween (Set.range g) (f 0) (f 1) :=
    ⟨gc,hgc,hgci,hgimage,(hgval 0 zero_mem_I).trans h0.symm,
      (hgval 1 one_mem_I).trans h1.symm⟩
  let fi : Plane → ℝ := Function.invFunOn fc I
  let gi : Plane → ℝ := Function.invFunOn gc I
  let u : Plane → Plane := gc ∘ fi
  let v : Plane → Plane := fc ∘ gi
  have hfic : ContinuousOn fi (Set.range f) := by
    rw [← hfimage]
    exact continuousOn_invFunOn_image' isCompact_I hfc hfci
  have hgic : ContinuousOn gi (Set.range g) := by
    rw [← hgimage]
    exact continuousOn_invFunOn_image' isCompact_I hgc hgci
  have hfiMap : MapsTo fi (Set.range f) I := by
    rintro x ⟨t,rfl⟩
    change Function.invFunOn fc I (f t) ∈ I
    rw [← hfval t t.property,hfci.leftInvOn_invFunOn t.property]
    exact t.property
  have hgiMap : MapsTo gi (Set.range g) I := by
    rintro x ⟨t,rfl⟩
    change Function.invFunOn gc I (g t) ∈ I
    rw [← hgval t t.property,hgci.leftInvOn_invFunOn t.property]
    exact t.property
  have hu (t : I) : u (f t) = g t := by
    dsimp [u,fi]
    rw [← hfval t t.property,hfci.leftInvOn_invFunOn t.property,hgval t t.property]
  have hv (t : I) : v (g t) = f t := by
    dsimp [v,gi]
    rw [← hgval t t.property,hgci.leftInvOn_invFunOn t.property,hfval t t.property]
  let h : ArcHomeo (Set.range f) (Set.range g) (f 0) (f 1) (f 0) (f 1) := {
    toFun := u
    invFun := v
    continuousOn_toFun := hgc.comp hfic hfiMap
    continuousOn_invFun := hfc.comp hgic hgiMap
    leftInvOn := by rintro x ⟨t,rfl⟩; rw [hu,hv]
    rightInvOn := by rintro x ⟨t,rfl⟩; rw [hv,hu]
    image_eq := by
      ext x
      constructor
      · rintro ⟨y,⟨t,rfl⟩,rfl⟩; exact ⟨t,(hu t).symm⟩
      · rintro ⟨t,rfl⟩; exact ⟨f t,Set.mem_range_self t,hu t⟩
    map_left := (hu 0).trans h0.symm
    map_right := (hu 1).trans h1.symm }
  have hAi : Set.range f \ {f 0,f 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,ht⟩
    have ht0 : t ≠ 0 := by intro he; apply ht; simp [he]
    have ht1 : t ≠ 1 := by intro he; apply ht; simp [he]
    exact hfi t (lt_of_le_of_ne t.property.1 ht0.symm)
      (lt_of_le_of_ne t.property.2 ht1)
  have hBi : Set.range g \ {f 0,f 1} ⊆ Plane.openSquare 0 1 := by
    rintro x ⟨⟨t,rfl⟩,ht⟩
    have ht0 : t ≠ 0 := by intro he; apply ht; simp [he,← h0]
    have ht1 : t ≠ 1 := by intro he; apply ht; simp [he,← h1]
    exact hgi t (lt_of_le_of_ne t.property.1 ht0.symm)
      (lt_of_le_of_ne t.property.2 ht1)
  obtain ⟨F,hpres,himage,hfixed⟩ := prescribed_relative_crosscut_replacement
    (Set.range f) (Set.range g) (f 0) (f 1) hA hB ha hb hAi hBi h
  refine ⟨F,?_,hfixed⟩
  intro t
  exact (hpres _ (Set.mem_range_self t)).trans (hu t)

#print axioms parametrized_relative_crosscut_replacement

end CurveComplex
