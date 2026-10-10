import Schoenflies.MatchedArc
import Schoenflies.JordanSchoenflies

open Set

namespace CurveComplex

open Schoenflies

/-- The prescribed map on one Jordan subdisk boundary: move the crosscut
while fixing its complementary boundary arc pointwise. -/
theorem exists_boundary_homeomorph_fixing_arc_of_arcHomeo
    {R A B : Set Plane} {a b : Plane}
    (hR : IsArcBetween R a b) (hA : IsArcBetween A a b)
    (hB : IsArcBetween B a b)
    (hRA : R ∩ A = {a, b}) (hRB : R ∩ B = {a, b})
    (h : ArcHomeo A B a b a b) :
    ∃ e : ↥(R ∪ A) ≃ₜ ↥(R ∪ B),
      (∀ x : R, e ⟨x, Or.inl x.property⟩ =
        ⟨x, Or.inl x.property⟩) ∧
      (∀ (x : Plane) (hx : x ∈ A),
        (e ⟨x, Or.inr hx⟩ : Plane) = h.toFun x) ∧
      Subtype.val '' (e '' {x : ↥(R ∪ A) | (x : Plane) ∈ A}) = B := by
  classical
  let f : Plane → Plane := fun x => if x ∈ R then x else h.toFun x
  let g : Plane → Plane := fun x => if x ∈ R then x else h.invFun x
  have hendR : a ∈ R ∧ b ∈ R := ⟨hR.left_mem, hR.right_mem⟩
  have hendA : a ∈ A ∧ b ∈ A := ⟨hA.left_mem, hA.right_mem⟩
  have hendB : a ∈ B ∧ b ∈ B := ⟨hB.left_mem, hB.right_mem⟩
  have hfixEnds : h.toFun a = a ∧ h.toFun b = b := ⟨h.map_left, h.map_right⟩
  have hfonA : ∀ x ∈ A, f x = h.toFun x := by
    intro x hxA
    by_cases hxR : x ∈ R
    · have hxEnd : x = a ∨ x = b := by
        have : x ∈ ({a, b} : Set Plane) := hRA ▸ ⟨hxR, hxA⟩
        simpa using this
      rcases hxEnd with rfl | rfl
      · simp [f, hendR.1, hfixEnds.1]
      · simp [f, hendR.2, hfixEnds.2]
    · simp [f, hxR]
  have hgonB : ∀ y ∈ B, g y = h.invFun y := by
    intro y hyB
    by_cases hyR : y ∈ R
    · have hyEnd : y = a ∨ y = b := by
        have : y ∈ ({a, b} : Set Plane) := hRB ▸ ⟨hyR, hyB⟩
        simpa using this
      have hi : h.invFun y = y := by
        rcases hyEnd with ha | hb
        · calc
            h.invFun y = h.invFun a := congrArg h.invFun ha
            _ = h.invFun (h.toFun a) := congrArg h.invFun hfixEnds.1.symm
            _ = a := h.leftInvOn hendA.1
            _ = y := ha.symm
        · calc
            h.invFun y = h.invFun b := congrArg h.invFun hb
            _ = h.invFun (h.toFun b) := congrArg h.invFun hfixEnds.2.symm
            _ = b := h.leftInvOn hendA.2
            _ = y := hb.symm
      simpa [g, hyR] using hi.symm
    · simp [g, hyR]
  have hfR : ContinuousOn f R :=
    (continuous_id.continuousOn).congr (fun x hx => by simp [f, hx])
  have hfA : ContinuousOn f A :=
    h.continuousOn_toFun.congr (fun x hx => hfonA x hx)
  have hgR : ContinuousOn g R :=
    (continuous_id.continuousOn).congr (fun x hx => by simp [g, hx])
  have hgB : ContinuousOn g B :=
    h.continuousOn_invFun.congr (fun x hx => hgonB x hx)
  have hf : ContinuousOn f (R ∪ A) :=
    Plane.continuousOn_union_of_isClosed hR.isArc.isCompact.isClosed
      hA.isArc.isCompact.isClosed hfR hfA
  have hg : ContinuousOn g (R ∪ B) :=
    Plane.continuousOn_union_of_isClosed hR.isArc.isCompact.isClosed
      hB.isArc.isCompact.isClosed hgR hgB
  have hfMaps : MapsTo f (R ∪ A) (R ∪ B) := by
    intro x hx
    rcases hx with hxR | hxA
    · rw [show f x = x by simp [f, hxR]]
      exact Or.inl hxR
    · rw [hfonA x hxA]
      exact Or.inr (h.mapsTo hxA)
  have hgMaps : MapsTo g (R ∪ B) (R ∪ A) := by
    intro y hy
    rcases hy with hyR | hyB
    · rw [show g y = y by simp [g, hyR]]
      exact Or.inl hyR
    · rw [hgonB y hyB]
      exact Or.inr (h.mapsTo_invFun hyB)
  have hleft : ∀ x ∈ R ∪ A, g (f x) = x := by
    intro x hx
    rcases hx with hxR | hxA
    · simp [f, g, hxR]
    · rw [hfonA x hxA, hgonB (h.toFun x) (h.mapsTo hxA)]
      exact h.leftInvOn hxA
  have hright : ∀ y ∈ R ∪ B, f (g y) = y := by
    intro y hy
    rcases hy with hyR | hyB
    · simp [f, g, hyR]
    · rw [hgonB y hyB, hfonA (h.invFun y) (h.mapsTo_invFun hyB)]
      exact h.rightInvOn hyB
  let E : ↥(R ∪ A) ≃ ↥(R ∪ B) := {
    toFun := fun x => ⟨f x, hfMaps x.property⟩
    invFun := fun y => ⟨g y, hgMaps y.property⟩
    left_inv := by intro x; apply Subtype.ext; exact hleft x x.property
    right_inv := by intro y; apply Subtype.ext; exact hright y y.property }
  let e : ↥(R ∪ A) ≃ₜ ↥(R ∪ B) := {
    toEquiv := E
    continuous_toFun := hf.domRestrict.subtype_mk _
    continuous_invFun := hg.domRestrict.subtype_mk _ }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change f x = x
    simp [f, x.property]
  · intro x hxA
    exact hfonA x hxA
  · rw [Set.image_image]
    ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      change f (x : Plane) ∈ B
      rw [hfonA x hxA]
      exact h.mapsTo hxA
    · intro hyB
      have hyImage : y ∈ h.toFun '' A := by rw [h.image_eq]; exact hyB
      obtain ⟨x, hxA, hxy⟩ := hyImage
      exact ⟨⟨x, Or.inr hxA⟩, hxA, (hfonA x hxA).trans hxy⟩

/-- Extend the fixed-arc boundary map across its Jordan subdisk. -/
theorem exists_closed_subdisk_homeomorph_fixing_arc
    {R A B : Set Plane} {a b : Plane}
    (hR : IsArcBetween R a b) (hA : IsArcBetween A a b)
    (hB : IsArcBetween B a b)
    (hRA : R ∩ A = {a, b}) (hRB : R ∩ B = {a, b})
    (h : ArcHomeo A B a b a b) :
    ∃ F G : Plane → Plane,
      IsHomeoOn F G ((R ∪ A) ∪ inside (R ∪ A))
        ((R ∪ B) ∪ inside (R ∪ B)) ∧
      (∀ x ∈ R, F x = x) ∧
      (∀ x ∈ A, F x = h.toFun x) ∧ F '' A = B := by
  have hJA : IsJordanCurve (R ∪ A) := by
    apply IsJordanCurve.of_two_arcs hR hA.reverse
    intro x hxR hxA
    have hx : x ∈ ({a, b} : Set Plane) := hRA ▸ ⟨hxR, hxA⟩
    simpa using hx
  have hJB : IsJordanCurve (R ∪ B) := by
    apply IsJordanCurve.of_two_arcs hR hB.reverse
    intro x hxR hxB
    have hx : x ∈ ({a, b} : Set Plane) := hRB ▸ ⟨hxR, hxB⟩
    simpa using hx
  obtain ⟨e, hfixed, hpoint, harc⟩ :=
    exists_boundary_homeomorph_fixing_arc_of_arcHomeo hR hA hB hRA hRB h
  obtain ⟨f, g, hfg, hf⟩ := exists_isHomeoOn_of_homeomorph e
  obtain ⟨F, G, hFG, hF⟩ :=
    closed_interior_extension squareExtension hJA hJB hfg
  refine ⟨F, G, hFG, ?_, ?_, ?_⟩
  · intro x hxR
    have hxC : x ∈ R ∪ A := Or.inl hxR
    calc
      F x = f x := hF hxC
      _ = (e ⟨x, hxC⟩ : Plane) := hf x hxC
      _ = x := by
        have he := hfixed ⟨x, hxR⟩
        exact congrArg Subtype.val he
  · intro x hxA
    have hxC : x ∈ R ∪ A := Or.inr hxA
    calc
      F x = f x := hF hxC
      _ = (e ⟨x, hxC⟩ : Plane) := hf x hxC
      _ = h.toFun x := hpoint x hxA
  · ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      have hxC : x ∈ R ∪ A := Or.inr hxA
      have hxe : (e ⟨x, hxC⟩ : Plane) ∈ B := by
        have he : (e ⟨x, hxC⟩ : Plane) ∈
            Subtype.val '' (e '' {z : ↥(R ∪ A) | (z : Plane) ∈ A}) :=
          ⟨e ⟨x, hxC⟩, ⟨⟨x, hxC⟩, hxA, rfl⟩, rfl⟩
        simpa only [harc] using he
      simpa [hF hxC, hf x hxC] using hxe
    · intro hyB
      have hyImage : y ∈ Subtype.val ''
          (e '' {z : ↥(R ∪ A) | (z : Plane) ∈ A}) := by
        rw [harc]
        exact hyB
      obtain ⟨z, ⟨x, hxA, hxe⟩, hzy⟩ := hyImage
      refine ⟨x, hxA, ?_⟩
      have hxC : (x : Plane) ∈ R ∪ A := x.property
      calc
        F x = f x := hF hxC
        _ = (e ⟨(x : Plane), hxC⟩ : Plane) := hf x hxC
        _ = (z : Plane) := congrArg Subtype.val hxe
        _ = y := hzy

theorem model_boundary_arc_meet_crosscut
    {R A : Set Plane} {a b : Plane}
    (hR : IsArcBetween R a b) (hRmodel : R ⊆ modelCurve)
    (hA : IsArcBetween A a b)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1) :
    R ∩ A = {a, b} := by
  ext x
  constructor
  · intro hx
    by_contra hxend
    have hxU : x ∈ Plane.openSquare 0 1 := hAi ⟨hx.2, hxend⟩
    have hxC : Plane.supNorm x = 1 := hRmodel hx.1
    have hxLt : Plane.supNorm x < 1 := mem_openSquare_zero_one.mp hxU
    linarith
  · intro hx
    have hxEnd : x = a ∨ x = b := by simpa using hx
    rcases hxEnd with rfl | rfl
    · exact ⟨hR.left_mem, hA.left_mem⟩
    · exact ⟨hR.right_mem, hA.right_mem⟩

/-- The two boundary-fixed Jordan subdisk maps supplied by the approved
crosscut hypotheses. Their compatibility on the crosscut and disk cover are
separate gluing obligations. -/
theorem exists_two_closed_subdisk_maps
    {A B : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
    ∃ R₁ R₂ : Set Plane, ∃ h : ArcHomeo A B a b a b,
      IsCutPair modelCurve a b R₁ R₂ ∧
      (∃ F₁ G₁ : Plane → Plane,
        IsHomeoOn F₁ G₁ ((R₁ ∪ A) ∪ inside (R₁ ∪ A))
          ((R₁ ∪ B) ∪ inside (R₁ ∪ B)) ∧
        (∀ x ∈ R₁, F₁ x = x) ∧
        (∀ x ∈ A, F₁ x = h.toFun x) ∧ F₁ '' A = B) ∧
      (∃ F₂ G₂ : Plane → Plane,
        IsHomeoOn F₂ G₂ ((R₂ ∪ A) ∪ inside (R₂ ∪ A))
          ((R₂ ∪ B) ∪ inside (R₂ ∪ B)) ∧
        (∀ x ∈ R₂, F₂ x = x) ∧
        (∀ x ∈ A, F₂ x = h.toFun x) ∧ F₂ '' A = B) := by
  obtain ⟨h⟩ := exists_arcHomeo hA hB
  obtain ⟨R₁, R₂, hcut⟩ :=
    exists_isCutPair isJordanCurve_modelCurve ha hb hA.ne
  have hR1A := model_boundary_arc_meet_crosscut hcut.fst
    hcut.fst_subset hA hAi
  have hR1B := model_boundary_arc_meet_crosscut hcut.fst
    hcut.fst_subset hB hBi
  have hR2A := model_boundary_arc_meet_crosscut hcut.snd
    hcut.snd_subset hA hAi
  have hR2B := model_boundary_arc_meet_crosscut hcut.snd
    hcut.snd_subset hB hBi
  exact ⟨R₁, R₂, h, hcut,
    exists_closed_subdisk_homeomorph_fixing_arc hcut.fst hA hB hR1A hR1B h,
    exists_closed_subdisk_homeomorph_fixing_arc hcut.snd hA hB hR2A hR2B h⟩

#print axioms exists_boundary_homeomorph_fixing_arc_of_arcHomeo
#print axioms exists_closed_subdisk_homeomorph_fixing_arc
#print axioms exists_two_closed_subdisk_maps

end CurveComplex
