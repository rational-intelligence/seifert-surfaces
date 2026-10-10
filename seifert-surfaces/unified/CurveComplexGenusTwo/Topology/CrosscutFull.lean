import CurveComplexGenusTwo.Topology.CrosscutSupport
import CurveComplexGenusTwo.Topology.CrosscutBoundary
import CurveComplexGenusTwo.Topology.CrosscutGlue
import CurveComplexGenusTwo.Topology.ArcStraightening

open Set

namespace CurveComplex

open Schoenflies

/-- The two Jordan subdisks cut out by an arbitrary proper square crosscut
cover the square and meet precisely on that crosscut. -/
theorem square_crosscut_subdisk_partition
    {P R₁ R₂ : Set Plane} {a b : Plane}
    (hP : IsArcBetween P a b)
    (hcut : IsCutPair modelCurve a b R₁ R₂)
    (hPi : P \ {a, b} ⊆ Plane.openSquare 0 1) :
    (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∪
      ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = Plane.closedSquare 0 1) ∧
    (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∩
      ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = P) := by
  have hPi' : P \ {a, b} ⊆ inside modelCurve := by
    simpa only [inside_modelCurve] using hPi
  have hclass := general_crosscut_arbitrary_of_endpoints
    isJordanCurve_modelCurve hP hcut hPi'
  have hside₁ : inside (R₁ ∪ P) ⊆ inside modelCurve \ P := by
    intro x hx
    rw [hclass.1]
    exact Or.inl hx
  have hside₂ : inside (R₂ ∪ P) ⊆ inside modelCurve \ P := by
    intro x hx
    rw [hclass.1]
    exact Or.inr hx
  have hPclosed : P ⊆ Plane.closedSquare 0 1 :=
    crosscut_subset_closedSquare
      (hcut.fst_subset hcut.fst.left_mem)
      (hcut.fst_subset hcut.fst.right_mem) hPi
  constructor
  · ext x
    constructor
    · intro hx
      have hx' : x ∈ modelCurve ∪ inside modelCurve := by
        rcases hx with ((hR₁ | hP₁) | hi₁) | ((hR₂ | hP₂) | hi₂)
        · exact Or.inl (hcut.fst_subset hR₁)
        · exact (modelCurve_union_inside.symm ▸ hPclosed hP₁)
        · exact Or.inr (hside₁ hi₁).1
        · exact Or.inl (hcut.snd_subset hR₂)
        · exact (modelCurve_union_inside.symm ▸ hPclosed hP₂)
        · exact Or.inr (hside₂ hi₂).1
      exact modelCurve_union_inside ▸ hx'
    · intro hx
      have hx' : x ∈ modelCurve ∪ inside modelCurve :=
        modelCurve_union_inside.symm ▸ hx
      rcases hx' with hxC | hxin
      · have hxb : x ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
        rcases hxb with hR₁ | hR₂
        · exact Or.inl (Or.inl (Or.inl hR₁))
        · exact Or.inr (Or.inl (Or.inl hR₂))
      · by_cases hxP : x ∈ P
        · exact Or.inl (Or.inl (Or.inr hxP))
        · have hinside : x ∈ inside (R₁ ∪ P) ∪ inside (R₂ ∪ P) := by
            rw [← hclass.1]
            exact ⟨hxin, hxP⟩
          rcases hinside with hi₁ | hi₂
          · exact Or.inl (Or.inr hi₁)
          · exact Or.inr (Or.inr hi₂)
  · ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      rcases hx₁ with (hR₁ | hP₁) | hi₁
      · rcases hx₂ with (hR₂ | hP₂) | hi₂
        · have hxEnds : x ∈ ({a, b} : Set Plane) :=
            hcut.inter_eq ▸ ⟨hR₁, hR₂⟩
          rcases (by simpa using hxEnds : x = a ∨ x = b) with rfl | rfl
          · exact hP.left_mem
          · exact hP.right_mem
        · exact hP₂
        · exact False.elim (inside_subset_compl (hside₂ hi₂).1 (hcut.fst_subset hR₁))
      · exact hP₁
      · rcases hx₂ with (hR₂ | hP₂) | hi₂
        · exact False.elim (inside_subset_compl (hside₁ hi₁).1 (hcut.snd_subset hR₂))
        · exact hP₂
        · exact False.elim (Set.disjoint_left.1 hclass.2.1 hi₁ hi₂)
    · intro hxP
      exact ⟨Or.inl (Or.inr hxP), Or.inl (Or.inr hxP)⟩

private theorem isClosed_crosscut_subdisk
    {R P : Set Plane} {a b : Plane}
    (hR : IsArcBetween R a b) (hP : IsArcBetween P a b)
    (hRP : R ∩ P = {a, b}) :
    IsClosed ((R ∪ P) ∪ inside (R ∪ P)) := by
  have hJ : IsJordanCurve (R ∪ P) := by
    apply isJordanCurve_union hR hP
    intro x hxR hxP
    have hx : x ∈ ({a, b} : Set Plane) := hRP ▸ ⟨hxR, hxP⟩
    simpa using hx
  exact isClosed_union_inside (jordan_curve_theorem hJ)

/-- Relative replacement of two proper crosscuts of the same square. -/
theorem position_relative_crosscut_replacement
    (A B : Set Plane) (a b : Plane)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
    ∃ F : Plane ≃ₜ Plane,
      F '' A = B ∧ ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  classical
  obtain ⟨R₁, R₂, h, hcut,
      ⟨F₁, G₁, h₁, hF₁fixed, hF₁arc, hF₁image⟩,
      ⟨F₂, G₂, h₂, hF₂fixed, hF₂arc, hF₂image⟩⟩ :=
    exists_two_closed_subdisk_maps hA hB ha hb hAi hBi
  let D₁ : Set Plane := (R₁ ∪ A) ∪ inside (R₁ ∪ A)
  let D₂ : Set Plane := (R₂ ∪ A) ∪ inside (R₂ ∪ A)
  let E₁ : Set Plane := (R₁ ∪ B) ∪ inside (R₁ ∪ B)
  let E₂ : Set Plane := (R₂ ∪ B) ∪ inside (R₂ ∪ B)
  let S : Set Plane := Plane.closedSquare 0 1
  have hpartA : D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = A :=
    square_crosscut_subdisk_partition hA hcut hAi
  have hpartB : E₁ ∪ E₂ = S ∧ E₁ ∩ E₂ = B :=
    square_crosscut_subdisk_partition hB hcut hBi
  have hR₁A := model_boundary_arc_meet_crosscut hcut.fst
    hcut.fst_subset hA hAi
  have hR₂A := model_boundary_arc_meet_crosscut hcut.snd
    hcut.snd_subset hA hAi
  have hR₁B := model_boundary_arc_meet_crosscut hcut.fst
    hcut.fst_subset hB hBi
  have hR₂B := model_boundary_arc_meet_crosscut hcut.snd
    hcut.snd_subset hB hBi
  have hD₁ : IsClosed D₁ := isClosed_crosscut_subdisk hcut.fst hA hR₁A
  have hD₂ : IsClosed D₂ := isClosed_crosscut_subdisk hcut.snd hA hR₂A
  have hE₁ : IsClosed E₁ := isClosed_crosscut_subdisk hcut.fst hB hR₁B
  have hE₂ : IsClosed E₂ := isClosed_crosscut_subdisk hcut.snd hB hR₂B
  have hagree : ∀ x ∈ D₁ ∩ D₂, F₁ x = F₂ x := by
    intro x hx
    have hxA : x ∈ A := hpartA.2 ▸ hx
    rw [hF₁arc x hxA, hF₂arc x hxA]
  have himageOverlap : F₁ '' (D₁ ∩ D₂) = E₁ ∩ E₂ := by
    rw [hpartA.2, hpartB.2]
    exact hF₁image
  obtain ⟨F, G, hFG, hFD₁, hFD₂⟩ :=
    glue_closed_homeoOn hD₁ hD₂ hE₁ hE₂ h₁ h₂ hagree himageOverlap
  have hFGS : IsHomeoOn F G S S := by
    simpa only [hpartA.1, hpartB.1] using hFG
  let E : S ≃ S := {
    toFun := fun x => ⟨F x, hFGS.mapsTo x.property⟩
    invFun := fun y => ⟨G y, hFGS.mapsTo_inv y.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact hFGS.invOn.1 x.property
    right_inv := by
      intro y
      apply Subtype.ext
      exact hFGS.invOn.2 y.property }
  let e : S ≃ₜ S := {
    toEquiv := E
    continuous_toFun := hFGS.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hFGS.continuousOn_inv.domRestrict.subtype_mk _ }
  have hboundary : ∀ x : S, (x : Plane) ∈ modelCurve → e x = x := by
    intro x hxC
    have hxR : (x : Plane) ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
    apply Subtype.ext
    rcases hxR with hxR₁ | hxR₂
    · exact (hFD₁ x (Or.inl (Or.inl hxR₁))).trans (hF₁fixed x hxR₁)
    · exact (hFD₂ x (Or.inl (Or.inl hxR₂))).trans (hF₂fixed x hxR₂)
  have hFA : F '' A = B := by
    have hEq : EqOn F F₁ A := by
      intro x hxA
      exact hFD₁ x (Or.inl (Or.inr hxA))
    exact hEq.image_eq.trans hF₁image
  have hAclosed : A ⊆ S := crosscut_subset_closedSquare ha hb hAi
  have hBclosed : B ⊆ S := crosscut_subset_closedSquare ha hb hBi
  have heImage : e '' {x : S | (x : Plane) ∈ A} =
      {x : S | (x : Plane) ∈ B} := by
    ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      have hxB : F x ∈ B := by
        rw [← hFA]
        exact ⟨x, hxA, rfl⟩
      exact hxB
    · intro hyB
      have hyImage : (y : Plane) ∈ F '' A := by rw [hFA]; exact hyB
      obtain ⟨x, hxA, hxy⟩ := hyImage
      refine ⟨⟨x, hAclosed hxA⟩, hxA, ?_⟩
      apply Subtype.ext
      exact hxy
  exact crosscut_replacement_of_closedSquare_homeomorph
    hAclosed hBclosed e hboundary heImage

#print axioms square_crosscut_subdisk_partition
#print axioms position_relative_crosscut_replacement

end CurveComplex
