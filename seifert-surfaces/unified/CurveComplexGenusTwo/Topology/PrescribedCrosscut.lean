import CurveComplexGenusTwo.Topology.CrosscutFull

open Set
namespace CurveComplex
open Schoenflies

private theorem prescribed_isClosed_crosscut_subdisk
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


/-- Extend a prescribed endpoint-preserving parametrization of proper square
crosscuts, fixing the exterior of the square. -/
theorem prescribed_relative_crosscut_replacement
    (A B : Set Plane) (a b : Plane)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
    (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1)
    (h : ArcHomeo A B a b a b) :
    ∃ F : Plane ≃ₜ Plane,
      (∀ x ∈ A, F x = h.toFun x) ∧
      F '' A = B ∧
      ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  classical
  obtain ⟨R₁, R₂, hcut⟩ :=
    exists_isCutPair isJordanCurve_modelCurve ha hb hA.ne
  obtain ⟨F₁, G₁, h₁, hF₁fixed, hF₁arc, hF₁image⟩ :=
    exists_closed_subdisk_homeomorph_fixing_arc hcut.fst hA hB
      (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hA hAi)
      (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hB hBi) h
  obtain ⟨F₂, G₂, h₂, hF₂fixed, hF₂arc, hF₂image⟩ :=
    exists_closed_subdisk_homeomorph_fixing_arc hcut.snd hA hB
      (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hA hAi)
      (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hB hBi) h
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
  have hD₁ : IsClosed D₁ := prescribed_isClosed_crosscut_subdisk hcut.fst hA hR₁A
  have hD₂ : IsClosed D₂ := prescribed_isClosed_crosscut_subdisk hcut.snd hA hR₂A
  have hE₁ : IsClosed E₁ := prescribed_isClosed_crosscut_subdisk hcut.fst hB hR₁B
  have hE₂ : IsClosed E₂ := prescribed_isClosed_crosscut_subdisk hcut.snd hB hR₂B
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
  let U : Set Plane := Plane.openSquare 0 1
  have hSU : U ⊆ S := by
    intro x hx
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le
  have hfix : ∀ x : S, (x : Plane) ∉ U → e x = x := by
    intro x hx
    apply hboundary
    rw [modelCurve_eq_frontier, (Plane.isClosed_closedSquare 0 1).frontier_eq,
      interior_closedSquare_zero_one]
    exact ⟨x.property, hx⟩
  let H := extendClosedHomeomorph S U (Plane.isClosed_closedSquare 0 1)
    (Plane.isOpen_openSquare 0 1) hSU e hfix
  have hpoint : ∀ x ∈ A, H x = h.toFun x := by
    intro x hx
    have hxS : x ∈ S := hAclosed hx
    have he : (e ⟨x, hxS⟩ : Plane) = h.toFun x :=
      (hFD₁ x (Or.inl (Or.inr hx))).trans (hF₁arc x hx)
    simpa [H, extendClosedHomeomorph, hxS] using he
  refine ⟨H, hpoint, ?_, ?_⟩
  · exact (show EqOn H h.toFun A from hpoint).image_eq.trans h.image_eq
  · intro x hx
    exact extendClosedHomeomorph_apply_outside S U (Plane.isClosed_closedSquare 0 1)
      (Plane.isOpen_openSquare 0 1) hSU e hfix x hx

end CurveComplex

#print axioms CurveComplex.prescribed_relative_crosscut_replacement
