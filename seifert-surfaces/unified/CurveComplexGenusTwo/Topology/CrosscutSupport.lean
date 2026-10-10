import Schoenflies.ModelCurve

open Set

namespace CurveComplex

/-- Extend a homeomorphism of a closed set by the identity, provided it is
already the identity outside an open subset of that set. -/
noncomputable def extendClosedHomeomorph {X : Type*} [TopologicalSpace X]
    (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hUS : U ⊆ S)
    (e : S ≃ₜ S) (hfix : ∀ x : S, (x : X) ∉ U → e x = x) : X ≃ₜ X := by
  classical
  let f : X → X := fun x => if hx : x ∈ S then (e ⟨x, hx⟩ : X) else x
  let g : X → X := fun x => if hx : x ∈ S then (e.symm ⟨x, hx⟩ : X) else x
  have hfix_symm : ∀ x : S, (x : X) ∉ U → e.symm x = x := by
    intro x hx
    have he : e x = x := hfix x hx
    apply e.injective
    simpa using he.symm
  have hfS : ContinuousOn f S := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : S => f x)
    have he : (fun x : S => f x) = fun x => (e x : X) := by
      funext x
      simp [f, x.property]
    rw [he]
    exact continuous_subtype_val.comp e.continuous
  have hgS : ContinuousOn g S := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : S => g x)
    have he : (fun x : S => g x) = fun x => (e.symm x : X) := by
      funext x
      simp [g, x.property]
    rw [he]
    exact continuous_subtype_val.comp e.symm.continuous
  have hfOutside : ∀ x, x ∉ U → f x = x := by
    intro x hxU
    by_cases hxS : x ∈ S
    · simp [f, hxS, hfix ⟨x, hxS⟩ hxU]
    · simp [f, hxS]
  have hgOutside : ∀ x, x ∉ U → g x = x := by
    intro x hxU
    by_cases hxS : x ∈ S
    · simp [g, hxS, hfix_symm ⟨x, hxS⟩ hxU]
    · simp [g, hxS]
  have hfC : Continuous f := by
    rw [← continuousOn_univ]
    have hcover : S ∪ Uᶜ = (univ : Set X) := by
      ext x
      simp only [mem_union, mem_univ, iff_true]
      by_cases hx : x ∈ U
      · exact Or.inl (hUS hx)
      · exact Or.inr hx
    rw [← hcover]
    apply ContinuousOn.union_of_isClosed hfS _ hS hU.isClosed_compl
    exact (continuous_id.continuousOn).congr (fun x hx => hfOutside x hx)
  have hgC : Continuous g := by
    rw [← continuousOn_univ]
    have hcover : S ∪ Uᶜ = (univ : Set X) := by
      ext x
      simp only [mem_union, mem_univ, iff_true]
      by_cases hx : x ∈ U
      · exact Or.inl (hUS hx)
      · exact Or.inr hx
    rw [← hcover]
    apply ContinuousOn.union_of_isClosed hgS _ hS hU.isClosed_compl
    exact (continuous_id.continuousOn).congr (fun x hx => hgOutside x hx)
  have hleft : Function.LeftInverse g f := by
    intro x
    by_cases hx : x ∈ S
    · simp [f, g, hx]
    · simp [f, g, hx]
  have hright : Function.RightInverse g f := by
    intro x
    by_cases hx : x ∈ S
    · simp [f, g, hx]
    · simp [f, g, hx]
  let E : X ≃ X := { toFun := f, invFun := g, left_inv := hleft, right_inv := hright }
  exact { toEquiv := E, continuous_toFun := hfC, continuous_invFun := hgC }

theorem extendClosedHomeomorph_apply_outside {X : Type*} [TopologicalSpace X]
    (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hUS : U ⊆ S)
    (e : S ≃ₜ S) (hfix : ∀ x : S, (x : X) ∉ U → e x = x)
    (x : X) (hx : x ∉ U) :
    extendClosedHomeomorph S U hS hU hUS e hfix x = x := by
  by_cases hxS : x ∈ S
  · simp [extendClosedHomeomorph, hxS, hfix ⟨x, hxS⟩ hx]
  · simp [extendClosedHomeomorph, hxS]

theorem crosscut_subset_closedSquare
    {A : Set Schoenflies.Plane} {a b : Schoenflies.Plane}
    (ha : a ∈ Schoenflies.modelCurve) (hb : b ∈ Schoenflies.modelCurve)
    (hAi : A \ {a, b} ⊆ Schoenflies.Plane.openSquare 0 1) :
    A ⊆ Schoenflies.Plane.closedSquare 0 1 := by
  intro x hxA
  by_cases hxend : x ∈ ({a, b} : Set Schoenflies.Plane)
  · rcases (Set.mem_insert_iff.mp hxend) with rfl | hxb
    · exact Schoenflies.modelCurve_subset_closedSquare ha
    · have : x = b := Set.mem_singleton_iff.mp hxb
      subst x
      exact Schoenflies.modelCurve_subset_closedSquare hb
  · have hxU : x ∈ Schoenflies.Plane.openSquare 0 1 := hAi ⟨hxA, hxend⟩
    exact Schoenflies.mem_closedSquare_zero_one.mpr
      (Schoenflies.mem_openSquare_zero_one.mp hxU).le

/-- Once the relative disk map is built, extension by identity supplies the
support clause of the crosscut replacement target. -/
theorem crosscut_replacement_of_closedSquare_homeomorph
    {A B : Set Schoenflies.Plane}
    (hA : A ⊆ Schoenflies.Plane.closedSquare 0 1)
    (hB : B ⊆ Schoenflies.Plane.closedSquare 0 1)
    (e : (Schoenflies.Plane.closedSquare 0 1) ≃ₜ
      (Schoenflies.Plane.closedSquare 0 1))
    (hboundary : ∀ x : Schoenflies.Plane.closedSquare 0 1,
      (x : Schoenflies.Plane) ∈ Schoenflies.modelCurve → e x = x)
    (himage : e '' {x : Schoenflies.Plane.closedSquare 0 1 |
      (x : Schoenflies.Plane) ∈ A} =
      {x : Schoenflies.Plane.closedSquare 0 1 |
        (x : Schoenflies.Plane) ∈ B}) :
    ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane,
      F '' A = B ∧
      ∀ x, x ∉ Schoenflies.Plane.openSquare 0 1 → F x = x := by
  let S : Set Schoenflies.Plane := Schoenflies.Plane.closedSquare 0 1
  let U : Set Schoenflies.Plane := Schoenflies.Plane.openSquare 0 1
  have hSU : U ⊆ S := by
    intro x hx
    exact Schoenflies.mem_closedSquare_zero_one.mpr
      (Schoenflies.mem_openSquare_zero_one.mp hx).le
  have hfix : ∀ x : S, (x : Schoenflies.Plane) ∉ U → e x = x := by
    intro x hx
    apply hboundary
    rw [Schoenflies.modelCurve_eq_frontier,
      (Schoenflies.Plane.isClosed_closedSquare 0 1).frontier_eq,
      Schoenflies.interior_closedSquare_zero_one]
    exact ⟨x.property, hx⟩
  let F := extendClosedHomeomorph S U
    (Schoenflies.Plane.isClosed_closedSquare 0 1)
    (Schoenflies.Plane.isOpen_openSquare 0 1) hSU e hfix
  refine ⟨F, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      have hxS : x ∈ S := hA hxA
      have hmem : e ⟨x, hxS⟩ ∈
          {z : S | (z : Schoenflies.Plane) ∈ B} := by
        rw [← himage]
        exact ⟨⟨x, hxS⟩, hxA, rfl⟩
      have hmem' : (e ⟨x, hxS⟩ : Schoenflies.Plane) ∈ B := hmem
      simpa [F, extendClosedHomeomorph, hxS] using hmem'
    · intro hyB
      have hyS : y ∈ S := hB hyB
      have hmem : (⟨y, hyS⟩ : S) ∈
          e '' {z : S | (z : Schoenflies.Plane) ∈ A} := by
        rw [himage]
        exact hyB
      obtain ⟨x, hxA, hxy⟩ := hmem
      refine ⟨x, hxA, ?_⟩
      have hxS : (x : Schoenflies.Plane) ∈ S := x.property
      have hxy' : (e x : Schoenflies.Plane) = y := congrArg Subtype.val hxy
      simpa [F, extendClosedHomeomorph, hxS] using hxy'
  · intro x hx
    exact extendClosedHomeomorph_apply_outside S U
      (Schoenflies.Plane.isClosed_closedSquare 0 1)
      (Schoenflies.Plane.isOpen_openSquare 0 1) hSU e hfix x hx

end CurveComplex

#print axioms CurveComplex.extendClosedHomeomorph_apply_outside
#print axioms CurveComplex.crosscut_replacement_of_closedSquare_homeomorph
