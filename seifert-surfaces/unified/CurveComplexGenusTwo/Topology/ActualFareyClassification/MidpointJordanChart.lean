import CurveComplexGenusTwo.Topology.ActualFareyClassification.MidpointSquareBoundary

open Set Topology Schoenflies

theorem jordan_pair_has_midpoint_square_chart
    {A P : Set Plane} {a b : Plane}
    (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
    (hmeet : A ∩ P = {a, b})
    (hJ : IsJordanCurve (A ∪ P)) :
    ∃ F : Plane ≃ₜ Plane, F '' P = {z : Plane | z∈modelCurve ∧ z 1≤0} ∧
      F a = (Plane.mk 1 0) ∧ F b = (Plane.mk (-1) 0) ∧
      F '' (A ∪ P) = modelCurve := by
  let B : Set Plane := {z : Plane | z∈modelCurve ∧ 0≤z 1}
  let Q : Set Plane := {z : Plane | z∈modelCurve ∧ z 1≤0}
  have hB : IsArcBetween B (Plane.mk 1 0) (Plane.mk (-1) 0) := square_boundary_upper_midpoint_arc
  obtain ⟨hQ,hmeetTarget,hModel⟩ := square_boundary_midpoint_arc_pair
  obtain ⟨e, hArcImage, hleft, hright⟩ :=
    exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
  let eModel : ↥(A ∪ P) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hModel)
  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve eModel
  have hImage : F '' P = Q := by
    ext y
    constructor
    · rintro ⟨x, hxP, rfl⟩
      have hxJ : x ∈ A ∪ P := Or.inr hxP
      have hxArc : (e ⟨x, hxJ⟩ : Plane) ∈ Q := by
        have hmem : (e ⟨x, hxJ⟩ : ↥(B ∪ Q)) ∈ e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P} :=
          ⟨⟨x, hxJ⟩, hxP, rfl⟩
        have hval : (e ⟨x, hxJ⟩ : Plane) ∈ Subtype.val ''
            (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := Set.mem_image_of_mem _ hmem
        rw [hArcImage] at hval
        exact hval
      have hfx : F x = (eModel ⟨x, hxJ⟩ : Plane) := hF ⟨x, hxJ⟩
      have hEmodel : (eModel ⟨x, hxJ⟩ : Plane) = (e ⟨x, hxJ⟩ : Plane) := by rfl
      rw [hfx, hEmodel]
      simpa [Q] using hxArc
    · intro hy
      have hyQ : y ∈ Q := by simpa [Q] using hy
      have hyImage : y ∈ Subtype.val ''
          (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := by rw [hArcImage]; exact hyQ
      obtain ⟨z, hzImage, hzy⟩ := hyImage
      obtain ⟨x, hxP, hzx⟩ := hzImage
      have hxJ : (x : Plane) ∈ A ∪ P := x.property
      refine ⟨(x : Plane), hxP, ?_⟩
      have hFz : F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) :=
        hF ⟨(x : Plane), hxJ⟩
      have hEmodel : (eModel ⟨(x : Plane), hxJ⟩ : Plane) =
          (e ⟨(x : Plane), hxJ⟩ : Plane) := rfl
      have hzx' : (e ⟨(x : Plane), hxJ⟩ : Plane) = (z : Plane) :=
        congrArg Subtype.val hzx
      calc
        F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) := hFz
        _ = (e ⟨(x : Plane), hxJ⟩ : Plane) := hEmodel
        _ = (z : Plane) := hzx'
        _ = y := hzy
  have hFa : F a = (Plane.mk 1 0) := by
    let x : ↥(A ∪ P) := ⟨a, Or.inl hA.left_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = (Plane.mk 1 0) := by
      have h := congrArg Subtype.val hleft
      exact h
    calc
      F a = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = (Plane.mk 1 0) := hxe
  have hFb : F b = (Plane.mk (-1) 0) := by
    let x : ↥(A ∪ P) := ⟨b, Or.inl hA.right_mem⟩
    have hxF : F (x : Plane) = (eModel x : Plane) := hF x
    have hxE : (eModel x : Plane) = (e x : Plane) := rfl
    have hxe : (e x : Plane) = (Plane.mk (-1) 0) := by
      have h := congrArg Subtype.val hright
      exact h
    calc
      F b = F (x : Plane) := rfl
      _ = (eModel x : Plane) := hxF
      _ = (e x : Plane) := hxE
      _ = (Plane.mk (-1) 0) := hxe
  have hwhole : F '' (A ∪ P) = modelCurve := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hF ⟨x, hx⟩]
      exact (eModel ⟨x, hx⟩).property
    · intro hy
      obtain ⟨x, hx⟩ := eModel.surjective ⟨y, hy⟩
      refine ⟨x.val, x.property, ?_⟩
      rw [hF x]
      exact congrArg Subtype.val hx
  exact ⟨F, hImage, hFa, hFb, hwhole⟩

#print axioms jordan_pair_has_midpoint_square_chart
