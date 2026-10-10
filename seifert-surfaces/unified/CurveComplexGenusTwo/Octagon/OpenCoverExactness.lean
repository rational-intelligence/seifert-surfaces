import CurveComplexGenusTwo.Octagon.OctagonChartGlueWave10

namespace CurveComplex.Octagon

/-- The face and outer collar are an actual open cover of the quotient. -/
theorem octagon_face_outerBand_cover_exact :
    IsOpen (mk '' diskInterior) ∧ IsOpen (mk '' outerBand) ∧
      (mk '' diskInterior) ∪ (mk '' outerBand) = Set.univ := by
  refine ⟨mk_image_diskInterior_isOpen, outerBand_image_isOpen, ?_⟩
  apply Set.eq_univ_of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
    by_cases hx : x ∈ diskInterior
    · exact Or.inl ⟨x, hx, rfl⟩
    · apply Or.inr
      refine ⟨x, ?_, rfl⟩
      change (1 / 2 : ℝ) < ‖(x : ℂ)‖
      have hnorm : 1 ≤ ‖(x : ℂ)‖ := by
        exact le_of_not_gt hx
      linarith

end CurveComplex.Octagon
