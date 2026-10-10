import CurveComplexGenusTwo.Octagon.OuterBandQuotient

namespace CurveComplex.Octagon

/-- The overlap of the face and outer collar is exactly the radial annulus in the
polygon representative.  This set-level identity is the input for any
Mayer–Vietoris calculation of the collar. -/
theorem diskInterior_inter_outerBand_eq_annulus :
    diskInterior ∩ outerBand =
      {x : Disk | (1 / 2 : ℝ) < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < 1} := by
  ext x
  simp [diskInterior, outerBand, and_comm]

/-- The outer collar is the inverse image of the radial annulus after quotienting. -/
theorem quotient_overlap_preimage_eq_annulus :
    mk ⁻¹' ((mk '' diskInterior) ∩ (mk '' outerBand)) =
      {x : Disk | (1 / 2 : ℝ) < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < 1} := by
  rw [Set.preimage_inter, mk_preimage_image_diskInterior,
    outerBand_preimage_image]
  exact diskInterior_inter_outerBand_eq_annulus

end CurveComplex.Octagon
