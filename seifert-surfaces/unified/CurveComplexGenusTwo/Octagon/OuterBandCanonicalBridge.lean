import CurveComplexGenusTwo.Octagon.OpenCoverExactness
import CurveComplexGenusTwo.Octagon.OuterBandAnnulus

namespace CurveComplex.Octagon

/-! A compiler-checked packet exposing the canonical outer-band data in the
form needed by quotient and Mayer--Vietoris clients. -/

theorem canonical_outerBand_packet :
    IsOpen outerBand ∧
      mk ⁻¹' (mk '' outerBand) = outerBand ∧
      Topology.IsQuotientMap ((mk '' outerBand).restrictPreimage mk) ∧
      IsOpen (mk '' diskInterior) ∧
      IsOpen (mk '' outerBand) ∧
      (mk '' diskInterior) ∪ (mk '' outerBand) = Set.univ := by
  rcases octagon_outerBand_open_saturated_quotient with ⟨hop, hsat, hq⟩
  rcases octagon_face_outerBand_cover_exact with ⟨hface, himage, hcover⟩
  exact ⟨hop, hsat, hq, hface, himage, hcover⟩

theorem canonical_outerBand_overlap_packet :
    mk ⁻¹' ((mk '' diskInterior) ∩ (mk '' outerBand)) =
      {x : Disk | (1 / 2 : ℝ) < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < 1} ∧
      diskInterior ∩ outerBand =
      {x : Disk | (1 / 2 : ℝ) < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < 1} := by
  exact ⟨quotient_overlap_preimage_eq_annulus,
    diskInterior_inter_outerBand_eq_annulus⟩

end CurveComplex.Octagon
