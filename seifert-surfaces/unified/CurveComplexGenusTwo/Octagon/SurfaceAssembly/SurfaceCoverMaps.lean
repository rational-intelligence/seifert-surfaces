import CurveComplexGenusTwo.Octagon.OuterBandCanonicalBridge
import Mathlib.Topology.Category.TopCat.Basic

namespace CurveComplex.Octagon

abbrev faceSet : Set Surface := mk '' diskInterior
abbrev bandSet : Set Surface := mk '' outerBand
abbrev overlapSet : Set Surface := faceSet ∩ bandSet
abbrev radialAnnulusSet : Set Disk :=
  {x : Disk | (1 / 2 : ℝ) < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < 1}

/-- The annulus coordinates used by the separate radial deformation packet. -/
abbrev scaledAnnulus := {z : ℂ // 1 < ‖z‖ ∧ ‖z‖ < 2}

noncomputable def faceCoordinates : diskInterior ≃ₜ faceSet :=
  interior_local_quotient_homeomorph

def faceToSurface : C(faceSet, Surface) := ⟨Subtype.val, continuous_subtype_val⟩
def bandToSurface : C(bandSet, Surface) := ⟨Subtype.val, continuous_subtype_val⟩
def overlapToSurface : C(overlapSet, Surface) := ⟨Subtype.val, continuous_subtype_val⟩

/-- Actual quotient map on annulus representatives, with codomain restricted to the overlap. -/
def annulusToOverlap : C(radialAnnulusSet, overlapSet) :=
  ⟨fun x => ⟨mk x.val, ⟨⟨x.val, x.property.2, rfl⟩, ⟨x.val, x.property.1, rfl⟩⟩⟩,
    (continuous_mk.comp continuous_subtype_val).subtype_mk _⟩

/-- The overlap-to-face map is the literal subtype inclusion. -/
def overlapToFace : C(overlapSet, faceSet) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The overlap-to-band map is the literal subtype inclusion. -/
def overlapToBand : C(overlapSet, bandSet) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Inclusion of radial annulus representatives in the interior of the disk. -/
def annulusToInterior : C(radialAnnulusSet, diskInterior) :=
  ⟨fun x => ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- Restriction of the quotient map to outer-band representatives. -/
def outerBandToBand : C(outerBand, bandSet) :=
  ⟨fun x => ⟨mk x.val, ⟨x.val, x.property, rfl⟩⟩,
    (continuous_mk.comp continuous_subtype_val).subtype_mk _⟩

/-- Literal inclusion of annulus representatives in the outer band. -/
def annulusToOuterBand : C(radialAnnulusSet, outerBand) :=
  ⟨fun x => ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩

theorem annulusToOverlap_val (x : radialAnnulusSet) :
    (annulusToOverlap x).val = mk x.val := by rfl

theorem overlapToFace_val (x : overlapSet) : (overlapToFace x).val = x.val := by rfl

theorem overlapToBand_val (x : overlapSet) : (overlapToBand x).val = x.val := by rfl

/-- No boundary identifications occur in this annulus. -/
noncomputable def annulusOverlapHomeomorph : radialAnnulusSet ≃ₜ overlapSet := by
  have himage : mk '' radialAnnulusSet = overlapSet := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2, rfl⟩, ⟨x, hx.1, rfl⟩⟩
    · rintro ⟨⟨x, hx, rfl⟩, ho⟩
      have hb : x ∈ outerBand := by
        rw [← outerBand_preimage_image]
        exact ho
      exact ⟨x, ⟨hb, hx⟩, rfl⟩
  have hsat : mk ⁻¹' (mk '' radialAnnulusSet) = radialAnnulusSet := by
    rw [himage]
    exact quotient_overlap_preimage_eq_annulus
  have hopen : IsOpen radialAnnulusSet := by
    rw [show radialAnnulusSet = diskInterior ∩ outerBand from diskInterior_inter_outerBand_eq_annulus.symm]
    exact diskInterior_isOpen.inter outerBand_isOpen
  exact (local_quotient_homeomorph_of_open_saturated_inj hopen hsat
    (fun _ hx _ hy he => mk_injective_on_diskInterior hx.2 hy.2 he)).trans
    (Homeomorph.setCongr himage)

theorem annulusOverlapHomeomorph_apply (x : radialAnnulusSet) :
    annulusOverlapHomeomorph x = annulusToOverlap x := by rfl

/-- Scaling by two identifies the octagon annulus with the radial-deformation model. -/
noncomputable def annulusScaleHomeomorph : radialAnnulusSet ≃ₜ scaledAnnulus where
  toFun x := ⟨(2 : ℂ) * (x.val : ℂ), by
    rw [norm_mul]
    norm_num
    constructor <;> linarith [x.property.1, x.property.2]⟩
  invFun z := ⟨⟨z.val / 2, by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_div]
    norm_num
    linarith [z.property.2]⟩, by
    change (1 / 2 : ℝ) < ‖z.val / 2‖ ∧ ‖z.val / 2‖ < 1
    rw [norm_div]
    norm_num
    constructor <;> linarith [z.property.1, z.property.2]⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.mul (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const _

theorem annulusScaleHomeomorph_val (x : radialAnnulusSet) :
    (annulusScaleHomeomorph x).val = (2 : ℂ) * (x.val : ℂ) := by rfl

/-- The quotient annulus inherits the coordinates of the radial-deformation model. -/
noncomputable def overlapAnnulusCoordinates : overlapSet ≃ₜ scaledAnnulus :=
  annulusOverlapHomeomorph.symm.trans annulusScaleHomeomorph

theorem overlap_face_ambient :
    faceToSurface.comp overlapToFace = overlapToSurface := by rfl

theorem overlap_band_ambient :
    bandToSurface.comp overlapToBand = overlapToSurface := by rfl

/-- Commuting face square needed to identify the first Mayer--Vietoris map. -/
theorem annulus_face_naturality :
    overlapToFace.comp annulusToOverlap =
      (⟨faceCoordinates, faceCoordinates.continuous⟩ : C(diskInterior, faceSet)).comp annulusToInterior := by rfl

/-- Commuting collar square needed to identify the second Mayer--Vietoris map. -/
theorem annulus_band_naturality :
    overlapToBand.comp annulusToOverlap =
      outerBandToBand.comp annulusToOuterBand := by rfl

end CurveComplex.Octagon
