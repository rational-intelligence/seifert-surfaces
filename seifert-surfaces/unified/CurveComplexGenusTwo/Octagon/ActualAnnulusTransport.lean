import CurveComplexGenusTwo.CWHurewicz.AnnulusHomotopy
import CurveComplexGenusTwo.Octagon.OuterBandCanonicalBridge
import CurveComplexGenusTwo.Octagon.OctagonChartGlueWave10
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Instances.Complex
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
open Set Topology
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
universe v u
section Homology
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  [CategoryWithHomology C]

-- Private combined proof probe; pending statement review.
private noncomputable def annulusHomologyIsoProbe (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of Annulus) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of MidCircle) := by
  let F := (singularHomologyFunctor C n).obj R
  let r : C(Annulus, MidCircle) := ⟨radial, radial_continuous⟩
  let i : C(MidCircle, Annulus) := ⟨incl, incl_continuous⟩
  have hri : r.comp i = ContinuousMap.id MidCircle := by
    ext z
    exact congrArg Subtype.val (radial_incl z)
  refine ⟨F.map (TopCat.ofHom r), F.map (TopCat.ofHom i), ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      annulusRadialHomotopy.symm R n
  · rw [← F.map_comp, ← F.map_id]
    have H : ContinuousMap.Homotopy (r.comp i) (ContinuousMap.id MidCircle) := by
      rw [hri]
      exact ContinuousMap.Homotopy.refl _
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n

private theorem annulusRadialHomology_isIsoProbe (R : C) (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (⟨radial, radial_continuous⟩ : C(Annulus, MidCircle)))) :=
  (annulusHomologyIsoProbe R n).isIso_hom

private theorem annulusInclHomology_isIsoProbe (R : C) (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj R).map
      (TopCat.ofHom (⟨incl, incl_continuous⟩ : C(MidCircle, Annulus)))) :=
  (annulusHomologyIsoProbe R n).isIso_inv
end Homology

private theorem midCircle_pathConnectedProbe : PathConnectedSpace MidCircle := by
  have h : IsPathConnected (Metric.sphere (0 : ℂ) (3/2 : ℝ)) :=
    isPathConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 (by norm_num)
  have hs : Metric.sphere (0 : ℂ) (3/2 : ℝ) = {z : ℂ | ‖z‖ = (3/2 : ℝ)} := by
    ext z
    simp [Metric.mem_sphere, dist_zero_right]
  rw [hs] at h
  exact isPathConnected_iff_pathConnectedSpace.mp h

section HomologyZero
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  [CategoryWithHomology C]

private noncomputable def midCircleHomologyZeroIsoProbe (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of MidCircle) ≅ R := by
  letI : PathConnectedSpace MidCircle := midCircle_pathConnectedProbe
  exact asIso ((TopCat.of MidCircle).singularHomology₀ε R)

private noncomputable def annulusHomologyZeroIsoProbe (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of Annulus) ≅ R :=
  annulusHomologyIsoProbe R 0 ≪≫ midCircleHomologyZeroIsoProbe R
end HomologyZero

namespace ActualAnnulusTransport
open CurveComplex.Octagon
abbrev ActualAnnulus := {z : ℂ // (1/2 : ℝ) < ‖z‖ ∧ ‖z‖ < 1}
abbrev Overlap := (mk '' diskInterior) ∩ (mk '' outerBand)
def scaleHomeomorph : ActualAnnulus ≃ₜ Annulus where
  toFun z := ⟨(2 : ℝ) • (z : ℂ), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<2)]
    constructor <;> linarith [z.property.1, z.property.2]⟩
  invFun z := ⟨(1/2 : ℝ) • (z : ℂ), by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    constructor <;> linarith [z.property.1, z.property.2]⟩
  left_inv z := by apply Subtype.ext; simp [smul_smul]
  right_inv z := by apply Subtype.ext; simp [smul_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous (fun _ : ActualAnnulus => (2 : ℝ))).smul continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous (fun _ : Annulus => (1/2 : ℝ))).smul continuous_subtype_val

theorem overlap_image : mk '' (diskInterior ∩ outerBand) = Overlap := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x,hx.1,rfl⟩,⟨x,hx.2,rfl⟩⟩
  · rintro ⟨⟨x,hx,rfl⟩,ho⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    have : x ∈ mk ⁻¹' (mk '' outerBand) := ho
    rwa [outerBand_preimage_image] at this

def diskAnnulusHomeomorph : ↥(diskInterior ∩ outerBand) ≃ₜ ActualAnnulus where
  toFun z := ⟨(z.val : ℂ), z.property.2, z.property.1⟩
  invFun z := ⟨⟨z.val, by simpa [Disk, Metric.mem_closedBall, dist_zero_right] using le_of_lt z.property.2⟩, z.property.2, z.property.1⟩
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk (fun z : ActualAnnulus => by simpa [Disk, Metric.mem_closedBall, dist_zero_right] using le_of_lt z.property.2)).subtype_mk _

def overlapHomeomorph : Overlap ≃ₜ ActualAnnulus := by
  have hsat : mk ⁻¹' (mk '' (diskInterior ∩ outerBand)) = diskInterior ∩ outerBand := by
    rw [overlap_image, quotient_overlap_preimage_eq_annulus, diskInterior_inter_outerBand_eq_annulus]
  have hi : Set.InjOn mk (diskInterior ∩ outerBand) :=
    fun _ hx _ hy he => mk_injective_on_diskInterior hx.1 hy.1 he
  exact ((Homeomorph.setCongr overlap_image.symm).trans
    (local_quotient_homeomorph_of_open_saturated_inj
      (diskInterior_isOpen.inter outerBand_isOpen) hsat hi).symm).trans diskAnnulusHomeomorph

def overlapModelHomeomorph : Overlap ≃ₜ Annulus :=
  overlapHomeomorph.trans scaleHomeomorph

def overlapRadial : C(Overlap, MidCircle) :=
  (⟨radial, radial_continuous⟩ : C(Annulus, MidCircle)).comp
    ⟨overlapModelHomeomorph, overlapModelHomeomorph.continuous⟩

def overlapIncl : C(MidCircle, Overlap) :=
  (⟨overlapModelHomeomorph.symm, overlapModelHomeomorph.symm.continuous⟩ : C(Annulus, Overlap)).comp ⟨incl, incl_continuous⟩

theorem overlapRadial_incl : overlapRadial.comp overlapIncl = ContinuousMap.id MidCircle := by
  ext z
  simp [overlapRadial, overlapIncl, radial_incl]

def overlapRadialHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id Overlap) (overlapIncl.comp overlapRadial) := by
  let e := overlapModelHomeomorph
  have H := (ContinuousMap.Homotopy.refl (⟨e.symm, e.symm.continuous⟩ : C(Annulus, Overlap))).comp
    (annulusRadialHomotopy.compContinuousMap (⟨e, e.continuous⟩ : C(Overlap, Annulus)))
  convert H using 1 <;> ext z <;> simp [e, overlapIncl, overlapRadial]

section Homology
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{0} C]
  [CategoryWithHomology C]
noncomputable def overlapHomologyIso (R : C) (n : ℕ) :
    ((singularHomologyFunctor C n).obj R).obj (TopCat.of Overlap) ≅
      ((singularHomologyFunctor C n).obj R).obj (TopCat.of MidCircle) := by
  let F := (singularHomologyFunctor C n).obj R
  refine ⟨F.map (TopCat.ofHom overlapRadial), F.map (TopCat.ofHom overlapIncl), ?_, ?_⟩
  · rw [← F.map_comp, ← F.map_id]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
      overlapRadialHomotopy.symm R n
  · rw [← F.map_comp, ← F.map_id]
    have H : ContinuousMap.Homotopy (overlapRadial.comp overlapIncl) (ContinuousMap.id MidCircle) := by
      rw [overlapRadial_incl]
      exact ContinuousMap.Homotopy.refl _
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor H R n

theorem overlapRadialHomology_isIso (R : C) (n : ℕ) :
    IsIso (((singularHomologyFunctor C n).obj R).map (TopCat.ofHom overlapRadial)) :=
  (overlapHomologyIso R n).isIso_hom
noncomputable def overlapHomologyZeroIso (R : C) :
    ((singularHomologyFunctor C 0).obj R).obj (TopCat.of Overlap) ≅ R :=
  overlapHomologyIso R 0 ≪≫ midCircleHomologyZeroIsoProbe R
end Homology
end ActualAnnulusTransport
