import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Topology.Instances.Complex
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
open Set Topology
noncomputable section
abbrev Annulus := {z : ℂ // 1 < ‖z‖ ∧ ‖z‖ < 2}
abbrev MidCircle := {z : ℂ // ‖z‖ = (3/2 : ℝ)}
def radial (z : Annulus) : MidCircle :=
  ⟨((3/2 : ℝ) / ‖(z : ℂ)‖) • (z : ℂ), by
    have hp : 0 < ‖(z : ℂ)‖ := lt_trans zero_lt_one z.property.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hp)]
    exact div_mul_cancel₀ _ (ne_of_gt hp)
  ⟩
def incl (z : MidCircle) : Annulus :=
  ⟨(z : ℂ), by
    constructor
    · rw [z.property]
      norm_num
    · rw [z.property]
      norm_num
  ⟩
lemma radial_continuous : Continuous radial := by
  apply Continuous.subtype_mk
  have hn : Continuous fun z : Annulus => ‖(z : ℂ)‖ :=
    continuous_norm.comp continuous_subtype_val
  have hn0 : ∀ z : Annulus, ‖(z : ℂ)‖ ≠ 0 :=
    fun z => ne_of_gt (lt_trans (by norm_num) z.property.1)
  exact (continuous_const.div₀ hn hn0).smul continuous_subtype_val
lemma incl_continuous : Continuous incl := by
  exact continuous_subtype_val.subtype_mk _
lemma radial_incl : ∀ z : MidCircle, radial (incl z) = z := by
  intro z
  apply Subtype.ext
  dsimp [radial, incl]
  rw [z.property]
  norm_num

-- Candidate scratch construction, pending statement review.
def radialScale (t : unitInterval) (z : Annulus) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * ((3/2 : ℝ) / ‖(z : ℂ)‖)

lemma radialScale_pos (t : unitInterval) (z : Annulus) : 0 < radialScale t z := by
  have hn : 0 < ‖(z : ℂ)‖ := lt_trans zero_lt_one z.property.1
  have hq : 0 < (3/2 : ℝ) / ‖(z : ℂ)‖ := div_pos (by norm_num) hn
  have ht0 := t.property.1
  have ht1 := t.property.2
  dsimp [radialScale]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hm := mul_pos (lt_of_le_of_ne ht0 (Ne.symm h)) hq
    linarith

lemma radialScale_norm (t : unitInterval) (z : Annulus) :
    ‖radialScale t z • (z : ℂ)‖ = (1 - (t : ℝ)) * ‖(z : ℂ)‖ + (t : ℝ) * (3/2 : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radialScale_pos t z)]
  dsimp [radialScale]
  have hn : ‖(z : ℂ)‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one z.property.1)
  field_simp
  <;> ring

lemma radialScale_mem (t : unitInterval) (z : Annulus) :
    1 < ‖radialScale t z • (z : ℂ)‖ ∧ ‖radialScale t z • (z : ℂ)‖ < 2 := by
  rw [radialScale_norm]
  have ht0 := t.property.1
  have ht1 := t.property.2
  have hz1 := z.property.1
  have hz2 := z.property.2
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (sub_pos.mpr hz1)),
    mul_nonneg (sub_nonneg.mpr ht1) (le_of_lt (sub_pos.mpr hz2))]

def radialDeform (p : unitInterval × Annulus) : Annulus :=
  ⟨radialScale p.1 p.2 • (p.2 : ℂ), radialScale_mem p.1 p.2⟩

lemma radialDeform_continuous : Continuous radialDeform := by
  apply Continuous.subtype_mk
  have ht : Continuous fun p : unitInterval × Annulus => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : unitInterval × Annulus => (p.2 : ℂ) :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (continuous_const.div₀ hz.norm
    (fun p => ne_of_gt (lt_trans zero_lt_one p.2.property.1))))).smul hz

def annulusRadialHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id Annulus)
      ((⟨incl, incl_continuous⟩ : C(MidCircle, Annulus)).comp ⟨radial, radial_continuous⟩) where
  toFun := radialDeform
  continuous_toFun := radialDeform_continuous
  map_zero_left := by
    intro z
    apply Subtype.ext
    simp [radialDeform, radialScale]
  map_one_left := by
    intro z
    apply Subtype.ext
    simp [radialDeform, radialScale, radial, incl]

lemma radialDeform_fixed (t : unitInterval) (z : MidCircle) :
    radialDeform (t, incl z) = incl z := by
  apply Subtype.ext
  simp [radialDeform, radialScale, incl, z.property]

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
