import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Contractible

noncomputable section
open Set
namespace CircleCoverGeometry

/-- Circle with the east endpoint deleted. -/
def eastArc : Set Circle := {1}ᶜ
/-- Circle with the west endpoint deleted. -/
def westArc : Set Circle := {-1}ᶜ
/-- Strict upper semicircle, with both real endpoints removed. -/
def upperArc : Set Circle := {z | 0 < (z : ℂ).im}
/-- Strict lower semicircle, with both real endpoints removed. -/
def lowerArc : Set Circle := {z | (z : ℂ).im < 0}

theorem eastArc_open : IsOpen eastArc := isOpen_compl_singleton
theorem westArc_open : IsOpen westArc := isOpen_compl_singleton
theorem arcs_cover : eastArc ∪ westArc = Set.univ := by
  ext z
  simp only [eastArc, westArc, Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  by_cases h : z = 1
  · right
    subst z
    intro h
    have := congrArg (fun w : Circle => (w : ℂ).re) h
    norm_num at this
  · exact Or.inl h
theorem upperArc_open : IsOpen upperArc :=
  isOpen_lt continuous_const (Complex.continuous_im.comp continuous_subtype_val)
theorem lowerArc_open : IsOpen lowerArc :=
  isOpen_lt (Complex.continuous_im.comp continuous_subtype_val) continuous_const
theorem intersection_split : eastArc ∩ westArc = upperArc ∪ lowerArc := by
  ext z
  change (z ≠ 1 ∧ z ≠ -1) ↔ 0 < (z : ℂ).im ∨ (z : ℂ).im < 0
  constructor
  · intro h
    by_contra hn
    have hi : (z : ℂ).im = 0 := by rcases not_or.mp hn with ⟨h₁, h₂⟩; linarith
    have hs := Circle.normSq_coe z
    rw [Complex.normSq_apply, hi] at hs
    have hr : (z : ℂ).re = 1 ∨ (z : ℂ).re = -1 := by
      have : ((z : ℂ).re - 1) * ((z : ℂ).re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
    rcases hr with hr | hr
    · exact h.1 (Subtype.ext (Complex.ext (by simpa using hr) (by simpa using hi)))
    · exact h.2 (Subtype.ext (Complex.ext (by simpa using hr) (by simpa using hi)))
  · intro h
    constructor <;> intro he <;> subst z <;> simpa using h
theorem components_disjoint : Disjoint upperArc lowerArc := by
  apply Set.disjoint_left.mpr
  intro z hu hl
  exact (lt_asymm (show 0 < (z : ℂ).im from hu) (show (z : ℂ).im < 0 from hl))


private abbrev ImagAxis := (ℝ ∙ (1 : ℂ))ᗮ

private def imagAxisHomeomorph : ImagAxis ≃ₜ ℝ where
  toFun z := (z : ℂ).im
  invFun t := ⟨t * Complex.I, by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    simp [Complex.inner]⟩
  left_inv z := by
    apply Subtype.ext
    have hz := z.property
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hz
    simp [Complex.inner] at hz
    apply Complex.ext <;> simp [hz]
  right_inv t := by simp
  continuous_toFun := Complex.continuous_im.comp continuous_subtype_val
  continuous_invFun := by fun_prop

private def eastStereo : OpenPartialHomeomorph Circle ImagAxis :=
  stereographic (v := (1 : ℂ)) (by simp)

def eastArcHomeomorph : eastArc ≃ₜ ℝ :=
  eastStereo.toHomeomorphSourceTarget.trans
    ((Homeomorph.Set.univ ImagAxis).trans imagAxisHomeomorph)
private def westToEast : westArc ≃ₜ eastArc where
  toFun z := ⟨-z.val, by
    change -z.val ≠ 1
    intro h
    apply z.property
    have := congrArg Neg.neg h
    simpa using this⟩
  invFun z := ⟨-z.val, by
    change -z.val ≠ -1
    intro h
    apply z.property
    exact neg_injective h⟩
  left_inv z := by ext; simp
  right_inv z := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def westArcHomeomorph : westArc ≃ₜ ℝ := westToEast.trans eastArcHomeomorph

private theorem east_inverse_im (t : ℝ) :
    ((eastArcHomeomorph.symm t).val : ℂ).im = (t ^ 2 + 4)⁻¹ * (4 * t) := by
  simp only [eastArcHomeomorph, Homeomorph.trans_apply,
    Homeomorph.symm_trans_apply]
  change (stereoInvFunAux (1 : ℂ) (↑t * Complex.I)).im = _
  simp only [stereoInvFunAux, Complex.smul_im, Complex.add_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_im,
    mul_zero, zero_add, mul_one, add_zero, norm_mul, Complex.norm_I, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, smul_eq_mul, mul_zero, add_zero]

private theorem east_im_pos_iff (z : eastArc) :
    0 < (z.val : ℂ).im ↔ 0 < eastArcHomeomorph z := by
  have h := east_inverse_im (eastArcHomeomorph z)
  rw [eastArcHomeomorph.symm_apply_apply] at h
  rw [h]
  have hp : 0 < (eastArcHomeomorph z ^ 2 + 4)⁻¹ := inv_pos.mpr (by positivity)
  simpa using (mul_pos_iff_of_pos_left hp :
    0 < (eastArcHomeomorph z ^ 2 + 4)⁻¹ * (4 * eastArcHomeomorph z) ↔
      0 < 4 * eastArcHomeomorph z)

private theorem east_im_neg_iff (z : eastArc) :
    (z.val : ℂ).im < 0 ↔ eastArcHomeomorph z < 0 := by
  have h := east_inverse_im (eastArcHomeomorph z)
  rw [eastArcHomeomorph.symm_apply_apply] at h
  rw [h]
  have hp : 0 < (eastArcHomeomorph z ^ 2 + 4)⁻¹ := inv_pos.mpr (by positivity)
  rw [mul_neg_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · linarith
    · exact (lt_asymm hp h).elim
  · intro h
    exact Or.inl ⟨hp, by linarith⟩

private def subsetLiftHomeomorph {s t : Set Circle} (h : s ⊆ t) :
    s ≃ₜ {z : t // z.val ∈ s} where
  toFun z := ⟨⟨z.val, h z.property⟩, z.property⟩
  invFun z := ⟨z.val.val, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem upper_subset_east : upperArc ⊆ eastArc := by
  intro z hz he
  have hz' : 0 < (z : ℂ).im := hz
  have he' : z = 1 := he
  subst z
  simpa using hz'

private theorem lower_subset_east : lowerArc ⊆ eastArc := by
  intro z hz he
  have hz' : (z : ℂ).im < 0 := hz
  have he' : z = 1 := he
  subst z
  simpa using hz'

def upperArcHomeomorph : upperArc ≃ₜ Set.Ioi (0 : ℝ) :=
  (subsetLiftHomeomorph upper_subset_east).trans
    (eastArcHomeomorph.subtype east_im_pos_iff)
def lowerArcHomeomorph : lowerArc ≃ₜ Set.Iio (0 : ℝ) :=
  (subsetLiftHomeomorph lower_subset_east).trans
    (eastArcHomeomorph.subtype east_im_neg_iff)

theorem eastArc_contractible : ContractibleSpace eastArc :=
  eastArcHomeomorph.contractibleSpace
theorem westArc_contractible : ContractibleSpace westArc :=
  westArcHomeomorph.contractibleSpace
theorem upperArc_contractible : ContractibleSpace upperArc := by
  letI : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
  exact upperArcHomeomorph.contractibleSpace
theorem lowerArc_contractible : ContractibleSpace lowerArc := by
  letI : ContractibleSpace (Set.Iio (0 : ℝ)) :=
    (convex_Iio (0 : ℝ)).contractibleSpace ⟨-1, by norm_num⟩
  exact lowerArcHomeomorph.contractibleSpace

private def componentInclusion : upperArc ⊕ lowerArc → Circle :=
  Sum.elim Subtype.val Subtype.val

private theorem componentInclusion_injective : Function.Injective componentInclusion := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (Subtype.ext h)
    | inr y =>
      have hy := y.property
      change x.val = y.val at h
      rw [← h] at hy
      exact (Set.disjoint_left.mp components_disjoint x.property hy).elim
  | inr x =>
    cases y with
    | inl y =>
      have hy := y.property
      change x.val = y.val at h
      rw [← h] at hy
      exact (Set.disjoint_left.mp components_disjoint hy x.property).elim
    | inr y => exact congrArg Sum.inr (Subtype.ext h)

private theorem componentInclusion_openEmbedding :
    Topology.IsOpenEmbedding componentInclusion :=
  upperArc_open.isOpenEmbedding_subtypeVal.sumElim
    lowerArc_open.isOpenEmbedding_subtypeVal componentInclusion_injective

private theorem componentInclusion_range :
    Set.range componentInclusion = eastArc ∩ westArc := by
  rw [intersection_split]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl x => exact Or.inl x.property
    | inr x => exact Or.inr x.property
  · rintro (h | h)
    · exact ⟨Sum.inl ⟨z, h⟩, rfl⟩
    · exact ⟨Sum.inr ⟨z, h⟩, rfl⟩

/-- The overlap is exactly two nonempty contractible components. -/
def intersectionHomeomorph : (eastArc ∩ westArc : Set Circle) ≃ₜ
    (upperArc ⊕ lowerArc) :=
  (componentInclusion_openEmbedding.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr componentInclusion_range)).symm

end CircleCoverGeometry
