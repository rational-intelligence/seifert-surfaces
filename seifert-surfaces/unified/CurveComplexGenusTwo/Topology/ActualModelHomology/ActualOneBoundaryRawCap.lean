import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualBoundaryCapConverse
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryDeletedArcGeometry

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def rawDeletedArc (p : ℕ) : Set Complex.ClosedUnitDisc :=
  Set.range (fun t : unitInterval => Complex.ClosedUnitDisc.bdyPtOfReal
    (-(1+(t:ℝ))/modelSideCount p))

theorem modelRotation_norm (p : ℕ) : ‖modelRotation p‖=1 := by
  exact Circle.norm_coe _

theorem modelRotation_ne_zero (p : ℕ) : modelRotation p≠0 := by
  intro h
  have hn := modelRotation_norm p
  rw [h,norm_zero] at hn
  norm_num at hn

theorem rawDeletedArc_iff_visible_cap (p : ℕ) (z : Complex.ClosedUnitDisc) :
    z ∈ rawDeletedArc p ↔ ‖(z:ℂ)‖=1 ∧
      1 ≤ modelRayOrigin p*(modelRotation p*(z:ℂ)).re := by
  constructor
  · rintro ⟨t,rfl⟩
    refine ⟨?_,deleted_arc_lies_in_visible_cap p (t:ℝ) t.property.1 t.property.2⟩
    exact Circle.norm_coe _
  · rintro ⟨hz,hcap⟩
    have hw : ‖modelRotation p*(z:ℂ)‖=1 := by rw [norm_mul,modelRotation_norm,hz,one_mul]
    have hc : Real.cos (modelCapAngle p)≤(modelRotation p*(z:ℂ)).re := by
      unfold modelRayOrigin at hcap
      rw [one_div_mul_eq_div] at hcap
      simpa using (le_div_iff₀ (modelCapCos_pos p)).mp hcap
    obtain ⟨t,ht⟩ := visible_cap_parameter (modelCapAngle p) (modelCapAngle_pos p)
      (by linarith [modelCapAngle_lt_half_pi p,Real.pi_pos])
      (modelRotation p*(z:ℂ)) hw hc
    refine ⟨t,?_⟩
    apply Subtype.ext
    apply mul_left_cancel₀ (modelRotation_ne_zero p)
    rw [rotated_deleted_arc_value]
    exact ht.symm

theorem cos_lt_of_between_cap_angles (θ x : ℝ) (hθ : 0≤θ)
    (hlo : θ<x) (hhi : x<2*Real.pi-θ) : Real.cos x<Real.cos θ := by
  by_cases hx : x≤Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ hx hlo
  · have h : 2*Real.pi-x≤Real.pi := by linarith
    have hh : θ<2*Real.pi-x := by linarith
    have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hθ h hh
    simpa only [Real.cos_two_pi_sub] using hc

theorem rawDeletedArc_boundary_iff (p : ℕ) (r : ℝ) :
    Complex.ClosedUnitDisc.bdyPtOfReal r ∈ rawDeletedArc p ↔
      Real.cos (modelCapAngle p)≤Real.cos (2*Real.pi*(3/(2*modelSideCount p)+r)) := by
  rw [rawDeletedArc_iff_visible_cap,rotated_boundary_real]
  have hn : ‖(Complex.ClosedUnitDisc.bdyPtOfReal r : ℂ)‖=1 := Circle.norm_coe _
  simp only [hn,true_and]
  unfold modelRayOrigin
  rw [one_div_mul_eq_div,le_div_iff₀ (modelCapCos_pos p)]
  simp

theorem modelCapAngle_mul_count (p : ℕ) : modelCapAngle p*modelSideCount p=Real.pi := by
  exact div_mul_cancel₀ _ (modelSideCount_pos p).ne'

theorem rawDeletedArc_scaled_boundary_iff (p : ℕ) (s : ℝ) :
    Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∈ rawDeletedArc p ↔
      Real.cos (modelCapAngle p)≤Real.cos ((3+2*s)*modelCapAngle p) := by
  rw [rawDeletedArc_boundary_iff]
  have he : 2*Real.pi*(3/(2*modelSideCount p)+s/modelSideCount p)=
      (3+2*s)*modelCapAngle p := by
    unfold modelCapAngle
    field_simp [(modelSideCount_pos p).ne']
  rw [he]

theorem handle_boundary_not_mem_rawDeletedArc (p : ℕ) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 4*(p:ℝ)) :
    Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∉ rawDeletedArc p := by
  rw [rawDeletedArc_scaled_boundary_iff]
  have ht := modelCapAngle_pos p
  have hm := modelCapAngle_mul_count p
  unfold modelSideCount at hm
  have hlo : modelCapAngle p<(3+2*s)*modelCapAngle p := by
    nlinarith [mul_nonneg hs0 ht.le]
  have hhi : (3+2*s)*modelCapAngle p<2*Real.pi-modelCapAngle p := by
    have hb := mul_le_mul_of_nonneg_right hs1 ht.le
    nlinarith
  exact not_le.mpr (cos_lt_of_between_cap_angles _ _ ht.le hlo hhi)

theorem seam_cap_cos_iff (p : ℕ) (x : ℝ) (hx0 : 0≤x) (hx1 : x≤1) :
    Real.cos (modelCapAngle p)≤Real.cos ((3-2*x)*modelCapAngle p) ↔ x=1 := by
  have ht := modelCapAngle_pos p
  have hm := modelCapAngle_mul_count p
  unfold modelSideCount at hm
  have hN : (0:ℝ)≤p := by positivity
  have htop : (3-2*x)*modelCapAngle p≤Real.pi := by
    nlinarith [mul_nonneg hx0 ht.le,mul_nonneg hN ht.le]
  constructor
  · intro hc
    by_contra he
    have hx : x<1 := lt_of_le_of_ne hx1 he
    have hangle : modelCapAngle p<(3-2*x)*modelCapAngle p := by
      nlinarith [mul_pos (sub_pos.mpr hx) ht]
    have hc' := Real.cos_lt_cos_of_nonneg_of_le_pi ht.le htop hangle
    linarith
  · rintro rfl
    norm_num

theorem rawDeletedArc_rel_invariant (p : ℕ) {z w : Complex.ClosedUnitDisc}
    (h : LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1 z w) :
    z ∈ rawDeletedArc p ↔ w ∈ rawDeletedArc p := by
  cases h with
  | a x i =>
    simp only [Nat.cast_one,mul_one]
    have hi : (i:ℝ)+1≤(p:ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hx0 := x.property.1
    have hx1 := x.property.2
    have hn : 0≤(i:ℝ) := by positivity
    have hl := handle_boundary_not_mem_rawDeletedArc p (4*(i:ℝ)+(x:ℝ))
      (by positivity) (by nlinarith)
    have hr := handle_boundary_not_mem_rawDeletedArc p (4*(i:ℝ)+3-(x:ℝ))
      (by nlinarith) (by nlinarith)
    change Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+(x:ℝ))/modelSideCount p) ∈ rawDeletedArc p ↔
      Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+3-(x:ℝ))/modelSideCount p) ∈ rawDeletedArc p
    exact iff_of_false hl hr
  | b x i =>
    simp only [Nat.cast_one,mul_one]
    have hi : (i:ℝ)+1≤(p:ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hx0 := x.property.1
    have hx1 := x.property.2
    have hn : 0≤(i:ℝ) := by positivity
    have hl := handle_boundary_not_mem_rawDeletedArc p (4*(i:ℝ)+1+(x:ℝ))
      (by positivity) (by nlinarith)
    have hr := handle_boundary_not_mem_rawDeletedArc p (4*(i:ℝ)+4-(x:ℝ))
      (by nlinarith) (by nlinarith)
    change Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+1+(x:ℝ))/modelSideCount p) ∈ rawDeletedArc p ↔
      Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+4-(x:ℝ))/modelSideCount p) ∈ rawDeletedArc p
    exact iff_of_false hl hr
  | c x i =>
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simp only [Fin.val_zero,Nat.cast_zero,Nat.cast_one,mul_one,mul_zero,zero_add]
    change Complex.ClosedUnitDisc.bdyPtOfReal (-((x:ℝ))/modelSideCount p) ∈ rawDeletedArc p ↔
      Complex.ClosedUnitDisc.bdyPtOfReal (- (3-(x:ℝ))/modelSideCount p) ∈ rawDeletedArc p
    rw [rawDeletedArc_scaled_boundary_iff,rawDeletedArc_scaled_boundary_iff]
    have hleft : 3+2*(-(x:ℝ))=3-2*(x:ℝ) := by ring
    have hright : (3+2*(-(3-(x:ℝ))))*modelCapAngle p= -((3-2*(x:ℝ))*modelCapAngle p) := by ring
    rw [hleft,hright,Real.cos_neg]

theorem rawDeletedArc_eqv_invariant (p : ℕ) {z w : Complex.ClosedUnitDisc}
    (h : Relation.EqvGen (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) z w) :
    z ∈ rawDeletedArc p ↔ w ∈ rawDeletedArc p := by
  induction h with
  | rel z w h => exact rawDeletedArc_rel_invariant p h
  | refl z => rfl
  | symm z w h ih => exact ih.symm
  | trans z w u h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem quotient_boundary_preimage (p : ℕ) (z : Complex.ClosedUnitDisc) :
    Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) z ∈
      ActualOneBoundaryOrientableBoundary p ↔ z ∈ rawDeletedArc p := by
  constructor
  · rintro ⟨t,ht⟩
    have hr := rawDeletedArc_eqv_invariant p (Quot.eqvGen_exact ht)
    exact hr.mp ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨t,rfl⟩

theorem rawDeletedArc_isClosed (p : ℕ) : IsClosed (rawDeletedArc p) := by
  have he : rawDeletedArc p={z : Complex.ClosedUnitDisc | ‖(z:ℂ)‖=1} ∩
      {z : Complex.ClosedUnitDisc | 1 ≤ modelRayOrigin p*(modelRotation p*(z:ℂ)).re} := by
    ext z
    exact rawDeletedArc_iff_visible_cap p z
  rw [he]
  apply IsClosed.inter
  · exact isClosed_eq continuous_subtype_val.norm continuous_const
  · apply isClosed_le continuous_const
    fun_prop

theorem quotient_boundary_isClosed (p : ℕ) : IsClosed (ActualOneBoundaryOrientableBoundary p) := by
  apply (isQuotientMap_quot_mk.isClosed_preimage).mp
  change IsClosed {z : Complex.ClosedUnitDisc | Quot.mk
    (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) z ∈
      ActualOneBoundaryOrientableBoundary p}
  convert rawDeletedArc_isClosed p using 1
  ext z
  exact quotient_boundary_preimage p z

end CurveComplex.Hyperbolic.OneBoundaryRay
