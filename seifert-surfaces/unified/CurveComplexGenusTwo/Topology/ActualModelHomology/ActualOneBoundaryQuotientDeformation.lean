import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawDeformation

namespace CurveComplex.Hyperbolic.OneBoundaryRay
open LeanEval.Topology.ClassificationOfSurfaces

noncomputable def rawOpenPreimageHomeomorph (p : ℕ) :
    RawOpenDisk p ≃ₜ {z : Complex.ClosedUnitDisc // Quot.mk (OrientableRel p 1) z ∉
      ActualOneBoundaryOrientableBoundary p} :=
  (Homeomorph.refl Complex.ClosedUnitDisc).subtype (fun z =>
    not_congr (quotient_boundary_preimage p z).symm)

noncomputable def rawQuotientMap (p : ℕ) : C(RawOpenDisk p,ActualOneBoundaryOrientableOpenModel p) where
  toFun z := ⟨Quot.mk (OrientableRel p 1) z.val,fun hc =>
    z.property ((quotient_boundary_preimage p z.val).mp hc)⟩
  continuous_toFun := (continuous_quot_mk.comp continuous_subtype_val).subtype_mk _

theorem rawQuotientMap_isQuotientMap (p : ℕ) : Topology.IsQuotientMap (rawQuotientMap p) := by
  have h := isQuotientMap_quot_mk.restrictPreimage_isOpen (quotient_boundary_isClosed p).isOpen_compl
  exact h.comp (rawOpenPreimageHomeomorph p).isQuotientMap

theorem rel_boundary_norm (p : ℕ) {z w : Complex.ClosedUnitDisc}
    (h : OrientableRel p 1 z w) : ‖(z:ℂ)‖=1 ∧ ‖(w:ℂ)‖=1 := by
  cases h <;> exact ⟨Circle.norm_coe _,Circle.norm_coe _⟩

theorem eqv_eq_or_boundary_norm (p : ℕ) {z w : Complex.ClosedUnitDisc}
    (h : Relation.EqvGen (OrientableRel p 1) z w) :
    z=w ∨ (‖(z:ℂ)‖=1 ∧ ‖(w:ℂ)‖=1) := by
  induction h with
  | rel z w h => exact Or.inr (rel_boundary_norm p h)
  | refl z => exact Or.inl rfl
  | symm z w h ih => exact ih.elim (fun he => Or.inl he.symm) (fun hb => Or.inr hb.symm)
  | trans z w u h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with rfl|⟨hz,hw⟩
    · exact ih₂
    · rcases ih₂ with rfl|⟨hw',hu⟩
      · exact Or.inr ⟨hz,hw⟩
      · exact Or.inr ⟨hz,hu⟩

theorem rawRayDeformation_respects_quotient (p : ℕ) (t : unitInterval)
    {z w : RawOpenDisk p} (h : rawQuotientMap p z=rawQuotientMap p w) :
    rawQuotientMap p (rawRayDeformation p (t,z))=
      rawQuotientMap p (rawRayDeformation p (t,w)) := by
  have hq : Quot.mk (OrientableRel p 1) z.val=Quot.mk (OrientableRel p 1) w.val :=
    congrArg Subtype.val h
  rcases eqv_eq_or_boundary_norm p (Quot.eqvGen_exact hq) with he|⟨hz,hw⟩
  · have he' : z=w := Subtype.ext he
    rw [he']
  · rw [rawRayDeformation_fixes_boundary p z hz,rawRayDeformation_fixes_boundary p w hw]
    exact h

noncomputable def quotientRawRep (p : ℕ) : ActualOneBoundaryOrientableOpenModel p → RawOpenDisk p :=
  Function.surjInv (rawQuotientMap_isQuotientMap p).surjective

@[simp]
theorem quotientRawRep_right_inverse (p : ℕ) (q : ActualOneBoundaryOrientableOpenModel p) :
    rawQuotientMap p (quotientRawRep p q)=q :=
  Function.rightInverse_surjInv (rawQuotientMap_isQuotientMap p).surjective q

noncomputable def quotientRayDeformationFun (p : ℕ)
    (x : unitInterval × ActualOneBoundaryOrientableOpenModel p) :
    ActualOneBoundaryOrientableOpenModel p :=
  rawQuotientMap p (rawRayDeformation p (x.1,quotientRawRep p x.2))

theorem quotientRayDeformationFun_rep (p : ℕ) (t : unitInterval) (z : RawOpenDisk p) :
    quotientRayDeformationFun p (t,rawQuotientMap p z)=
      rawQuotientMap p (rawRayDeformation p (t,z)) := by
  apply rawRayDeformation_respects_quotient
  exact quotientRawRep_right_inverse p (rawQuotientMap p z)

theorem continuous_quotientRayDeformationFun (p : ℕ) : Continuous (quotientRayDeformationFun p) := by
  apply (rawQuotientMap_isQuotientMap p).continuous_lift_prod_right
  convert (rawQuotientMap p).continuous.comp (rawRayDeformation p).continuous using 1
  funext x
  exact quotientRayDeformationFun_rep p x.1 x.2

noncomputable def quotientRayRetraction (p : ℕ) :
    C(ActualOneBoundaryOrientableOpenModel p,ActualOneBoundaryOrientableOpenModel p) where
  toFun q := quotientRayDeformationFun p (1,q)
  continuous_toFun := (continuous_quotientRayDeformationFun p).comp
    (continuous_const.prodMk continuous_id)

noncomputable def quotientRayDeformation (p : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (ActualOneBoundaryOrientableOpenModel p))
      (quotientRayRetraction p) where
  toFun := quotientRayDeformationFun p
  continuous_toFun := continuous_quotientRayDeformationFun p
  map_zero_left q := by
    change rawQuotientMap p (rawRayDeformation p (0,quotientRawRep p q))=q
    exact (congrArg (rawQuotientMap p) ((rawRayDeformation p).map_zero_left
      (quotientRawRep p q))).trans (quotientRawRep_right_inverse p q)
  map_one_left q := rfl

theorem quotientRayDeformation_fixes_boundary (p : ℕ) (z : RawOpenDisk p)
    (hz : ‖(z.val:ℂ)‖=1) (t : unitInterval) :
    quotientRayDeformation p (t,rawQuotientMap p z)=rawQuotientMap p z := by
  change quotientRayDeformationFun p (t,rawQuotientMap p z)=_
  rw [quotientRayDeformationFun_rep,rawRayDeformation_fixes_boundary p z hz]

theorem rawRayRetraction_norm (p : ℕ) (z : RawOpenDisk p) :
    ‖((rawRayRetraction p z).val:ℂ)‖=1 := by
  change ‖((rotatedToRaw p ((diskRayRetraction (modelRayOrigin p)
    (modelRayOrigin_gt_one p)) (rawToRotated p z))).val:ℂ)‖=1
  rw [rotatedToRaw_val,inv_rotation_norm]
  change ‖rayEndpoint (modelRayOrigin p) (rawToRotated p z).val‖=1
  have hs := rayEndpoint_normSq (modelRayOrigin p) (modelRayOrigin_gt_one p)
    (rawToRotated p z).val (rawToRotated p z).property.1
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (rayEndpoint (modelRayOrigin p) (rawToRotated p z).val)]

noncomputable def actualSurvivingBoundary (p : ℕ) : Set (ActualOneBoundaryOrientableOpenModel p) :=
  Set.range (fun z : {z : RawOpenDisk p // ‖(z.val:ℂ)‖=1} => rawQuotientMap p z.val)

theorem quotientRayRetraction_mem_survivingBoundary (p : ℕ)
    (q : ActualOneBoundaryOrientableOpenModel p) :
    quotientRayRetraction p q ∈ actualSurvivingBoundary p := by
  refine ⟨⟨rawRayRetraction p (quotientRawRep p q),rawRayRetraction_norm p _⟩,?_⟩
  change rawQuotientMap p (rawRayRetraction p (quotientRawRep p q))=
    rawQuotientMap p (rawRayDeformation p (1,quotientRawRep p q))
  exact congrArg (rawQuotientMap p) ((rawRayDeformation p).map_one_left _).symm

noncomputable def actualBoundaryRayRetraction (p : ℕ) :
    C(ActualOneBoundaryOrientableOpenModel p,actualSurvivingBoundary p) where
  toFun q := ⟨quotientRayRetraction p q,quotientRayRetraction_mem_survivingBoundary p q⟩
  continuous_toFun := (quotientRayRetraction p).continuous.subtype_mk _

noncomputable def actualBoundaryInclusion (p : ℕ) :
    C(actualSurvivingBoundary p,ActualOneBoundaryOrientableOpenModel p) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

noncomputable def actualModelHomotopyEquivSurvivingBoundary (p : ℕ) :
    ContinuousMap.HomotopyEquiv (ActualOneBoundaryOrientableOpenModel p) (actualSurvivingBoundary p) where
  toFun := actualBoundaryRayRetraction p
  invFun := actualBoundaryInclusion p
  left_inv := ⟨(quotientRayDeformation p).symm⟩
  right_inv := by
    have he : (actualBoundaryRayRetraction p).comp (actualBoundaryInclusion p)=
        ContinuousMap.id (actualSurvivingBoundary p) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      obtain ⟨z,hz⟩ := q.property
      change quotientRayRetraction p q.val=q.val
      rw [← hz]
      exact quotientRayDeformation_fixes_boundary p z.val z.property 1
    rw [he]

end CurveComplex.Hyperbolic.OneBoundaryRay
