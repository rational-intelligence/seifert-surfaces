import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryQuotientDeformation

namespace CurveComplex.Hyperbolic.OneBoundaryRay

abbrev RawSurvivingBoundary (p : ℕ) := {z : RawOpenDisk p // ‖(z.val:ℂ)‖=1}

noncomputable def rawBoundaryRetraction (p : ℕ) : C(RawOpenDisk p,RawSurvivingBoundary p) where
  toFun z := ⟨rawRayRetraction p z,rawRayRetraction_norm p z⟩
  continuous_toFun := (rawRayRetraction p).continuous.subtype_mk _

noncomputable def rawBoundaryInclusion (p : ℕ) : C(RawSurvivingBoundary p,RawOpenDisk p) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

noncomputable def survivingBoundaryQuotientMap (p : ℕ) :
    C(RawSurvivingBoundary p,actualSurvivingBoundary p) where
  toFun z := ⟨rawQuotientMap p z.val,⟨z,rfl⟩⟩
  continuous_toFun := ((rawQuotientMap p).continuous.comp continuous_subtype_val).subtype_mk _

theorem actualBoundaryRetraction_right_inverse (p : ℕ) (z : actualSurvivingBoundary p) :
    actualBoundaryRayRetraction p (actualBoundaryInclusion p z)=z := by
  apply Subtype.ext
  obtain ⟨w,hw⟩ := z.property
  change quotientRayRetraction p z.val=z.val
  rw [← hw]
  exact quotientRayDeformation_fixes_boundary p w.val w.property 1

theorem actualBoundaryRayRetraction_isQuotientMap (p : ℕ) :
    Topology.IsQuotientMap (actualBoundaryRayRetraction p) := by
  apply Topology.IsQuotientMap.of_comp (actualBoundaryInclusion p).continuous
    (actualBoundaryRayRetraction p).continuous
  have he : (fun z : actualSurvivingBoundary p =>
    actualBoundaryRayRetraction p (actualBoundaryInclusion p z))=id := by
    funext z
    exact actualBoundaryRetraction_right_inverse p z
  change Topology.IsQuotientMap (fun z : actualSurvivingBoundary p =>
    actualBoundaryRayRetraction p (actualBoundaryInclusion p z))
  rw [he]
  exact Topology.IsQuotientMap.id

theorem survivingBoundaryQuotientMap_retraction_square (p : ℕ) (z : RawOpenDisk p) :
    survivingBoundaryQuotientMap p (rawBoundaryRetraction p z)=
      actualBoundaryRayRetraction p (rawQuotientMap p z) := by
  apply Subtype.ext
  change rawQuotientMap p (rawRayRetraction p z)=
    quotientRayDeformationFun p (1,rawQuotientMap p z)
  rw [quotientRayDeformationFun_rep]
  exact congrArg (rawQuotientMap p) ((rawRayDeformation p).map_one_left z).symm

theorem survivingBoundaryQuotientMap_isQuotientMap (p : ℕ) :
    Topology.IsQuotientMap (survivingBoundaryQuotientMap p) := by
  apply Topology.IsQuotientMap.of_comp (rawBoundaryRetraction p).continuous
    (survivingBoundaryQuotientMap p).continuous
  have he : (fun z : RawOpenDisk p => survivingBoundaryQuotientMap p (rawBoundaryRetraction p z))=
      fun z => actualBoundaryRayRetraction p (rawQuotientMap p z) := by
    funext z
    exact survivingBoundaryQuotientMap_retraction_square p z
  change Topology.IsQuotientMap (fun z : RawOpenDisk p =>
    survivingBoundaryQuotientMap p (rawBoundaryRetraction p z))
  rw [he]
  exact (actualBoundaryRayRetraction_isQuotientMap p).comp (rawQuotientMap_isQuotientMap p)

end CurveComplex.Hyperbolic.OneBoundaryRay
