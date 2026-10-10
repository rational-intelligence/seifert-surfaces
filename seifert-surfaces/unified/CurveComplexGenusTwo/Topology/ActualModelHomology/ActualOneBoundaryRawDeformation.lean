import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawCap

namespace CurveComplex.Hyperbolic.OneBoundaryRay

abbrev RawOpenDisk (p : ℕ) := {z : Complex.ClosedUnitDisc // z ∉ rawDeletedArc p}

theorem disc_norm_le (z : Complex.ClosedUnitDisc) : ‖(z:ℂ)‖≤1 := by
  simpa only [Metric.mem_closedBall,dist_zero_right] using z.property

theorem disc_normSq_le (z : Complex.ClosedUnitDisc) : Complex.normSq (z:ℂ)≤1 := by
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [disc_norm_le z,norm_nonneg (z:ℂ)]

theorem rotation_normSq (p : ℕ) (z : ℂ) :
    Complex.normSq (modelRotation p*z)=Complex.normSq z := by
  rw [Complex.normSq_mul,Complex.normSq_eq_norm_sq (modelRotation p),modelRotation_norm]
  simp

theorem raw_rotated_keep (p : ℕ) (z : RawOpenDisk p) :
    Complex.normSq (modelRotation p*(z.val:ℂ))<1 ∨
      modelRayOrigin p*(modelRotation p*(z.val:ℂ)).re<1 := by
  rw [rotation_normSq]
  by_cases hi : Complex.normSq (z.val:ℂ)<1
  · exact Or.inl hi
  · right
    have hs : Complex.normSq (z.val:ℂ)=1 := by linarith [disc_normSq_le z.val]
    have hn : ‖(z.val:ℂ)‖=1 := by
      rw [Complex.normSq_eq_norm_sq] at hs
      nlinarith [norm_nonneg (z.val:ℂ)]
    by_contra hf
    exact z.property ((rawDeletedArc_iff_visible_cap p z.val).mpr ⟨hn,le_of_not_gt hf⟩)

noncomputable def rawToRotated (p : ℕ) : C(RawOpenDisk p,DeletedCapDisk (modelRayOrigin p)) where
  toFun z := ⟨modelRotation p*(z.val:ℂ),by
    rw [rotation_normSq]
    exact disc_normSq_le z.val,raw_rotated_keep p z⟩
  continuous_toFun := (continuous_const.mul
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

theorem inv_rotation_norm (p : ℕ) (z : ℂ) :
    ‖(modelRotation p)⁻¹*z‖=‖z‖ := by
  rw [norm_mul,norm_inv,modelRotation_norm,inv_one,one_mul]

theorem rotated_to_raw_keep (p : ℕ) (z : DeletedCapDisk (modelRayOrigin p)) :
    ∃ w : RawOpenDisk p, (w.val:ℂ)=(modelRotation p)⁻¹*z.val := by
  have hn : ‖z.val‖≤1 := by
    have hs := z.property.1
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg z.val]
  let w : Complex.ClosedUnitDisc := ⟨(modelRotation p)⁻¹*z.val,by
    simpa only [Metric.mem_closedBall,dist_zero_right,inv_rotation_norm] using hn⟩
  have hk : w ∉ rawDeletedArc p := by
    intro hc
    obtain ⟨hw,hcap⟩ := (rawDeletedArc_iff_visible_cap p w).mp hc
    have hrot : modelRotation p*(w:ℂ)=z.val := by
      dsimp [w]
      rw [← mul_assoc,mul_inv_cancel₀ (modelRotation_ne_zero p),one_mul]
    rw [hrot] at hcap
    have hnorm : ‖z.val‖=1 := by
      simpa only [w,inv_rotation_norm] using hw
    have hsq : Complex.normSq z.val=1 := by rw [Complex.normSq_eq_norm_sq,hnorm]; norm_num
    rcases z.property.2 with hi|hf
    · linarith
    · linarith
  exact ⟨⟨w,hk⟩,rfl⟩

noncomputable def rotatedToRaw (p : ℕ) : C(DeletedCapDisk (modelRayOrigin p),RawOpenDisk p) where
  toFun z := Classical.choose (rotated_to_raw_keep p z)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have he : (fun z : DeletedCapDisk (modelRayOrigin p) =>
      ((Classical.choose (rotated_to_raw_keep p z)).val:ℂ))=
        fun z => (modelRotation p)⁻¹*z.val := by
      funext z
      exact Classical.choose_spec (rotated_to_raw_keep p z)
    convert (continuous_const.mul continuous_subtype_val :
      Continuous (fun z : DeletedCapDisk (modelRayOrigin p) => (modelRotation p)⁻¹*z.val)) using 1
    funext z
    exact Classical.choose_spec (rotated_to_raw_keep p z)

@[simp]
theorem rotatedToRaw_val (p : ℕ) (z : DeletedCapDisk (modelRayOrigin p)) :
    ((rotatedToRaw p z).val:ℂ)=(modelRotation p)⁻¹*z.val :=
  Classical.choose_spec (rotated_to_raw_keep p z)

noncomputable def rawRotationHomeomorph (p : ℕ) :
    RawOpenDisk p ≃ₜ DeletedCapDisk (modelRayOrigin p) where
  toFun := rawToRotated p
  invFun := rotatedToRaw p
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    rw [rotatedToRaw_val]
    change (modelRotation p)⁻¹*(modelRotation p*(z.val:ℂ))=(z.val:ℂ)
    rw [← mul_assoc,inv_mul_cancel₀ (modelRotation_ne_zero p),one_mul]
  right_inv z := by
    apply Subtype.ext
    change modelRotation p*((rotatedToRaw p z).val:ℂ)=z.val
    rw [rotatedToRaw_val,← mul_assoc,mul_inv_cancel₀ (modelRotation_ne_zero p),one_mul]
  continuous_toFun := (rawToRotated p).continuous
  continuous_invFun := (rotatedToRaw p).continuous

noncomputable def rawRayRetraction (p : ℕ) : C(RawOpenDisk p,RawOpenDisk p) :=
  (rotatedToRaw p).comp ((diskRayRetraction (modelRayOrigin p) (modelRayOrigin_gt_one p)).comp
    (rawToRotated p))

noncomputable def rawRayDeformation (p : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (RawOpenDisk p)) (rawRayRetraction p) where
  toFun x := rotatedToRaw p (diskRayDeformation (modelRayOrigin p) (modelRayOrigin_gt_one p)
    (x.1,rawToRotated p x.2))
  continuous_toFun := (rotatedToRaw p).continuous.comp
    ((diskRayDeformation (modelRayOrigin p) (modelRayOrigin_gt_one p)).continuous.comp
      (continuous_fst.prodMk ((rawToRotated p).continuous.comp continuous_snd)))
  map_zero_left z := by
    change rotatedToRaw p (diskRayDeformation _ _ (0,rawToRotated p z))=z
    exact (congrArg (rotatedToRaw p)
      ((diskRayDeformation (modelRayOrigin p) (modelRayOrigin_gt_one p)).map_zero_left
        (rawToRotated p z))).trans ((rawRotationHomeomorph p).left_inv z)
  map_one_left z := by
    change rotatedToRaw p (diskRayDeformation _ _ (1,rawToRotated p z))=rawRayRetraction p z
    exact congrArg (rotatedToRaw p)
      ((diskRayDeformation (modelRayOrigin p) (modelRayOrigin_gt_one p)).map_one_left
        (rawToRotated p z))

theorem rawRayDeformation_fixes_boundary (p : ℕ) (z : RawOpenDisk p)
    (hz : ‖(z.val:ℂ)‖=1) (t : unitInterval) : rawRayDeformation p (t,z)=z := by
  have hs : Complex.normSq (rawToRotated p z).val=1 := by
    change Complex.normSq (modelRotation p*(z.val:ℂ))=1
    rw [rotation_normSq,Complex.normSq_eq_norm_sq,hz]
    norm_num
  change rotatedToRaw p (diskRayDeformation _ _ (t,rawToRotated p z))=z
  rw [diskRayDeformation_fixes_boundary _ _ _ hs]
  exact (rawRotationHomeomorph p).left_inv z

end CurveComplex.Hyperbolic.OneBoundaryRay
