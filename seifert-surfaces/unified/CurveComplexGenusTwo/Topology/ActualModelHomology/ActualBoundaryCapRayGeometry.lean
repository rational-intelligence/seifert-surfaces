import Mathlib

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def rayA (a : ℝ) (z : ℂ) : ℝ := (z.re-a)^2+z.im^2
noncomputable def rayB (a : ℝ) (z : ℂ) : ℝ := a*(z.re-a)
noncomputable def rayD (a : ℝ) (z : ℂ) : ℝ :=
  (rayB a z)^2 + rayA a z*(1-a^2)
noncomputable def rayScale (a : ℝ) (z : ℂ) : ℝ :=
  (-rayB a z+Real.sqrt (rayD a z))/rayA a z
noncomputable def rayEndpoint (a : ℝ) (z : ℂ) : ℂ :=
  (a : ℂ)+(rayScale a z : ℂ)*(z-(a : ℂ))

theorem rayA_pos (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    0 < rayA a z := by
  have hr : z.re ≤ 1 := by
    simp only [Complex.normSq_apply] at hz
    nlinarith [sq_nonneg z.im]
  have hn : z.re-a < 0 := by linarith
  dsimp [rayA]
  nlinarith [sq_pos_of_neg hn,sq_nonneg z.im]

theorem ray_discriminant_identity (a : ℝ) (z : ℂ) :
    rayD a z-(rayA a z+rayB a z)^2 = rayA a z*(1-Complex.normSq z) := by
  simp only [rayD,rayA,rayB,Complex.normSq_apply]
  ring

theorem rayD_nonneg (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    0 ≤ rayD a z := by
  have hA := rayA_pos a ha z hz
  have hid := ray_discriminant_identity a z
  nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hz),sq_nonneg (rayA a z+rayB a z)]

theorem rayScale_mul (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    rayA a z*rayScale a z = -rayB a z+Real.sqrt (rayD a z) := by
  rw [rayScale,mul_div_cancel₀ _ (rayA_pos a ha z hz).ne']

theorem rayScale_ge_one (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    1 ≤ rayScale a z := by
  have hA := rayA_pos a ha z hz
  have hid := ray_discriminant_identity a z
  have hle : (rayA a z+rayB a z)^2 ≤ rayD a z := by
    nlinarith [mul_nonneg hA.le (sub_nonneg.mpr hz)]
  have hs := Real.le_sqrt_of_sq_le hle
  have hm := rayScale_mul a ha z hz
  nlinarith

theorem rayScale_quadratic (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    rayA a z*(rayScale a z)^2+2*rayB a z*rayScale a z+a^2=1 := by
  have hA := rayA_pos a ha z hz
  have hm := rayScale_mul a ha z hz
  have hs := Real.sq_sqrt (rayD_nonneg a ha z hz)
  have hsq : (rayA a z*rayScale a z+rayB a z)^2 = rayD a z := by
    rw [show rayA a z*rayScale a z+rayB a z = Real.sqrt (rayD a z) by linarith,hs]
  dsimp only [rayD] at hsq
  nlinarith

theorem rayEndpoint_normSq (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1) :
    Complex.normSq (rayEndpoint a z)=1 := by
  have hq := rayScale_quadratic a ha z hz
  simp only [rayA,rayB] at hq
  simp only [Complex.normSq_apply,rayEndpoint,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] 
  nlinarith [hq]

theorem rayScale_fixed (a : ℝ) (ha : 1<a) (z : ℂ)
    (hz : Complex.normSq z=1) (hfar : a*z.re≤1) : rayScale a z=1 := by
  have hA := rayA_pos a ha z hz.le
  have hid := ray_discriminant_identity a z
  have hab : 0≤rayA a z+rayB a z := by
    simp only [rayA,rayB,Complex.normSq_apply] at *
    nlinarith
  have hD : rayD a z=(rayA a z+rayB a z)^2 := by rw [hz] at hid; nlinarith
  rw [rayScale,hD,Real.sqrt_sq hab]
  field_simp [hA.ne']
  ring

theorem rayEndpoint_fixed (a : ℝ) (ha : 1<a) (z : ℂ)
    (hz : Complex.normSq z=1) (hfar : a*z.re≤1) : rayEndpoint a z=z := by
  rw [rayEndpoint,rayScale_fixed a ha z hz hfar]
  simp

theorem rayD_pos (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1)
    (hkeep : Complex.normSq z < 1 ∨ a*z.re<1) : 0 < rayD a z := by
  have hA := rayA_pos a ha z hz
  have hid := ray_discriminant_identity a z
  by_cases hi : Complex.normSq z < 1
  · nlinarith [mul_pos hA (sub_pos.mpr hi),sq_nonneg (rayA a z+rayB a z)]
  · have he : Complex.normSq z=1 := by linarith
    have hf := hkeep.resolve_left hi
    have hab : 0<rayA a z+rayB a z := by
      simp only [rayA,rayB,Complex.normSq_apply] at *
      nlinarith
    rw [he] at hid
    nlinarith [sq_pos_of_pos hab]

theorem rayEndpoint_far (a : ℝ) (ha : 1<a) (z : ℂ) (hz : Complex.normSq z ≤ 1)
    (hkeep : Complex.normSq z < 1 ∨ a*z.re<1) : a*(rayEndpoint a z).re<1 := by
  have hq := rayScale_quadratic a ha z hz
  have hm := rayScale_mul a ha z hz
  have hl := rayScale_ge_one a ha z hz
  have hs : 0<Real.sqrt (rayD a z) := Real.sqrt_pos.mpr (rayD_pos a ha z hz hkeep)
  have hid : 1-a*(rayEndpoint a z).re = rayScale a z*Real.sqrt (rayD a z) := by
    simp only [rayEndpoint,Complex.add_re,Complex.mul_re,Complex.sub_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] 
    have he : Real.sqrt (rayD a z)=rayA a z*rayScale a z+rayB a z := by linarith
    rw [he]
    dsimp only [rayB] at hq ⊢
    nlinarith
  have hpos := mul_pos (show 0<rayScale a z by linarith) hs
  linarith

theorem normSq_convex_combination (t : ℝ) (z w : ℂ) :
    Complex.normSq ((1-t : ℝ) • z+t • w)=
      (1-t)*Complex.normSq z+t*Complex.normSq w-
        t*(1-t)*Complex.normSq (z-w) := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,Complex.sub_re,Complex.sub_im]
  ring

noncomputable def raySegment (a t : ℝ) (z : ℂ) : ℂ :=
  (1-t : ℝ) • z+t • rayEndpoint a z

theorem raySegment_normSq_le (a : ℝ) (ha : 1<a) (z : ℂ)
    (hz : Complex.normSq z ≤ 1) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    Complex.normSq (raySegment a t z) ≤ 1 := by
  rw [raySegment,normSq_convex_combination,rayEndpoint_normSq a ha z hz]
  have hn := Complex.normSq_nonneg (z-rayEndpoint a z)
  have hp := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) hn
  have hweight := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hz)
  nlinarith

theorem raySegment_keep (a : ℝ) (ha : 1<a) (z : ℂ)
    (hz : Complex.normSq z ≤ 1)
    (hkeep : Complex.normSq z<1 ∨ a*z.re<1)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    Complex.normSq (raySegment a t z)<1 ∨ a*(raySegment a t z).re<1 := by
  have hf := rayEndpoint_far a ha z hz hkeep
  by_cases hi : Complex.normSq z<1
  · by_cases he : t=1
    · right
      simpa [raySegment,he] using hf
    · left
      have hlt : t<1 := lt_of_le_of_ne ht1 he
      rw [raySegment,normSq_convex_combination,rayEndpoint_normSq a ha z hz]
      have hn := Complex.normSq_nonneg (z-rayEndpoint a z)
      have hp := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr ht1)) hn
      have hweight := mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hi)
      nlinarith
  · right
    have hfz := hkeep.resolve_left hi
    have hx : (raySegment a t z).re=(1-t)*z.re+t*(rayEndpoint a z).re := by
      simp [raySegment]
    rw [hx]
    have hleft := mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hfz.le)
    have hright := mul_nonneg ht (sub_nonneg.mpr hf.le)
    by_cases he : t=0
    · simpa [he] using hfz
    · have htp : 0<t := lt_of_le_of_ne ht (Ne.symm he)
      have hstrict := mul_pos htp (sub_pos.mpr hf)
      nlinarith

abbrev DeletedCapDisk (a : ℝ) :=
  {z : ℂ // Complex.normSq z ≤ 1 ∧ (Complex.normSq z<1 ∨ a*z.re<1)}

 theorem continuous_rayEndpoint (a : ℝ) (ha : 1<a) :
    Continuous (fun z : DeletedCapDisk a => rayEndpoint a z.val) := by
  have hA : Continuous (fun z : DeletedCapDisk a => rayA a z.val) := by
    unfold rayA
    fun_prop
  have hB : Continuous (fun z : DeletedCapDisk a => rayB a z.val) := by
    unfold rayB
    fun_prop
  have hD : Continuous (fun z : DeletedCapDisk a => rayD a z.val) := by
    unfold rayD
    exact (hB.pow 2).add (hA.mul continuous_const)
  have hs : Continuous (fun z : DeletedCapDisk a => rayScale a z.val) := by
    unfold rayScale
    exact (hB.neg.add (Real.continuous_sqrt.comp hD)).div hA
      (fun z => (rayA_pos a ha z.val z.property.1).ne')
  unfold rayEndpoint
  exact continuous_const.add ((Complex.continuous_ofReal.comp hs).mul
    (continuous_subtype_val.sub continuous_const))

 theorem continuous_raySegment (a : ℝ) (ha : 1<a) :
    Continuous (fun x : unitInterval × DeletedCapDisk a =>
      raySegment a (x.1 : ℝ) x.2.val) := by
  unfold raySegment
  exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
    (continuous_subtype_val.comp continuous_snd) |>.add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((continuous_rayEndpoint a ha).comp continuous_snd))

noncomputable def diskRayRetraction (a : ℝ) (ha : 1<a) :
    C(DeletedCapDisk a, DeletedCapDisk a) where
  toFun z := ⟨rayEndpoint a z.val,
    (rayEndpoint_normSq a ha z.val z.property.1).le,
    Or.inr (rayEndpoint_far a ha z.val z.property.1 z.property.2)⟩
  continuous_toFun := (continuous_rayEndpoint a ha).subtype_mk _

noncomputable def diskRayDeformation (a : ℝ) (ha : 1<a) :
    ContinuousMap.Homotopy (ContinuousMap.id (DeletedCapDisk a))
      (diskRayRetraction a ha) where
  toFun x := ⟨raySegment a (x.1 : ℝ) x.2.val,
    raySegment_normSq_le a ha x.2.val x.2.property.1
      (x.1 : ℝ) x.1.property.1 x.1.property.2,
    raySegment_keep a ha x.2.val x.2.property.1 x.2.property.2
      (x.1 : ℝ) x.1.property.1 x.1.property.2⟩
  continuous_toFun := (continuous_raySegment a ha).subtype_mk _
  map_zero_left z := by
    apply Subtype.ext
    simp [raySegment]
  map_one_left z := by
    apply Subtype.ext
    simp [raySegment,diskRayRetraction]

theorem diskRayDeformation_fixes_boundary (a : ℝ) (ha : 1<a)
    (z : DeletedCapDisk a) (hz : Complex.normSq z.val=1) (t : unitInterval) :
    diskRayDeformation a ha (t,z)=z := by
  apply Subtype.ext
  change raySegment a (t : ℝ) z.val=z.val
  have hf : a*z.val.re<1 := z.property.2.resolve_left (by rw [hz]; exact lt_irrefl _)
  rw [raySegment,rayEndpoint_fixed a ha z.val hz hf.le]
  rw [← add_smul]
  simp

abbrev SurvivingBoundary (a : ℝ) :=
  {z : DeletedCapDisk a // Complex.normSq z.val=1}

noncomputable def boundaryRayRetraction (a : ℝ) (ha : 1<a) :
    C(DeletedCapDisk a,SurvivingBoundary a) where
  toFun z := ⟨diskRayRetraction a ha z,rayEndpoint_normSq a ha z.val z.property.1⟩
  continuous_toFun := (diskRayRetraction a ha).continuous.subtype_mk _

noncomputable def boundaryRayInclusion (a : ℝ) :
    C(SurvivingBoundary a,DeletedCapDisk a) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

noncomputable def deletedCapDiskHomotopyEquivBoundary (a : ℝ) (ha : 1<a) :
    ContinuousMap.HomotopyEquiv (DeletedCapDisk a) (SurvivingBoundary a) where
  toFun := boundaryRayRetraction a ha
  invFun := boundaryRayInclusion a
  left_inv := ⟨(diskRayDeformation a ha).symm⟩
  right_inv := by
    have he : (boundaryRayRetraction a ha).comp (boundaryRayInclusion a)=
        ContinuousMap.id (SurvivingBoundary a) := by
      ext z
      exact rayEndpoint_fixed a ha z.val.val z.property
        ((z.val.property.2.resolve_left (by rw [z.property]; exact lt_irrefl _)).le)
    rw [he]

end CurveComplex.Hyperbolic.OneBoundaryRay
