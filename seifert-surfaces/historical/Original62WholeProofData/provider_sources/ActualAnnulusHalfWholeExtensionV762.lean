import ActualPlanarPolarCoordinatesV761

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualAnnulusHalfWholeExtensionV762

abbrev Disk2 := Metric.closedBall (0 : Plane) 2

/-- Fill the inner disk by the identity, and extend the entire prescribed
    annulus half pointwise. The original fixed core is retained as a set of points. -/
theorem annulus_half_whole_extension (q : C(Circle × Time,Plane)) (hq : IsEmbedding q)
    (hq0 : ∀ z,q (z,0) = circleVector z)
    (hqout : ∀ z t,t ≠ 0 → 1 < ‖q (z,t)‖) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ x : Plane,‖x‖ ≤ 1 → H x = x) ∧
      (∀ (z : Circle) (t : Time),H ((1+(t:ℝ)) • circleVector z) = q (z,t)) := by
  classical
  let r : Disk2 → Time := fun x => Set.projIcc 0 1 zero_le_one (‖x.val‖-1)
  have hrc : Continuous r := continuous_projIcc.comp
    (continuous_subtype_val.norm.sub continuous_const)
  have hr (x : Disk2) (hx : 1 ≤ ‖x.val‖) : (r x : ℝ) = ‖x.val‖-1 := by
    have hx2 : ‖x.val‖ ≤ 2 := mem_closedBall_zero_iff.mp x.property
    exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one
      (show ‖x.val‖-1 ∈ Icc (0:ℝ) 1 by constructor <;> linarith))
  have hr0 (x : Disk2) (hx : ‖x.val‖ = 1) : r x = 0 :=
    Subtype.ext (by rw [hr x hx.ge,hx]; norm_num)
  have hrpos (x : Disk2) (hx : 1 < ‖x.val‖) : r x ≠ 0 := by
    intro he
    have hh := congrArg Subtype.val he
    change (r x : ℝ) = 0 at hh
    rw [hr x hx.le] at hh
    linarith
  let f : Disk2 → Plane := fun x => if ‖x.val‖ ≤ 1 then x.val else q (angle x.val,r x)
  have hfinner (x : Disk2) (hx : ‖x.val‖ ≤ 1) : f x = x.val := ite_eq_left hx
  have hfouter (x : Disk2) (hx : 1 < ‖x.val‖) : f x = q (angle x.val,r x) :=
    ite_eq_right (not_le_of_gt hx)
  have hfc : Continuous f := by
    apply continuous_if_le continuous_subtype_val.norm continuous_const
      continuous_subtype_val.continuousOn
    · apply q.continuous.comp_continuousOn
      apply ContinuousOn.prodMk _ hrc.continuousOn
      apply angle_continuousOn.comp continuous_subtype_val.continuousOn
      intro x hx
      change x.val ≠ 0
      intro hz
      have hn : 1 ≤ ‖x.val‖ := hx
      rw [hz,norm_zero] at hn
      norm_num at hn
    · intro x hx
      rw [hr0 x hx,hq0]
      have hx0 : x.val ≠ 0 := by intro hz; rw [hz,norm_zero] at hx; norm_num at hx
      have hp := polar_reconstruction x.val hx0
      rw [hx,one_smul] at hp
      exact hp.symm
  have hfi : Function.Injective f := by
    intro x y he
    by_cases hx : ‖x.val‖ ≤ 1 <;> by_cases hy : ‖y.val‖ ≤ 1
    · apply Subtype.ext
      simpa only [hfinner x hx,hfinner y hy] using he
    · have hy' : 1 < ‖y.val‖ := lt_of_not_ge hy
      rw [hfinner x hx,hfouter y hy'] at he
      have hh := hqout (angle y.val) (r y) (hrpos y hy')
      rw [← he] at hh
      linarith
    · have hx' : 1 < ‖x.val‖ := lt_of_not_ge hx
      rw [hfouter x hx',hfinner y hy] at he
      have hh := hqout (angle x.val) (r x) (hrpos x hx')
      rw [he] at hh
      linarith
    · have hx' : 1 < ‖x.val‖ := lt_of_not_ge hx
      have hy' : 1 < ‖y.val‖ := lt_of_not_ge hy
      rw [hfouter x hx',hfouter y hy'] at he
      have hh := hq.injective he
      have hangle : angle x.val = angle y.val := congrArg Prod.fst hh
      have hrad := congrArg (fun p : Circle × Time => (p.2 : ℝ)) hh
      change (r x : ℝ) = (r y : ℝ) at hrad
      rw [hr x hx'.le,hr y hy'.le] at hrad
      have hn : ‖x.val‖ = ‖y.val‖ := by linarith
      apply Subtype.ext
      rw [← polar_reconstruction x.val (norm_ne_zero_iff.mp (by linarith : ‖x.val‖ ≠ 0)),
        ← polar_reconstruction y.val (norm_ne_zero_iff.mp (by linarith : ‖y.val‖ ≠ 0)),hn,hangle]
  let d : Disk → Disk2 := fun x => ⟨(2:ℝ) • x.val,by
    rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mem_closedBall_zero_iff.mp x.property]⟩
  have hdc : Continuous d := by
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous (fun _ : Disk => (2:ℝ))).smul continuous_subtype_val
  have hdi : Function.Injective d := by
    intro x y he
    apply Subtype.ext
    have hh : (2:ℝ) • x.val = (2:ℝ) • y.val := congrArg Subtype.val he
    have hh' := congrArg (fun z : Plane => (1/2:ℝ) • z) hh
    simpa only [smul_smul,show (1/2:ℝ)*2 = 1 by norm_num,one_smul] using hh'
  let f₁ : C(Disk,Plane) := ⟨f ∘ d,hfc.comp hdc⟩
  have hf₁ : IsEmbedding f₁ := (f₁.continuous.isClosedEmbedding (hfi.comp hdi)).isEmbedding
  obtain ⟨H₁,hH₁⟩ := CompressionActualPlanarWholeEmbeddingExtensionV759.whole_disk_embedding_extension f₁ hf₁
  let H := (Homeomorph.smulOfNeZero (1/2:ℝ) (by norm_num) : Plane ≃ₜ Plane).trans H₁
  have hHf (x : Disk2) : H x = f x := by
    let y : Disk := ⟨(1/2:ℝ) • x.val,by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      nlinarith [mem_closedBall_zero_iff.mp x.property]⟩
    have hd : d y = x := by
      apply Subtype.ext
      change (2:ℝ) • ((1/2:ℝ) • x.val) = x.val
      rw [smul_smul,show (2:ℝ)*(1/2)=1 by norm_num,one_smul]
    change H₁ y = f x
    rw [hH₁]
    change f (d y) = f x
    rw [hd]
  refine ⟨H,?_,?_⟩
  · intro x hx
    let x' : Disk2 := ⟨x,mem_closedBall_zero_iff.mpr (by linarith)⟩
    exact (hHf x').trans (hfinner x' hx)
  · intro z t
    let x : Disk2 := ⟨(1+(t:ℝ)) • circleVector z,by
      rw [mem_closedBall_zero_iff,norm_smul,circleVector_norm,Real.norm_eq_abs,
        abs_of_pos (by linarith [t.property.1] : 0 < 1+(t:ℝ)),mul_one]
      linarith [t.property.2]⟩
    have hn : ‖x.val‖ = 1+(t:ℝ) := by
      rw [norm_smul,circleVector_norm,Real.norm_eq_abs,
        abs_of_pos (by linarith [t.property.1] : 0 < 1+(t:ℝ)),mul_one]
    have hx0 : circleVector z ≠ 0 := by
      intro hz
      have hh := circleVector_norm z
      rw [hz,norm_zero] at hh
      norm_num at hh
    have hangle : angle x.val = z :=
      (angle_positive_smul (1+(t:ℝ)) (by linarith [t.property.1]) _ hx0).trans (angle_circleVector z)
    have hrt : r x = t := Subtype.ext (by rw [hr x (by rw [hn]; linarith [t.property.1]),hn]; ring)
    change H x = q (z,t)
    rw [hHf]
    by_cases ht : t = 0
    · rw [ht,hq0]
      have hx1 : ‖x.val‖ ≤ 1 := by rw [hn,ht]; norm_num
      rw [hfinner x hx1]
      change (1+(t:ℝ)) • circleVector z = circleVector z
      simp [ht]
    · have htpos : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun he => ht (Subtype.ext he.symm))
      rw [hfouter x (by rw [hn]; linarith),hangle,hrt]

end CompressionActualAnnulusHalfWholeExtensionV762
