import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleEdges
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawInteriorFibers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingArcNormalization
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
theorem source_surviving_raw_circle_interval_homeomorphism (p : ℕ) :
    ∃ T : Ioo (-1:ℝ) (4*(p:ℝ)+1) ≃ₜ RawSurvivingBoundary p,
      ∀ s, (T s).val.val=rawBoundaryPoint p s.val := by
  classical
  have hRawArc (p : ℕ) (a b : ℝ) (hab : b-a < modelSideCount p)
      (hcap : ∀ s ∈ Ioo a b, Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∉ rawDeletedArc p) :
      ∃ q : C(Ioo a b,RawSurvivingBoundary p), IsOpenEmbedding q ∧
        ∀ s, q s=⟨⟨Complex.ClosedUnitDisc.bdyPtOfReal (s.val/modelSideCount p),hcap s s.property⟩,
          Circle.norm_coe _⟩ := by
    classical
    let d : C(Circle,Complex.ClosedUnitDisc) := {
      toFun := fun w => ⟨w.val,by simp⟩
      continuous_toFun := by fun_prop
    }
    let W : Set Circle := {w | d w ∉ rawDeletedArc p}
    have hWO : IsOpen W := (rawDeletedArc_isClosed p).isOpen_compl.preimage d.continuous
    let T : W ≃ₜ RawSurvivingBoundary p := {
      toFun := fun w => ⟨⟨d w.val,w.property⟩,Circle.norm_coe w.val⟩
      invFun := fun z => ⟨⟨z.val.val.val,by change z.val.val.val ∈ Metric.sphere (0:ℂ) 1; exact mem_sphere_zero_iff_norm.mpr z.property⟩,z.val.property⟩
      left_inv := by intro w; rfl
      right_inv := by intro z; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop
    }
    let k : ℝ := 2*Real.pi/modelSideCount p
    have hk : 0 < k := div_pos (by positivity) (modelSideCount_pos p)
    let f : C(Ioo a b,Circle) := ⟨fun s => Circle.exp (k*s.val),by fun_prop⟩
    have hfO : IsOpenMap f := by
      exact isLocalHomeomorph_circleExp.isOpenMap.comp
        ((Homeomorph.mulLeft₀ k hk.ne').isOpenMap.comp isOpen_Ioo.isOpenEmbedding_subtypeVal.isOpenMap)
    have hwidth : k*b-k*a < 2*Real.pi := by
      have hm := mul_lt_mul_of_pos_left hab hk
      have hc : k*modelSideCount p=2*Real.pi := div_mul_cancel₀ _ (modelSideCount_pos p).ne'
      nlinarith
    have hfI : Function.Injective f := by
      intro s t hst
      have he := Circle.exp_injOn_Icc hwidth
        ⟨mul_le_mul_of_nonneg_left s.property.1.le hk.le,mul_le_mul_of_nonneg_left s.property.2.le hk.le⟩
        ⟨mul_le_mul_of_nonneg_left t.property.1.le hk.le,mul_le_mul_of_nonneg_left t.property.2.le hk.le⟩ hst
      apply Subtype.ext
      exact mul_left_cancel₀ hk.ne' he
    have hfE : IsOpenEmbedding f :=
      IsOpenEmbedding.of_continuous_injective_isOpenMap f.continuous hfI hfO
    have hfD (s : Ioo a b) : d (f s)=Complex.ClosedUnitDisc.bdyPtOfReal (s.val/modelSideCount p) := by
      apply Subtype.ext
      change (Circle.exp (k*s.val) : ℂ)=Real.fourierChar (s.val/modelSideCount p)
      rw [Real.fourierChar_apply']
      have heq : k*s.val=2*Real.pi*(s.val/modelSideCount p) := by dsimp [k]; ring
      rw [heq]
    have hfW : ∀ s : Ioo a b, f s ∈ W := by
      intro s
      change d (f s) ∉ rawDeletedArc p
      rw [hfD]; exact hcap s s.property
    let fw : C(Ioo a b,W) := ⟨fun s => ⟨f s,hfW s⟩,f.continuous.subtype_mk hfW⟩
    have hfwE : IsOpenEmbedding fw :=
      (IsOpenEmbedding.of_comp_iff fw hWO.isOpenEmbedding_subtypeVal).mp hfE
    let q : C(Ioo a b,RawSurvivingBoundary p) := ⟨T ∘ fw,T.continuous.comp fw.continuous⟩
    refine ⟨q,T.isOpenEmbedding.comp hfwE,?_⟩
    intro s
    apply Subtype.ext;apply Subtype.ext
    exact hfD s
  have hSafe (s : ℝ) (hs : s ∈ Ioo (-1:ℝ) (4*(p:ℝ)+1)) :
      Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p) ∉ rawDeletedArc p := by
    rw [rawDeletedArc_scaled_boundary_iff]
    have ht := modelCapAngle_pos p
    have hm := modelCapAngle_mul_count p
    unfold modelSideCount at hm
    have hlo : modelCapAngle p<(3+2*s)*modelCapAngle p := by
      nlinarith [mul_pos (by linarith [hs.1] : 0<s+1) ht]
    have hhi : (3+2*s)*modelCapAngle p<2*Real.pi-modelCapAngle p := by
      nlinarith [mul_pos (by linarith [hs.2] : 0<4*(p:ℝ)+1-s) ht]
    exact not_le.mpr (cos_lt_of_between_cap_angles _ _ ht.le hlo hhi)
  obtain ⟨q,hq,hqv⟩ := hRawArc p (-1) (4*(p:ℝ)+1) (by dsimp [modelSideCount];linarith) hSafe
  have hsurj : Function.Surjective q := by
    intro z
    obtain ⟨s,hs0,hs1,hs⟩ := surviving_raw_circle_normalization p z.val z.property
    refine ⟨⟨s,hs0,hs1⟩,?_⟩
    rw [hqv]
    apply Subtype.ext;apply Subtype.ext
    exact hs.symm
  let T := ((isHomeomorph_iff_isEmbedding_surjective).mpr ⟨hq.isEmbedding,hsurj⟩).homeomorph q
  refine ⟨T,?_⟩
  intro s
  change (q s).val.val=rawBoundaryPoint p s.val
  rw [hqv]
  rfl
end CurveComplex.Hyperbolic.OneBoundaryRay
