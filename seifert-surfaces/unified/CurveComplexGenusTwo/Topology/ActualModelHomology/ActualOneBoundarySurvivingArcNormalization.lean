import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawInteriorFibers
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleVertices
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryQuotientDeformation

namespace CurveComplex.Hyperbolic.OneBoundaryRay

theorem complement_cap_arg_bound (θ : ℝ) (hθ : 0<θ) (hθpi : θ<Real.pi)
    (w : ℂ) (hw : ‖w‖=1) (hf : w.re<Real.cos θ) :
    |(-w).arg|<Real.pi-θ := by
  have hc : Real.cos (-w).arg=(-w).re := by
    simpa [hw] using Complex.norm_mul_cos_arg (-w)
  by_contra hn
  have ht := Real.cos_le_cos_of_nonneg_of_le_pi (sub_pos.mpr hθpi).le
    (Complex.abs_arg_le_pi (-w)) (le_of_not_gt hn)
  rw [Real.cos_abs,hc,Real.cos_pi_sub] at ht
  simp only [Complex.neg_re] at ht
  linarith

theorem rotated_raw_boundary_point (p : ℕ) (s : ℝ) :
    modelRotation p*(rawBoundaryPoint p s : ℂ)=
      Complex.exp (((3+2*s)*modelCapAngle p : ℝ)*Complex.I) := by
  change (Real.fourierChar (3/(2*modelSideCount p)) : ℂ)*
    (Real.fourierChar (s/modelSideCount p) : ℂ)=_
  rw [← Circle.coe_mul,← AddChar.map_add_eq_mul,Real.fourierChar_apply]
  congr 2
  congr 1
  unfold modelCapAngle
  field_simp [(modelSideCount_pos p).ne']

theorem surviving_raw_circle_normalization (p : ℕ) (z : RawOpenDisk p)
    (hz : ‖(z.val:ℂ)‖=1) :
    ∃ s : ℝ, -1<s ∧ s<4*(p:ℝ)+1 ∧ z.val=rawBoundaryPoint p s := by
  let w : ℂ := modelRotation p*(z.val:ℂ)
  have hw : ‖w‖=1 := by dsimp [w]; rw [norm_mul,modelRotation_norm,hz,one_mul]
  have hs : Complex.normSq (modelRotation p*(z.val:ℂ))=1 := by
    rw [rotation_normSq,Complex.normSq_eq_norm_sq,hz]
    norm_num
  have hf : modelRayOrigin p*w.re<1 :=
    (raw_rotated_keep p z).resolve_left (by rw [hs]; exact lt_irrefl _)
  have hfar : w.re<Real.cos (modelCapAngle p) := by
    unfold modelRayOrigin at hf
    rw [one_div_mul_eq_div] at hf
    simpa using (div_lt_iff₀ (modelCapCos_pos p)).mp hf
  have hθ := modelCapAngle_pos p
  have hθpi : modelCapAngle p<Real.pi := by
    linarith [modelCapAngle_lt_half_pi p,Real.pi_pos]
  have hb := complement_cap_arg_bound _ hθ hθpi w hw hfar
  let v : ℝ := (-w).arg
  have hv0 : -Real.pi+modelCapAngle p<v := by
    have h := (abs_lt.mp hb).1
    dsimp [v]
    linarith
  have hv1 : v<Real.pi-modelCapAngle p := (abs_lt.mp hb).2
  let s : ℝ := (v+Real.pi)/(2*modelCapAngle p)-3/2
  have hm := modelCapAngle_mul_count p
  unfold modelSideCount at hm
  have hden : 0<2*modelCapAngle p := by positivity
  have hl : (1:ℝ)/2<(v+Real.pi)/(2*modelCapAngle p) := by
    apply (lt_div_iff₀ hden).mpr
    linarith
  have hu : (v+Real.pi)/(2*modelCapAngle p)<4*(p:ℝ)+5/2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  refine ⟨s,by dsimp [s]; linarith,by dsimp [s]; linarith,?_⟩
  have hphase : (3+2*s)*modelCapAngle p=v+Real.pi := by
    dsimp [s]
    field_simp [hθ.ne']
    <;> ring
  have hexp : Complex.exp ((v:ℂ)*Complex.I) = -w := by
    simpa [v,hw] using Complex.norm_mul_exp_arg_mul_I (-w)
  apply Subtype.ext
  apply mul_left_cancel₀ (modelRotation_ne_zero p)
  change w=modelRotation p*(rawBoundaryPoint p s:ℂ)
  rw [rotated_raw_boundary_point,hphase,Complex.ofReal_add,add_mul,Complex.exp_add,
    Complex.exp_pi_mul_I,hexp]
  ring

theorem rawBoundaryPoint_add_count (p : ℕ) (s : ℝ) :
    rawBoundaryPoint p (s+modelSideCount p)=rawBoundaryPoint p s := by
  have hratio : (s+modelSideCount p)/modelSideCount p=s/modelSideCount p+1 := by
    field_simp [(modelSideCount_pos p).ne']
  have hc : Real.fourierChar ((s+modelSideCount p)/modelSideCount p)=
      Real.fourierChar (s/modelSideCount p) := by
    rw [Real.fourierChar_apply',Real.fourierChar_apply',hratio]
    convert Circle.exp_add_two_pi (2*Real.pi*(s/modelSideCount p)) using 1
    congr 1
    ring
  apply Subtype.ext
  exact congrArg (fun c : Circle => (c:ℂ)) hc

theorem seam_right_normalized_point (p : ℕ) (t : unitInterval) :
    rawBoundaryPoint p (4*(p:ℝ)+(t:ℝ))=rawEdgePoint (p:=p) (.inr ()) t true := by
  rw [rawEdgePoint_seam]
  simp only [Bool.true_eq,↓reduceIte]
  have he : 4*(p:ℝ)+(t:ℝ)= -(3-(t:ℝ))+modelSideCount p := by
    unfold modelSideCount
    ring
  rw [he,rawBoundaryPoint_add_count]

theorem raw_seam_zero_main_class (p : ℕ) (e : Bool) :
    Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1)
      (rawEdgePoint (p:=p) (.inr ()) 0 e)=rawBoundaryClass p 0 := by
  rw [rawEdgePoint_seam]
  cases e
  · simp [rawBoundaryPoint,rawBoundaryClass]
  · simp only [Bool.true_eq,↓reduceIte,show ((0:unitInterval):ℝ)=0 from rfl,sub_zero]
    have he : (4*(p:ℝ))= -3+modelSideCount p := by unfold modelSideCount; ring
    have hp : rawBoundaryPoint p (-3)=rawBoundaryPoint p (4*(p:ℝ)) := by
      rw [he,rawBoundaryPoint_add_count]
    change Quot.mk _ (rawBoundaryPoint p (-3))=rawBoundaryClass p 0
    rw [hp]
    exact handle_initial_vertex_class p p le_rfl

end CurveComplex.Hyperbolic.OneBoundaryRay
