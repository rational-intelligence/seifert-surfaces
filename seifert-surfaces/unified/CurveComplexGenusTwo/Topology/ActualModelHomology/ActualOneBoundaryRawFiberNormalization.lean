import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawCap

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def rawBoundaryPoint (p : ℕ) (s : ℝ) : Complex.ClosedUnitDisc :=
  Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p)

theorem rawBoundaryPoint_eq_period (p : ℕ) (x y : ℝ)
    (he : rawBoundaryPoint p x=rawBoundaryPoint p y) :
    ∃ m : ℤ, x=y+(m:ℝ)*modelSideCount p := by
  have hc : Real.fourierChar (x/modelSideCount p)=Real.fourierChar (y/modelSideCount p) :=
    by
      apply Subtype.ext
      exact congrArg (fun z : Complex.ClosedUnitDisc => (z:ℂ)) he
  rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
  obtain ⟨m,hm⟩ := Circle.exp_eq_exp.mp hc
  have hpi : 2*Real.pi≠0 := by positivity
  have hr : x/modelSideCount p=y/modelSideCount p+(m:ℝ) := by
    apply mul_left_cancel₀ hpi
    nlinarith [hm]
  have h := congrArg (fun r : ℝ => r*modelSideCount p) hr
  rw [add_mul,div_mul_cancel₀ _ (modelSideCount_pos p).ne',
    div_mul_cancel₀ _ (modelSideCount_pos p).ne'] at h
  exact ⟨m,h⟩

theorem rawBoundaryPoint_eq_of_interior_normalized (p : ℕ) (x y : ℝ)
    (hx0 : -3<x) (hx1 : x<4*(p:ℝ)) (hy0 : -3≤y) (hy1 : y≤4*(p:ℝ))
    (he : rawBoundaryPoint p x=rawBoundaryPoint p y) : x=y := by
  obtain ⟨m,hm⟩ := rawBoundaryPoint_eq_period p x y he
  have hN := modelSideCount_pos p
  have hlo : -modelSideCount p<x-y := by unfold modelSideCount; linarith
  have hhi : x-y< modelSideCount p := by unfold modelSideCount; linarith
  have hm0 : (-1:ℝ)<(m:ℝ) := by nlinarith
  have hm1 : (m:ℝ)<1 := by nlinarith
  have hi0 : (-1:ℤ)< m := by exact_mod_cast hm0
  have hi1 : m<(1:ℤ) := by exact_mod_cast hm1
  have he0 : m=0 := by omega
  simpa [he0] using hm

theorem rawBoundaryPoint_interior_eq_iff (p : ℕ) (x y : ℝ)
    (hx0 : -3<x) (hx1 : x<4*(p:ℝ)) (hy0 : -3≤y) (hy1 : y≤4*(p:ℝ)) :
    rawBoundaryPoint p x=rawBoundaryPoint p y ↔ x=y :=
  ⟨rawBoundaryPoint_eq_of_interior_normalized p x y hx0 hx1 hy0 hy1,fun h => congrArg _ h⟩

theorem integer_fraction_unique (n m : ℤ) (t x : ℝ)
    (ht0 : 0<t) (ht1 : t<1) (hx0 : 0≤x) (hx1 : x≤1)
    (he : (n:ℝ)+t=(m:ℝ)+x) : n=m ∧ t=x := by
  have hlo : (-1:ℝ)<((n-m:ℤ):ℝ) := by push_cast; linarith
  have hhi : ((n-m:ℤ):ℝ)<1 := by push_cast; linarith
  have hi0 : (-1:ℤ)<n-m := by exact_mod_cast hlo
  have hi1 : n-m<(1:ℤ) := by exact_mod_cast hhi
  have hnm : n=m := by omega
  refine ⟨hnm,?_⟩
  rw [hnm] at he
  linarith

end CurveComplex.Hyperbolic.OneBoundaryRay
