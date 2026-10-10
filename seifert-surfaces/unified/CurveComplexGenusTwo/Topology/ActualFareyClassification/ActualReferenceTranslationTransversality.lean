import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualRenewedFamilyTransversality

open Set Topology Schoenflies CurveComplex

theorem actual_translation_transports_whole_family_axis_charts
    (G : ℝ→Plane) (T c : ℝ) (d : Plane)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
 : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => (G x+d)+Plane.mk 0 ((j:ℝ)*T))) → q 0=(c+d 0)+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=(c+d 0)+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => (G x+d)+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) := by
  let F := Homeomorph.addRight d
  have hFamily (z : Plane) :
      z∈(⋃ j : ℤ, range (fun x : ℝ => (G x+d)+Plane.mk 0 ((j:ℝ)*T))) ↔
        F.symm z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
    constructor
    · intro hz
      obtain ⟨j,x,hx⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨j,x,?_⟩
      change G x+Plane.mk 0 ((j:ℝ)*T)=z-d
      change (G x+d)+Plane.mk 0 ((j:ℝ)*T)=z at hx
      rw [←hx]
      abel
    · intro hz
      obtain ⟨j,x,hx⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨j,x,?_⟩
      change (G x+d)+Plane.mk 0 ((j:ℝ)*T)=z
      change G x+Plane.mk 0 ((j:ℝ)*T)=z-d at hx
      calc (G x+d)+Plane.mk 0 ((j:ℝ)*T)=(G x+Plane.mk 0 ((j:ℝ)*T))+d := by abel
        _=(z-d)+d := congrArg (fun w : Plane => w+d) hx
        _=z := sub_add_cancel _ _
  intro q i hq hi
  have hqF := (hFamily q).mp hq
  have hiF : F.symm q 0=c+(i:ℝ)*T := by
    change q 0-d 0=c+(i:ℝ)*T
    linarith
  obtain ⟨U,V,hqU,h,hU,hV,hq0,haxis⟩ := htrans (F.symm q) i hqF hiF
  let U' := F '' U
  have hqU' : q∈U' := ⟨F.symm q,hqU,F.apply_symm_apply _⟩
  let e : U' ≃ₜ V := (F.image U).symm.trans h
  have hback (z : Plane) (hz : z∈U') : F.symm z∈U := by
    obtain ⟨w,hw,he⟩ := hz
    rw [←he,F.symm_apply_apply]
    exact hw
  have hFormula (z : Plane) (hz : z∈U') : ((e ⟨z,hz⟩ : V) : ℝ×ℝ)=
      ((h ⟨F.symm z,hback z hz⟩ : V) : ℝ×ℝ) := rfl
  refine ⟨U',V,hqU',e,F.isOpenMap _ hU,hV,?_,?_⟩
  · exact (hFormula q hqU').trans hq0
  · intro z hz
    rw [hFormula z hz]
    obtain ⟨hfirst,hsecond⟩ := haxis (F.symm z) (hback z hz)
    refine ⟨?_,(hFamily z).trans hsecond⟩
    have hh : (z 0=(c+d 0)+(i:ℝ)*T) ↔ F.symm z 0=c+(i:ℝ)*T := by
      change (z 0=(c+d 0)+(i:ℝ)*T) ↔ z 0-d 0=c+(i:ℝ)*T
      constructor <;> intro ht <;> linarith
    exact hh.trans hfirst

#print axioms actual_translation_transports_whole_family_axis_charts
