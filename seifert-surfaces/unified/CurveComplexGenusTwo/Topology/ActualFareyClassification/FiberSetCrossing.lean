import CurveComplexGenusTwo.Topology.ActualFareyClassification.SetCrossingHalfSide

open Set Topology Schoenflies Metric CurveComplex

/-- A genuine common-axis chart at a fiber contact forces the actual second
set to meet both sides of the fiber in every open neighborhood. -/
theorem actual_fiber_set_crossing_has_both_sides
    (L : Set Plane) (q : Plane) (c : ℝ) (hqc : q 0=c)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hq0 : ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈L ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))
    (N : Set Plane) (hN : IsOpen N) (hqN : q∈N) :
    (∃ z∈N∩L, z 0<c) ∧ (∃ z∈N∩L, c<z 0) := by
  let F : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 1-q 1) (z 0-c)
    invFun := fun z => Plane.mk (z 1+c) (z 0+q 1)
    left_inv := by intro z; ext i; fin_cases i <;> simp
    right_inv := by intro z; ext i; fin_cases i <;> simp
    continuous_toFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    continuous_invFun := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop }
  let E := F.toOpenPartialHomeomorph.restr (N∩U)
  have hsource : E.source=N∩U := by
    rw [OpenPartialHomeomorph.restr_source' _ _ (hN.inter hU)]
    simp [F]
  have hqE : q∈E.source := by rw [hsource]; exact ⟨hqN,hqU⟩
  have hE : ∀ z : Plane, E z=F z := by intro z; rfl
  have hEp : E q=0 := by
    rw [hE]
    ext i
    fin_cases i <;> simp [F,hqc]
  have hcross : ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hpU : q∈U) (h : U ≃ₜ V),
      IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hpU⟩ : V) : ℝ×ℝ)=(0,0) ∧
      (∀ z (hz : z∈U),
        (z∈{z : Plane | z 0=c} ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
        (z∈L ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) :=
    ⟨U,V,hqU,h,hU,hV,hq0,haxes⟩
  have haxis (z : Plane) (hz : z∈E.source) (_ : ‖E z‖<1) :
      z∈{z : Plane | z 0=c} ↔ E z 1=0 := by
    rw [hE]
    change z 0=c ↔ z 0-c=0
    exact sub_eq_zero.symm
  have hneq (z : Plane) (hz : z∈E.source) (hzL : z∈L) (hzq : z≠q) : z 0≠c := by
    intro hzc
    have hzU : z∈U := (hsource ▸ hz).2
    have h0 := (haxes z hzU).1.mp hzc
    have h1 := (haxes z hzU).2.mp hzL
    have heq : h ⟨z,hzU⟩=h ⟨q,hqU⟩ := by
      apply Subtype.ext
      rw [hq0]
      exact Prod.ext h0 h1
    exact hzq (congrArg Subtype.val (h.injective heq))
  constructor
  · by_contra hn
    push Not at hn
    apply set_crossing_cannot_stay_in_one_half {z : Plane | z 0=c} L q hcross E hqE hEp 1 1 (by norm_num) haxis
    intro z hz hzNorm hzL hzq
    have hzN : z∈N := (hsource ▸ hz).1
    have hle := hn z ⟨hzN,hzL⟩
    have hlt : c<z 0 := lt_of_le_of_ne hle (Ne.symm (hneq z hz hzL hzq))
    rw [hE]
    change 0<1*(z 0-c)
    linarith
  · by_contra hn
    push Not at hn
    apply set_crossing_cannot_stay_in_one_half {z : Plane | z 0=c} L q hcross E hqE hEp 1 (-1) (by norm_num) haxis
    intro z hz hzNorm hzL hzq
    have hzN : z∈N := (hsource ▸ hz).1
    have hle := hn z ⟨hzN,hzL⟩
    have hlt : z 0<c := lt_of_le_of_ne hle (hneq z hz hzL hzq)
    rw [hE]
    change 0<(-1)*(z 0-c)
    linarith

#print axioms actual_fiber_set_crossing_has_both_sides
