import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSmallMarkedGridSlide

open Set Topology Schoenflies CurveComplex

/-- Actual finite composition inside the puncture gap relates any two
reference grids there by a puncture-relative equivariant ambient isotopy. -/
theorem actual_reference_grids_in_puncture_gap_are_relative_isotopic
    (T c b : ℝ) (p : Plane) (hT : 0<T)
    (hpc : p 0<c) (hcp : c<p 0+T)
    (hpb : p 0<b) (hbp : b<p 0+T) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ), H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      H.finalMap '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
        {z : Plane | ∃ i : ℤ, z 0=b+(i:ℝ)*T} := by
  let m := min (min (c-p 0) (p 0+T-c)) (min (b-p 0) (p 0+T-b))
  have hm : 0< m := by dsimp [m]; positivity
  have hmc1 : m ≤ c-p 0 := (min_le_left _ _).trans (min_le_left _ _)
  have hmc2 : m ≤ p 0+T-c := (min_le_left _ _).trans (min_le_right _ _)
  have hmb1 : m ≤ b-p 0 := (min_le_right _ _).trans (min_le_left _ _)
  have hmb2 : m ≤ p 0+T-b := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨N,hN⟩ := exists_nat_gt (|b-c|/m+1)
  have hNpos : 0<(N:ℝ) := by
    have hh : 0 ≤ |b-c|/m := div_nonneg (abs_nonneg _) hm.le
    linarith
  have hNne : (N:ℝ)≠0 := ne_of_gt hNpos
  let e := (b-c)/(N:ℝ)
  have he : |e|< m := by
    rw [abs_div,abs_of_pos hNpos]
    apply (div_lt_iff₀ hNpos).mpr
    have hh := (div_lt_iff₀ hm).mp (lt_trans (by linarith : |b-c|/m < |b-c|/m+1) hN)
    nlinarith
  have hTotal : (N:ℝ)*e=b-c := by dsimp [e]; field_simp
  let phase (j : ℕ) := c+(j:ℝ)*e
  have hAtN : phase N=b := by dsimp [phase]; linarith
  have hBetween (j : ℕ) (hj : j ≤ N) : min c b ≤ phase j ∧ phase j ≤ max c b := by
    have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
    have hjN : (j:ℝ) ≤ (N:ℝ) := by exact_mod_cast hj
    by_cases hcb : c ≤ b
    · have he0 : 0 ≤ e := by dsimp [e]; positivity
      have hlow := mul_nonneg hj0 he0
      have hhigh := mul_le_mul_of_nonneg_right hjN he0
      rw [min_eq_left hcb,max_eq_right hcb]
      dsimp [phase]
      constructor <;> linarith
    · have hbc : b ≤ c := le_of_not_ge hcb
      have he0 : e ≤ 0 := by dsimp [e]; exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbc) hNpos.le
      have hlow := mul_le_mul_of_nonpos_right hjN he0
      have hhigh := mul_nonpos_of_nonneg_of_nonpos hj0 he0
      rw [min_eq_right hbc,max_eq_left hbc]
      dsimp [phase]
      constructor <;> linarith
  have hMargin (j : ℕ) (hj : j ≤ N) :
      m ≤ phase j-p 0 ∧ m ≤ p 0+T-phase j := by
    have hh := hBetween j hj
    have hLow : p 0+m ≤ min c b := le_min (by linarith) (by linarith)
    have hHigh : max c b ≤ p 0+T-m := max_le (by linarith) (by linarith)
    constructor <;> linarith [hh.1,hh.2]
  have hStage (j : ℕ) (hj : j ≤ N) :
      ∃ H : AmbientIsotopy Plane,
        (∀ t (i : ℤ×ℤ), H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
        (∀ t (i : ℤ×ℤ) z,
          H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
            H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
        H.finalMap '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
          {z : Plane | ∃ i : ℤ, z 0=phase j+(i:ℝ)*T} := by
    induction j with
    | zero =>
      refine ⟨AmbientIsotopy.identity Plane,fun _ _ => rfl,fun _ _ _ => rfl,?_⟩
      change (fun z : Plane => z) '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
        {z : Plane | ∃ i : ℤ, z 0=phase 0+(i:ℝ)*T}
      simp [phase]
    | succ j ih =>
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      obtain ⟨H,hHfix,hHeq,hHgrid⟩ := ih hjN
      obtain ⟨hm1,hm2⟩ := hMargin j hjN
      have hpcj : p 0<phase j := by linarith
      have hcpj : phase j<p 0+T := by linarith
      have hej : |e| < min (phase j-p 0) (p 0+T-phase j) := lt_of_lt_of_le he (le_min hm1 hm2)
      obtain ⟨J,hJfix,hJeq,hJgrid⟩ := actual_small_horizontal_grid_slide_relative_puncture T (phase j) e p hT hpcj hcpj hej
      refine ⟨H.compose J,?_,?_,?_⟩
      · intro t i
        change J.map (t,H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))=_
        rw [hHfix,hJfix]
      · intro t i z
        change J.map (t,H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))=_
        rw [hHeq,hJeq]
        rfl
      · rw [AmbientIsotopy.compose_finalMap,image_comp,hHgrid,hJgrid]
        have hAt : phase j+e=phase (j+1) := by dsimp [phase]; push_cast; ring
        rw [hAt]
  obtain ⟨H,hHfix,hHeq,hHgrid⟩ := hStage N le_rfl
  exact ⟨H,hHfix,hHeq,by rwa [hAtN] at hHgrid⟩

#print axioms actual_reference_grids_in_puncture_gap_are_relative_isotopic
