import CurveComplexGenusTwo.Topology.ActualFareyClassification.PositiveGaugeRadialHomeomorph

open Set Topology Schoenflies

/-- The square with two actual nonzero rectangular attachment ports is the
image of a closed square under a constructed global radial homeomorphism. -/
theorem square_with_two_ports_radial_model
    (rho sigma : ℝ) (hrho : 0<rho) (hrho1 : rho ≤ 1) (hsigma : 0<sigma) (hsigma1 : sigma ≤ 1) :
    ∃ H : Plane ≃ₜ Plane,
      H '' Plane.closedSquare 0 1 =
        (Plane.closedSquare 0 1∪{z : Plane | 1 ≤ z 0 ∧ z 0 ≤ 2 ∧ |z 1| ≤ rho})∪
          {z : Plane | -2 ≤ z 0 ∧ z 0 ≤  -1 ∧ |z 1| ≤ sigma} := by
  let gR : (Fin 2→ℝ)→ℝ := fun x => max (|x 0|/2) (|x 1|/rho)+max (-x 0) 0
  let gL : (Fin 2→ℝ)→ℝ := fun x => max (|x 0|/2) (|x 1|/sigma)+max (x 0) 0
  let g : (Fin 2→ℝ)→ℝ := fun x => min ‖x‖ (min (gR x) (gL x))
  have normEq (x : Fin 2→ℝ) : ‖x‖=max |x 0| |x 1| := by
    simp [Pi.norm_def,Finset.univ_fin2,Real.norm_eq_abs]
  have hg : Continuous g := by dsimp [g,gR,gL]; fun_prop
  have hhom : ∀ (r : ℝ) (x : Fin 2→ℝ), 0 ≤ r → g (r • x)=r*g x := by
    intro r x hr
    have hR : gR (r • x)=r*gR x := by
      change max (|r*x 0|/2) (|r*x 1|/rho)+max (-(r*x 0)) 0=r*(max (|x 0|/2) (|x 1|/rho)+max (-x 0) 0)
      simp only [abs_mul,abs_of_nonneg hr,mul_div_assoc,mul_add,mul_max_of_nonneg _ _ hr,mul_neg,mul_zero]
    have hL : gL (r • x)=r*gL x := by
      change max (|r*x 0|/2) (|r*x 1|/sigma)+max (r*x 0) 0=r*(max (|x 0|/2) (|x 1|/sigma)+max (x 0) 0)
      simp only [abs_mul,abs_of_nonneg hr,mul_div_assoc,mul_add,mul_max_of_nonneg _ _ hr,mul_zero]
    dsimp only [g]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,hR,hL,mul_min_of_nonneg _ _ hr,mul_min_of_nonneg _ _ hr]
  have hRbound (x : Fin 2→ℝ) : ‖x‖/2 ≤ gR x := by
    have hx := le_max_left (|x 0|/2) (|x 1|/rho)
    have hy := le_max_right (|x 0|/2) (|x 1|/rho)
    have hh : |x 1|/2 ≤ |x 1|/rho := div_le_div_of_nonneg_left (abs_nonneg _) hrho (by linarith)
    have ha := le_max_right (-x 0) 0
    rw [normEq, ←max_div_div_right (by norm_num : (0:ℝ) ≤ 2)]
    exact max_le (by dsimp [gR]; linarith) (by dsimp [gR]; linarith)
  have hLbound (x : Fin 2→ℝ) : ‖x‖/2 ≤ gL x := by
    have hx := le_max_left (|x 0|/2) (|x 1|/sigma)
    have hy := le_max_right (|x 0|/2) (|x 1|/sigma)
    have hh : |x 1|/2 ≤ |x 1|/sigma := div_le_div_of_nonneg_left (abs_nonneg _) hsigma (by linarith)
    have ha := le_max_right (x 0) 0
    rw [normEq, ←max_div_div_right (by norm_num : (0:ℝ) ≤ 2)]
    exact max_le (by dsimp [gL]; linarith) (by dsimp [gL]; linarith)
  have hb (x : Fin 2→ℝ) : (1/2)*‖x‖ ≤ g x ∧ g x ≤ 1*‖x‖ := by
    constructor
    · dsimp [g]
      exact le_min (by nlinarith [norm_nonneg x]) (le_min (by nlinarith [hRbound x]) (by nlinarith [hLbound x]))
    · simp [g]
  obtain ⟨R,_,_,hR⟩ := positive_homogeneous_gauge_radial_homeomorph g hg hhom (1/2) 1 (by norm_num) (by norm_num) hb
  let J : Plane ≃ₜ (Fin 2→ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
  let H := J.trans (R.trans J.symm)
  have hQ : J '' Plane.closedSquare 0 1={x : Fin 2→ℝ | ‖x‖ ≤ 1} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      rw [mem_closedSquare_zero_one] at hz
      simpa [J,normEq,Plane.supNorm] using hz
    · intro hx
      refine ⟨J.symm x,?_,J.apply_symm_apply _⟩
      rw [mem_closedSquare_zero_one]
      simpa [J,normEq,Plane.supNorm] using hx
  have hModel (z : Plane) : g (J z) ≤ 1 ↔
      z∈(Plane.closedSquare 0 1∪{z : Plane | 1 ≤ z 0 ∧ z 0 ≤ 2 ∧ |z 1| ≤ rho})∪
          {z : Plane | -2 ≤ z 0 ∧ z 0 ≤  -1 ∧ |z 1| ≤ sigma} := by
    change min ‖J z‖ (min (gR (J z)) (gL (J z))) ≤ 1 ↔ _
    rw [min_le_iff,min_le_iff]
    have hn : ‖J z‖=Plane.supNorm z := by simp [J,normEq,Plane.supNorm]
    have hrdef : gR (J z)=max (|z 0|/2) (|z 1|/rho)+max (-z 0) 0 := rfl
    have hldef : gL (J z)=max (|z 0|/2) (|z 1|/sigma)+max (z 0) 0 := rfl
    constructor
    · rintro (hq|hr|hl)
      · exact Or.inl (Or.inl (mem_closedSquare_zero_one.mpr (hn ▸ hq)))
      · rw [hrdef] at hr
        have hx : |z 0|/2 ≤ 1 := by have hh := le_max_left (|z 0|/2) (|z 1|/rho); have h0 := le_max_right (-z 0) 0; linarith
        have hy : |z 1| ≤ rho := by
          have hh := le_max_right (|z 0|/2) (|z 1|/rho)
          have h0 := le_max_right (-z 0) 0
          exact (div_le_one hrho).mp (by linarith)
        by_cases hpos : 1 ≤ z 0
        · exact Or.inl (Or.inr ⟨hpos,by linarith [le_abs_self (z 0)],hy⟩)
        · have hx' : |z 0| ≤ 1 := by
            rw [abs_le]
            refine ⟨?_,le_of_not_ge hpos⟩
            have hh := le_max_left (-z 0) 0
            have h0 : 0 ≤ max (|z 0|/2) (|z 1|/rho) := (by positivity)
            linarith
          exact Or.inl (Or.inl (mem_closedSquare_zero_one.mpr (max_le hx' (hy.trans hrho1))))
      · rw [hldef] at hl
        have hx : |z 0|/2 ≤ 1 := by have hh := le_max_left (|z 0|/2) (|z 1|/sigma); have h0 := le_max_right (z 0) 0; linarith
        have hy : |z 1| ≤ sigma := by
          have hh := le_max_right (|z 0|/2) (|z 1|/sigma)
          have h0 := le_max_right (z 0) 0
          exact (div_le_one hsigma).mp (by linarith)
        by_cases hneg : z 0 ≤  -1
        · exact Or.inr ⟨by linarith [neg_abs_le (z 0)],hneg,hy⟩
        · have hx' : |z 0| ≤ 1 := by
            rw [abs_le]
            refine ⟨by linarith,?_⟩
            have hh := le_max_left (z 0) 0
            have h0 : 0 ≤ max (|z 0|/2) (|z 1|/sigma) := (by positivity)
            linarith
          exact Or.inl (Or.inl (mem_closedSquare_zero_one.mpr (max_le hx' (hy.trans hsigma1))))
    · rintro ((hq|hr)|hl)
      · exact Or.inl (hn.symm ▸ mem_closedSquare_zero_one.mp hq)
      · right; left
        rw [hrdef,max_eq_right (by linarith [hr.1] : -z 0 ≤ 0),add_zero,max_le_iff]
        exact ⟨by rw [abs_of_nonneg (by linarith [hr.1])]; linarith [hr.2.1],(div_le_one hrho).mpr hr.2.2⟩
      · right; right
        rw [hldef,max_eq_right (by linarith [hl.2.1] : z 0 ≤ 0),add_zero,max_le_iff]
        exact ⟨by rw [abs_of_nonpos (by linarith [hl.2.1])]; linarith [hl.1],(div_le_one hsigma).mpr hl.2.2⟩
  refine ⟨H,?_⟩
  rw [show H '' Plane.closedSquare 0 1=J.symm '' (R '' (J '' Plane.closedSquare 0 1)) by rw [image_image,image_image]; rfl,hQ,hR]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hModel _).mp (by simpa using hx)
  · intro hz
    exact ⟨J z,(hModel z).mpr hz,J.symm_apply_apply z⟩

#print axioms square_with_two_ports_radial_model
