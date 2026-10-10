import CurveComplexGenusTwo.Topology.ActualFareyClassification.AttachedPortSquareModel

open Set Topology Schoenflies CurveComplex unitInterval

/-- Actual affine coordinates for either rectangular port. -/
theorem rectangular_port_actual_coordinates (rho epsilon : ℝ) (hrho : 0<rho)
    (hepsilon : epsilon=1 ∨ epsilon= -1) :
    ∃ e : ↥{z : Plane | 1≤epsilon*z 0 ∧ epsilon*z 0≤2 ∧ |z 1|≤rho} ≃ₜ
      (I×Icc (-1:ℝ) 1),
      (∀ z, (e z).1=⟨epsilon*(z:Plane) 0-1,by constructor <;> linarith [z.property.1,z.property.2.1]⟩) ∧
      (∀ z, ((e z).2:ℝ)=epsilon*(z:Plane) 1/rho) ∧
      (∀ t w, ((e.symm (t,w)):Plane)=Plane.mk (epsilon*(1+t)) (epsilon*rho*w)) := by
  have heps2 : epsilon*epsilon=1 := by rcases hepsilon with rfl|rfl <;> norm_num
  have habs : |epsilon|=1 := by rcases hepsilon with rfl|rfl <;> norm_num
  let R := {z : Plane | 1≤epsilon*z 0 ∧ epsilon*z 0≤2 ∧ |z 1|≤rho}
  let f : R→I×Icc (-1:ℝ) 1 := fun z =>
    (⟨epsilon*(z:Plane) 0-1,by constructor <;> linarith [z.property.1,z.property.2.1]⟩,
      ⟨epsilon*(z:Plane) 1/rho,by
        change -1≤epsilon*(z:Plane) 1/rho ∧ epsilon*(z:Plane) 1/rho≤1
        rw [←abs_le,abs_div,abs_mul,habs,abs_of_pos hrho,one_mul]
        exact (div_le_one hrho).mpr z.property.2.2⟩)
  let k : I×Icc (-1:ℝ) 1 → R := fun z =>
    ⟨Plane.mk (epsilon*(1+z.1)) (epsilon*rho*z.2),by
      change 1≤epsilon*(epsilon*(1+(z.1:ℝ))) ∧ epsilon*(epsilon*(1+(z.1:ℝ)))≤2 ∧
        |epsilon*rho*(z.2:ℝ)|≤rho
      rw [←mul_assoc,heps2,one_mul]
      refine ⟨by linarith [z.1.property.1],by linarith [z.1.property.2],?_⟩
      rw [abs_mul,abs_mul,habs,abs_of_pos hrho,one_mul]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hrho.le).trans (by simp)⟩
  have hkf : ∀ z, k (f z)=z := by
    intro z
    apply Subtype.ext
    ext i
    fin_cases i
    · change epsilon*(1+(epsilon*(z:Plane) 0-1))=(z:Plane) 0
      nlinarith [congrArg (fun a : ℝ => a*(z:Plane) 0) heps2]
    · change epsilon*rho*(epsilon*(z:Plane) 1/rho)=(z:Plane) 1
      field_simp
      nlinarith [congrArg (fun a : ℝ => a*rho*(z:Plane) 1) heps2]
  have hfk : ∀ z, f (k z)=z := by
    intro z
    apply Prod.ext <;> apply Subtype.ext
    · change epsilon*(epsilon*(1+(z.1:ℝ)))-1=(z.1:ℝ)
      rw [←mul_assoc,heps2,one_mul]; ring
    · change epsilon*(epsilon*rho*(z.2:ℝ))/rho=(z.2:ℝ)
      rw [←mul_assoc,←mul_assoc,heps2,one_mul,mul_div_cancel_left₀ _ hrho.ne']
  let e : R ≃ₜ (I×Icc (-1:ℝ) 1) := {
    toFun := f
    invFun := k
    left_inv := hkf
    right_inv := hfk
    continuous_toFun := by dsimp [f]; fun_prop
    continuous_invFun := by dsimp [k]; fun_prop }
  exact ⟨e,fun _ => rfl,fun _ => rfl,fun _ _ => rfl⟩

#print axioms rectangular_port_actual_coordinates
