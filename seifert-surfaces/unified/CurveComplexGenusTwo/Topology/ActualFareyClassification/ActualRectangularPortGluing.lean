import CurveComplexGenusTwo.Topology.ActualFareyClassification.RectangularPortCoordinates
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSourceAttachedFamilySupport
import CurveComplexGenusTwo.Topology.BandGlobalGluing.FullSquareExtensionHeader

open Set Topology Schoenflies CurveComplex unitInterval

/-- The actual attachment equations produce compatible restricted
homeomorphisms, including the entire closed port overlap. -/
theorem actual_rectangular_port_restricted_homeomorphism
    (K : Set Plane) (F : Plane ≃ₜ Plane) (hFK : F '' K=Plane.closedSquare 0 1)
    (rho epsilon : ℝ) (hrho : 0<rho) (hrho1 : rho≤1) (heps : epsilon=1 ∨ epsilon= -1)
    (E : I×Icc (-1:ℝ) 1→Plane) (hE : IsEmbedding E)
    (hport : ∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk epsilon (epsilon*rho*w)))
    (hEK : range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk epsilon (epsilon*rho*w))) '' univ) :
    let R := {z : Plane | 1≤epsilon*z 0 ∧ epsilon*z 0≤2 ∧ |z 1|≤rho}
    ∃ f g : Plane→Plane, IsHomeoOn f g R (range E) ∧
      (∀ z∈Plane.closedSquare 0 1∩R, f z=F.symm z) ∧
      F.symm '' (Plane.closedSquare 0 1∩R)=K∩range E := by
  let R := {z : Plane | 1≤epsilon*z 0 ∧ epsilon*z 0≤2 ∧ |z 1|≤rho}
  have heps2 : epsilon*epsilon=1 := by rcases heps with rfl|rfl <;> norm_num
  have habs : |epsilon|=1 := by rcases heps with rfl|rfl <;> norm_num
  obtain ⟨e,het,hew,heinv⟩ := rectangular_port_actual_coordinates rho epsilon hrho heps
  let v : R ≃ₜ range E := e.trans hE.toHomeomorph
  obtain ⟨f,g,hfg,hfe⟩ := exists_isHomeoOn_of_homeomorph v
  have hcoord (z : Plane) (hz : z∈Plane.closedSquare 0 1∩R) : epsilon*z 0=1 := by
    have hh := mem_closedSquare_zero_one.mp hz.1
    have hx : |z 0|≤1 := (le_max_left _ _).trans hh
    have hzR := hz.2
    change 1≤epsilon*z 0 ∧ epsilon*z 0≤2 ∧ |z 1|≤rho at hzR
    rcases heps with h|h
    · rw [h] at hzR ⊢
      exact le_antisymm (by simpa using (le_abs_self (z 0)).trans hx) hzR.1
    · rw [h] at hzR ⊢
      have hn : -z 0≤1 := (neg_le_abs (z 0)).trans hx
      linarith [hzR.1]
  have hagree (z : Plane) (hz : z∈Plane.closedSquare 0 1∩R) : f z=F.symm z := by
    rw [hfe z hz.2]
    change E (e ⟨z,hz.2⟩)=F.symm z
    have hfirst : (e ⟨z,hz.2⟩).1=0 := by
      rw [het]
      apply Subtype.ext
      simp [hcoord z hz]
    have hp : e ⟨z,hz.2⟩=(0,(e ⟨z,hz.2⟩).2) := Prod.ext hfirst rfl
    rw [hp,hport]
    congr 1
    ext i
    fin_cases i
    · change epsilon=z 0
      calc
        epsilon=epsilon*(epsilon*z 0) := by rw [hcoord z hz,mul_one]
        _=(epsilon*epsilon)*z 0 := by ring
        _=z 0 := by rw [heps2,one_mul]
    · change epsilon*rho*((e ⟨z,hz.2⟩).2:ℝ)=z 1
      rw [hew]
      field_simp
      nlinarith [congrArg (fun a : ℝ => a*rho*z 1) heps2]
  refine ⟨f,g,hfg,hagree,?_⟩
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hxK : F.symm x∈K := by
      rw [←hFK] at hx
      obtain ⟨y,hy,he⟩ := hx.1
      rwa [←he,F.symm_apply_apply]
    exact ⟨hxK,(hagree x hx) ▸ hfg.mapsTo hx.2⟩
  · rintro ⟨hzK,hzE⟩
    have hz : z∈range E∩K := ⟨hzE,hzK⟩
    rw [hEK] at hz
    obtain ⟨w,_,hw⟩ := hz
    refine ⟨Plane.mk epsilon (epsilon*rho*w),⟨?_,?_⟩,hw⟩
    · rw [mem_closedSquare_zero_one]
      change max |epsilon| |epsilon*rho*(w:ℝ)|≤1
      rw [abs_mul,abs_mul,habs,abs_of_pos hrho,one_mul]
      exact max_le le_rfl ((mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hrho.le).trans (by simpa using hrho1))
    · change 1≤epsilon*epsilon ∧ epsilon*epsilon≤2 ∧ |epsilon*rho*(w:ℝ)|≤rho
      rw [heps2,abs_mul,abs_mul,habs,abs_of_pos hrho,one_mul]
      exact ⟨le_rfl,by norm_num,(mul_le_mul_of_nonneg_left (abs_le.mpr w.property) hrho.le).trans (by simp)⟩

#print axioms actual_rectangular_port_restricted_homeomorphism
