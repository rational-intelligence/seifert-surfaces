import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualSourceFamilyOperationChart

open Set Topology Schoenflies CurveComplex

/-- The actual normalized line period implies invariance of the entire row
family under every horizontal/mixed lattice translate. -/
theorem normalized_actual_row_family_lattice_invariant
    (G : C(ℝ,Plane)) (T : ℝ)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0) :
    ∀ (i : ℤ×ℤ) z,
      z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
      z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
  have forward (i : ℤ×ℤ) (z : Plane)
      (hz : z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))) :
      z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
    obtain ⟨j,x,rfl⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨j+i.2,x+(i.1:ℝ)*T,?_⟩
    change G (x+(i.1:ℝ)*T)+Plane.mk 0 (((j+i.2:ℤ):ℝ)*T)=G x+Plane.mk 0 ((j:ℝ)*T)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)
    rw [hp]
    ext k; fin_cases k <;> simp [Plane.mk,Int.cast_add]
    all_goals ring
  intro i z
  constructor
  · exact forward i z
  · intro hz
    have hh := forward (-i) _ hz
    have he : z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)+Plane.mk (((-i).1:ℝ)*T) (((-i).2:ℝ)*T)=z := by
      ext k; fin_cases k <;> simp [Plane.mk]
    rwa [he] at hh

/-- An actual single-cell family receipt transports to the complete lattice
orbit. In particular, the open support supplies PeriodicEventErase's whole
source-locality receipt, with no locality certificate assumed. -/
theorem normalized_actual_family_disk_full_lattice_contact
    (G : C(ℝ,Plane)) (T a b : ℝ)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (phi : Plane ≃ₜ Plane)
    (hcontact : (phi '' Plane.closedSquare 0 1)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b) :
    (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))∩
      (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.closedSquare 0 1))=
      (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc a b)) ∧
    range G∩(⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.openSquare 0 1))⊆
      (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc a b)) := by
  let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  have hOrbit : L∩(⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.closedSquare 0 1))=
      (⋃ i : ℤ×ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (G '' Icc a b)) := by
    ext z
    constructor
    · rintro ⟨hzL,hz⟩
      obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
      have hwL := (normalized_actual_row_family_lattice_invariant G T hp i w).mpr hzL
      have hwA : w∈G '' Icc a b := hcontact ▸ (show w∈(phi '' Plane.closedSquare 0 1)∩L from ⟨hw,hwL⟩)
      exact mem_iUnion.mpr ⟨i,w,hwA,rfl⟩
    · intro hz
      obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
      have hwDL : w∈(phi '' Plane.closedSquare 0 1)∩L := hcontact.symm ▸ hw
      exact ⟨(normalized_actual_row_family_lattice_invariant G T hp i w).mp hwDL.2,
        mem_iUnion.mpr ⟨i,w,hwDL.1,rfl⟩⟩
  refine ⟨hOrbit,?_⟩
  rintro z ⟨hzG,hz⟩
  rw [←hOrbit]
  have hzL : z∈L := by
    obtain ⟨t,rfl⟩ := hzG
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i; fin_cases i <;> simp [Plane.mk]
  refine ⟨hzL,?_⟩
  obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hz
  refine mem_iUnion.mpr ⟨i,w,?_,he⟩
  exact image_mono (fun z hz => mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hz).le) hw

#print axioms normalized_actual_row_family_lattice_invariant
#print axioms normalized_actual_family_disk_full_lattice_contact
