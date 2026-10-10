import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualMarkedGridReferenceBridge

open Set Topology Schoenflies CurveComplex

theorem actual_puncture_free_reference_has_gap_representative
    (T c : ℝ) (p : Plane) (hT : 0<T)
    (hpgrid : ∀ i : ℤ, p 0+(i:ℝ)*T≠c) :
    ∃ b : ℝ, p 0<b ∧ b<p 0+T ∧
      {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={z : Plane | ∃ i : ℤ, z 0=b+(i:ℝ)*T} := by
  let b := toIcoMod hT (p 0) c
  have hb := toIcoMod_mem_Ico hT (p 0) c
  obtain ⟨_,k,hk⟩ := (toIcoMod_eq_iff hT).mp (show toIcoMod hT (p 0) c=b from rfl)
  have hk' : c=b+(k:ℝ)*T := by simpa only [zsmul_eq_mul] using hk
  have hpb : p 0<b := by
    apply lt_of_le_of_ne hb.1
    intro hh
    apply hpgrid k
    change p 0=b at hh
    rw [hk',←hh]
  refine ⟨b,hpb,hb.2,?_⟩
  ext z
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨k+i,?_⟩
    push_cast
    rw [hk'] at hi
    linarith
  · rintro ⟨i,hi⟩
    refine ⟨i-k,?_⟩
    push_cast
    rw [hk']
    linarith

/-- ANY actual puncture-free translated vertical reference retains the same
puncture-relative ambient isotopy class. The actual finite grid motion fixes
all puncture lifts throughout; no relative-class certificate is input. -/
theorem actual_puncture_free_vertical_reference_grids_are_relative_isotopic
    (T c b : ℝ) (p : Plane) (hT : 0<T)
    (hpc : ∀ i : ℤ, p 0+(i:ℝ)*T≠c)
    (hpb : ∀ i : ℤ, p 0+(i:ℝ)*T≠b) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t (i : ℤ×ℤ), H.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ) z,
        H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      H.finalMap '' {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}=
        {z : Plane | ∃ i : ℤ, z 0=b+(i:ℝ)*T} := by
  obtain ⟨c0,hpc0,hc0p,hc0⟩ := actual_puncture_free_reference_has_gap_representative T c p hT hpc
  obtain ⟨b0,hpb0,hb0p,hb0⟩ := actual_puncture_free_reference_has_gap_representative T b p hT hpb
  obtain ⟨H,hHfix,hHeq,hHgrid⟩ := actual_reference_grids_in_puncture_gap_are_relative_isotopic
    T c0 b0 p hT hpc0 hc0p hpb0 hb0p
  refine ⟨H,hHfix,hHeq,?_⟩
  rw [hc0,hb0]
  exact hHgrid

#print axioms actual_puncture_free_reference_has_gap_representative
#print axioms actual_puncture_free_vertical_reference_grids_are_relative_isotopic
