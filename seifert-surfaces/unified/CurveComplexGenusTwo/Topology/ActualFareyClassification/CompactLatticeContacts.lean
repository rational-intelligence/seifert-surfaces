import CurveComplexGenusTwo.Topology.TorusStrip.NormalizedDeckFamily
import Mathlib

open Set Topology Schoenflies

/-- A full lattice orbit of an actual finite set has finitely many contacts in
any compact planar support. The global orbit need not be finite. -/
theorem finite_lattice_orbit_contacts_in_compact
    (F K : Set Plane) (hF : F.Finite) (hK : IsCompact K) (T : ℝ) (hT : 0<T) :
    ((⋃ i : ℤ × ℤ, (fun z : Plane =>
      z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' F) ∩ K).Finite := by
  obtain ⟨A,hA⟩ := (hF.isCompact.image (continuous_abs.comp (EuclideanSpace.proj 0).continuous)).bddAbove
  obtain ⟨B,hB⟩ := (hF.isCompact.image (continuous_abs.comp (EuclideanSpace.proj 1).continuous)).bddAbove
  obtain ⟨C,hC⟩ := (hK.image (continuous_abs.comp (EuclideanSpace.proj 0).continuous)).bddAbove
  obtain ⟨D,hD⟩ := (hK.image (continuous_abs.comp (EuclideanSpace.proj 1).continuous)).bddAbove
  obtain ⟨N,hN⟩ := exists_nat_gt ((max (A+C) (B+D))/T)
  have hNT := (div_lt_iff₀ hT).mp hN
  let J : Set (ℤ × ℤ) := Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ))
  have hbound (i : ℤ × ℤ) (z : Plane) (hz : z∈F)
      (hzK : z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) ∈ K) : i∈J := by
    have hza := abs_le.mp (hA ⟨z,hz,rfl⟩)
    have hzb := abs_le.mp (hB ⟨z,hz,rfl⟩)
    change -A ≤ z 0 ∧ z 0 ≤ A at hza
    change -B ≤ z 1 ∧ z 1 ≤ B at hzb
    have hzc := abs_le.mp (hC ⟨_,hzK,rfl⟩)
    have hzd := abs_le.mp (hD ⟨_,hzK,rfl⟩)
    change -C ≤ z 0+(i.1:ℝ)*T ∧ z 0+(i.1:ℝ)*T ≤ C at hzc
    change -D ≤ z 1+(i.2:ℝ)*T ∧ z 1+(i.2:ℝ)*T ≤ D at hzd
    have hi0 : -(N:ℝ)<(i.1:ℝ) ∧ (i.1:ℝ)<N := by
      constructor <;> nlinarith [le_max_left (A+C) (B+D)]
    have hi1 : -(N:ℝ)<(i.2:ℝ) ∧ (i.2:ℝ)<N := by
      constructor <;> nlinarith [le_max_right (A+C) (B+D)]
    exact ⟨⟨by exact_mod_cast hi0.1.le,by exact_mod_cast hi1.1.le⟩,
      ⟨by exact_mod_cast hi0.2.le,by exact_mod_cast hi1.2.le⟩⟩
  have hAll := (finite_Icc (-(N:ℤ),-(N:ℤ)) ((N:ℤ),(N:ℤ))).biUnion
    (fun i _ => hF.image (fun z => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)))
  apply hAll.subset
  rintro z ⟨hz,hzK⟩
  obtain ⟨i,w,hw,rfl⟩ := mem_iUnion.mp hz
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hbound i w hw hzK,w,hw,rfl⟩⟩

/-- The full orbit of actual fiber events is exactly the contact set between
the actual deck-line family and the whole periodic vertical grid. -/
theorem normalized_line_grid_contacts_eq_fiber_event_orbit
    (G : ℝ → Plane) (T c : ℝ)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0) :
    (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∩
      {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T} =
    ⋃ i : ℤ × ℤ, (fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
      (G '' {t : ℝ | G t 0=c}) := by
  ext z
  constructor
  · rintro ⟨hz,⟨i,hi⟩⟩
    obtain ⟨j,t,rfl⟩ := mem_iUnion.mp hz
    have hshift := hp i (t-(i:ℝ)*T)
    have ht : t-(i:ℝ)*T+(i:ℝ)*T=t := by ring
    rw [ht] at hshift
    have hc : G (t-(i:ℝ)*T) 0=c := by
      have hh := congrArg (fun w : Plane => w 0) hshift
      change G t 0=G (t-(i:ℝ)*T) 0+(i:ℝ)*T at hh
      have hi0 : G t 0=c+(i:ℝ)*T := by simpa [Plane.mk] using hi
      linarith
    refine mem_iUnion.mpr ⟨(i,j),G (t-(i:ℝ)*T),⟨t-(i:ℝ)*T,hc,rfl⟩,?_⟩
    dsimp only
    rw [hshift]
    ext k
    fin_cases k <;> simp [Plane.mk]
  · intro hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    obtain ⟨w,⟨t,ht,rfl⟩,rfl⟩ := hi
    refine ⟨mem_iUnion.mpr ⟨i.2,t+(i.1:ℝ)*T,?_⟩,⟨i.1,?_⟩⟩
    · dsimp only
      rw [hp]
      ext k
      fin_cases k <;> simp [Plane.mk]
    · change G t 0+(i.1:ℝ)*T=c+(i.1:ℝ)*T
      rw [ht]

/-- Compact full-grid contacts are finite directly from normalized actual
line data and actual finite fiber intersections. -/
theorem normalized_line_full_grid_contacts_finite_in_compact
    (G : ℝ → Plane) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (K : Set Plane) (hK : IsCompact K) :
    (((⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∩
      {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}) ∩ K).Finite := by
  rw [normalized_line_grid_contacts_eq_fiber_event_orbit G T c hp]
  exact finite_lattice_orbit_contacts_in_compact _ K (hfinite.image G) hK T hT

#print axioms finite_lattice_orbit_contacts_in_compact
#print axioms normalized_line_grid_contacts_eq_fiber_event_orbit
#print axioms normalized_line_full_grid_contacts_finite_in_compact
