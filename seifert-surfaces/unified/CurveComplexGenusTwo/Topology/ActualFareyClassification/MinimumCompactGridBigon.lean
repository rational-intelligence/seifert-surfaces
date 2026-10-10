import CurveComplexGenusTwo.Topology.ActualFareyClassification.VerticalBigonSeparation
import CurveComplexGenusTwo.Topology.ActualFareyClassification.CompactLatticeContacts
import CurveComplexGenusTwo.Topology.ActualFareyClassification.JordanSubdiskContacts
import CurveComplexGenusTwo.Topology.TorusStrip.NestedBands

open Set Topology Schoenflies Bornology

/-- An actual closed subdisk inherits separation of the vertical translated
open disks. This lets descent preserve the previously constructed geometry. -/
theorem jordan_subdisk_inherits_vertical_separation
    (C D : Set Plane) (hC : IsJordanCurve C) (hD : IsJordanCurve D) (T : ℝ)
    (hboundary : D ⊆ closure (inside C))
    (hsep : Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' C)))) :
    Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' D))
      (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' D))) := by
  have hs := (jordan_subdisk_of_boundary_in_closed_disk C D hC hD hboundary).1
  have hsub (i : ℤ) :
      inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' D) ⊆
      inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' C) := by
    change inside ((Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) '' D) ⊆
      inside ((Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) '' C)
    rw [← (plane_homeomorph_inside_transport (Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) D).1,
      ← (plane_homeomorph_inside_transport (Homeomorph.addRight (Plane.mk 0 ((i:ℝ)*T))) C).1]
    exact image_mono hs
  exact fun i j hij => (hsep hij).mono (hsub i) (hsub j)

/-- The finite compact full-grid minimum is constructed from normalized actual
source data. Entering any OTHER grid fiber gives a smaller actual subdisk,
while the vertical separation already produced upstream is preserved. -/
theorem normalized_actual_line_select_horizontal_grid_free_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard) :
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      Pairwise (fun i j : ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      (∀ i : ℤ, i≠k → ∀ t : ℝ, Plane.mk (c+(i:ℝ)*T) t ∉
        inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  classical
  let L := ⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))
  let E := L ∩ {z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}
  let C := fun r s : ℝ => (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let Sep := fun D : Set Plane => Pairwise (fun i j : ℤ => Disjoint
    (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' D))
    (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' D)))
  let Cand := fun (k : ℤ) (r s : ℝ) => r<s ∧ G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
    IsJordanCurve (C r s) ∧ Disjoint (inside (C r s)) L ∧ Sep (C r s)
  let count := fun r s : ℝ => (E ∩ closure (inside (C r s))).ncard
  let Q : ℕ → Prop := fun n => ∃ k r s, Cand k r s ∧ count r s=n
  have hex : ∃ n, Q n := by
    obtain ⟨r,s,hrs,hr,hs,hJ,hno,he,hsep⟩ :=
      normalized_actual_line_select_periodically_empty_bigon G hG T c hT hp hc hfinite hcount
    refine ⟨count r s,0,r,s,?_,rfl⟩
    exact ⟨hrs,by simpa using hr,by simpa using hs,hJ,he,hsep⟩
  obtain ⟨k,r,s,hcand,hn⟩ := Nat.find_spec hex
  obtain ⟨hrs,hr,hs,hJ,he,hsep⟩ := hcand
  have hmin (i : ℤ) (a b : ℝ) (hab : Cand i a b) : count r s ≤ count a b := by
    rw [hn]
    exact Nat.find_min' hex ⟨i,a,b,hab,rfl⟩
  refine ⟨k,r,s,hrs,hr,hs,hJ,he,hsep,?_⟩
  intro i hik t ht
  have hcc : c+(i:ℝ)*T≠c+(k:ℝ)*T := by
    intro hh
    have hcast : (i:ℝ)=(k:ℝ) := by nlinarith
    exact hik (Int.cast_injective hcast)
  have hGL : range G ⊆ L := by
    rintro z ⟨u,rfl⟩
    refine mem_iUnion.mpr ⟨0,u,?_⟩
    ext q
    fin_cases q <;> simp [Plane.mk]
  have hcompact : IsCompact (closure (inside (C r s))) :=
    (jordan_curve_theorem hJ).isBounded_inside.isCompact_closure
  have hEf : (E ∩ closure (inside (C r s))).Finite :=
    normalized_line_full_grid_contacts_finite_in_compact G T c hT hp hfinite _ hcompact
  have hcontact : G r∈E := ⟨hGL ⟨r,rfl⟩,k,hr⟩
  obtain ⟨a,b,hra,hab,hbs,ha0,hb0,hD,hcl,hDe,hlt⟩ :=
    shifted_fiber_actual_subdisk_strict_contacts G hG (c+(k:ℝ)*T) (c+(i:ℝ)*T) r s
      hrs hr hs hcc hJ L E hGL he hEf hcontact t ht
  have hboundary : C a b ⊆ closure (inside (C r s)) := by
    have hDc : C a b ⊆ closure (inside (C a b)) := by
      intro z hz
      exact frontier_subset_closure ((jordan_curve_theorem hD).frontier_inside.symm ▸ hz)
    exact hDc.trans hcl
  have hDsep : Sep (C a b) :=
    jordan_subdisk_inherits_vertical_separation _ _ hJ hD T hboundary hsep
  have hle := hmin i a b ⟨hab,ha0,hb0,hD,hDe,hDsep⟩
  exact not_lt_of_ge hle hlt

#print axioms jordan_subdisk_inherits_vertical_separation
#print axioms normalized_actual_line_select_horizontal_grid_free_bigon
