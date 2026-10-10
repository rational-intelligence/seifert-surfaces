import CurveComplexGenusTwo.Topology.ActualFareyClassification.TransverseFamilyArcContacts

open Set Topology Schoenflies Metric

/-- Finite source selection plus actual common-axis transversality charts
produces a short bigon whose curve side has exactly two grid events and whose
straight side meets the entire lifted family only at the same two corners.
Neither contact identity is a supplied geometric certificate. -/
theorem normalized_actual_transverse_select_clean_short_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1<{t : ℝ | G t 0=c}.ncard)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 0=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))) :
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ s-r<T ∧ G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 0≠c+(i:ℝ)*T) ∧
      segment ℝ (G r) (G s) ∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s} ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      ((∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T-T≤z 0 ∧ z 0≤c+(k:ℝ)*T) ∨
        (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T≤z 0 ∧ z 0≤c+(k:ℝ)*T+T)) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hgrid,hsep⟩ :=
    normalized_actual_line_select_short_full_lattice_bigon G hG T c hT hp hc hfinite hcount
  let d := c+(k:ℝ)*T
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  have hGL : range G⊆L := by
    rintro z ⟨u,rfl⟩
    refine mem_iUnion.mpr ⟨0,u,?_⟩
    ext q
    fin_cases q <;> simp [Plane.mk]
  have no (i : ℤ) (z : Plane) (hz : z∈inside C) : z 0≠c+(i:ℝ)*T := by
    intro hh
    apply hgrid i (z 1)
    have hez : Plane.mk (c+(i:ℝ)*T) (z 1)=z := by
      ext q
      fin_cases q <;> simp [hh]
    rwa [hez]
  have hslab := grid_free_jordan_boundary_in_adjacent_slab C hJ d T hT (G r)
    (Or.inl ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩) hr (by
      intro z hz
      refine ⟨no k z hz,?_,?_⟩
      · have hh := no (k-1) z hz
        convert hh using 1
        dsimp [d]
        push_cast
        ring
      · have hh := no (k+1) z hz
        convert hh using 1
        dsimp [d]
        push_cast
        ring)
  have hno (i : ℤ) (t : ℝ) (ht : t∈Ioo r s) : G t 0≠c+(i:ℝ)*T := by
    intro htc
    obtain ⟨U,V,htU,h,hU,hV,ht0,haxes⟩ := htrans (G t) i (hGL ⟨t,rfl⟩) htc
    have htC : G t∈C := Or.inl ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩
    have hside : (∀ u∈Icc r s, G u 0≤c+(i:ℝ)*T) ∨
        (∀ u∈Icc r s, c+(i:ℝ)*T≤G u 0) := by
      rcases hslab with hl|hright
      · have hbound := hl (G t) htC
        have hii : i=k-1 ∨ i=k := by
          dsimp [d] at hbound
          rw [htc] at hbound
          have hlow : (k:ℝ)-1≤(i:ℝ) := by nlinarith [hbound.1]
          have hupp : (i:ℝ)≤(k:ℝ) := by nlinarith [hbound.2]
          have hlow' : k-1 ≤ i := by exact_mod_cast hlow
          have hupp' : i ≤ k := by exact_mod_cast hupp
          omega
        rcases hii with rfl|rfl
        · right
          intro u hu
          have hh := (hl (G u) (Or.inl ⟨u,hu,rfl⟩)).1
          dsimp [d] at hh
          push_cast
          linarith
        · left
          exact fun u hu => (hl (G u) (Or.inl ⟨u,hu,rfl⟩)).2
      · have hbound := hright (G t) htC
        have hii : i=k ∨ i=k+1 := by
          dsimp [d] at hbound
          rw [htc] at hbound
          have hlow : (k:ℝ)≤(i:ℝ) := by nlinarith [hbound.1]
          have hupp : (i:ℝ)≤(k:ℝ)+1 := by nlinarith [hbound.2]
          have hlow' : k ≤ i := by exact_mod_cast hlow
          have hupp' : i ≤ k+1 := by exact_mod_cast hupp
          omega
        rcases hii with rfl|rfl
        · right
          exact fun u hu => (hright (G u) (Or.inl ⟨u,hu,rfl⟩)).1
        · left
          intro u hu
          have hh := (hright (G u) (Or.inl ⟨u,hu,rfl⟩)).2
          dsimp [d] at hh
          push_cast
          linarith
    exact normalized_transverse_family_no_internal_halfplane_touch G hG T r s t
      (c+(i:ℝ)*T) hT hp hc ht htc hside U V htU h hU hV ht0 haxes
  have hcontact : segment ℝ (G r) (G s)∩L={G r,G s} := by
    ext q
    constructor
    · rintro ⟨hqS,hqL⟩
      have hqc : q 0=d := by
        rw [segment_eq_image_lineMap] at hqS
        obtain ⟨u,hu,heq⟩ := hqS
        have hh := congrArg (fun z : Plane => z 0) heq
        simp only [AffineMap.lineMap_apply] at hh
        change u*(G s 0-G r 0)+G r 0=q 0 at hh
        rw [hr,hs] at hh
        dsimp [d]
        linarith
      obtain ⟨U,V,hqU,h,hU,hV,hq0,haxes⟩ := htrans q k hqL hqc
      have hside : (∀ z∈C, z 0≤d) ∨ (∀ z∈C, d≤z 0) := by
        rcases hslab with hl|hright
        · exact Or.inl (fun z hz => (hl z hz).2)
        · exact Or.inr (fun z hz => (hright z hz).1)
      obtain ⟨u,hu,heq⟩ := transverse_fiber_contact_of_empty_bigon_on_curve_side G r s d hr hs hJ L he hside q hqS hqL
        U V hqU h hU hV hq0 haxes
      have hend : u=r ∨ u=s := by
        by_cases hur : u=r
        · exact Or.inl hur
        by_cases hus : u=s
        · exact Or.inr hus
        have hui : u∈Ioo r s := ⟨lt_of_le_of_ne hu.1 (Ne.symm hur),lt_of_le_of_ne hu.2 hus⟩
        apply False.elim
        apply hno k u hui
        rw [heq]
        exact hqc
      rcases hend with rfl|rfl
      · exact Or.inl heq.symm
      · exact Or.inr (mem_singleton_iff.mpr heq.symm)
    · intro hq
      rcases hq with hh|hh
      · rw [hh]
        exact ⟨left_mem_segment ℝ _ _,hGL ⟨r,rfl⟩⟩
      · rw [mem_singleton_iff.mp hh]
        exact ⟨right_mem_segment ℝ _ _,hGL ⟨s,rfl⟩⟩
  exact ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hsep,hslab⟩

#print axioms normalized_actual_transverse_select_clean_short_bigon
