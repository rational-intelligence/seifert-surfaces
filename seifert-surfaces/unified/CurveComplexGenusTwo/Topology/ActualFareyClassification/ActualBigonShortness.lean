import CurveComplexGenusTwo.Topology.ActualFareyClassification.GridFreeJordanSlab
import CurveComplexGenusTwo.Topology.ActualFareyClassification.FullLatticeBigonSeparation

open Set Topology Schoenflies

/-- Periodicity and actual finite fiber events force any boundary arc in an
adjacent closed lattice slab to have length strictly less than one period. -/
theorem normalized_finite_fiber_slab_arc_short
    (G : C(ℝ,Plane)) (T c r s : ℝ) (hT : 0<T) (_hrs : r<s)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hr : G r 0=c) (hs : G s 0=c)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hslab : (∀ t∈Icc r s, c-T≤G t 0 ∧ G t 0≤c) ∨
      (∀ t∈Icc r s, c≤G t 0 ∧ G t 0≤c+T)) : s-r<T := by
  have hperiod (t : ℝ) : G (t+T) 0=G t 0+T := by
    simpa using congrArg (fun z : Plane => z 0) (hp 1 t)
  by_contra hbad
  have hle : T ≤ s-r := le_of_not_gt hbad
  by_cases heq : s-r=T
  · have he : s=r+T := by linarith
    rw [he,hperiod,hr] at hs
    linarith
  have hstrict : T<s-r := lt_of_le_of_ne hle (Ne.symm heq)
  have hlt : r<s-T := by linarith
  have hfinitePrev : {t : ℝ | G t 0=c-T}.Finite := by
    apply (hfinite.image (fun t : ℝ => t-T)).subset
    intro t ht
    refine ⟨t+T,?_,by ring⟩
    change G (t+T) 0=c
    rw [hperiod]
    change G t 0=c-T at ht
    linarith
  have hconstant : Icc r (s-T)⊆{t : ℝ | G t 0=c} ∪ {t : ℝ | G t 0=c-T} := by
    intro t ht
    have ht0 : t∈Icc r s := ⟨ht.1,by linarith [ht.2]⟩
    have ht1 : t+T∈Icc r s := ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rcases hslab with hl|hr
    · have h0 := hl t ht0
      have h1 := hl (t+T) ht1
      rw [hperiod] at h1
      right
      change G t 0=c-T
      linarith
    · have h0 := hr t ht0
      have h1 := hr (t+T) ht1
      rw [hperiod] at h1
      left
      change G t 0=c
      linarith
  exact (Set.Icc_infinite hlt).not_finite ((hfinite.union hfinitePrev).subset hconstant)

#print axioms normalized_finite_fiber_slab_arc_short

/-- Actual finite-intersection source data selects a periodically empty,
full-lattice-separated Jordan bigon AND derives shortness. No short-arc,
slab, innermostness or separation certificate is a source premise. -/
theorem normalized_actual_line_select_short_full_lattice_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1<{t : ℝ | G t 0=c}.ncard) :
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ s-r<T ∧ G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun t => G t+Plane.mk 0 ((j:ℝ)*T))) ∧
      (∀ i : ℤ, ∀ t : ℝ, Plane.mk (c+(i:ℝ)*T) t ∉
        inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) := by
  obtain ⟨k,r,s,hrs,hr,hs,hJ,he,hvert,hgrid⟩ :=
    normalized_actual_line_select_all_grid_free_bigon G hG T c hT hp hc hfinite hcount
  let d := c+(k:ℝ)*T
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
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
  have hfiniteD : {t : ℝ | G t 0=d}.Finite := by
    have hsub : {t : ℝ | G t 0=d}⊆(fun t : ℝ => t+(k:ℝ)*T) '' {t : ℝ | G t 0=c} := by
      intro t ht
      refine ⟨t-(k:ℝ)*T,?_,by ring⟩
      have hh := congrArg (fun z : Plane => z 0) (hp k (t-(k:ℝ)*T))
      have heq : t-(k:ℝ)*T+(k:ℝ)*T=t := by ring
      rw [heq] at hh
      change G t 0=G (t-(k:ℝ)*T) 0+(k:ℝ)*T at hh
      change G t 0=d at ht
      dsimp [d] at ht
      change G (t-(k:ℝ)*T) 0=c
      linarith
    exact (hfinite.image _).subset hsub
  have hshort : s-r<T := by
    apply normalized_finite_fiber_slab_arc_short G T d r s hT hrs hp hr hs hfiniteD
    rcases hslab with hl|hr
    · exact Or.inl (fun t ht => hl (G t) (Or.inl ⟨t,ht,rfl⟩))
    · exact Or.inr (fun t ht => hr (G t) (Or.inl ⟨t,ht,rfl⟩))
  refine ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hgrid,
    full_lattice_separation_of_vertical_and_other_columns C hJ T hT hvert ?_⟩
  intro n hn
  apply disjoint_left.mpr
  rintro z hz ⟨w,hw,rfl⟩
  rcases hw with ⟨t,ht,rfl⟩ | hw
  · have hh : G t+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)=
        G (t+(n.1:ℝ)*T)+Plane.mk 0 ((n.2:ℝ)*T) := by
      rw [hp]
      ext q
      fin_cases q <;> simp [Plane.mk]
    apply disjoint_left.mp he hz
    exact mem_iUnion.mpr ⟨n.2,t+(n.1:ℝ)*T,hh.symm⟩
  · have hw0 : w 0=d := by
      rw [segment_eq_image_lineMap] at hw
      obtain ⟨t,ht,rfl⟩ := hw
      simp only [AffineMap.lineMap_apply]
      change t*(G s 0-G r 0)+G r 0=d
      rw [hr,hs]
      ring
    apply no (k+n.1) (w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) hz
    change w 0+(n.1:ℝ)*T=c+((k+n.1:ℤ):ℝ)*T
    rw [hw0]
    dsimp [d]
    push_cast
    ring

#print axioms normalized_actual_line_select_short_full_lattice_bigon
