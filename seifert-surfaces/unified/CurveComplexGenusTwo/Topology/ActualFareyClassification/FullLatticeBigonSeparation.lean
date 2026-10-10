import CurveComplexGenusTwo.Topology.ActualFareyClassification.MinimumCompactGridBigon
import CurveComplexGenusTwo.Topology.TorusStrip.NestedBands

open Set Topology Schoenflies Bornology

/-- A nonzero first coordinate excludes nesting even for a mixed translation. -/
theorem bounded_ne_subset_mixed_translate
    (S : Set Plane) (hS : IsBounded S) (hne : S.Nonempty)
    (d : Plane) (hd : d 0≠0) : ¬ S ⊆ (Homeomorph.addRight d) '' S := by
  intro hsub
  let e := Homeomorph.addRight d
  have hcl : closure S ⊆ e '' closure S := by
    rw [e.image_closure]
    exact closure_mono hsub
  have hc := hS.isCompact_closure
  have hn : (closure S).Nonempty := hne.mono subset_closure
  rcases lt_or_gt_of_ne hd with hd | hd
  · obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn hn (EuclideanSpace.proj 0).continuous.continuousOn
    obtain ⟨y,hy,he⟩ := hcl hx
    have hxy : y 0≤x 0 := hmax hy
    have hh := congrArg (fun z : Plane => z 0) he
    change y 0+d 0=x 0 at hh
    linarith
  · obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn hn (EuclideanSpace.proj 0).continuous.continuousOn
    obtain ⟨y,hy,he⟩ := hcl hx
    have hxy : x 0≤y 0 := hmin hy
    have hh := congrArg (fun z : Plane => z 0) he
    change y 0+d 0=x 0 at hh
    linarith

theorem jordan_disk_mixed_translate_disjoint_of_boundary_avoidance
    (C : Set Plane) (hC : IsJordanCurve C) (d : Plane) (hd : d 0≠0)
    (havoid : Disjoint (inside C) ((Homeomorph.addRight d) '' C)) :
    Disjoint (inside C) (inside ((Homeomorph.addRight d) '' C)) := by
  let e := Homeomorph.addRight d
  have hD : IsJordanCurve (e '' C) := by
    obtain ⟨g,hg,hgC⟩ := hC
    refine ⟨e ∘ g,⟨e.continuous.comp_continuousOn hg.continuousOn,?_,?_⟩,?_⟩
    · simp only [Function.comp_apply,hg.closes]
    · exact e.injective.injOn.comp hg.injOn (mapsTo_univ _ _)
    · rw [image_comp,hgC]
  have hc := jordan_curve_theorem hC
  have hdisk := jordan_curve_theorem hD
  have hcover : inside C ⊆ inside (e '' C) ∪ outside (e '' C) := by
    rw [inside_union_outside]
    exact fun z hz h => disjoint_left.mp havoid hz h
  rcases hc.isConnected_inside.isPreconnected.subset_or_subset
    hdisk.isOpen_inside hdisk.isOpen_outside disjoint_inside_outside hcover with h | h
  · rw [← (plane_homeomorph_inside_transport e C).1] at h
    exact False.elim (bounded_ne_subset_mixed_translate _ hc.isBounded_inside
      hc.isConnected_inside.nonempty d hd h)
  · exact disjoint_left.mpr (fun z hz hz' => disjoint_left.mp disjoint_inside_outside hz' (h hz))

/-- The actual horizontal-column boundary avoidance combines with the
previously produced vertical separation to cover EVERY lattice translate. -/
theorem full_lattice_separation_of_vertical_and_other_columns
    (C : Set Plane) (hC : IsJordanCurve C) (T : ℝ) (hT : 0<T)
    (hvert : Pairwise (fun i j : ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk 0 ((i:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk 0 ((j:ℝ)*T)) '' C))))
    (hother : ∀ n : ℤ × ℤ, n.1≠0 → Disjoint (inside C)
      ((fun z : Plane => z+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) '' C)) :
    Pairwise (fun i j : ℤ × ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) '' C))) := by
  let Z := fun n : ℤ × ℤ => Homeomorph.addRight (Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T))
  have base (n : ℤ × ℤ) (hn : n≠0) : Disjoint (inside C) (inside (Z n '' C)) := by
    by_cases hn0 : n.1=0
    · have hn1 : n.2≠0 := by
        intro hh
        apply hn
        exact Prod.ext hn0 hh
      have hh := hvert (show (0:ℤ)≠n.2 from hn1.symm)
      have hzero : Plane.mk 0 0=(0:Plane) := by ext q; fin_cases q <;> rfl
      change Disjoint (inside C)
        (inside ((fun z : Plane => z+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) '' C))
      rw [hn0]
      simpa only [Int.cast_zero,zero_mul,hzero,add_zero,image_id'] using hh
    · apply jordan_disk_mixed_translate_disjoint_of_boundary_avoidance C hC
        (Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T))
        (mul_ne_zero (Int.cast_ne_zero.mpr hn0) hT.ne') (hother n hn0)
  have comp (i j : ℤ × ℤ) (S : Set Plane) : Z (i+j) '' S=Z i '' (Z j '' S) := by
    rw [← image_comp]
    congr 1
    funext z
    ext q
    fin_cases q <;> simp [Z,Plane.mk,Int.cast_add] <;> ring
  intro i j hij
  change Disjoint (inside (Z i '' C)) (inside (Z j '' C))
  rw [← (plane_homeomorph_inside_transport (Z i) C).1,
    ← (plane_homeomorph_inside_transport (Z j) C).1]
  have hj : j=i+(j-i) := by abel
  rw [hj,comp]
  have hb := base (j-i) (sub_ne_zero.mpr hij.symm)
  rw [← (plane_homeomorph_inside_transport (Z (j-i)) C).1] at hb
  exact (disjoint_image_iff (Z i).injective).mpr hb

/-- Full lattice open-disk separation is PRODUCED from normalized actual
source data, with no assumed disk separation, width bound, or empty support. -/
theorem normalized_actual_line_select_full_lattice_separated_bigon
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
      Pairwise (fun i j : ℤ × ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) := by
  obtain ⟨k,r,s,hrs,hr,hs,hJ,he,hvert,hgrid⟩ :=
    normalized_actual_line_select_horizontal_grid_free_bigon G hG T c hT hp hc hfinite hcount
  refine ⟨k,r,s,hrs,hr,hs,hJ,he,
    full_lattice_separation_of_vertical_and_other_columns _ hJ T hT hvert ?_⟩
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
  · have hw0 : w 0=c+(k:ℝ)*T := by
      rw [segment_eq_image_lineMap] at hw
      obtain ⟨t,ht,rfl⟩ := hw
      simp only [AffineMap.lineMap_apply]
      change t*(G s 0-G r 0)+G r 0=c+(k:ℝ)*T
      rw [hr,hs]
      ring
    have hn' : k+n.1≠k := by omega
    have hz0 : (w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) 0=c+((k+n.1:ℤ):ℝ)*T := by
      change w 0+(n.1:ℝ)*T=c+((k+n.1:ℤ):ℝ)*T
      rw [hw0,Int.cast_add]
      ring
    have hm : Plane.mk (c+((k+n.1:ℤ):ℝ)*T)
        ((w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) 1)=
        w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T) := by
      ext q
      fin_cases q
      · exact hz0.symm
      · rfl
    change (w+Plane.mk ((n.1:ℝ)*T) ((n.2:ℝ)*T)) ∈
      inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) at hz
    exact hgrid (k+n.1) hn' _ (hm.symm ▸ hz)

#print axioms bounded_ne_subset_mixed_translate
#print axioms jordan_disk_mixed_translate_disjoint_of_boundary_avoidance
#print axioms full_lattice_separation_of_vertical_and_other_columns
#print axioms normalized_actual_line_select_full_lattice_separated_bigon
