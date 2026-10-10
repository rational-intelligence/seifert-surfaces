import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualClosedBigonProducer

open Set Topology Schoenflies Metric

/-- The actual empty clean closed Jordan disk meets the entire lifted family
exactly in its curve side. This includes the straight side's corners. -/
theorem clean_empty_bigon_closed_disk_family_contact
    (G : C(ℝ,Plane)) (r s : ℝ) (hrs : r<s) (L : Set Plane)
    (hGL : range G⊆L)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hcontact : segment ℝ (G r) (G s)∩L={G r,G s}) :
    closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))∩L=G '' Icc r s := by
  rw [closure_eq_self_union_frontier,(jordan_curve_theorem hJ).frontier_inside]
  ext z
  constructor
  · rintro ⟨hz,hzL⟩
    rcases hz with hz|hz
    · exact False.elim (disjoint_left.mp he hz hzL)
    · rcases hz with hz|hz
      · exact hz
      · have hh := hcontact ▸ (show z∈segment ℝ (G r) (G s)∩L from ⟨hz,hzL⟩)
        rcases hh with hh|hh
        · rw [hh]; exact ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩
        · rw [mem_singleton_iff.mp hh]; exact ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩
  · intro hz
    exact ⟨Or.inr (Or.inl hz),hGL (image_subset_range G _ hz)⟩

/-- A CLEAN actual whole closed bigon, rather than only its curve side,
produces an enlarged compact full-lattice-separated operation neighborhood
isolated from all lifted-family tails. The forbidden tails are actual closed
sets derived from properness and normalized deck-row local finiteness. -/
theorem clean_normalized_closed_bigon_enlarged_uniform_support
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))))
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (hdeck : ∀ i : ℤ×ℤ, i≠0 → Disjoint
      (closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧
      ∃ U V : Set Plane, IsOpen U ∧
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))⊆U ∧
        closure U⊆V ∧ IsCompact V ∧
        V∩(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))⊆G '' Ioo a b ∧
        (∀ i : ℤ×ℤ, i≠0 → Disjoint V
          ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' V)) := by
  let e := (T-(s-r))/4
  let a := r-e
  let b := s+e
  have hepos : 0<e := by dsimp [e]; linarith
  have har : a<r := by dsimp [a]; linarith
  have hsb : s<b := by dsimp [b]; linarith
  have hba : b-a<T := by dsimp [a,b,e]; linarith
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  change Pairwise (fun i j => Disjoint (L i) (L j)) at hpair
  have hL0 : L 0=range G := by
    have hh : (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=G := by
      funext x
      ext k
      fin_cases k <;> simp [Plane.mk]
    change range (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=range G
    rw [hh]
  let J := ⋃ j : {j : ℤ // j≠0}, L j.val
  have hJclosed : IsClosed J :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hj
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let K := closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
  have hK : IsCompact K := (jordan_curve_theorem hJ).isBounded_inside.isCompact_closure
  let bad := (G '' (Ioo a b)ᶜ)∪J
  have hbad : IsClosed bad := (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJclosed
  have hGL : range G⊆⋃ j : ℤ,L j := by
    intro z hz
    exact mem_iUnion.mpr ⟨0,hL0.symm ▸ hz⟩
  have hKL : K∩(⋃ j : ℤ,L j)=G '' Icc r s :=
    clean_empty_bigon_closed_disk_family_contact G r s hrs _ hGL hJ he hcontact
  have hKbad : Disjoint K bad := by
    apply disjoint_left.mpr
    intro z hz hzb
    rcases hzb with ⟨u,hu,heq⟩|hzJ
    · have hzG : z∈range G := ⟨u,heq⟩
      have hcore : z∈G '' Icc r s := hKL ▸ ⟨hz,hGL hzG⟩
      obtain ⟨v,hv,hev⟩ := hcore
      have huv := hG.injective (heq.trans hev.symm)
      subst u
      exact hu ⟨lt_of_lt_of_le har hv.1,lt_of_le_of_lt hv.2 hsb⟩
    · have hzL : z∈⋃ j : ℤ,L j := by
        obtain ⟨j,hj⟩ := mem_iUnion.mp hzJ
        exact mem_iUnion.mpr ⟨j.val,hj⟩
      have hcore : z∈G '' Icc r s := hKL ▸ ⟨hz,hzL⟩
      exact disjoint_left.mp hGJ (image_subset_range G _ hcore) hzJ
  obtain ⟨U,V,hU,hKU,hUV,hV,hVbad,hVD⟩ :=
    compact_deck_free_marked_uniform_support K bad hK hbad hKbad T hT hdeck
  refine ⟨a,b,har,hsb,hba,U,V,hU,hKU,hUV,hV,?_,hVD⟩
  rintro z ⟨hzV,hzL⟩
  change z∈⋃ j : ℤ,L j at hzL
  obtain ⟨j,hj⟩ := mem_iUnion.mp hzL
  have hj0 : j=0 := by
    by_contra hn
    exact disjoint_left.mp hVbad hzV (Or.inr (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩))
  subst j
  rw [hL0] at hj
  obtain ⟨u,hu⟩ := hj
  refine ⟨u,?_,hu⟩
  by_contra hn
  exact disjoint_left.mp hVbad hzV (Or.inl ⟨u,hn,hu⟩)

#print axioms clean_empty_bigon_closed_disk_family_contact
#print axioms clean_normalized_closed_bigon_enlarged_uniform_support
