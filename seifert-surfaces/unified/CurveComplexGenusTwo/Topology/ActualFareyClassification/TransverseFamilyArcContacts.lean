import CurveComplexGenusTwo.Topology.ActualFareyClassification.TransverseArcContacts

open Set Topology Schoenflies Metric

/-- Actual normalized deck rows are locally separated. Therefore a transverse
fiber contact of the full family at an internal point of the original arc
cannot be a contact with the edge of a closed half-plane containing that arc. -/
theorem normalized_transverse_family_no_internal_halfplane_touch
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s t c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (ht : t∈Ioo r s) (htc : G t 0=c)
    (hside : (∀ u∈Icc r s, G u 0≤c) ∨ (∀ u∈Icc r s, c≤G u 0))
    (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (ht0 : ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
        ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) : False := by
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
  have hJ : IsClosed J :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hj
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let bad := (G '' (Ioo r s)ᶜ)∪J
  have hbad : IsClosed bad := (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJ
  have htbad : G t∉bad := by
    rintro (⟨u,hu,he⟩|hh)
    · exact hu (hG.injective he ▸ ht)
    · exact disjoint_left.mp hGJ ⟨t,rfl⟩ hh
  obtain ⟨hl,hr⟩ := actual_fiber_set_crossing_has_both_sides
    (⋃ j : ℤ,L j) (G t) c htc U V htU h hU hV ht0 haxes
    badᶜ hbad.isOpen_compl htbad
  have hnear (z : Plane) (hz : z∈badᶜ∩(⋃ j : ℤ,L j)) : ∃ u∈Icc r s, G u=z := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz.2
    have hj0 : j=0 := by
      by_contra hn
      exact hz.1 (Or.inr (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩))
    subst j
    rw [hL0] at hj
    obtain ⟨u,hu⟩ := hj
    refine ⟨u,?_,hu⟩
    have huI : u∈Ioo r s := by
      by_contra hn
      exact hz.1 (Or.inl ⟨u,hn,hu⟩)
    exact ⟨huI.1.le,huI.2.le⟩
  rcases hside with hleft|hright
  · obtain ⟨z,hz,hzc⟩ := hr
    obtain ⟨u,hu,rfl⟩ := hnear z hz
    exact not_lt_of_ge (hleft u hu) hzc
  · obtain ⟨z,hz,hzc⟩ := hl
    obtain ⟨u,hu,rfl⟩ := hnear z hz
    exact not_lt_of_ge (hright u hu) hzc

#print axioms normalized_transverse_family_no_internal_halfplane_touch
