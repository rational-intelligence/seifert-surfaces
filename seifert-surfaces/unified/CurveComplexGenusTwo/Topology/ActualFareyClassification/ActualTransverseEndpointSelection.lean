import CurveComplexGenusTwo.Topology.ActualFareyClassification.TransverseFamilyArcContacts

open Set Topology Schoenflies Metric

/-- A genuine family crossing produces actual points on the original source
line on both sides, arbitrarily near its actual parameter and geometric point. -/
theorem normalized_transverse_family_has_both_sides_near_parameter
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T t c d : ℝ) (hT : 0<T) (hd : 0<d)
    (hp : ∀ (k : ℤ) (u : ℝ), G (u+(k:ℝ)*T)=G u+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (htc : G t 0=c)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (ht0 : ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
        ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))
    (N : Set Plane) (hN : IsOpen N) (htN : G t∈N) :
    (∃ a∈Ioo (t-d) (t+d), G a∈N ∧ G a 0<c) ∧
    (∃ b∈Ioo (t-d) (t+d), G b∈N ∧ c<G b 0) := by
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
  let bad := (G '' (Ioo (t-d) (t+d))ᶜ)∪J
  have hbad : IsClosed bad := (hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJ
  have htbad : G t∉bad := by
    rintro (⟨u,hu,he⟩|hh)
    · have hut := hG.injective he
      subst u
      exact hu ⟨by linarith,by linarith⟩
    · exact disjoint_left.mp hGJ ⟨t,rfl⟩ hh
  obtain ⟨hl,hr⟩ := actual_fiber_set_crossing_has_both_sides
    (⋃ j : ℤ,L j) (G t) c htc U V htU h hU hV ht0 haxes
    (N∩badᶜ) (hN.inter hbad.isOpen_compl) ⟨htN,htbad⟩
  have hnear (z : Plane) (hz : z∈(N∩badᶜ)∩(⋃ j : ℤ,L j)) :
      ∃ u∈Ioo (t-d) (t+d), G u=z ∧ G u∈N := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz.2
    have hj0 : j=0 := by
      by_contra hn
      exact hz.1.2 (Or.inr (mem_iUnion.mpr ⟨⟨j,hn⟩,hj⟩))
    subst j
    rw [hL0] at hj
    obtain ⟨u,hu⟩ := hj
    refine ⟨u,?_,hu,hu.symm ▸ hz.1.1⟩
    by_contra hn
    exact hz.1.2 (Or.inl ⟨u,hn,hu⟩)
  constructor
  · obtain ⟨z,hz,hzc⟩ := hl
    obtain ⟨u,hu,he,hN⟩ := hnear z hz
    exact ⟨u,hu,hN,he.symm ▸ hzc⟩
  · obtain ⟨z,hz,hzc⟩ := hr
    obtain ⟨u,hu,he,hN⟩ := hnear z hz
    exact ⟨u,hu,hN,he.symm ▸ hzc⟩

#print axioms normalized_transverse_family_has_both_sides_near_parameter
