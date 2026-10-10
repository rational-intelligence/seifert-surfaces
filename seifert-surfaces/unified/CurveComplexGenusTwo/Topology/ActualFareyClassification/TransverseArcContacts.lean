import CurveComplexGenusTwo.Topology.ActualFareyClassification.TransverseFiberBoundaryContacts

open Set Topology Schoenflies Metric

/-- A proper line's compact internal arc lies in one closed half-plane. At
an internal parameter it cannot have a genuine common-axis crossing with the
bounding fiber; the actual distant tails are removed using properness. -/
theorem transverse_fiber_cannot_touch_internal_one_sided_arc
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (r s t c : ℝ)
    (ht : t∈Ioo r s) (htc : G t 0=c)
    (hside : (∀ u∈Icc r s, G u 0≤c) ∨ (∀ u∈Icc r s, c≤G u 0))
    (U : Set Plane) (V : Set (ℝ×ℝ)) (htU : G t∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (ht0 : ((h ⟨G t,htU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 0=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈range G ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) : False := by
  let bad := G '' (Ioo r s)ᶜ
  have hbad : IsClosed bad := hG.isClosedMap _ isOpen_Ioo.isClosed_compl
  have htbad : G t∉bad := by
    rintro ⟨u,hu,he⟩
    exact hu (hG.injective he ▸ ht)
  obtain ⟨hl,hr⟩ := actual_fiber_set_crossing_has_both_sides (range G) (G t) c htc U V htU h hU hV ht0 haxes
    badᶜ hbad.isOpen_compl htbad
  have hnear (z : Plane) (hz : z∈badᶜ∩range G) : ∃ u∈Icc r s, G u=z := by
    obtain ⟨u,hu⟩ := hz.2
    refine ⟨u,?_,hu⟩
    have huI : u∈Ioo r s := by
      by_contra hn
      exact hz.1 ⟨u,hn,hu⟩
    exact ⟨huI.1.le,huI.2.le⟩
  rcases hside with hleft|hright
  · obtain ⟨z,hz,hzc⟩ := hr
    obtain ⟨u,hu,rfl⟩ := hnear z hz
    exact not_lt_of_ge (hleft u hu) hzc
  · obtain ⟨z,hz,hzc⟩ := hl
    obtain ⟨u,hu,rfl⟩ := hnear z hz
    exact not_lt_of_ge (hright u hu) hzc

#print axioms transverse_fiber_cannot_touch_internal_one_sided_arc
