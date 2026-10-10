import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingEssential
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter

namespace CurveComplex.LocalSurgery

/-- The first return along an actual finite transverse curve is an embedded
arc whose interior misses the other curve. Closing it along the second curve
produces a genuine compact embedded surgical boundary. No disk or
nonseparating property of this new boundary is assumed or claimed. -/
theorem source_two_curve_first_return_boundary {S : Type*} [TopologicalSpace S] [T2Space S]
    (a b : Curve S) (ht : Transverse a b)
    (u v : S) (hu : u ∈ a.image ∩ b.image) (hv : v ∈ a.image ∩ b.image) (huv : u ≠ v) :
    ∃ w : S, u ≠ w ∧ w ∈ a.image ∩ b.image ∧
      ∃ f g : C(Interval,S),
        Topology.IsEmbedding f ∧ Topology.IsEmbedding g ∧
        f 0 = u ∧ g 0 = u ∧ f 1 = w ∧ g 1 = w ∧
        Set.range f ⊆ a.image ∧ Set.range g ⊆ b.image ∧
        (∀ t : Interval, t ≠ 0 → t ≠ 1 → f t ∉ b.image) ∧
        Set.range f ∩ Set.range g = {u,w} ∧
        ∃ c : Curve S, c.image = Set.range f ∪ Set.range g ∧ IsCompact c.image := by
  have curveArc (c : Curve S) {x z : S} (hx : x ∈ c.image) (hz : z ∈ c.image)
      (hxz : x ≠ z) : ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
        f 0 = x ∧ f 1 = z ∧ Set.range f ⊆ c.image := by
    obtain ⟨s,rfl⟩ := hx
    obtain ⟨t,rfl⟩ := hz
    have hst : s ≠ t := fun h => hxz (congrArg c.map h)
    let f : C(Interval,S) := ⟨c.map ∘ Circle.path s t,
      c.embedded.continuous.comp (Circle.path s t).continuous⟩
    have hfi : Function.Injective f := c.embedded.injective.comp (Circle.path_injective_of_ne hst)
    refine ⟨f,(f.continuous.isClosedEmbedding hfi).isEmbedding,?_,?_,?_⟩
    · exact congrArg c.map (Circle.path s t).source
    · exact congrArg c.map (Circle.path s t).target
    · rintro z ⟨x,rfl⟩
      exact ⟨Circle.path s t x,rfl⟩
  obtain ⟨p,hp,hp0,hp1,hpa⟩ := curveArc a hu.1 hv.1 huv
  let bad : Set Interval := {t | t ≠ 0 ∧ p t ∈ b.image}
  have hbfinite : bad.Finite := by
    apply (ht.1.preimage hp.injective.injOn).subset
    intro t ht
    exact ⟨hpa ⟨t,rfl⟩,ht.2⟩
  have hbne : bad.Nonempty := by
    refine ⟨1,by norm_num,?_⟩
    simpa only [hp1] using hv.2
  obtain ⟨τ,hτ,hmin⟩ := Set.exists_min_image bad (fun t : Interval => t.val) hbfinite hbne
  have hτpos : 0 < τ.val := lt_of_le_of_ne τ.property.1 (by
    intro h
    exact hτ.1 (Subtype.ext h.symm))
  let φ : Interval → Interval := fun t => ⟨τ.val*t.val,⟨mul_nonneg τ.property.1 t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 τ.property.1).trans (by simpa using τ.property.2)⟩⟩
  have hφc : Continuous φ := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have hφi : Function.Injective φ := by
    intro s t h
    apply Subtype.ext
    exact (mul_left_cancel₀ (ne_of_gt hτpos)) (congrArg Subtype.val h)
  have hφ0 : φ 0 = 0 := Subtype.ext (by simp [φ])
  have hφ1 : φ 1 = τ := Subtype.ext (by simp [φ])
  let f : C(Interval,S) := ⟨p ∘ φ,p.continuous.comp hφc⟩
  have hfi : Function.Injective f := hp.injective.comp hφi
  have hf0 : f 0 = u := by change p (φ 0) = u; rw [hφ0,hp0]
  have hf1 : f 1 = p τ := by change p (φ 1) = p τ; rw [hφ1]
  have huw : u ≠ p τ := by
    intro h
    exact hτ.1 (hp.injective (h.symm.trans hp0.symm))
  have hw : p τ ∈ a.image ∩ b.image := ⟨hpa ⟨τ,rfl⟩,hτ.2⟩
  have hfavoid (t : Interval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) : f t ∉ b.image := by
    intro htb
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (by
      intro h; exact ht0 (Subtype.ext h.symm))
    have htlt : t.val < 1 := lt_of_le_of_ne t.property.2 (by
      intro h; exact ht1 (Subtype.ext h))
    have hφbad : φ t ∈ bad := by
      refine ⟨?_,htb⟩
      intro h
      have hz : τ.val*t.val = 0 := congrArg Subtype.val h
      exact (ne_of_gt (mul_pos hτpos htpos)) hz
    have hle := hmin (φ t) hφbad
    change τ.val ≤ τ.val*t.val at hle
    nlinarith
  obtain ⟨g,hg,hg0,hg1,hgb⟩ := curveArc b hu.2 hw.2 huw
  have hcross (s t : Interval) (heq : f s = g t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    by_cases hs0 : s = 0
    · left
      refine ⟨hs0,?_⟩
      apply hg.injective
      rw [← heq,hs0,hf0,hg0]
    · have hs1 : s = 1 := by
        by_contra hs1
        exact hfavoid s hs0 hs1 (heq ▸ hgb ⟨t,rfl⟩)
      right
      refine ⟨hs1,?_⟩
      apply hg.injective
      rw [← heq,hs1,hf1,hg1]
  have hmeet : Set.range f ∩ Set.range g = {u,p τ} := by
    ext z
    constructor
    · rintro ⟨⟨s,rfl⟩,⟨t,ht⟩⟩
      rcases hcross s t ht.symm with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · simp [hf0]
      · simp [hf1]
    · intro hz
      rcases hz with hz | hz
      · subst z
        exact ⟨⟨0,hf0⟩,⟨0,hg0⟩⟩
      · have hz' : z = p τ := hz
        subst z
        exact ⟨⟨1,hf1⟩,⟨1,hg1⟩⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hfi hg.injective
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcross
  refine ⟨p τ,huw,hw,f,g,(f.continuous.isClosedEmbedding hfi).isEmbedding,hg,
    hf0,hg0,hf1,hg1,?_,hgb,hfavoid,hmeet,c,hc,?_⟩
  · rintro z ⟨t,rfl⟩
    exact hpa ⟨φ t,rfl⟩
  · exact isCompact_range c.embedded.continuous


end CurveComplex.LocalSurgery

#print axioms CurveComplex.LocalSurgery.source_two_curve_first_return_boundary
