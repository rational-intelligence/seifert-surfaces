import ActualCollarCoreProductPastingV782

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations
noncomputable section
namespace CompressionActualCollarCoreProductEmbeddingV784

/-- Joint embedding follows from joint embedding of the two actual product
    patches and their exact cross-intersection, including the common level. -/
theorem pasted_product_embedding
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    (c : C(Circle × Time,X)) (r : Time)
    (out : C((Circle × Time) × Time,Y)) (core : C(X × Time,Y))
    (hout : InjOn out {p : (Circle × Time) × Time | p.1.2.val ≤ r.val})
    (hcore : Function.Injective core)
    (hcross : ∀ z s t p u,s.val ≤ r.val →
      p ∉ c '' {q : Circle × Time | q.2.val < r.val} →
      out ((z,s),t) = core (p,u) → p = c (z,s) ∧ u = t)
    (J : C(X × Time,Y))
    (hJout : ∀ z s t,s.val ≤ r.val → J (c (z,s),t) = out ((z,s),t))
    (hJcore : ∀ p t,p ∉ c '' {q : Circle × Time | q.2.val < r.val} → J (p,t) = core (p,t)) :
    IsEmbedding J := by
  let C : Set X := c '' {q : Circle × Time | q.2.val ≤ r.val}
  let O : Set X := c '' {q : Circle × Time | q.2.val < r.val}
  have hOC : O ⊆ C := by
    rintro x ⟨q,hq,rfl⟩
    refine ⟨q,?_,rfl⟩
    change q.2.val ≤ r.val
    change q.2.val < r.val at hq
    exact hq.le
  have hcross' (p q : X × Time) (hp : p.1 ∈ C) (hq : q.1 ∉ C)
      (he : J p = J q) : p = q := by
    obtain ⟨⟨z,s⟩,hs,hcs⟩ := hp
    have hqO : q.1 ∉ O := fun hx => hq (hOC hx)
    have he' : out ((z,s),p.2) = core (q.1,q.2) := by
      rw [← hJout z s p.2 hs,hcs]
      exact he.trans (hJcore q.1 q.2 hqO)
    obtain ⟨h₁,h₂⟩ := hcross z s p.2 q.1 q.2 hs hqO he'
    exact Prod.ext (hcs.symm.trans h₁.symm) h₂.symm
  have hJinj : Function.Injective J := by
    intro p q he
    by_cases hp : p.1 ∈ C
    · by_cases hq : q.1 ∈ C
      · obtain ⟨⟨z,s⟩,hs,hcs⟩ := hp
        obtain ⟨⟨w,v⟩,hv,hcv⟩ := hq
        have he' : out ((z,s),p.2) = out ((w,v),q.2) := by
          rw [← hJout z s p.2 hs,← hJout w v q.2 hv,hcs,hcv]
          exact he
        have hh := hout hs hv he'
        have hparam := congrArg (fun a : (Circle × Time) × Time => a.1) hh
        have htime := congrArg (fun a : (Circle × Time) × Time => a.2) hh
        exact Prod.ext (hcs.symm.trans ((congrArg c hparam).trans hcv)) htime
      · exact hcross' p q hp hq he
    · by_cases hq : q.1 ∈ C
      · exact (hcross' q p hq hp he.symm).symm
      · have hpO : p.1 ∉ O := fun hx => hp (hOC hx)
        have hqO : q.1 ∉ O := fun hx => hq (hOC hx)
        apply hcore
        exact (hJcore p.1 p.2 hpO).symm.trans (he.trans (hJcore q.1 q.2 hqO))
  exact (J.continuous.isClosedEmbedding hJinj).isEmbedding

end CompressionActualCollarCoreProductEmbeddingV784
