import ActualCollarCoreProductEmbeddingV784
import ActualUniformOuterCollarSeparationV785
import ActualVariableAnnulusOuterProductExactV788

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualWholeCollarCoreProductV789

theorem smaller_collar_open
    {X : Type} [TopologicalSpace X] (c : C(Circle × Time,X)) (hc : IsEmbedding c)
    (ho : IsOpen (c '' {p : Circle × Time | p.2.val < 1}))
    (r : Time) : IsOpen (c '' {p : Circle × Time | p.2.val < r.val}) := by
  have hs : IsOpen {p : Circle × Time | p.2.val < r.val} :=
    isOpen_lt continuous_snd.subtype_val continuous_const
  obtain ⟨V,hV,hEq⟩ := hc.isInducing.image_eq_isOpen_inter_range hs
  have hsub : c '' {p : Circle × Time | p.2.val < r.val} ⊆
      c '' {p : Circle × Time | p.2.val < 1} := by
    rintro x ⟨p,hp,rfl⟩
    exact ⟨p,hp.trans_le r.property.2,rfl⟩
  have heq : c '' {p : Circle × Time | p.2.val < r.val} =
      V ∩ (c '' {p : Circle × Time | p.2.val < 1}) := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨(hEq ▸ hx).1,hsub hx⟩
    · intro x hx
      rw [hEq]
      exact ⟨hx.1,image_subset_range _ _ hx.2⟩
  rw [heq]
  exact hV.inter ho

/-- The entire prescribed outer product is attached to the entire supplied
    disk core product. Global cross-intersection is derived from compact
    separation and the normal coordinate, with no missing core premise. -/
theorem whole_collar_core_product
    {X Y : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (c : C(Circle × Time,X)) (hc : IsEmbedding c)
    (ho : IsOpen (c '' {p : Circle × Time | p.2.val < 1}))
    (a : Time) (ha : 0 < a.val)
    (wide : C(Time × (Circle × Time),Y)) (hwide : IsEmbedding wide)
    (b : C(Circle × Time,Circle × Time)) (hb : IsEmbedding b)
    (H : C(Time × (Circle × Time),Circle × Time))
    (hH : ∀ s,IsEmbedding (fun p => H (s,p)))
    (hH0 : ∀ p,H (0,p) = b p) (hH1 : ∀ p,H (1,p) = p)
    (hHcore : ∀ s z,H (s,(z,middleTime)) = (z,middleTime))
    (core : C(X × Time,Y)) (hcore : IsEmbedding core)
    (hcollar : ∀ z s t,s.val ≤ a.val → core (c (z,s),t) = wide (s,b (z,t)))
    (hfar : ∀ p,p ∉ c '' {q : Circle × Time | q.2.val < a.val} →
      ∀ t z,core (p,t) ≠ wide (0,z)) :
    ∃ r : Time,0 < r.val ∧ r.val < a.val ∧
      ∃ J : C(X × Time,Y),IsEmbedding J ∧
        (∀ z t,J (c (z,0),t) = wide (0,(z,t))) ∧
        (∀ p t,p ∉ c '' {q : Circle × Time | q.2.val < r.val} → J (p,t) = core (p,t)) ∧
        ∀ z s,s.val ≤ r.val → J (c (z,s),middleTime) = wide (s,(z,middleTime)) := by
  classical
  let F : Set X := (c '' {q : Circle × Time | q.2.val < a.val})ᶜ
  have hF : IsCompact F := (smaller_collar_open c hc ho a).isClosed_compl.isCompact
  let K : Set Y := core '' (F ×ˢ (univ:Set Time))
  have hK : IsClosed K := ((hF.prod isCompact_univ).image core.continuous).isClosed
  have hz (z : Circle × Time) : wide (0,z) ∉ K := by
    rintro ⟨⟨p,t⟩,⟨hp,ht⟩,he⟩
    exact hfar p hp t z he
  obtain ⟨ρ,hρ,hsep⟩ :=
    CompressionActualUniformOuterCollarSeparationV785.uniform_outer_collar_separation wide K hK hz
  let rv : ℝ := min ρ.val (a.val/2)
  have hrv : 0 < rv := lt_min hρ (half_pos ha)
  have hrva : rv < a.val := (min_le_right _ _).trans_lt (half_lt_self ha)
  have hrvρ : rv ≤ ρ.val := min_le_left _ _
  let r : Time := ⟨rv,hrv.le,(hrva.le.trans a.property.2)⟩
  obtain ⟨out,houtval,hout,hout0,houtr,houtcore⟩ :=
    CompressionActualVariableAnnulusOuterProductExactV788.variable_annulus_outer_product_exact
      wide hwide H hH hH1 hHcore r hrv
  have hmatch (z : Circle) (t : Time) : out ((z,r),t) = core (c (z,r),t) := by
    rw [houtr,hH0,hcollar z r t hrva.le]
  obtain ⟨J,hJout,hJcore⟩ :=
    CompressionActualCollarCoreProductPastingV782.collar_core_product_pasting c hc r
      (smaller_collar_open c hc ho r) out core hmatch
  have hcross (z : Circle) (s t : Time) (p : X) (u : Time) (hs : s.val ≤ r.val)
      (hp : p ∉ c '' {q : Circle × Time | q.2.val < r.val})
      (he : out ((z,s),t) = core (p,u)) : p = c (z,s) ∧ u = t := by
    have hpF : p ∉ F := by
      intro hf
      have hk : core (p,u) ∈ K := ⟨(p,u),⟨hf,mem_univ u⟩,rfl⟩
      rw [← he,houtval] at hk
      exact hsep s _ (hs.trans hrvρ) hk
    have hpnear : p ∈ c '' {q : Circle × Time | q.2.val < a.val} := not_not.mp hpF
    obtain ⟨⟨w,v⟩,hv,hcv⟩ := hpnear
    have he' : wide (s,H (Set.projIcc 0 1 zero_le_one (1-s.val/r.val),(z,t))) =
        wide (v,b (w,u)) := by
      rw [← houtval,← hcollar w v u hv.le,hcv]
      exact he
    have hh := hwide.injective he'
    have hsv := congrArg (fun q : Time × (Circle × Time) => q.1) hh
    have hbval := congrArg (fun q : Time × (Circle × Time) => q.2) hh
    change s = v at hsv
    have hvr : r.val ≤ v.val := by
      apply le_of_not_gt
      intro hlt
      exact hp ⟨(w,v),hlt,hcv⟩
    have hsr : s = r := Subtype.ext (le_antisymm hs (by rwa [hsv]))
    have hproj : Set.projIcc 0 1 zero_le_one (1-s.val/r.val) = (0:Time) := by
      rw [hsr,div_self hrv.ne']
      norm_num
    change H (Set.projIcc 0 1 zero_le_one (1-s.val/r.val),(z,t)) = b (w,u) at hbval
    rw [hproj,hH0] at hbval
    have hwu := hb.injective hbval
    obtain ⟨hzw,htu⟩ := Prod.mk.inj hwu
    refine ⟨?_,htu.symm⟩
    rw [← hcv,← hzw,← hsv]
  have hJ : IsEmbedding J :=
    CompressionActualCollarCoreProductEmbeddingV784.pasted_product_embedding c r out core
      (fun _ _ _ _ he => hout.injective he) hcore.injective hcross J hJout hJcore
  refine ⟨r,hrv,hrva,J,hJ,?_,hJcore,?_⟩
  · intro z t
    rw [hJout z 0 t (by change (0:ℝ) ≤ rv; exact hrv.le),hout0]
  · intro z s hs
    rw [hJout z s middleTime hs,houtcore]

end CompressionActualWholeCollarCoreProductV789
