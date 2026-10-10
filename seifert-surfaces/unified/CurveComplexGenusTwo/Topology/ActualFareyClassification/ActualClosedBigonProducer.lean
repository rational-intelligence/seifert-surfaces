import CurveComplexGenusTwo.Topology.ActualFareyClassification.CleanBigonClosedSupport

open Set Topology Schoenflies Metric

theorem normalized_actual_transverse_select_closed_deck_free_bigon
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
      (∀ i : ℤ×ℤ, i≠0 → Disjoint
        (closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      Pairwise (fun i j : ℤ×ℤ => Disjoint
        (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
        (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
          ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))) ∧
      ((∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T-T≤z 0 ∧ z 0≤c+(k:ℝ)*T) ∨
        (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s),
          c+(k:ℝ)*T≤z 0 ∧ z 0≤c+(k:ℝ)*T+T)) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hsep,hslab⟩ :=
    normalized_actual_transverse_select_clean_short_bigon G hG T c hT hp hc hfinite hcount htrans
  have hclosed := clean_normalized_bigon_closed_disk_deck_free G hG T r s (c+(k:ℝ)*T)
    hT hrs hshort hr hs hp hc hcontact hJ hsep
  exact ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hclosed,hsep,hslab⟩

#print axioms normalized_actual_transverse_select_closed_deck_free_bigon
