import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualAttachedFamilyCollars

open Set Topology Schoenflies CurveComplex unitInterval

theorem normalized_actual_transverse_has_attached_family_isolated_support
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
    ∃ k : ℤ, ∃ r s : ℝ, r<s ∧ s-r<T ∧
      G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 0≠c+(i:ℝ)*T) ∧
    let K := closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
    let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
    ∃ a b rho sigma : ℝ, a<r ∧ s<b ∧ b-a<T ∧ 0<rho ∧ rho≤1 ∧ 0<sigma ∧ sigma≤1 ∧
    ∃ F : Plane ≃ₜ Plane, F (G r)=Plane.mk 1 0 ∧ F (G s)=Plane.mk (-1) 0 ∧
      F '' K=Plane.closedSquare 0 1 ∧
    ∃ E Q : I×Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧ IsEmbedding Q ∧ Disjoint (range E) (range Q) ∧
      (∀ w : Icc (-1:ℝ) 1, E (0,w)=F.symm (Plane.mk 1 (rho*w))) ∧
      (∀ w : Icc (-1:ℝ) 1, Q (0,w)=F.symm (Plane.mk (-1) (-sigma*w))) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩)=G (reparam r a t)) ∧
      (∀ t : I, Q (t,⟨0,by norm_num⟩)=G (reparam s b t)) ∧
      range E∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk 1 (rho*w))) '' univ ∧
      range Q∩K=(fun w : Icc (-1:ℝ) 1 => F.symm (Plane.mk (-1) (-sigma*w))) '' univ ∧
      ((K∪range E)∪range Q)∩L=G '' Icc a b ∧
      IsCompact ((K∪range E)∪range Q) ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint ((K∪range E)∪range Q)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ((K∪range E)∪range Q))) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hdeck,_,_⟩ :=
    normalized_actual_transverse_select_closed_deck_free_bigon G hG T c hT hp hc hfinite hcount htrans
  refine ⟨k,r,s,hrs,hshort,hr,hs,hno,?_⟩
  exact normalized_clean_bigon_has_actual_attached_family_collars G hG T r s hT hrs hshort hp hc hJ he hcontact hdeck

#print axioms normalized_actual_transverse_has_attached_family_isolated_support
