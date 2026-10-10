import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTwoPortDiskChart

open Set Topology Schoenflies CurveComplex unitInterval

theorem normalized_actual_transverse_has_actual_closed_family_disk
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
    ∃ k : ℤ, ∃ r s a b : ℝ, r<s ∧ a<r ∧ s<b ∧ b-a<T ∧
      G r 0=c+(k:ℝ)*T ∧ G s 0=c+(k:ℝ)*T ∧
      (∀ i : ℤ, ∀ t∈Ioo r s, G t 0≠c+(i:ℝ)*T) ∧
    ∃ Phi : Plane ≃ₜ Plane,
      (Phi '' Plane.closedSquare 0 1)∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (Phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          (Phi '' Plane.closedSquare 0 1))) := by
  obtain ⟨k,r,s,hrs,_,hr,hs,hno,a,b,rho,sigma,har,hsb,hba,hrho,hrho1,hsigma,hsigma1,
    F,hrF,hsF,hFK,E,Q,hE,hQ,hEQ,hEport,hQport,hEcenter,hQcenter,hEK,hQK,hcontact,_,hdeck⟩ :=
    normalized_actual_transverse_has_attached_family_isolated_support G hG T c hT hp hc hfinite hcount htrans
  obtain ⟨Phi,hPhi⟩ := actual_two_attached_half_collars_disk_chart _ F hFK rho sigma hrho hrho1 hsigma hsigma1
    E Q hE hQ hEQ hEport hQport hEK hQK
  refine ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,Phi,?_,?_⟩
  · rwa [hPhi]
  · rwa [hPhi]

#print axioms normalized_actual_transverse_has_actual_closed_family_disk
