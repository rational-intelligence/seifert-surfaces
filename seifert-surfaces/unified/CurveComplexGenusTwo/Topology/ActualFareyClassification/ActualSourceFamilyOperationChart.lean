import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFamilyIsolatedOperationChart

open Set Topology Schoenflies CurveComplex unitInterval

theorem normalized_actual_transverse_has_family_isolated_operation_chart
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
    ∃ phi : Plane ≃ₜ Plane,
      (phi '' Plane.closedSquare 0 1)∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      phi.symm (G a)∈modelCurve ∧ phi.symm (G b)∈modelCurve ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
          (phi '' Plane.closedSquare 0 1))) := by
  obtain ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,Phi,hcontact,hdeck⟩ :=
    normalized_actual_transverse_has_actual_closed_family_disk G hG T c hT hp hc hfinite hcount htrans
  obtain ⟨phi,_,hcontact',hInterior,haModel,hbModel,hdeck'⟩ :=
    normalized_actual_closed_family_disk_operation_chart G hG T a b hT (har.trans (hrs.trans hsb)) hp hc Phi hcontact hdeck
  exact ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hno,phi,hcontact',hInterior,haModel,hbModel,hdeck'⟩

#print axioms normalized_actual_transverse_has_family_isolated_operation_chart
