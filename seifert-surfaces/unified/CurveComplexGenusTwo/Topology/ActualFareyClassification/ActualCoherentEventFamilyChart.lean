import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualAttachedFamilyCollarsInOpen
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFamilyOperationChartInOpen
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualBigonEventGap
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTwoPortDiskChart

open Set Topology Schoenflies CurveComplex unitInterval

theorem normalized_actual_transverse_has_coherent_event_family_chart
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
      IsJordanCurve ((G '' Icc r s)∪segment ℝ (G r) (G s)) ∧
      Disjoint (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ∧
      segment ℝ (G r) (G s)∩(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s} ∧
      ((∀ t∈Icc r s, G t 0 ≤ c+(k:ℝ)*T) ∨ (∀ t∈Icc r s, c+(k:ℝ)*T ≤ G t 0)) ∧
      (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={G r,G s} ∧
    ∃ phi : Plane ≃ₜ Plane,
      (phi '' Plane.closedSquare 0 1)∩(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      phi.symm (G a)∈modelCurve ∧ phi.symm (G b)∈modelCurve ∧
      segment ℝ (G r) (G s)⊆phi '' Plane.openSquare 0 1 ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.closedSquare 0 1))) := by
  obtain ⟨k,r,s,hrs,hshort,hr,hs,hJ,he,hno,hcontact,hclosed,hsep,hslab⟩ :=
    normalized_actual_transverse_select_closed_deck_free_bigon G hG T c hT hp hc hfinite hcount htrans
  obtain ⟨a0,b0,ha0,hb0,hwidth,hgap⟩ :=
    normalized_clean_bigon_has_actual_enlarged_two_event_interval G hG T c r s hT hrs hshort hp hfinite hno
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  obtain ⟨hclosedRows,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  change Pairwise (fun i j => Disjoint (L i) (L j)) at hpair
  have hL0 : L 0=range G := by
    have hh : (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=G := by
      funext x
      ext k
      fin_cases k <;> simp [Plane.mk]
    change range (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=range G
    rw [hh]
  let J := ⋃ j : {j : ℤ // j≠0}, L j.val
  have hJclosed : IsClosed J :=
    (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosedRows j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hj
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let W := ((G '' (Ioo a0 b0)ᶜ)∪J)ᶜ
  have hW : IsOpen W := ((hG.isClosedMap _ isOpen_Ioo.isClosed_compl).union hJclosed).isOpen_compl
  have hGL : range G⊆(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) := by
    rintro z ⟨t,rfl⟩
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i
    fin_cases i <;> simp [Plane.mk]
  let K := closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
  have hKL : K∩(⋃ j : ℤ,L j)=G '' Icc r s :=
    clean_empty_bigon_closed_disk_family_contact G r s hrs _ hGL hJ he hcontact
  have hKW : K⊆W := by
    intro z hz
    rintro (⟨t,ht,htz⟩|hzJ)
    · have hzL := hGL ⟨t,htz⟩
      obtain ⟨u,hu,huZ⟩ := hKL ▸ (show z∈K∩(⋃ j : ℤ,L j) from ⟨hz,hzL⟩)
      have hut := hG.injective (huZ.trans htz.symm)
      subst t
      exact ht ⟨lt_of_lt_of_le ha0 hu.1,lt_of_le_of_lt hu.2 hb0⟩
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hzJ
      obtain ⟨u,hu,huZ⟩ := hKL ▸ (show z∈K∩(⋃ j : ℤ,L j) from ⟨hz,mem_iUnion.mpr ⟨j.val,hj⟩⟩)
      exact disjoint_left.mp hGJ ⟨u,huZ⟩ hzJ
  obtain ⟨a,b,rho,sigma,har,hsb,hba,hrho,hrho1,hsigma,hsigma1,
    F,hrF,hsF,hFK,E,Q,hE,hQ,hEQ,hEport,hQport,hEcenter,hQcenter,hEK,hQK,hfamily,hSW,_,hdeck⟩ :=
    normalized_clean_bigon_has_attached_family_collars_in_open G hG T r s hT hrs hshort hp hc
      hJ he hcontact W hW hKW hclosed
  obtain ⟨Phi,hPhi⟩ := actual_two_attached_half_collars_disk_chart _ F hFK rho sigma hrho hrho1 hsigma hsigma1
    E Q hE hQ hEQ hEport hQport hEK hQK
  have hPhiW : Phi '' Plane.closedSquare 0 1⊆W := by rwa [hPhi]
  have hPhiFamily : (Phi '' Plane.closedSquare 0 1)∩(⋃ j : ℤ,L j)=G '' Icc a b := by rwa [hPhi]
  have hPhiDeck : ∀ i : ℤ×ℤ, i≠0 → Disjoint (Phi '' Plane.closedSquare 0 1)
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (Phi '' Plane.closedSquare 0 1)) := by
    rwa [hPhi]
  obtain ⟨phi,hcontain,hphiW,hwhole,hphiFamily,hAi,haBoundary,hbBoundary,hphiDeck⟩ :=
    normalized_actual_family_disk_operation_chart_in_open G hG T a b hT (lt_trans har (lt_trans hrs hsb)) hp hc
      Phi hPhiFamily W hW hPhiW hPhiDeck
  have hGaS : G a∈Phi '' Plane.closedSquare 0 1 :=
    (show G a∈(Phi '' Plane.closedSquare 0 1)∩(⋃ j : ℤ,L j) from
      hPhiFamily.symm ▸ ⟨a,⟨le_rfl,(lt_trans har (lt_trans hrs hsb)).le⟩,rfl⟩).1
  have hGbS : G b∈Phi '' Plane.closedSquare 0 1 :=
    (show G b∈(Phi '' Plane.closedSquare 0 1)∩(⋃ j : ℤ,L j) from
      hPhiFamily.symm ▸ ⟨b,⟨(lt_trans har (lt_trans hrs hsb)).le,le_rfl⟩,rfl⟩).1
  have haI : a∈Ioo a0 b0 := by
    by_contra hn
    exact hPhiW hGaS (Or.inl ⟨a,hn,rfl⟩)
  have hbI : b∈Ioo a0 b0 := by
    by_contra hn
    exact hPhiW hGbS (Or.inl ⟨b,hn,rfl⟩)
  have hold : (G '' Icc a b)∩{z : Plane | ∃ i : ℤ, z 0=c+(i:ℝ)*T}={G r,G s} := by
    apply subset_antisymm
    · rintro z ⟨⟨t,ht,rfl⟩,hz⟩
      rcases hgap t ⟨haI.1.le.trans ht.1,ht.2.trans hbI.2.le⟩ hz with htr|hts
      · exact Or.inl (congrArg G htr)
      · exact Or.inr (congrArg G hts)
    · intro z hz
      rcases hz with hz|hz
      · subst z; exact ⟨⟨r,⟨har.le,hrs.le.trans hsb.le⟩,rfl⟩,⟨k,hr⟩⟩
      · have hz' : z=G s := hz
        subst z; exact ⟨⟨s,⟨har.le.trans hrs.le,hsb.le⟩,rfl⟩,⟨k,hs⟩⟩
  have hFKsub : segment ℝ (G r) (G s)⊆K := by
    intro z hz
    apply frontier_subset_closure
    rw [(jordan_curve_theorem hJ).frontier_inside]
    exact Or.inr hz
  have hFiberInterior : segment ℝ (G r) (G s)⊆phi '' Plane.openSquare 0 1 := by
    intro z hz
    apply hwhole
    refine ⟨?_,?_⟩
    · rw [hPhi]; exact Or.inl (Or.inl (hFKsub hz))
    · intro hzEnd
      have hzL : z∈⋃ j : ℤ,L j := by
        rcases hzEnd with hzEnd|hzEnd
        · exact hGL ⟨a,hzEnd.symm⟩
        · exact hGL ⟨b,(show z=G b from hzEnd).symm⟩
      have hzRoot : z∈({G r,G s} : Set Plane) := hcontact ▸ ⟨hz,hzL⟩
      rcases hzEnd with hza|hzb <;> rcases hzRoot with hzr|hzs
      · have hh := hG.injective (hza.symm.trans hzr); linarith
      · have hh := hG.injective (hza.symm.trans (show z=G s from hzs)); linarith
      · have hh := hG.injective ((show z=G b from hzb).symm.trans hzr); linarith
      · have hh := hG.injective ((show z=G b from hzb).symm.trans (show z=G s from hzs)); linarith
  refine ⟨k,r,s,a,b,hrs,har,hsb,hba,hr,hs,hJ,he,hcontact,?_,hold,phi,hphiFamily,hAi,haBoundary,hbBoundary,hFiberInterior,hphiDeck⟩
  rcases hslab with hl|hr'
  · exact Or.inl (fun t ht => (hl (G t) (Or.inl ⟨t,ht,rfl⟩)).2)
  · exact Or.inr (fun t ht => (hr' (G t) (Or.inl ⟨t,ht,rfl⟩)).1)

#print axioms normalized_actual_transverse_has_coherent_event_family_chart
