import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualRightWhiskerFamilyCollar
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualWhiskerNeighborhood

open Set Topology Schoenflies CurveComplex unitInterval

/-- An actual empty clean closed bigon constructs two mutually disjoint
family-isolated attached half-collars. The union with the old disk meets the
ENTIRE normalized lifted family exactly in the resulting enlarged source arc.
The compact support and all its lattice separation are constructed. -/
theorem normalized_clean_bigon_has_attached_family_collars_in_open
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (hJ : IsJordanCurve ((G '' Icc r s)∪segment ℝ (G r) (G s)))
    (he : Disjoint (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))))
    (hcontact : segment ℝ (G r) (G s)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (N : Set Plane) (hN : IsOpen N)
    (hKN : closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))⊆N)
    (hdeck : ∀ i : ℤ×ℤ, i≠0 → Disjoint
      (closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s))))
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
        closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s))))) :
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
      ((K∪range E)∪range Q)⊆N ∧
      IsCompact ((K∪range E)∪range Q) ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint ((K∪range E)∪range Q)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' ((K∪range E)∪range Q))) := by
  let K := closure (inside ((G '' Icc r s)∪segment ℝ (G r) (G s)))
  let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  have hGL : range G⊆L := by
    rintro z ⟨t,rfl⟩
    refine mem_iUnion.mpr ⟨0,t,?_⟩
    ext i; fin_cases i <;> simp [Plane.mk]
  have hKL : K∩L=G '' Icc r s := clean_empty_bigon_closed_disk_family_contact G r s hrs L hGL hJ he hcontact
  have hcore : G '' Icc r s⊆K := fun z hz => (show z∈K∩L from hKL.symm ▸ hz).1
  have hmeet : (G '' Icc r s)∩segment ℝ (G r) (G s)={G r,G s} := by
    apply subset_antisymm
    · rintro z ⟨hz,hzF⟩
      exact hcontact ▸ (show z∈segment ℝ (G r) (G s)∩L from ⟨hzF,hGL (image_subset_range G _ hz)⟩)
    · intro z hz
      rcases hz with hz|hz
      · subst z; exact ⟨⟨r,⟨le_rfl,hrs.le⟩,rfl⟩,left_mem_segment ℝ _ _⟩
      · have hz' : z=G s := hz
        subst z; exact ⟨⟨s,⟨hrs.le,le_rfl⟩,rfl⟩,right_mem_segment ℝ _ _⟩
  obtain ⟨F,_,hrF,hsF,hwhole⟩ := jordan_pair_has_midpoint_square_chart
    (continuous_injective_interval_isArcBetween G hG.injective hrs)
    (isArcBetween_segment (fun hh => hrs.ne (hG.injective hh))) hmeet hJ
  have hin : F '' inside ((G '' Icc r s)∪segment ℝ (G r) (G s))=Plane.openSquare 0 1 := by
    rw [(plane_homeomorph_inside_transport F _).1,hwhole,inside_modelCurve]
  have hFK : F '' K=Plane.closedSquare 0 1 := by
    dsimp [K]
    rw [closure_eq_self_union_frontier,(jordan_curve_theorem hJ).frontier_inside,image_union,hin,hwhole]
    ext z
    simp only [mem_union,mem_openSquare_zero_one,modelCurve,mem_ofPred_eq,mem_closedSquare_zero_one]
    constructor
    · rintro (hz|hz) <;> linarith
    · exact fun hz => lt_or_eq_of_le hz
  obtain ⟨a0,b0,_,_,_,U,V,hU,hKU,hUV,hV,_,hVD⟩ :=
    clean_normalized_closed_bigon_enlarged_uniform_support G hG T r s hT hrs hshort hp hc hJ he hcontact hdeck
  let UN := U∩N
  have hUN : IsOpen UN := hU.inter hN
  have hKUN : K⊆UN := fun z hz => ⟨hKU hz,hKN hz⟩
  obtain ⟨a1,b1,ha1,hb1,hwidth,p0,q0,_,_,hp0R,hq0R,hp0U,hq0U,_,_,_,_⟩ :=
    clean_bigon_open_neighborhood_has_short_actual_whiskers G hG T r s hrs hshort L hGL hJ he hcontact UN hUN hKUN
  obtain ⟨p,q,hpE,hqE,hpt,hqt,hpR,hqR,hpK,hqK,hpq,_⟩ :=
    clean_actual_bigon_endpoint_whiskers G hG r s a1 b1 hrs ha1 hb1 L hGL hJ he hcontact
  have hpU : range p⊆UN := by rw [hpR,←hp0R]; exact hp0U
  have hqU : range q⊆UN := by rw [hqR,←hq0R]; exact hq0U
  let W := UN\range q
  have hW : IsOpen W := hUN.sdiff (isCompact_range hqE.continuous).isClosed
  have hpW : range p⊆W := fun z hz => ⟨hpU hz,fun hh => disjoint_left.mp hpq hz hh⟩
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  obtain ⟨rho,hrho,hrho1,E,hE,hEW,hEport,hEcenter,hEK,hEL⟩ :=
    actual_left_whisker_family_collar_of_closed_rows G hG T a1 r s ha1 hrs hclosed hpair hlf
      K hcore F hFK hrF p hpE hpt hpR hpK W hW hpW
  let Z := UN\range E
  have hZ : IsOpen Z := hUN.sdiff (isCompact_range hE.continuous).isClosed
  have hqZ : range q⊆Z := by
    intro z hz
    refine ⟨hqU hz,?_⟩
    intro hzE
    exact (hEW hzE).2 hz
  obtain ⟨sigma,hsigma,hsigma1,Q,hQ,hQZ,hQport,hQcenter,hQK,hQL⟩ :=
    normalized_actual_right_whisker_family_collar G hG T r s b1 hT hrs hb1 hp hc
      K hcore F hFK hsF q hqE hqt hqR hqK Z hZ hqZ
  let a := (a1+r)/2
  let b := (s+b1)/2
  have har : a<r := by dsimp [a]; linarith
  have hsb : s<b := by dsimp [b]; linarith
  have hEQ : Disjoint (range E) (range Q) := disjoint_left.mpr (fun z hzE hzQ => (hQZ hzQ).2 hzE)
  have hEV : range E⊆V := fun z hz => hUV (subset_closure ((hEW hz).1.1))
  have hQV : range Q⊆V := fun z hz => hUV (subset_closure ((hQZ hz).1.1))
  have hKV : K⊆V := hKU.trans (subset_closure.trans hUV)
  have hcenterImage (x y : ℝ) (H : I×Icc (-1:ℝ) 1 → Plane)
      (hh : ∀ t : I, H (t,⟨0,by norm_num⟩)=G (reparam x y t)) (hxy : x≠y) :
      G '' uIcc x y⊆range H := by
    obtain ⟨v,_,hvt,hvr⟩ := actual_embedded_line_interval_path G hG.injective x y hxy
    have hvfun : v=(fun t : I => G (reparam x y t)) := funext hvt
    rw [hvfun] at hvr
    rw [←hvr]
    rintro z ⟨t,rfl⟩
    exact ⟨(t,⟨0,by norm_num⟩),hh t⟩
  have hleft : G '' Icc a r⊆range E := by
    have hh := hcenterImage r a E hEcenter har.ne'
    rwa [uIcc_of_ge har.le] at hh
  have hright : G '' Icc s b⊆range Q := by
    have hh := hcenterImage s b Q hQcenter hsb.ne
    rwa [uIcc_of_le hsb.le] at hh
  have hcontact' : ((K∪range E)∪range Q)∩L=G '' Icc a b := by
    apply subset_antisymm
    · rintro z ⟨((hz|hz)|hz),hzL⟩
      · exact image_mono (Icc_subset_Icc har.le hsb.le) (hKL ▸ (show z∈K∩L from ⟨hz,hzL⟩))
      · by_cases hzK : z∈K
        · exact image_mono (Icc_subset_Icc har.le hsb.le) (hKL ▸ (show z∈K∩L from ⟨hzK,hzL⟩))
        · have hh : z∈(range E\K)∩L := ⟨⟨hz,hzK⟩,hzL⟩
          rw [hEL] at hh
          exact image_mono (Icc_subset_Icc le_rfl (hrs.le.trans hsb.le)) hh.1
      · by_cases hzK : z∈K
        · exact image_mono (Icc_subset_Icc har.le hsb.le) (hKL ▸ (show z∈K∩L from ⟨hzK,hzL⟩))
        · have hh : z∈(range Q\K)∩L := ⟨⟨hz,hzK⟩,hzL⟩
          rw [hQL] at hh
          exact image_mono (Icc_subset_Icc (har.le.trans hrs.le) le_rfl) hh.1
    · rintro z ⟨t,ht,rfl⟩
      refine ⟨?_,hGL (mem_range_self _)⟩
      by_cases htr : t ≤ r
      · exact Or.inl (Or.inr (hleft ⟨t,⟨ht.1,htr⟩,rfl⟩))
      by_cases hts : t ≤ s
      · exact Or.inl (Or.inl (hcore ⟨t,⟨le_of_not_ge htr,hts⟩,rfl⟩))
      · exact Or.inr (hright ⟨t,⟨le_of_not_ge hts,ht.2⟩,rfl⟩)
  have hSsub : (K∪range E)∪range Q⊆V := union_subset (union_subset hKV hEV) hQV
  refine ⟨a,b,rho,sigma,har,hsb,by dsimp [a,b]; linarith,hrho,hrho1,hsigma,hsigma1,F,hrF,hsF,hFK,
    E,Q,hE,hQ,hEQ,hEport,hQport,hEcenter,hQcenter,hEK,hQK,hcontact',?_,?_,?_⟩
  · exact union_subset (union_subset hKN (fun z hz => (hEW hz).1.2))
      (fun z hz => (hQZ hz).1.2)
  · exact ((jordan_curve_theorem hJ).isBounded_inside.isCompact_closure.union (isCompact_range hE.continuous)).union
      (isCompact_range hQ.continuous)
  · intro i hi
    exact (hVD i hi).mono hSsub (image_mono hSsub)

#print axioms normalized_clean_bigon_has_attached_family_collars_in_open
