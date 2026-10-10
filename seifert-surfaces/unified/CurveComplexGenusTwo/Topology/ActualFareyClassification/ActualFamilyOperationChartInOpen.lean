import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFamilyDiskEndpointBoundary
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ClosedBallTailAvoidingEnlargement

open Set Topology Schoenflies CurveComplex Metric

/-- The actual closed-family disk constructs an enlarged operation chart.
Its whole closed support still meets the full family exactly in the source
arc, and the arc is now a genuine interior crosscut except at fixed endpoints.
The forbidden tails and the variable-width enlargement are derived. -/
theorem normalized_actual_family_disk_operation_chart_in_open
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T a b : ℝ) (hT : 0<T) (hab : a<b)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (Phi : Plane ≃ₜ Plane)
    (hcontact : (Phi '' Plane.closedSquare 0 1)∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b)
    (W : Set Plane) (hW : IsOpen W)
    (hSW : Phi '' Plane.closedSquare 0 1⊆W)
    (hdeck : ∀ i : ℤ×ℤ, i≠0 → Disjoint (Phi '' Plane.closedSquare 0 1)
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (Phi '' Plane.closedSquare 0 1))) :
    ∃ phi : Plane ≃ₜ Plane,
      Phi '' Plane.closedSquare 0 1⊆phi '' Plane.closedSquare 0 1 ∧
      phi '' Plane.closedSquare 0 1⊆W ∧
      (Phi '' Plane.closedSquare 0 1)\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      (phi '' Plane.closedSquare 0 1)∩
        (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))=G '' Icc a b ∧
      (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1 ∧
      phi.symm (G a)∈modelCurve ∧ phi.symm (G b)∈modelCurve ∧
      (∀ i : ℤ×ℤ, i≠0 → Disjoint (phi '' Plane.closedSquare 0 1)
        ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' (phi '' Plane.closedSquare 0 1))) := by
  let S := Phi '' Plane.closedSquare 0 1
  let L : ℤ → Set Plane := fun j => range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  obtain ⟨hclosed,hpair,hlf⟩ := normalized_line_deck_family G hG T hT hp hc
  change Pairwise (fun i j => Disjoint (L i) (L j)) at hpair
  have hL0 : L 0=range G := by
    have hh : (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=G := by
      funext x; ext i; fin_cases i <;> simp [Plane.mk]
    change range (fun x : ℝ => G x+Plane.mk 0 (((0:ℤ):ℝ)*T))=range G
    rw [hh]
  have hGL : range G⊆⋃ j : ℤ,L j := fun z hz => mem_iUnion.mpr ⟨0,hL0.symm ▸ hz⟩
  let J := ⋃ j : {j : ℤ // j≠0}, L j.val
  have hJ : IsClosed J := (hlf.comp_injective Subtype.val_injective).isClosed_iUnion (fun j => hclosed j.val)
  have hGJ : Disjoint (range G) J := by
    apply disjoint_left.mpr
    intro z hz hj
    obtain ⟨j,hj⟩ := mem_iUnion.mp hj
    exact disjoint_left.mp (hpair (Ne.symm j.property)) (hL0.symm ▸ hz) hj
  let bad := (G '' Iic a∪G '' Ici b)∪J
  have hbad : IsClosed bad := ((hG.isClosedMap _ isClosed_Iic).union (hG.isClosedMap _ isClosed_Ici)).union hJ
  have hGaBad : G a∈bad := Or.inl (Or.inl ⟨a,by simp,rfl⟩)
  have hGbBad : G b∈bad := Or.inl (Or.inr ⟨b,by simp,rfl⟩)
  have hA : G '' Icc a b⊆S := fun z hz => (show z∈S∩(⋃ j : ℤ,L j) from hcontact.symm ▸ hz).1
  have hlinecontact : S∩range G=G '' Icc a b := by
    apply subset_antisymm
    · rintro z ⟨hz,hzG⟩; exact hcontact ▸ (show z∈S∩(⋃ j : ℤ,L j) from ⟨hz,hGL hzG⟩)
    · intro z hz; exact ⟨hA hz,image_subset_range G _ hz⟩
  obtain ⟨haBoundary,hbBoundary⟩ := actual_line_interval_disk_endpoints_on_boundary G hG.injective a b hab Phi hlinecontact
  have hS : IsCompact S := (isCompact_closedSquare 0 1).image Phi.continuous
  obtain ⟨U,V,hU,hSU,hUV,_,_,hVD⟩ := compact_deck_free_marked_uniform_support S ∅ hS isClosed_empty (disjoint_empty _) T hT hdeck
  let UW := U∩W
  have hUW : IsOpen UW := hU.inter hW
  have hSUW : S⊆UW := fun z hz => ⟨hSU hz,hSW hz⟩
  let P : Plane ≃ₜ (Fin 2→ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
  have hnorm (z : Plane) : ‖P z‖=Plane.supNorm z := by simp [P,Pi.norm_def,Finset.univ_fin2,Plane.supNorm,Real.norm_eq_abs]
  have hPclosed : P '' Plane.closedSquare 0 1=closedBall (0:Fin 2→ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩; simpa [hnorm] using mem_closedSquare_zero_one.mp hz
    · intro hx
      refine ⟨P.symm x,?_,P.apply_symm_apply _⟩
      rw [mem_closedSquare_zero_one,←hnorm,P.apply_symm_apply]
      simpa using hx
  have hPopen : P '' Plane.openSquare 0 1=ball (0:Fin 2→ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩; simpa [hnorm] using mem_openSquare_zero_one.mp hz
    · intro hx
      refine ⟨P.symm x,?_,P.apply_symm_apply _⟩
      rw [mem_openSquare_zero_one,←hnorm,P.apply_symm_apply]
      simpa using hx
  let C := Phi.symm.trans P
  have hCS : C '' S=closedBall (0:Fin 2→ℝ) 1 := by
    rw [show C '' S=P '' Plane.closedSquare 0 1 by
      dsimp only [S]
      rw [image_image]
      change (fun z => P (Phi.symm (Phi z))) '' Plane.closedSquare 0 1=_
      simp]
    exact hPclosed
  let B := C '' bad
  have hB : IsClosed B := C.isClosedMap _ hbad
  have hBn : B.Nonempty := ⟨C (G a),mem_image_of_mem C hGaBad⟩
  have hU' : IsOpen (C '' UW) := C.isOpenMap _ hUW
  have hQU : closedBall (0:Fin 2→ℝ) 1⊆C '' UW := by rw [←hCS]; exact image_mono hSUW
  obtain ⟨H,hHU,hHB,hInterior,hHfix⟩ := closed_ball_actual_forbidden_avoiding_enlargement B (C '' UW) hB hBn hU' hQU
  let phi := P.trans (H.trans C.symm)
  have hphiC : ∀ z, C (phi z)=H (P z) := fun z => C.apply_symm_apply _
  have hphiClosed : C '' (phi '' Plane.closedSquare 0 1)=H '' closedBall (0:Fin 2→ℝ) 1 := by
    rw [image_image]
    change (fun z => C (phi z)) '' Plane.closedSquare 0 1=_
    simp_rw [hphiC]
    rw [←image_image,hPclosed]
  have hphiOpen : C '' (phi '' Plane.openSquare 0 1)=H '' ball (0:Fin 2→ℝ) 1 := by
    rw [image_image]
    change (fun z => C (phi z)) '' Plane.openSquare 0 1=_
    simp_rw [hphiC]
    rw [←image_image,hPopen]
  have pullClosed (z : Plane) : z∈phi '' Plane.closedSquare 0 1 ↔ C z∈H '' closedBall (0:Fin 2→ℝ) 1 := by
    rw [←hphiClosed]
    constructor
    · exact mem_image_of_mem C
    · rintro ⟨x,hx,he⟩; exact C.injective he ▸ hx
  have pullOld (z : Plane) : z∈S ↔ C z∈closedBall (0:Fin 2→ℝ) 1 := by
    rw [←hCS]
    constructor
    · exact mem_image_of_mem C
    · rintro ⟨x,hx,he⟩; exact C.injective he ▸ hx
  have hcontains : S⊆phi '' Plane.closedSquare 0 1 := by
    intro z hz
    apply (pullClosed z).mpr
    by_cases hzB : C z∈B
    · exact (show C z∈(H '' closedBall (0:Fin 2→ℝ) 1)∩B from hHB.symm ▸ ⟨(pullOld z).mp hz,hzB⟩).1
    · exact image_mono (ball_subset_closedBall) (hInterior ⟨(pullOld z).mp hz,hzB⟩)
  have hNoNewBad (z : Plane) (hz : z∈phi '' Plane.closedSquare 0 1) (hzBad : z∈bad) : z∈S := by
    apply (pullOld z).mpr
    exact (show C z∈closedBall (0:Fin 2→ℝ) 1∩B from hHB ▸ ⟨(pullClosed z).mp hz,mem_image_of_mem C hzBad⟩).1
  have hAInterior : (G '' Icc a b)\{G a,G b}⊆phi '' Plane.openSquare 0 1 := by
    rintro z ⟨⟨t,ht,rfl⟩,hne⟩
    have ht' : a<t ∧ t<b := by
      constructor
      · exact lt_of_le_of_ne ht.1 (by intro hh; subst t; exact hne (Or.inl rfl))
      · exact lt_of_le_of_ne ht.2 (by intro hh; subst t; exact hne (Or.inr (mem_singleton _)))
    have hgtBad : G t∉bad := by
      rintro ((⟨u,hu,he⟩|⟨u,hu,he⟩)|hzJ)
      · have hut := hG.injective he
        change u≤a at hu
        linarith [ht'.1]
      · have hut := hG.injective he
        change b≤u at hu
        linarith [ht'.2]
      · exact disjoint_left.mp hGJ (mem_range_self _) hzJ
    have hgtB : C (G t)∉B := by
      rintro ⟨x,hx,he⟩; exact hgtBad (C.injective he ▸ hx)
    have hh : C (G t)∈H '' ball (0:Fin 2→ℝ) 1 := hInterior ⟨(pullOld _).mp (hA ⟨t,ht,rfl⟩),hgtB⟩
    rw [←hphiOpen] at hh
    obtain ⟨x,hx,he⟩ := hh
    exact C.injective he ▸ hx
  have hcontact' : (phi '' Plane.closedSquare 0 1)∩(⋃ j : ℤ,L j)=G '' Icc a b := by
    apply subset_antisymm
    · rintro z ⟨hz,hzL⟩
      by_cases hzA : z∈G '' Icc a b
      · exact hzA
      have hzBad : z∈bad := by
        obtain ⟨j,hj⟩ := mem_iUnion.mp hzL
        by_cases hj0 : j=0
        · subst j; rw [hL0] at hj
          obtain ⟨t,rfl⟩ := hj
          have ht : t∉Icc a b := fun hh => hzA ⟨t,hh,rfl⟩
          rcases not_and_or.mp ht with hl|hr
          · exact Or.inl (Or.inl ⟨t,le_of_not_ge hl,rfl⟩)
          · exact Or.inl (Or.inr ⟨t,le_of_not_ge hr,rfl⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨⟨j,hj0⟩,hj⟩)
      exact hcontact ▸ (show z∈S∩(⋃ j : ℤ,L j) from ⟨hNoNewBad z hz hzBad,hzL⟩)
    · intro z hz
      exact ⟨hcontains (hA hz),hGL (image_subset_range G _ hz)⟩
  have hend (t : ℝ) (ht : t=a ∨ t=b) : phi.symm (G t)∈modelCurve := by
    have hpB : Phi.symm (G t)∈modelCurve := by
      rcases ht with ht|ht
      · rw [ht]; exact haBoundary
      · rw [ht]; exact hbBoundary
    have hn1 : ‖C (G t)‖=1 := hnorm _ |>.trans hpB
    have htBad : G t∈bad := by
      rcases ht with ht|ht
      · rw [ht]; exact hGaBad
      · rw [ht]; exact hGbBad
    have hfix := hHfix (C (G t)) hn1 (mem_image_of_mem C htBad)
    change P.symm (H.symm (C (G t)))∈modelCurve
    rw [hfix]
    change P.symm (P (Phi.symm (G t)))∈modelCurve
    rwa [P.symm_apply_apply]
  have hphiU : phi '' Plane.closedSquare 0 1⊆UW := by
    intro z hz
    obtain ⟨x,hx,he⟩ := hHU ((pullClosed z).mp hz)
    exact C.injective he ▸ hx
  have hphiV := (hphiU.trans inter_subset_left).trans (subset_closure.trans hUV)
  have hWholeInterior : S\{G a,G b}⊆phi '' Plane.openSquare 0 1 := by
    rintro z ⟨hz,hne⟩
    have hzBad : z∉bad := by
      rintro ((⟨t,ht,he⟩|⟨t,ht,he⟩)|hzJ)
      · have htz : G t∈S := he ▸ hz
        obtain ⟨u,hu,heu⟩ := hlinecontact ▸ (show G t∈S∩range G from ⟨htz,mem_range_self _⟩)
        have hut := hG.injective heu
        change t≤a at ht
        have hta : t=a := by linarith [hu.1]
        exact hne (Or.inl (by rw [←he,hta]))
      · have htz : G t∈S := he ▸ hz
        obtain ⟨u,hu,heu⟩ := hlinecontact ▸ (show G t∈S∩range G from ⟨htz,mem_range_self _⟩)
        have hut := hG.injective heu
        change b≤t at ht
        have htb : t=b := by linarith [hu.2]
        exact hne (Or.inr (by rw [←he,htb]; rfl))
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hzJ
        obtain ⟨t,ht,he⟩ := hcontact ▸ (show z∈S∩(⋃ j : ℤ,L j) from ⟨hz,mem_iUnion.mpr ⟨j.val,hj⟩⟩)
        exact disjoint_left.mp hGJ ⟨t,he⟩ hzJ
    have hzB : C z∉B := by
      rintro ⟨x,hx,he⟩
      exact hzBad (C.injective he ▸ hx)
    have hh := hInterior ⟨(pullOld z).mp hz,hzB⟩
    rw [←hphiOpen] at hh
    obtain ⟨x,hx,he⟩ := hh
    exact C.injective he ▸ hx
  refine ⟨phi,hcontains,hphiU.trans inter_subset_right,hWholeInterior,hcontact',hAInterior,hend a (Or.inl rfl),hend b (Or.inr rfl),?_⟩
  intro i hi
  exact (hVD i hi).mono hphiV (image_mono hphiV)

#print axioms normalized_actual_family_disk_operation_chart_in_open
