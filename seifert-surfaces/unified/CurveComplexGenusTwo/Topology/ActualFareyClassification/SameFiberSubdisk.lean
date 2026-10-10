import CurveComplexGenusTwo.Topology.ActualFareyClassification.JordanSubdiskContacts

open Set Topology Schoenflies

/-- A component of a vertical fiber in the interior cannot end in the open
part of that same fiber's old boundary segment. Hence both crosscut endpoints
belong to the actual curve side, even for the supporting fiber itself. -/
theorem supporting_fiber_crosscut_endpoints_on_curve
    (G : C(ℝ,Plane)) (c r s u v : ℝ) (hrs : r<s) (huv : u<v)
    (hr : G r 0=c) (hs : G s 0=c)
    (huC : Plane.mk c u∈(G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hvC : Plane.mk c v∈(G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hin : ∀ t∈Ioo u v, Plane.mk c t∈inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    Plane.mk c u∈G '' Icc r s ∧ Plane.mk c v∈G '' Icc r s := by
  let l := min (G r 1) (G s 1)
  let h := max (G r 1) (G s 1)
  have hcoords (z : Plane) (hz : z 0=c) : z=Plane.mk c (z 1) := by
    ext i
    fin_cases i <;> simp [hz]
  have hseg : segment ℝ (G r) (G s)=(fun t : ℝ => Plane.mk c t) '' Icc l h := by
    rw [hcoords (G r) hr,hcoords (G s) hs]
    by_cases hh : G r 1≤G s 1
    · simpa [l,h,min_eq_left hh,max_eq_right hh] using
        (vertical_fiber_interval_image c (G r 1) (G s 1) hh).symm
    · have hh' : G s 1≤G r 1 := (le_of_not_ge hh)
      rw [segment_symm]
      simpa [l,h,min_eq_right hh',max_eq_left hh'] using
        (vertical_fiber_interval_image c (G s 1) (G r 1) hh').symm
  have hnone (t : ℝ) (ht : t∈Ioo u v) : t∉Icc l h := by
    intro hh
    apply inside_subset_compl (hin t ht)
    right
    rw [hseg]
    exact ⟨t,hh,rfl⟩
  have hend (w : ℝ) (hw : w=u ∨ w=v)
      (hwC : Plane.mk c w∈(G '' Icc r s) ∪ segment ℝ (G r) (G s)) :
      Plane.mk c w∈G '' Icc r s := by
    rcases hwC with hh | hh
    · exact hh
    rw [hseg] at hh
    obtain ⟨t,ht,he⟩ := hh
    have htw : t=w := by simpa [Plane.mk] using congrArg (fun z : Plane => z 1) he
    subst t
    have hnot : ¬(l<w ∧ w<h) := by
      rintro ⟨hlw,hwh⟩
      rcases hw with hwu | hwv
      · rw [hwu] at hlw hwh
        let z := (u+min v h)/2
        have huz : u<z := by dsimp [z]; linarith [lt_min huv hwh]
        have hzv : z<v := by dsimp [z]; linarith [min_le_left v h]
        have hzl : l≤z := by linarith
        have hzh : z≤h := by dsimp [z]; linarith [min_le_right v h]
        exact hnone z ⟨huz,hzv⟩ ⟨hzl,hzh⟩
      · rw [hwv] at hlw hwh
        let z := (max u l+v)/2
        have huz : u<z := by dsimp [z]; linarith [le_max_left u l]
        have hzv : z<v := by dsimp [z]; linarith [max_lt huv hlw]
        have hzl : l≤z := by dsimp [z]; linarith [le_max_right u l]
        have hzh : z≤h := by linarith
        exact hnone z ⟨huz,hzv⟩ ⟨hzl,hzh⟩
    have hew : w=l ∨ w=h := by
      rcases le_iff_lt_or_eq.mp ht.1 with hh|hh
      · exact Or.inr (le_antisymm ht.2 (le_of_not_gt (fun hw => hnot ⟨hh,hw⟩)))
      · exact Or.inl hh.symm
    have hwends : w=G r 1 ∨ w=G s 1 := by
      rcases hew with hew|hew
      · by_cases hh : G r 1≤G s 1
        · exact Or.inl (hew.trans (min_eq_left hh))
        · exact Or.inr (hew.trans (min_eq_right (le_of_not_ge hh)))
      · by_cases hh : G r 1≤G s 1
        · exact Or.inr (hew.trans (max_eq_right hh))
        · exact Or.inl (hew.trans (max_eq_left (le_of_not_ge hh)))
    rcases hwends with hew|hew
    · exact ⟨r,⟨le_rfl, hrs.le⟩,by
        rw [hew]; exact hcoords (G r) hr⟩
    · exact ⟨s,⟨hrs.le,le_rfl⟩,by
        rw [hew]; exact hcoords (G s) hs⟩
  exact ⟨hend u (Or.inl rfl) huC,hend v (Or.inr rfl) hvC⟩

/-- A genuine fiber crosscut forming a closed proper subinterval removes at
least one old corner, including when one new endpoint is an old corner. -/
theorem fiber_crosscut_subinterval_omits_old_corner
    (G : C(ℝ,Plane)) (hi : Function.Injective G) (r s a b : ℝ)
    (hrs : r<s) (ha : a∈Icc r s) (hb : b∈Icc r s) (hab : a<b)
    (hSeg : ∀ z∈segment ℝ (G a) (G b), z=G a ∨ z=G b ∨
      z∈inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∃ p ∈ ({G r,G s} : Set Plane), p ∉ (G '' Icc a b) ∪ segment ℝ (G a) (G b) := by
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  have hrC : G r∈C := Or.inr (left_mem_segment ℝ _ _)
  have hsC : G s∈C := Or.inr (right_mem_segment ℝ _ _)
  have hproper : ¬(a=r ∧ b=s) := by
    rintro ⟨har,hbs⟩
    rw [har,hbs] at hSeg
    have hne : G r≠G s := fun he => (ne_of_lt hrs) (hi he)
    have hmid := midpoint_mem_segment (𝕜 := ℝ) (G r) (G s)
    rcases hSeg _ hmid with hh|hh|hh
    · exact hne ((midpoint_eq_left_iff (R := ℝ)).mp hh)
    · exact hne ((midpoint_eq_right_iff (R := ℝ)).mp hh)
    · exact inside_subset_compl hh (Or.inr hmid)
  by_cases hra : r<a
  · refine ⟨G r,by simp,?_⟩
    rintro (⟨x,hx,he⟩|hh)
    · have hxr := hi he
      subst x
      exact not_le_of_gt hra hx.1
    · rcases hSeg _ hh with he|he|he
      · have hh := hi he
        linarith
      · have hh := hi he
        linarith
      · exact inside_subset_compl he hrC
  · have har : a=r := le_antisymm (le_of_not_gt hra) ha.1
    have hbs : b<s := lt_of_le_of_ne hb.2 (fun hh => hproper ⟨har,hh⟩)
    refine ⟨G s,by simp,?_⟩
    rintro (⟨x,hx,he⟩|hh)
    · have hxs := hi he
      subst x
      exact not_le_of_gt hbs hx.2
    · rcases hSeg _ hh with he|he|he
      · have hh := hi he
        linarith
      · have hh := hi he
        linarith
      · exact inside_subset_compl he hsC

theorem supporting_fiber_entering_empty_bigon_has_actual_subdisk
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c r s : ℝ)
    (hrs : r<s) (hr : G r 0=c) (hs : G s 0=c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (hempty : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) (range G))
    (t : ℝ) (ht : Plane.mk c t ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∃ a b : ℝ, r ≤ a ∧ a<b ∧ b ≤ s ∧ G a 0=c ∧ G b 0=c ∧
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      (((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))) ∧
      (∃ p ∈ ({G r,G s} : Set Plane), p ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) := by
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let F : C(ℝ,Plane) := ⟨fun u => Plane.mk c u, by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩
  obtain ⟨u,v,hut,htv,huC,hvC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut F (vertical_fiber_isClosedEmbedding c) C hC t ht
  have huv : u<v := hut.trans htv
  obtain ⟨huG,hvG⟩ := supporting_fiber_crosscut_endpoints_on_curve G c r s u v hrs huv hr hs huC hvC hin
  have hend (w : ℝ) (hw : F w ∈ G '' Icc r s) : ∃ a ∈ Icc r s, G a=F w := hw
  obtain ⟨a,ha,hea⟩ := hend u huG
  obtain ⟨b,hb,heb⟩ := hend v hvG
  have hne : a≠b := by
    intro he
    have hh : F u=F v := hea.symm.trans (he ▸ heb)
    exact (ne_of_lt huv) ((vertical_fiber_isClosedEmbedding c).injective hh)
  have hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C := by
    intro z hz
    rw [hea,heb] at hz
    change z ∈ segment ℝ (Plane.mk c u) (Plane.mk c v) at hz
    rw [← vertical_fiber_interval_image c u v huv.le] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    by_cases hwu : w=u
    · left
      simpa only [hwu,F,ContinuousMap.coe_mk] using hea.symm
    by_cases hwv : w=v
    · right; left
      simpa only [hwv,F,ContinuousMap.coe_mk] using heb.symm
    · right; right
      exact hin w ⟨lt_of_le_of_ne hw.1 (Ne.symm hwu),lt_of_le_of_ne hw.2 hwv⟩
  have hCcl : C ⊆ closure (inside C) := by
    have hh : frontier (inside C)=C := (jordan_curve_theorem hC).frontier_inside
    intro z hz
    exact frontier_subset_closure (hh.symm ▸ hz)
  have build (a b : ℝ) (ha : a∈Icc r s) (hb : b∈Icc r s)
      (hab : a<b) (ha0 : G a 0=c) (hb0 : G b 0=c)
      (hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C) :
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆ closure (inside C) ∧
      (∃ p ∈ ({G r,G s} : Set Plane), p ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) := by
    have hJ : IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) := by
      apply isJordanCurve_union (continuous_injective_interval_isArcBetween G hG.injective hab)
        (isArcBetween_segment (fun he => (ne_of_lt hab) (hG.injective he)))
      intro z hz hzS
      rcases hSeg z hzS with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact False.elim (disjoint_left.mp hempty hh (image_subset_range G _ hz))
    refine ⟨hJ,?_,?_⟩
    · intro z hz
      rcases hz with ⟨w,hw,rfl⟩ | hz
      · exact hCcl (Or.inl ⟨w,⟨ha.1.trans hw.1,hw.2.trans hb.2⟩,rfl⟩)
      · rcases hSeg z hz with hh | hh | hh
        · rw [hh]; exact hCcl (Or.inl ⟨a,⟨ha.1,ha.2⟩,rfl⟩)
        · rw [hh]; exact hCcl (Or.inl ⟨b,⟨hb.1,hb.2⟩,rfl⟩)
        · exact subset_closure hh
    · exact fiber_crosscut_subinterval_omits_old_corner G hG.injective r s a b hrs ha hb hab hSeg
  have ha0 : G a 0=c := by rw [hea]; rfl
  have hb0 : G b 0=c := by rw [heb]; rfl
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨hJ,hcl,hcorner⟩ := build a b ha hb hab ha0 hb0 hSeg
    exact ⟨a,b,ha.1,hab,hb.2,ha0,hb0,hJ,hcl,hcorner⟩
  · have hSeg' : ∀ z ∈ segment ℝ (G b) (G a), z=G b ∨ z=G a ∨ z∈inside C := by
      intro z hz
      rw [segment_symm] at hz
      rcases hSeg z hz with hh | hh | hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inl hh
      · exact Or.inr (Or.inr hh)
    obtain ⟨hJ,hcl,hcorner⟩ := build b a hb ha hba hb0 ha0 hSeg'
    exact ⟨b,a,hb.1,hba,ha.2,hb0,ha0,hJ,hcl,hcorner⟩


#print axioms supporting_fiber_crosscut_endpoints_on_curve
#print axioms fiber_crosscut_subinterval_omits_old_corner
#print axioms supporting_fiber_entering_empty_bigon_has_actual_subdisk
