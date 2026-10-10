import CurveComplexGenusTwo.Topology.ActualFareyClassification.ProperLineJordanCrosscut
import Schoenflies.JordanClosed
import Mathlib

open Set Topology Schoenflies Bornology

/-- A Jordan boundary contained in an actual closed Jordan disk bounds a
subdisk; containment is proved using the unbounded exterior component. -/
theorem jordan_subdisk_of_boundary_in_closed_disk
    (C D : Set Plane) (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hboundary : D ⊆ closure (inside C)) :
    inside D ⊆ inside C ∧ closure (inside D) ⊆ closure (inside C) := by
  have hc := jordan_curve_theorem hC
  have hd := jordan_curve_theorem hD
  have hsep : Disjoint (outside C) (closure (inside C)) :=
    disjoint_inside_outside.symm.closure_right hc.isOpen_outside
  have hout : outside C ⊆ outside D := by
    have hcover : outside C ⊆ inside D ∪ outside D := by
      rw [inside_union_outside]
      intro z hz hzD
      exact disjoint_left.mp hsep hz (hboundary hzD)
    rcases hc.isConnected_outside.isPreconnected.subset_or_subset
      hd.isOpen_inside hd.isOpen_outside disjoint_inside_outside hcover with h | h
    · exact False.elim (hc.not_isBounded_outside (hd.isBounded_inside.subset h))
    · exact h
  have hn : Disjoint (inside D) (closure (outside C)) :=
    (disjoint_inside_outside.mono_right hout).closure_right hd.isOpen_inside
  have hinside : inside D ⊆ inside C := by
    intro z hz
    have hnC : z ∉ C := by
      intro hzC
      have hzcl : z ∈ closure (outside C) := by
        rw [← hc.frontier_outside] at hzC
        exact frontier_subset_closure hzC
      exact disjoint_left.mp hn hz hzcl
    have hp : z ∈ inside C ∪ outside C := by
      rw [inside_union_outside]
      exact hnC
    rcases hp with hp | hp
    · exact hp
    · exact False.elim (disjoint_left.mp hn hz (subset_closure hp))
  exact ⟨hinside,closure_mono hinside⟩

/-- The only old boundary points retained in a closed subdisk are points on
its new boundary. Thus deleting an old corner loses an actual contact. -/
theorem jordan_closed_subdisk_old_boundary_contacts
    (C D : Set Plane) (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hboundary : D ⊆ closure (inside C)) :
    closure (inside D) ∩ C ⊆ D := by
  have hinside := (jordan_subdisk_of_boundary_in_closed_disk C D hC hD hboundary).1
  intro z hz
  rw [closure_eq_self_union_frontier, (jordan_curve_theorem hD).frontier_inside] at hz
  rcases hz.1 with hzI | hzD
  · exact False.elim (inside_subset_compl (hinside hzI) hz.2)
  · exact hzD

/-- A proper closed subdisk loses a finite event located at a removed old
boundary point. No strict reduction certificate is assumed. -/
theorem jordan_subdisk_contact_count_strict
    (C D E : Set Plane) (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hboundary : D ⊆ closure (inside C))
    (hfinite : (E ∩ closure (inside C)).Finite)
    (p : Plane) (hpE : p ∈ E) (hpC : p ∈ C) (hpD : p ∉ D) :
    (E ∩ closure (inside D)).ncard < (E ∩ closure (inside C)).ncard := by
  have hsub := (jordan_subdisk_of_boundary_in_closed_disk C D hC hD hboundary).2
  have hED : E ∩ closure (inside D) ⊆ E ∩ closure (inside C) :=
    fun z hz => ⟨hz.1,hsub hz.2⟩
  have hpcl : p ∈ closure (inside C) := by
    rw [← (jordan_curve_theorem hC).frontier_inside] at hpC
    exact frontier_subset_closure hpC
  apply ncard_lt_ncard _ hfinite
  apply ssubset_iff_subset_ne.mpr
  refine ⟨hED,?_⟩
  intro he
  have hpp : p ∈ E ∩ closure (inside C) := ⟨hpE,hpcl⟩
  rw [← he] at hpp
  exact hpD (jordan_closed_subdisk_old_boundary_contacts C D hC hD hboundary ⟨hpp.2,hpC⟩)

/-- The real vertical fiber is an actual proper embedded line. -/
theorem vertical_fiber_isClosedEmbedding (c : ℝ) :
    IsClosedEmbedding (fun t : ℝ => Plane.mk c t) := by
  have hcont : Continuous (fun t : ℝ => Plane.mk c t) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop
  have hleft : Function.LeftInverse (fun z : Plane => z 1) (fun t : ℝ => Plane.mk c t) :=
    fun _ => rfl
  have he := hleft.isEmbedding (EuclideanSpace.proj 1).continuous hcont
  refine ⟨he,?_⟩
  have hr : range (fun t : ℝ => Plane.mk c t) = {z : Plane | z 0=c} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      rfl
    · intro hz
      refine ⟨z 1,?_⟩
      ext i
      fin_cases i
      · exact hz.symm
      · rfl
  rw [hr]
  exact isClosed_eq (EuclideanSpace.proj 0).continuous continuous_const

#print axioms jordan_subdisk_of_boundary_in_closed_disk
#print axioms jordan_closed_subdisk_old_boundary_contacts
#print axioms jordan_subdisk_contact_count_strict
#print axioms vertical_fiber_isClosedEmbedding

/-- The image of a real interval under the actual vertical fiber is exactly
its straight segment, not an abstract crosscut certificate. -/
theorem vertical_fiber_interval_image (c a b : ℝ) (hab : a≤b) :
    (fun t : ℝ => Plane.mk c t) '' Icc a b =
      segment ℝ (Plane.mk c a) (Plane.mk c b) := by
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap (Plane.mk c 0) (Plane.mk c 1)
  have hf (t : ℝ) : f t=Plane.mk c t := by
    ext i
    fin_cases i <;> simp [f,AffineMap.lineMap_apply,Plane.mk]
  have hh := image_segment ℝ f a b
  rw [segment_eq_Icc hab] at hh
  simpa only [hf] using hh

/-- A translated fiber entering an actual line-empty bigon cuts off an actual
closed Jordan subdisk and removes both old corners. -/
theorem shifted_fiber_entering_empty_bigon_has_actual_subdisk
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c c' r s : ℝ)
    (_hrs : r<s) (hr : G r 0=c) (hs : G s 0=c) (hcc : c'≠c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (hempty : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) (range G))
    (t : ℝ) (ht : Plane.mk c' t ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∃ a b : ℝ, r<a ∧ a<b ∧ b<s ∧ G a 0=c' ∧ G b 0=c' ∧
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      (((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))) ∧
      G r ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) := by
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let F : C(ℝ,Plane) := ⟨fun u => Plane.mk c' u, by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩
  obtain ⟨u,v,hut,htv,huC,hvC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut F (vertical_fiber_isClosedEmbedding c') C hC t ht
  have huv : u<v := hut.trans htv
  have hOldFiber (z : Plane) (hz : z ∈ segment ℝ (G r) (G s)) : z 0=c := by
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change w*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  have hend (w : ℝ) (hw : F w ∈ C) : ∃ a ∈ Ioo r s, G a=F w := by
    rcases hw with hw | hw
    · obtain ⟨a,ha,hea⟩ := hw
      have har : a≠r := by
        intro he
        subst a
        exact hcc (by simpa [F] using (congrArg (fun z : Plane => z 0) hea).symm.trans hr)
      have has : a≠s := by
        intro he
        subst a
        exact hcc (by simpa [F] using (congrArg (fun z : Plane => z 0) hea).symm.trans hs)
      exact ⟨a,⟨lt_of_le_of_ne ha.1 har.symm,lt_of_le_of_ne ha.2 has⟩,hea⟩
    · exact False.elim (hcc (hOldFiber _ hw))
  obtain ⟨a,ha,hea⟩ := hend u huC
  obtain ⟨b,hb,heb⟩ := hend v hvC
  have hne : a≠b := by
    intro he
    have hh : F u=F v := hea.symm.trans (he ▸ heb)
    exact (ne_of_lt huv) ((vertical_fiber_isClosedEmbedding c').injective hh)
  have hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C := by
    intro z hz
    rw [hea,heb] at hz
    change z ∈ segment ℝ (Plane.mk c' u) (Plane.mk c' v) at hz
    rw [← vertical_fiber_interval_image c' u v huv.le] at hz
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
  have build (a b : ℝ) (ha : a∈Ioo r s) (hb : b∈Ioo r s)
      (hab : a<b) (ha0 : G a 0=c') (hb0 : G b 0=c')
      (hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C) :
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆ closure (inside C) ∧
      G r ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) := by
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
      · exact hCcl (Or.inl ⟨w,⟨ha.1.le.trans hw.1,hw.2.trans hb.2.le⟩,rfl⟩)
      · rcases hSeg z hz with hh | hh | hh
        · rw [hh]; exact hCcl (Or.inl ⟨a,⟨ha.1.le,ha.2.le⟩,rfl⟩)
        · rw [hh]; exact hCcl (Or.inl ⟨b,⟨hb.1.le,hb.2.le⟩,rfl⟩)
        · exact subset_closure hh
    · intro hz
      rcases hz with ⟨w,hw,he⟩ | hz
      · have hew := hG.injective he
        subst w
        exact not_le_of_gt ha.1 hw.1
      · have hz0 : G r 0=c' := by
          rw [segment_eq_image_lineMap] at hz
          obtain ⟨w,hw,he⟩ := hz
          have hh := congrArg (fun z : Plane => z 0) he
          simp only [AffineMap.lineMap_apply] at hh
          change w*(G b 0-G a 0)+G a 0=G r 0 at hh
          rw [ha0,hb0] at hh
          linarith
        exact hcc (hz0.symm.trans hr)
  have ha0 : G a 0=c' := by rw [hea]; rfl
  have hb0 : G b 0=c' := by rw [heb]; rfl
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

#print axioms vertical_fiber_interval_image
#print axioms shifted_fiber_entering_empty_bigon_has_actual_subdisk

/-- An entering horizontally shifted fiber produces strict reduction of
ACTUAL finite compact contacts, while retaining whole-family emptiness. -/
theorem shifted_fiber_actual_subdisk_strict_contacts
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c c' r s : ℝ)
    (hrs : r<s) (hr : G r 0=c) (hs : G s 0=c) (hcc : c'≠c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (L E : Set Plane) (hGL : range G ⊆ L)
    (hempty : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hfinite : (E ∩ closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))).Finite)
    (hcontact : G r∈E)
    (t : ℝ) (ht : Plane.mk c' t ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∃ a b : ℝ, r<a ∧ a<b ∧ b<s ∧ G a 0=c' ∧ G b 0=c' ∧
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      closure (inside ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) ⊆
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) ∧
      Disjoint (inside ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) L ∧
      (E ∩ closure (inside ((G '' Icc a b) ∪ segment ℝ (G a) (G b)))).ncard <
        (E ∩ closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))).ncard := by
  obtain ⟨a,b,hra,hab,hbs,ha0,hb0,hD,hsub,hcorner⟩ :=
    shifted_fiber_entering_empty_bigon_has_actual_subdisk G hG c c' r s hrs hr hs hcc
      hC (hempty.mono_right hGL) t ht
  have hinside := jordan_subdisk_of_boundary_in_closed_disk _ _ hC hD hsub
  have hlt := jordan_subdisk_contact_count_strict _ _ E hC hD hsub hfinite
    (G r) hcontact (Or.inl ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩) hcorner
  exact ⟨a,b,hra,hab,hbs,ha0,hb0,hD,hinside.2,hempty.mono_left hinside.1,hlt⟩

#print axioms shifted_fiber_actual_subdisk_strict_contacts
