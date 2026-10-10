import CurveComplexGenusTwo.Topology.TorusStrip.ArcInterval
import Mathlib

open Set Topology Schoenflies

theorem finite_fiber_select_consecutive_hits
    (G : ℝ → Plane) (c : ℝ) (hfinite : {t : ℝ | G t 0=c}.Finite)
    (x y : ℝ) (hxy : x < y) (hx : G x 0=c) (hy : G y 0=c) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      ∀ t ∈ Ioo r s, G t 0 ≠ c := by
  let E : Set ℝ := {t | G t 0=c}
  let F : Set ℝ := E ∩ Ioi x
  have hF : F.Finite := hfinite.inter_of_left _
  obtain ⟨s,hs,hmin⟩ := Set.exists_min_image F id hF ⟨y,hy,hxy⟩
  refine ⟨x,s,hs.2,hx,hs.1,?_⟩
  intro t ht he
  have hh := hmin t ⟨he,ht.1⟩
  exact not_le_of_gt ht.2 hh

/-- A genuine Jordan bigon candidate is selected directly from the finite
intersection events of an actual embedded lift with a vertical fiber. -/
theorem actual_finite_fiber_has_jordan_bigon
    (G : C(ℝ,Plane)) (hG : Function.Injective G) (c : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (x y : ℝ) (hxy : x < y) (hx : G x 0=c) (hy : G y 0=c) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      IsArcBetween (G '' Icc r s) (G r) (G s) ∧
      IsArcBetween (segment ℝ (G r) (G s)) (G r) (G s) ∧
      (G '' Icc r s) ∩ segment ℝ (G r) (G s) = {G r,G s} ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      ∀ t ∈ Ioo r s, G t 0 ≠ c := by
  obtain ⟨r,s,hrs,hr,hs,hno⟩ := finite_fiber_select_consecutive_hits G c hfinite x y hxy hx hy
  have hne : G r ≠ G s := fun he => (ne_of_lt hrs) (hG he)
  have hA := continuous_injective_interval_isArcBetween G hG hrs
  have hB := isArcBetween_segment hne
  have hfiber : ∀ z ∈ segment ℝ (G r) (G s), z 0=c := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change t*(G s 0-G r 0)+G r 0=c
    rw [hr,hs]
    ring
  have hmeet : ∀ z ∈ G '' Icc r s, z ∈ segment ℝ (G r) (G s) →
      z=G r ∨ z=G s := by
    rintro z ⟨t,ht,rfl⟩ hz
    by_cases htr : t=r
    · exact Or.inl (congrArg G htr)
    by_cases hts : t=s
    · exact Or.inr (congrArg G hts)
    exact False.elim (hno t ⟨lt_of_le_of_ne ht.1 (Ne.symm htr),
      lt_of_le_of_ne ht.2 hts⟩ (hfiber _ hz))
  have hinter : (G '' Icc r s) ∩ segment ℝ (G r) (G s) = {G r,G s} := by
    ext z
    constructor
    · intro hz
      rcases hmeet z hz.1 hz.2 with he | he <;> simp [he]
    · intro hz
      rcases hz with hz | hz
      · subst z
        exact ⟨hA.left_mem,hB.left_mem⟩
      · subst z
        exact ⟨hA.right_mem,hB.right_mem⟩
  exact ⟨r,s,hrs,hr,hs,hA,hB,hinter,isJordanCurve_union hA hB hmeet,hno⟩

#print axioms finite_fiber_select_consecutive_hits
#print axioms actual_finite_fiber_has_jordan_bigon

/-- The finite projected intersection set gives finite ACTUAL lifted fiber
events: deck-collision exclusion rules out multiple vertical representatives. -/
theorem normalized_fiber_hits_finite_of_projected_intersection
    (G : ℝ → Plane) (hinj : Function.Injective G) (c : ℝ)
    (hc : ∀ (x y : ℝ) (a b : ℤ),
      G x=G y+Plane.mk ((a:ℝ)*(2*Real.pi)) ((b:ℝ)*(2*Real.pi)) → b=0)
    (hfinite : ((range (fun t => (Circle.exp (G t 0),Circle.exp (G t 1)))) ∩
      {z : Circle × Circle | z.1=Circle.exp c}).Finite) :
    {t : ℝ | G t 0=c}.Finite := by
  let E : Set ℝ := {t | G t 0=c}
  let f : ℝ → Circle × Circle := fun t => (Circle.exp (G t 0),Circle.exp (G t 1))
  have him : (f '' E).Finite := hfinite.subset (by
    rintro z ⟨t,ht,rfl⟩
    exact ⟨mem_range_self _,by change Circle.exp (G t 0)=Circle.exp c; rw [ht]⟩)
  apply him.of_finite_image
  intro x hx y hy he
  have hsecond : Circle.exp (G x 1)=Circle.exp (G y 1) := congrArg Prod.snd he
  obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hsecond
  have hxy : G x=G y+Plane.mk 0 ((k:ℝ)*(2*Real.pi)) := by
    ext i
    fin_cases i
    · change G x 0=G y 0+0
      rw [hx,hy,add_zero]
    · exact hk
  have hkzero : k=0 := hc x y 0 k (by simpa using hxy)
  apply hinj
  have hm : Plane.mk 0 0=(0:Plane) := by ext i; fin_cases i <;> rfl
  simpa [hkzero,hm] using hxy

#print axioms normalized_fiber_hits_finite_of_projected_intersection

/-- Select an actual consecutive-hit candidate with minimum number of original
lifted events on its fiber-side segment. The minimum is constructed from the
finite input, not received as a disk/innermostness certificate. -/
theorem finite_fiber_select_minimum_side_crossings
    (G : ℝ → Plane) (c : ℝ) (hfinite : {t : ℝ | G t 0=c}.Finite)
    (x y : ℝ) (hxy : x < y) (hx : G x 0=c) (hy : G y 0=c) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧
      ∀ a b : ℝ, a < b → G a 0=c → G b 0=c →
        (∀ t ∈ Ioo a b, G t 0 ≠ c) →
        {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}.ncard ≤
          {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G a) (G b)}.ncard := by
  classical
  let count (r s : ℝ) := {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}.ncard
  let Q : ℕ → Prop := fun n => ∃ r s : ℝ,
    r < s ∧ G r 0=c ∧ G s 0=c ∧ (∀ t ∈ Ioo r s, G t 0 ≠ c) ∧ count r s=n
  have hex : ∃ n, Q n := by
    obtain ⟨r,s,hrs,hr,hs,hno⟩ := finite_fiber_select_consecutive_hits G c hfinite x y hxy hx hy
    exact ⟨count r s,r,s,hrs,hr,hs,hno,rfl⟩
  obtain ⟨r,s,hrs,hr,hs,hno,hn⟩ := Nat.find_spec hex
  refine ⟨r,s,hrs,hr,hs,hno,?_⟩
  intro a b hab ha hb havoid
  change count r s ≤ count a b
  rw [hn]
  exact Nat.find_min' hex ⟨a,b,hab,ha,hb,havoid,rfl⟩

#print axioms finite_fiber_select_minimum_side_crossings

theorem actual_fiber_side_crossing_count_at_least_two
    (G : ℝ → Plane) (c r s : ℝ) (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hrs : r < s) (hr : G r 0=c) (hs : G s 0=c) :
    2 ≤ {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}.ncard := by
  have hE : {t : ℝ | G t 0=c ∧ G t ∈ segment ℝ (G r) (G s)}.Finite :=
    hfinite.subset (fun _ h => h.1)
  have hsub : ({r,s} : Set ℝ) ⊆ {t : ℝ | G t 0=c ∧
      G t ∈ segment ℝ (G r) (G s)} := by
    intro t ht
    rcases ht with ht | ht
    · subst t
      exact ⟨hr,left_mem_segment ℝ _ _⟩
    · subst t
      exact ⟨hs,right_mem_segment ℝ _ _⟩
  have hh := ncard_le_ncard hsub hE
  rwa [ncard_pair (ne_of_lt hrs)] at hh

#print axioms actual_fiber_side_crossing_count_at_least_two

theorem actual_finite_multiple_fiber_hits_select_bigon
    (G : C(ℝ,Plane)) (hG : Function.Injective G) (c : ℝ)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hcount : 1 < {t : ℝ | G t 0=c}.ncard) :
    ∃ r s : ℝ, r < s ∧ G r 0=c ∧ G s 0=c ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) ∧
      ∀ t ∈ Ioo r s, G t 0 ≠ c := by
  obtain ⟨x,y,hx,hy,hne⟩ := (one_lt_ncard_iff hfinite).mp hcount
  have hpair : ∃ x y : ℝ, x < y ∧ G x 0=c ∧ G y 0=c := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨x,y,hlt,hx,hy⟩
    · exact ⟨y,x,hgt,hy,hx⟩
  obtain ⟨x,y,hxy,hx,hy⟩ := hpair
  obtain ⟨r,s,hrs,hr,hs,hA,hB,hmeet,hJ,hno⟩ :=
    actual_finite_fiber_has_jordan_bigon G hG c hfinite x y hxy hx hy
  exact ⟨r,s,hrs,hr,hs,hJ,hno⟩

#print axioms actual_finite_multiple_fiber_hits_select_bigon
