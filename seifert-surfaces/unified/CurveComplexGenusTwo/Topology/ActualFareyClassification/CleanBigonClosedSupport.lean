import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTransverseBigonContacts
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ShortArcUniformSupport

open Set Topology Schoenflies Metric

/-- Exact actual lifted-family contacts force the straight side's height to
be strictly smaller than one vertical period. -/
theorem clean_fiber_side_has_short_height
    (G : C(ℝ,Plane)) (T r s c : ℝ) (hT : 0<T)
    (hr : G r 0=c) (hs : G s 0=c)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s}) :
    |G s 1-G r 1|<T := by
  have hcoords (z : Plane) (hz : z 0=c) : z=Plane.mk c (z 1) := by
    ext i
    fin_cases i <;> simp [hz]
  have hseg := hcontact
  rw [hcoords (G r) hr,hcoords (G s) hs] at hseg
  by_contra hn
  have hlarge : T  ≤ |G s 1-G r 1| := le_of_not_gt hn
  have check (j : ℤ) (hj : j≠0)
      (hzS : G r+Plane.mk 0 ((j:ℝ)*T)∈segment ℝ (G r) (G s)) : False := by
    have hzL : G r+Plane.mk 0 ((j:ℝ)*T)∈
        ⋃ j : ℤ,range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := mem_iUnion.mpr ⟨j,r,rfl⟩
    have hzends : G r+Plane.mk 0 ((j:ℝ)*T)∈({G r,G s} : Set Plane) := hcontact ▸ ⟨hzS,hzL⟩
    rcases hzends with hh|hh
    · have hy := congrArg (fun z : Plane => z 1) hh
      change G r 1+(j:ℝ)*T=G r 1 at hy
      exact (mul_ne_zero (Int.cast_ne_zero.mpr hj) hT.ne') (by linarith)
    · have hh' : G s=G r+Plane.mk (((0:ℤ):ℝ)*T) ((j:ℝ)*T) := by
        simpa only [Int.cast_zero,zero_mul] using (mem_singleton_iff.mp hh).symm
      exact hj (hc s r 0 j hh')
  rcases le_total (G r 1) (G s 1) with hle|hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hlarge
    apply check 1 (by norm_num)
    rw [hcoords (G r) hr,hcoords (G s) hs,
      ←vertical_fiber_interval_image c (G r 1) (G s 1) hle]
    refine ⟨G r 1+T,⟨by linarith,by linarith⟩,?_⟩
    ext i
    fin_cases i <;> simp [Plane.mk]
  · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hlarge
    apply check (-1) (by norm_num)
    rw [hcoords (G r) hr,hcoords (G s) hs,segment_symm,
      ←vertical_fiber_interval_image c (G s 1) (G r 1) hle]
    refine ⟨G r 1-T,⟨by linarith,by linarith⟩,?_⟩
    ext i
    fin_cases i <;> simp [Plane.mk]
    ring

/-- Clean actual bigon boundary sides have closed full-lattice separation.
The source curve side is short; the straight side's short height is derived
from its actual family contacts rather than supplied as a width bound. -/
theorem clean_normalized_bigon_boundary_deck_free
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T) (hr : G r 0=c) (hs : G s 0=c)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s}) :
    ∀ i : ℤ×ℤ, i≠0 → Disjoint ((G '' Icc r s) ∪ segment ℝ (G r) (G s))
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
        ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) := by
  let K := G '' Icc r s
  let F := segment ℝ (G r) (G s)
  let L := ⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))
  have hheight := clean_fiber_side_has_short_height G T r s c hT hr hs hc hcontact
  have hFbox (z : Plane) (hz : z∈F) : c ≤ z 0 ∧ z 0 ≤ c+0 ∧
      min (G r 1) (G s 1) ≤ z 1 ∧ z 1 ≤ min (G r 1) (G s 1)+|G s 1-G r 1| := by
    change z∈segment ℝ (G r) (G s) at hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨u,hu,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change c ≤ u*(G s 0-G r 0)+G r 0 ∧
      u*(G s 0-G r 0)+G r 0 ≤ c+0 ∧
      min (G r 1) (G s 1) ≤ u*(G s 1-G r 1)+G r 1 ∧
      u*(G s 1-G r 1)+G r 1 ≤ min (G r 1) (G s 1)+|G s 1-G r 1|
    rw [hr,hs]
    rcases le_total (G r 1) (G s 1) with hle|hle
    · rw [min_eq_left hle,abs_of_nonneg (sub_nonneg.mpr hle)]
      constructor
      · ring_nf; exact le_rfl
      constructor
      · ring_nf; exact le_rfl
      constructor <;> nlinarith [hu.1,hu.2]
    · rw [min_eq_right hle,abs_of_nonpos (sub_nonpos.mpr hle)]
      constructor
      · ring_nf; exact le_rfl
      constructor
      · ring_nf; exact le_rfl
      constructor <;> nlinarith [hu.1,hu.2]
  have hFdeck := plane_narrow_box_lattice_disjoint F T c (min (G r 1) (G s 1))
    0 |G s 1-G r 1| hT hT hheight hFbox
  have hKdeck := normalized_plane_short_arc_deck_free G hG T r s hT hshort hp hc
  have hGL : range G⊆L := by
    rintro z ⟨u,rfl⟩
    refine mem_iUnion.mpr ⟨0,u,?_⟩
    ext q
    fin_cases q <;> simp [Plane.mk]
  have shiftG (x : ℝ) (i : ℤ×ℤ) : G x+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈L := by
    refine mem_iUnion.mpr ⟨i.2,x+(i.1:ℝ)*T,?_⟩
    dsimp only
    rw [hp]
    ext q
    fin_cases q <;> simp [Plane.mk]
  have negShiftG (x : ℝ) (i : ℤ×ℤ) : G x-Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)∈L := by
    have hh := shiftG x (-i)
    convert hh using 1
    ext q
    fin_cases q <;> simp [Plane.mk] <;> ring
  have hFK : F∩L⊆K := by
    rw [hcontact]
    intro z hz
    rcases hz with hh|hh
    · rw [hh]
      exact ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩
    · rw [mem_singleton_iff.mp hh]
      exact ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩
  intro i hi
  apply disjoint_left.mpr
  rintro z hz ⟨w,hw,heq⟩
  rcases hz with hzK|hzF <;> rcases hw with hwK|hwF
  · exact disjoint_left.mp (hKdeck i hi) hzK ⟨w,hwK,heq⟩
  · obtain ⟨x,hx,rfl⟩ := hzK
    have hwL : w∈L := by
      have hh := negShiftG x i
      have hwEq : w=G x-Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := by
        change w+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)=G x at heq
        exact eq_sub_iff_add_eq.mpr heq
      rwa [←hwEq] at hh
    exact disjoint_left.mp (hKdeck i hi) ⟨x,hx,rfl⟩ ⟨w,hFK ⟨hwF,hwL⟩,heq⟩
  · obtain ⟨x,hx,rfl⟩ := hwK
    have hzL : z∈L := heq ▸ shiftG x i
    exact disjoint_left.mp (hKdeck i hi) (hFK ⟨hzF,hzL⟩) ⟨G x,⟨x,hx,rfl⟩,heq⟩
  · exact disjoint_left.mp (hFdeck i hi) hzF ⟨w,hwF,heq⟩

#print axioms clean_fiber_side_has_short_height
#print axioms clean_normalized_bigon_boundary_deck_free

/-- Open Jordan-disk separation together with actual boundary separation
implies closed operation supports are disjoint. -/
theorem separated_open_jordan_disks_and_boundaries_closed_disjoint
    (C D : Set Plane) (hC : IsJordanCurve C) (hD : IsJordanCurve D)
    (hd : Disjoint (inside C) (inside D)) (hb : Disjoint C D) :
    Disjoint (closure (inside C)) (closure (inside D)) := by
  have hc := jordan_curve_theorem hC
  have hdd := jordan_curve_theorem hD
  have hleft : Disjoint (inside C) (closure (inside D)) := hd.closure_right hc.isOpen_inside
  have hright : Disjoint (closure (inside C)) (inside D) := hd.closure_left hdd.isOpen_inside
  apply disjoint_left.mpr
  intro z hzC hzD
  rw [closure_eq_self_union_frontier,hc.frontier_inside] at hzC
  rw [closure_eq_self_union_frontier,hdd.frontier_inside] at hzD
  rcases hzC with hzCi|hzCb
  · apply disjoint_left.mp hleft hzCi
    rw [closure_eq_self_union_frontier,hdd.frontier_inside]
    exact hzD
  · rcases hzD with hzDi|hzDb
    · apply disjoint_left.mp hright _ hzDi
      rw [closure_eq_self_union_frontier,hc.frontier_inside]
      exact Or.inr hzCb
    · exact disjoint_left.mp hb hzCb hzDb

/-- The actual clean normalized bigon admits closed full-lattice operation
support separation. Both its sides' width bounds are derived upstream from
source geometry; only the previously proved open separation is used. -/
theorem clean_normalized_bigon_closed_disk_deck_free
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T r s c : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T) (hr : G r 0=c) (hs : G s 0=c)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hcontact : segment ℝ (G r) (G s) ∩
      (⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)))={G r,G s})
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (hsep : Pairwise (fun i j : ℤ×ℤ => Disjoint
      (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
        ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
      (inside ((fun z : Plane => z+Plane.mk ((j.1:ℝ)*T) ((j.2:ℝ)*T)) ''
        ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))))) :
    ∀ i : ℤ×ℤ, i≠0 → Disjoint
      (closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))))
      ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ''
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))) := by
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  have hbound := clean_normalized_bigon_boundary_deck_free G hG T r s c hT hrs hshort hr hs hp hc hcontact
  intro i hi
  let e := Homeomorph.addRight (Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))
  have hD : IsJordanCurve (e '' C) := by
    obtain ⟨g,hg,hgC⟩ := hJ
    refine ⟨e ∘ g,⟨e.continuous.comp_continuousOn hg.continuousOn,?_,?_⟩,?_⟩
    · simp only [Function.comp_apply,hg.closes]
    · exact e.injective.injOn.comp hg.injOn (mapsTo_univ _ _)
    · rw [image_comp,hgC]
  have hopen : Disjoint (inside C) (inside (e '' C)) := by
    have hh := hsep (show (0:ℤ×ℤ)≠i from Ne.symm hi)
    have hzero : Plane.mk (0:ℝ) 0=0 := by ext q; fin_cases q <;> rfl
    change Disjoint (inside C) (inside ((fun z : Plane => z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) '' C))
    simpa only [Prod.fst_zero,Prod.snd_zero,Int.cast_zero,zero_mul,hzero,add_zero,image_id'] using hh
  have hh := separated_open_jordan_disks_and_boundaries_closed_disjoint C (e '' C) hJ hD hopen (hbound i hi)
  rw [←(plane_homeomorph_inside_transport e C).1,←e.image_closure] at hh
  exact hh

#print axioms separated_open_jordan_disks_and_boundaries_closed_disjoint
#print axioms clean_normalized_bigon_closed_disk_deck_free
