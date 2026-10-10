import CurveComplexGenusTwo.Topology.ActualFareyClassification.JordanPairSquareChart
import Schoenflies.Concatenate

open Set Topology Schoenflies

/-- The actual upper half of the square boundary is an arc between edge
midpoints, rather than between corners. -/
theorem square_boundary_upper_midpoint_arc :
    IsArcBetween {z : Plane | z∈modelCurve ∧ 0≤z 1} (Plane.mk 1 0) (Plane.mk (-1) 0) := by
  let R := segment ℝ (Plane.mk 1 0) cornerNE
  let L := segment ℝ cornerNW (Plane.mk (-1) 0)
  have hR (z : Plane) : z∈R ↔ z 0=1 ∧ z 1∈Icc (0:ℝ) 1 := by
    dsimp [R,cornerNE]
    rw [mem_segment_vert]
    simp [segment_eq_Icc]
  have hL (z : Plane) : z∈L ↔ z 0= -1 ∧ z 1∈Icc (0:ℝ) 1 := by
    dsimp [L,cornerNW]
    rw [mem_segment_vert]
    rw [segment_symm]
    simp [segment_eq_Icc]
  have harR : IsArcBetween R (Plane.mk 1 0) cornerNE :=
    isArcBetween_segment (by intro he; have hh := congrArg (fun z : Plane => z 1) he; norm_num [cornerNE,Plane.mk] at hh)
  have harL : IsArcBetween L cornerNW (Plane.mk (-1) 0) :=
    isArcBetween_segment (by intro he; have hh := congrArg (fun z : Plane => z 1) he; norm_num [cornerNW,Plane.mk] at hh)
  have hRT : ∀ z∈R, z∈sideTop → z=cornerNE := by
    intro z hz ht
    have hr := (hR z).mp hz
    have ht' := mem_sideTop.mp ht
    ext i; fin_cases i <;> simp [cornerNE,Plane.mk,hr.1,ht'.1]
  have hRL : ∀ z∈R∪sideTop, z∈L → z=cornerNW := by
    intro z hz hl
    have hl' := (hL z).mp hl
    rcases hz with hz|hz
    · have hr := (hR z).mp hz
      linarith [hr.1,hl'.1]
    · have ht := mem_sideTop.mp hz
      ext i; fin_cases i <;> simp [cornerNW,Plane.mk,hl'.1,ht.1]
  have har := (harR.concatenate isArcBetween_sideTop hRT).concatenate harL hRL
  have hset : (R∪sideTop)∪L={z : Plane | z∈modelCurve ∧ 0≤z 1} := by
    ext z
    rw [mem_union,mem_union,hR,hL]
    constructor
    · rintro ((hr|ht)|hl)
      · refine ⟨?_,hr.2.1⟩
        change max |z 0| |z 1|=1
        rw [hr.1,abs_one,max_eq_left (abs_le.mpr ⟨by linarith [hr.2.1],hr.2.2⟩)]
      · have ht' := mem_sideTop.mp ht
        refine ⟨?_,by linarith [ht'.1]⟩
        change max |z 0| |z 1|=1
        rw [ht'.1,abs_one,max_eq_right ht'.2]
      · refine ⟨?_,hl.2.1⟩
        change max |z 0| |z 1|=1
        rw [hl.1,abs_neg,abs_one,max_eq_left (abs_le.mpr ⟨by linarith [hl.2.1],hl.2.2⟩)]
    · rintro ⟨hm,hy⟩
      change max |z 0| |z 1|=1 at hm
      have hx : |z 0|≤1 := (le_max_left _ _).trans hm.le
      have hy1 : z 1≤1 := by have hh := (le_max_right _ _).trans hm.le; rwa [abs_of_nonneg hy] at hh
      by_cases ht : z 1=1
      · exact Or.inl (Or.inr (mem_sideTop.mpr ⟨ht,hx⟩))
      have ha : |z 0|=1 := by
        have hh : |z 1|<1 := by rw [abs_of_nonneg hy]; exact lt_of_le_of_ne hy1 ht
        exact ((max_eq_iff.mp hm).resolve_right (by intro h; exact hh.ne h.1)).1
      rcases le_total 0 (z 0) with hp|hn
      · rw [abs_of_nonneg hp] at ha
        exact Or.inl (Or.inl ⟨ha,hy,hy1⟩)
      · rw [abs_of_nonpos hn] at ha
        exact Or.inr ⟨by linarith,hy,hy1⟩
  rwa [hset] at har

theorem square_boundary_midpoint_arc_pair :
    IsArcBetween {z : Plane | z∈modelCurve ∧ z 1≤0} (Plane.mk 1 0) (Plane.mk (-1) 0) ∧
    ({z : Plane | z∈modelCurve ∧ 0≤z 1}∩{z : Plane | z∈modelCurve ∧ z 1≤0})=
      {Plane.mk 1 0,Plane.mk (-1) 0} ∧
    ({z : Plane | z∈modelCurve ∧ 0≤z 1}∪{z : Plane | z∈modelCurve ∧ z 1≤0})=modelCurve := by
  have hN : (fun z : Plane => -z) '' {z : Plane | z∈modelCurve ∧ 0≤z 1}=
      {z : Plane | z∈modelCurve ∧ z 1≤0} := by
    ext z
    constructor
    · rintro ⟨w,⟨hm,hw⟩,rfl⟩
      refine ⟨?_,by simpa using neg_nonpos.mpr hw⟩
      change Plane.supNorm (-w)=1
      simpa [modelCurve,Plane.supNorm] using hm
    · rintro ⟨hm,hz⟩
      refine ⟨-z,⟨?_,by simpa using neg_nonneg.mpr hz⟩,neg_neg z⟩
      change Plane.supNorm (-z)=1
      simpa [modelCurve,Plane.supNorm] using hm
  have hB := square_boundary_upper_midpoint_arc.image_of_injOn (subset_univ _)
    (Homeomorph.neg Plane).continuous.continuousOn (Homeomorph.neg Plane).injective.injOn
  change IsArcBetween ((fun z : Plane => -z) '' {z : Plane | z∈modelCurve ∧ 0≤z 1})
    (-(Plane.mk 1 0)) (-(Plane.mk (-1) 0)) at hB
  rw [hN] at hB
  have he1 : -(Plane.mk 1 0)=Plane.mk (-1) 0 := by ext i; fin_cases i <;> simp [Plane.mk]
  have he2 : -(Plane.mk (-1) 0)=Plane.mk 1 0 := by ext i; fin_cases i <;> simp [Plane.mk]
  rw [he1,he2] at hB
  refine ⟨hB.reverse,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨⟨hm,hp⟩,⟨_,hn⟩⟩
      have hy : z 1=0 := le_antisymm hn hp
      have hx : |z 0|=1 := by
        change max |z 0| |z 1|=1 at hm
        simpa [hy] using hm
      rcases le_total 0 (z 0) with h|h
      · rw [abs_of_nonneg h] at hx
        left
        ext i; fin_cases i <;> simp [hx,hy]
      · rw [abs_of_nonpos h] at hx
        right
        apply mem_singleton_iff.mpr
        ext i; fin_cases i <;> simp [hy]; linarith
    · intro hz
      rcases hz with hz|hz
      · subst z; norm_num [modelCurve,Plane.supNorm,Plane.mk]
      · have he : z=Plane.mk (-1) 0 := hz
        subst z; norm_num [modelCurve,Plane.supNorm,Plane.mk]
  · ext z
    constructor
    · rintro (hz|hz) <;> exact hz.1
    · intro hz
      rcases le_total 0 (z 1) with hp|hn
      · exact Or.inl ⟨hz,hp⟩
      · exact Or.inr ⟨hz,hn⟩

#print axioms square_boundary_upper_midpoint_arc
#print axioms square_boundary_midpoint_arc_pair
