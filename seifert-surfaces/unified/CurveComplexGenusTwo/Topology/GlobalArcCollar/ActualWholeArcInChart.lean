import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches
import CurveComplexGenusTwo.Topology.FrontierCircle.BandStraightening

namespace CurveComplex
open Set Topology Schoenflies Metric

/-- Construct a whole strip around an actual planar embedded interval in any
prescribed open neighborhood. The center parametrization is exact, and all
nonzero transverse tracks avoid the whole original arc. -/
theorem source_whole_planar_arc_strip
    (f : C(Interval,Plane)) (hf : IsEmbedding f)
    (U : Set Plane) (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ E : Interval × Set.Icc (-1:ℝ) 1 → Plane,
      IsEmbedding E ∧ (∀ t, E (t,⟨0,by norm_num⟩) = f t) ∧
      Set.range E ⊆ U ∧
      ∀ z, E z ∈ Set.range f ↔ (z.2:ℝ) = 0 := by
  let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
  have hfc : Continuous fc := f.continuous.comp continuous_projIcc
  have hfcval (t : Interval) : fc t = f t := by
    simp [fc,Set.projIcc_of_mem zero_le_one t.property]
  have hfi : InjOn fc (Set.Icc (0:ℝ) 1) := by
    intro t ht u hu he
    have he' : f ⟨t,ht⟩ = f ⟨u,hu⟩ := by
      simpa only [← hfcval] using he
    exact congrArg Subtype.val (hf.injective he')
  have hfcim : fc '' Set.Icc (0:ℝ) 1 = Set.range f := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,ht⟩,by simp [fc,Set.projIcc_of_mem zero_le_one ht]⟩
    · rintro ⟨t,rfl⟩
      exact ⟨t,t.property,hfcval t⟩
  have hP : IsArcBetween (Set.range f) (f 0) (f 1) :=
    ⟨fc,hfc.continuousOn,hfi,hfcim,hfcval 0,hfcval 1⟩
  obtain ⟨A,hA,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hP
  obtain ⟨F,hF⟩ := exists_ambient_straightening_to_top hA hP hmeet hJ
  have hcoord (t : Interval) : F (f t) 1 = 1 := by
    apply (mem_sideTop.mp _).1
    exact hF ▸ Set.mem_image_of_mem F (Set.mem_range_self t)
  have hK : IsCompact (F '' Set.range f) :=
    (isCompact_range f.continuous).image F.continuous
  obtain ⟨δ,hδ,hδU⟩ := hK.exists_cthickening_subset_open
    (F.isOpenMap U hU) (Set.image_mono hfU)
  let E : Interval × Set.Icc (-1:ℝ) 1 → Plane :=
    fun z => F.symm (F (f z.1) + (δ*(z.2:ℝ)) • Plane.mk 0 1)
  have hEc : Continuous E := by
    dsimp [E]
    fun_prop
  have hEi : Function.Injective E := by
    intro z w he
    have he' := F.symm.injective he
    have hx := congrArg (fun q : Plane => q 0) he'
    have hy := congrArg (fun q : Plane => q 1) he'
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,Plane.mk] at hx hy
    norm_num at hx hy
    have hFsame : F (f z.1) = F (f w.1) := by
      ext i
      fin_cases i
      · exact hx
      · exact (hcoord z.1).trans (hcoord w.1).symm
    have ht : z.1 = w.1 := hf.injective (F.injective hFsame)
    have hw : z.2 = w.2 := by
      apply Subtype.ext
      rw [hcoord z.1,hcoord w.1] at hy
      have hh : δ*((z.2:ℝ)-(w.2:ℝ)) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hδ))
    exact Prod.ext ht hw
  have hEU : Set.range E ⊆ U := by
    rintro x ⟨z,rfl⟩
    have hd : dist (F (f z.1)+(δ*(z.2:ℝ)) • Plane.mk 0 1) (F (f z.1)) ≤ δ := by
      have hw : |(z.2:ℝ)| ≤ 1 := abs_le.mpr z.2.property
      have hm := mul_le_mul_of_nonneg_left hw hδ.le
      simpa [dist_eq_norm,norm_smul,abs_mul,abs_of_pos hδ,
        EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk] using hm
    obtain ⟨y,hy,hey⟩ := hδU
      (mem_cthickening_of_dist_le _ _ δ _
        (Set.mem_image_of_mem F (Set.mem_range_self z.1)) hd)
    change F.symm _ ∈ U
    rw [← hey,F.symm_apply_apply]
    exact hy
  refine ⟨E,(hEc.isClosedEmbedding hEi).isEmbedding,?_,hEU,?_⟩
  · intro t
    simp [E]
  · intro z
    constructor
    · rintro ⟨t,ht⟩
      have he : F (f t) = F (f z.1)+(δ*(z.2:ℝ)) • Plane.mk 0 1 := by
        rw [ht]
        exact F.apply_symm_apply _
      have hy := congrArg (fun q : Plane => q 1) he
      simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,Plane.mk] at hy
      norm_num at hy
      rw [hcoord t,hcoord z.1] at hy
      have hh : δ*(z.2:ℝ) = 0 := by linarith
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hδ)
    · intro hz
      refine ⟨z.1,?_⟩
      simp [E,hz]

/-- Whole-arc strip construction transported through an actual source chart.
This is a complete construction for arcs contained in that chart; nonzero
tracks avoid the entire original surface arc. -/
theorem source_whole_arc_strip_in_chart
    {S : Type} [TopologicalSpace S] [T2Space S]
    (e : OpenPartialHomeomorph S Plane)
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (hfe : Set.range f ⊆ e.source)
    (U : Set S) (hU : IsOpen U) (hfU : Set.range f ⊆ U) :
    ∃ E : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding E ∧ (∀ t, E (t,⟨0,by norm_num⟩) = f t) ∧
      Set.range E ⊆ U ∩ e.source ∧
      ∀ z, E z ∈ Set.range f ↔ (z.2:ℝ) = 0 := by
  let g : C(Interval,Plane) :=
    ⟨fun t => e (f t),by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact (e.continuousAt (hfe (Set.mem_range_self t))).comp f.continuous.continuousAt⟩
  have hgi : Function.Injective g := by
    intro t u he
    exact hf.injective (e.injOn (hfe (Set.mem_range_self t))
      (hfe (Set.mem_range_self u)) he)
  have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
  let V : Set Plane := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hgV : Set.range g ⊆ V := by
    rintro x ⟨t,rfl⟩
    refine ⟨e.map_source (hfe (Set.mem_range_self t)),?_⟩
    change e.symm (e (f t)) ∈ U
    rw [e.left_inv (hfe (Set.mem_range_self t))]
    exact hfU (Set.mem_range_self t)
  obtain ⟨B,hB,hcenter,hBV,hBavoid⟩ := source_whole_planar_arc_strip g hg V hV hgV
  have hBt (z) : B z ∈ e.target := (hBV (Set.mem_range_self z)).1
  let E : Interval × Set.Icc (-1:ℝ) 1 → S := e.symm ∘ B
  have hEc : Continuous E := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (e.continuousAt_symm (hBt z)).comp hB.continuous.continuousAt
  have hEi : Function.Injective E := by
    intro z w he
    exact hB.injective (e.symm.injOn (hBt z) (hBt w) he)
  refine ⟨E,(hEc.isClosedEmbedding hEi).isEmbedding,?_,?_,?_⟩
  · intro t
    change e.symm (B _) = f t
    rw [hcenter]
    exact e.left_inv (hfe (Set.mem_range_self t))
  · rintro x ⟨z,rfl⟩
    exact ⟨(hBV (Set.mem_range_self z)).2,e.map_target (hBt z)⟩
  · intro z
    constructor
    · rintro ⟨t,ht⟩
      apply (hBavoid z).mp
      refine ⟨t,?_⟩
      change e (f t) = B z
      rw [ht]
      exact e.right_inv (hBt z)
    · intro hz
      have hb : B z ∈ Set.range g := (hBavoid z).mpr hz
      obtain ⟨t,ht⟩ := hb
      refine ⟨t,?_⟩
      change f t = e.symm (B z)
      rw [← ht]
      exact (e.left_inv (hfe (Set.mem_range_self t))).symm

end CurveComplex

#print axioms CurveComplex.source_whole_planar_arc_strip
#print axioms CurveComplex.source_whole_arc_strip_in_chart
