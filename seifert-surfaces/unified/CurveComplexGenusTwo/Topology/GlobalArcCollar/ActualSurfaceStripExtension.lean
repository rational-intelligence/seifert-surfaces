import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInitialArcStrip
import CurveComplexGenusTwo.Topology.BandGlobalGluing.ActualWholeWhiskerHalfCollarScaffold
namespace CurveComplex
open Set Topology Schoenflies Metric
private abbrev Width := Icc (-1:ℝ) 1

/-- A terminal square is constructed inside the next source chart by narrowing
an existing strip uniformly; no whole-strip chart containment is assumed. -/
theorem source_terminal_strip_square_in_chart
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Interval × Width → S) (hB : IsEmbedding B)
    (e : OpenPartialHomeomorph S Plane)
    (hbe : B (1,⟨0,by norm_num⟩) ∈ e.source) :
    ∃ η a : ℝ, ∃ hη : 0 < η ∧ η ≤ 1,
      0 < a ∧ a < 1 ∧
      ∃ T : ↥(Plane.closedSquare 0 1) → S,
        IsEmbedding T ∧ range T ⊆ e.source ∧ range T ⊆ range B ∧
        (∀ w : Width, T ⟨Plane.mk 1 w,by
          rw [mem_closedSquare_zero_one]
          change max |(1:ℝ)| |(w:ℝ)| ≤ 1
          exact max_le (by norm_num) (abs_le.mpr w.property)⟩ =
          B (1,⟨η*(w:ℝ),by constructor <;>
            nlinarith [hη.1,hη.2,w.property.1,w.property.2]⟩)) ∧
        (∀ t : Interval, a ≤ (t:ℝ) → ∀ w : Width,
          B (t,⟨η*(w:ℝ),by constructor <;>
            nlinarith [hη.1,hη.2,w.property.1,w.property.2]⟩) ∈ range T) := by
  have hopen : IsOpen (B ⁻¹' e.source) := e.open_source.preimage hB.continuous
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hbe)
  let η : ℝ := min (r/2) (1/2)
  have hη : 0 < η ∧ η ≤ 1 := by
    constructor
    · dsimp [η]; positivity
    · have hh := min_le_right (r/2) (1/2:ℝ); dsimp [η]; linarith
  have hηhalf : η ≤ 1/2 := min_le_right _ _
  have hηr : η < r := by
    have hh := min_le_left (r/2) (1/2:ℝ); dsimp [η]; linarith
  let a : ℝ := 1-η
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith [hη.1]
  have hx (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 0 ∧ (z:Plane) 0 ≤ 1 :=
    abs_le.mp ((Plane.abs_zero_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
  have hy (z : ↥(Plane.closedSquare 0 1)) : -1 ≤ (z:Plane) 1 ∧ (z:Plane) 1 ≤ 1 :=
    abs_le.mp ((Plane.abs_one_le_supNorm z).trans (mem_closedSquare_zero_one.mp z.property))
  let k : ↥(Plane.closedSquare 0 1) → Interval × Width := fun z =>
    (⟨a+η*((z:Plane) 0+1)/2,by
      constructor <;> dsimp [a] <;> nlinarith [(hx z).1,(hx z).2,hη.1,hη.2]⟩,
     ⟨η*(z:Plane) 1,by constructor <;> nlinarith [(hy z).1,(hy z).2,hη.1,hη.2]⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    have h0 := congrArg (fun q => (q.1:ℝ)) he
    have h1 := congrArg (fun q => (q.2:ℝ)) he
    apply Subtype.ext
    ext i
    fin_cases i
    · change a+η*((z:Plane) 0+1)/2 = a+η*((w:Plane) 0+1)/2 at h0
      change (z:Plane) 0 = (w:Plane) 0
      nlinarith [hη.1]
    · change η*(z:Plane) 1 = η*(w:Plane) 1 at h1
      exact mul_left_cancel₀ hη.1.ne' h1
  let T := B ∘ k
  letI : CompactSpace ↥(Plane.closedSquare 0 1) := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  have hT : IsEmbedding T := ((hB.continuous.comp hkc).isClosedEmbedding
    (hB.injective.comp hki)).isEmbedding
  have hTe : range T ⊆ e.source := by
    rintro x ⟨z,rfl⟩
    apply hball
    rw [mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
    apply max_lt
    · change |(a+η*((z:Plane) 0+1)/2)-1| < r
      apply abs_lt.mpr
      dsimp [a]
      constructor <;> nlinarith [(hx z).1,(hx z).2,hη.1]
    · change |η*(z:Plane) 1-0| < r
      rw [sub_zero,abs_mul,abs_of_pos hη.1]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr (hy z)) hη.1.le).trans_lt
        (by simpa using hηr)
  refine ⟨η,a,hη,ha,ha1,T,hT,hTe,range_comp_subset_range _ _,?_,?_⟩
  · intro w
    apply congrArg B
    apply Prod.ext
    · apply Subtype.ext
      change a+η*(1+1)/2 = 1
      dsimp [a]
      ring
    · apply Subtype.ext
      rfl
  · intro t ht w
    let x : ℝ := 2*((t:ℝ)-a)/η-1
    have hx' : -1 ≤ x ∧ x ≤ 1 := by
      dsimp [x]
      have hlow : 0 ≤ ((t:ℝ)-a)/η := div_nonneg (sub_nonneg.mpr ht) hη.1.le
      have hhigh : ((t:ℝ)-a)/η ≤ 1 := (div_le_one hη.1).mpr (by dsimp [a]; linarith [t.property.2])
      rw [mul_div_assoc]
      constructor <;> linarith
    have hp : Plane.mk x w ∈ Plane.closedSquare 0 1 := by
      rw [mem_closedSquare_zero_one]
      change max |x| |(w:ℝ)| ≤ 1
      exact max_le (abs_le.mpr hx') (abs_le.mpr w.property)
    refine ⟨⟨Plane.mk x w,hp⟩,?_⟩
    apply congrArg B
    apply Prod.ext
    · apply Subtype.ext
      change a+η*(x+1)/2 = (t:ℝ)
      dsimp [x]
      field_simp [hη.1.ne']
      <;> ring
    · apply Subtype.ext
      rfl
/-- Attach an actual chart-contained exterior arc to an existing surface strip.
Both half-strips and their exact common seam are constructed, with no compatible
strip/collar input. Only the center arc's geometric incidence is supplied. -/
theorem source_attach_chart_arc_to_surface_strip
    {S : Type} [TopologicalSpace S] [T2Space S]
    (B : Interval × Width → S) (hB : IsEmbedding B)
    (Q : C(Interval,S)) (hQ : IsEmbedding Q)
    (hstart : Q 0 = B (1,⟨0,by norm_num⟩))
    (hmeet : range Q ∩ range B = {Q 0})
    (e : OpenPartialHomeomorph S Plane) (hQe : range Q ⊆ e.source)
    (U : Set S) (hU : IsOpen U) (hBU : range B ⊆ U) (hQU : range Q ⊆ U) :
    ∃ L R : Interval × Width → S,
      IsEmbedding L ∧ IsEmbedding R ∧
      (∀ t, L (t,⟨0,by norm_num⟩) = B (t,⟨0,by norm_num⟩)) ∧
      (∀ t, R (t,⟨0,by norm_num⟩) = Q t) ∧
      range L ⊆ range B ∧ range R ⊆ U ∧
      (∀ w, L (1,w) = R (0,w)) ∧
      range L ∩ range R = range (fun w => L (1,w)) := by
  classical
  have hbe : B (1,⟨0,by norm_num⟩) ∈ e.source :=
    hstart ▸ hQe (mem_range_self (0:Interval))
  obtain ⟨η,a,hη,ha,ha1,T,hT,hTe,hTB,hTport,hfill⟩ :=
    source_terminal_strip_square_in_chart B hB e hbe
  letI : CompactSpace ↥(Plane.closedSquare 0 1) := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  have hATc : Continuous (e ∘ T) :=
    e.continuousOn.comp_continuous hT.continuous (fun z => hTe (mem_range_self z))
  have hATi : Function.Injective (e ∘ T) := by
    intro z w he
    exact hT.injective (e.injOn (hTe (mem_range_self z)) (hTe (mem_range_self w)) he)
  obtain ⟨H,hH⟩ := exists_ambient_extension_of_embedded_closed_square
    (e ∘ T) ((hATc.isClosedEmbedding hATi).isEmbedding)
  have hHport (w : Width) : H (Plane.mk 1 w) =
      e (B (1,⟨η*(w:ℝ),by constructor <;>
        nlinarith [hη.1,hη.2,w.property.1,w.property.2]⟩)) := by
    have hh := hH ⟨Plane.mk 1 w,by
      rw [mem_closedSquare_zero_one]
      change max |(1:ℝ)| |(w:ℝ)| ≤ 1
      exact max_le (by norm_num) (abs_le.mpr w.property)⟩
    change H (Plane.mk 1 w) = e (T _) at hh
    rw [hTport] at hh
    exact hh
  let ai : Interval := ⟨a,⟨ha.le,ha1.le⟩⟩
  let F : Set S := B '' ((Iic ai) ×ˢ univ)
  have hF : IsClosed F := ((isClosed_Iic.isCompact.prod isCompact_univ).image hB.continuous).isClosed
  have hQF (t : Interval) : Q t ∉ F := by
    rintro ⟨z,hz,he⟩
    have hh : Q t ∈ range Q ∩ range B := ⟨mem_range_self t,⟨z,he⟩⟩
    rw [hmeet] at hh
    have hEq : Q t = Q 0 := hh
    have hbEq : B z = B (1,⟨0,by norm_num⟩) := he.trans (hEq.trans hstart)
    have htEq := congrArg (fun z : Interval × Width => (z.1:ℝ)) (hB.injective hbEq)
    have hza : (z.1:ℝ) ≤ a := hz.1
    rw [htEq] at hza
    norm_num at hza
    linarith
  let q : Interval → Plane := fun t => H.symm (e (Q t))
  have hqc : Continuous q := H.symm.continuous.comp
    (e.continuousOn.comp_continuous Q.continuous (fun t => hQe (mem_range_self t)))
  have hqi : Function.Injective q := by
    intro t u he
    exact hQ.injective (e.injOn (hQe (mem_range_self t))
      (hQe (mem_range_self u)) (H.symm.injective he))
  have hq0 : q 0 = Plane.mk 1 0 := by
    apply H.injective
    change H (H.symm (e (Q 0))) = H (Plane.mk 1 0)
    rw [H.apply_symm_apply,hstart]
    have hh := hHport (⟨0,by norm_num⟩:Width)
    simpa only [mul_zero] using hh.symm
  let p : Path (Plane.mk 1 0) (q 1) :=
    { toFun := q
      continuous_toFun := hqc
      source' := hq0
      target' := rfl }
  have hp : IsEmbedding p := (hqc.isClosedEmbedding hqi).isEmbedding
  have hpmeet : range p ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0} := by
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      have heEq : e (Q t) = e (T ⟨p t,ht⟩) := by
        have hh := hH ⟨p t,ht⟩
        change H (q t) = e (T _) at hh
        simpa only [q,H.apply_symm_apply] using hh
      have hEq : Q t = T ⟨p t,ht⟩ := e.injOn
        (hQe (mem_range_self t)) (hTe (mem_range_self _)) heEq
      have hm : Q t ∈ range Q ∩ range B :=
        ⟨mem_range_self t,hEq ▸ hTB (mem_range_self _)⟩
      rw [hmeet] at hm
      have ht0 : t = 0 := hQ.injective hm
      subst t
      exact hq0
    · intro hx
      have he : x = Plane.mk 1 0 := hx
      rw [he]
      refine ⟨⟨0,hq0⟩,?_⟩
      rw [mem_closedSquare_zero_one]
      norm_num [Plane.supNorm,Plane.mk]
  let V : Set Plane := H ⁻¹' (e.target ∩ e.symm ⁻¹' (U \ F))
  have hV : IsOpen V := (e.isOpen_inter_preimage_symm (hU.sdiff hF)).preimage H.continuous
  have hpV : range p ⊆ V := by
    rintro x ⟨t,rfl⟩
    change H (q t) ∈ e.target ∩ e.symm ⁻¹' (U \ F)
    rw [show H (q t) = e (Q t) from H.apply_symm_apply _]
    refine ⟨e.map_source (hQe (mem_range_self t)),?_⟩
    change e.symm (e (Q t)) ∈ U \ F
    rw [e.left_inv (hQe (mem_range_self t))]
    exact ⟨hQU (mem_range_self t),hQF t⟩
  obtain ⟨ρ,hρ,hρ1,P,hP,hPport,hPcent,hPV,hPmeet⟩ :=
    actual_whole_exterior_whisker_half_collar p hp hpmeet V hV hpV
  have hHP (z) : H (P z) ∈ e.target := (hPV (mem_range_self z)).1
  let R : Interval × Width → S := e.symm ∘ H ∘ P
  have hRc : Continuous R := e.continuousOn_symm.comp_continuous
    (H.continuous.comp hP.continuous) hHP
  have hRi : Function.Injective R := by
    intro z w he
    exact hP.injective (H.injective (e.symm.injOn (hHP z) (hHP w) he))
  have hR : IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
  have hRF (z) : R z ∈ U \ F := (hPV (mem_range_self z)).2
  have hRcent (t) : R (t,⟨0,by norm_num⟩) = Q t := by
    change e.symm (H (P _)) = _
    rw [hPcent]
    change e.symm (H (H.symm (e (Q t)))) = _
    rw [H.apply_symm_apply,e.left_inv (hQe (mem_range_self t))]
  let θ := η*ρ
  have hθ : 0 < θ ∧ θ ≤ 1 :=
    ⟨mul_pos hη.1 hρ,mul_le_one₀ hη.2 hρ.le hρ1⟩
  let k : Interval × Width → Interval × Width := fun z =>
    (z.1,⟨θ*(z.2:ℝ),by constructor <;>
      nlinarith [hθ.1,hθ.2,z.2.property.1,z.2.property.2]⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Prod.ext
    · simpa only [k] using congrArg Prod.fst he
    · apply Subtype.ext
      exact mul_left_cancel₀ hθ.1.ne' (congrArg (fun z => (z.2:ℝ)) he)
  let L := B ∘ k
  have hL : IsEmbedding L := ((hB.continuous.comp hkc).isClosedEmbedding
    (hB.injective.comp hki)).isEmbedding
  have hport (w : Width) : R (0,w) = L (1,w) := by
    let u : Width := ⟨ρ*(w:ℝ),by constructor <;>
      nlinarith [hρ,hρ1,w.property.1,w.property.2]⟩
    have hPu : P (0,w) = Plane.mk 1 u := hPport w
    change e.symm (H (P (0,w))) = B (k (1,w))
    rw [hPu,hHport u]
    have hBrange : B (1,⟨η*(u:ℝ),by constructor <;>
        nlinarith [hη.1,hη.2,u.property.1,u.property.2]⟩) ∈ e.source := by
      rw [← hTport u]
      exact hTe (mem_range_self _)
    rw [e.left_inv hBrange]
    apply congrArg B
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change η*(ρ*(w:ℝ)) = (η*ρ)*(w:ℝ)
      ring
  refine ⟨L,R,hL,hR,?_,hRcent,range_comp_subset_range _ _,
    fun x hx => by obtain ⟨z,rfl⟩ := hx; exact (hRF z).1,
    fun w => (hport w).symm,?_⟩
  · intro t
    apply congrArg B
    exact Prod.ext rfl (Subtype.ext (mul_zero _))
  · ext x
    constructor
    · rintro ⟨⟨z,rfl⟩,w,hw⟩
      have hza : a ≤ (z.1:ℝ) := by
        by_contra hn
        exact (hRF w).2 ⟨k z,⟨(not_le.mp hn).le,mem_univ _⟩,hw.symm⟩
      let u : Width := ⟨ρ*(z.2:ℝ),by constructor <;>
        nlinarith [hρ,hρ1,z.2.property.1,z.2.property.2]⟩
      have hLT : L z ∈ range T := by
        have hh := hfill z.1 hza u
        convert hh using 1
        apply congrArg B
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          change (η*ρ)*(z.2:ℝ) = η*(ρ*(z.2:ℝ))
          ring
      obtain ⟨v,hv⟩ := hLT
      have hnorm : P w = (v:Plane) := by
        apply H.injective
        have hh := congrArg e (hw.trans hv.symm)
        change e (e.symm (H (P w))) = e (T v) at hh
        rw [e.right_inv (hHP w)] at hh
        exact hh.trans (hH v).symm
      have hPm : P w ∈ range P ∩ Plane.closedSquare 0 1 :=
        ⟨mem_range_self w,hnorm ▸ v.property⟩
      rw [hPmeet] at hPm
      obtain ⟨v',_,hv'⟩ := hPm
      have hPw : P w = P (0,v') := hv'.symm.trans (hPport v').symm
      have hRw : R w = R (0,v') := congrArg (fun x => e.symm (H x)) hPw
      exact ⟨v',(hport v').symm.trans (hRw.symm.trans hw)⟩
    · rintro ⟨w,rfl⟩
      exact ⟨mem_range_self (1,w),⟨(0,w),hport w⟩⟩

end CurveComplex
#print axioms CurveComplex.source_terminal_strip_square_in_chart

#print axioms CurveComplex.source_attach_chart_arc_to_surface_strip
