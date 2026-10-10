import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualPrefixStripAssembly
namespace CurveComplex
open Set Topology Schoenflies
private abbrev Width := Icc (-1:ℝ) 1

/-- An actual strip over an initial parameter segment. Its longitudinal
parametrization may vary; its center carrier and both endpoints are literal. -/
structure SourceArcPrefixStrip {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (U : Set S) (b : Interval) where
  map : Interval × Width → S
  embedded : IsEmbedding map
  image_subset : range map ⊆ U
  source : map (0,⟨0,by norm_num⟩) = f 0
  target : map (1,⟨0,by norm_num⟩) = f b
  center_range : range (fun t => map (t,⟨0,by norm_num⟩)) = f '' Icc 0 b
  avoids : ∀ z, map z ∈ range f ↔ (z.2:ℝ) = 0

/-- Exact affine parametrization of any nondegenerate interval segment. -/
theorem source_affine_subinterval (a b : Interval) (hab : (a:ℝ) < b) :
    ∃ q : C(Interval,Interval), IsEmbedding q ∧ q 0 = a ∧ q 1 = b ∧
      range q = Icc a b ∧ ∀ t, (q t:ℝ) = (a:ℝ)+((b:ℝ)-a)*(t:ℝ) := by
  let q : C(Interval,Interval) := ⟨fun t =>
    ⟨(a:ℝ)+((b:ℝ)-a)*(t:ℝ),by
      constructor
      · nlinarith [a.property.1,t.property.1]
      · nlinarith [b.property.2,t.property.2]⟩,by fun_prop⟩
  have hqi : Function.Injective q := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change (a:ℝ)+((b:ℝ)-a)*(t:ℝ) = (a:ℝ)+((b:ℝ)-a)*(u:ℝ) at hh
    nlinarith
  refine ⟨q,(q.continuous.isClosedEmbedding hqi).isEmbedding,?_,?_,?_,fun _ => rfl⟩
  · apply Subtype.ext; simp [q]
  · apply Subtype.ext; simp [q]
  · ext s
    constructor
    · rintro ⟨t,rfl⟩
      constructor
      · change (a:ℝ) ≤ (a:ℝ)+((b:ℝ)-a)*(t:ℝ)
        nlinarith [t.property.1]
      · change (a:ℝ)+((b:ℝ)-a)*(t:ℝ) ≤ (b:ℝ)
        nlinarith [t.property.2]
    · intro hs
      have hs' : (a:ℝ) ≤ s ∧ (s:ℝ) ≤ b := hs
      let t : Interval := ⟨((s:ℝ)-a)/((b:ℝ)-a),⟨
        div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr hab).le,
        (div_le_one (sub_pos.mpr hab)).mpr (by linarith [hs'.2])⟩⟩
      refine ⟨t,Subtype.ext ?_⟩
      change (a:ℝ)+((b:ℝ)-a)*(((s:ℝ)-a)/((b:ℝ)-a)) = (s:ℝ)
      field_simp [sub_ne_zero.mpr hab.ne']
      <;> ring

/-- The verified endpoint seed supplies an actual prefix strip. -/
theorem source_exists_initial_arc_prefix_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ b : Interval, 0 < (b:ℝ) ∧ (b:ℝ) < 1 ∧ Nonempty (SourceArcPrefixStrip f U b) := by
  obtain ⟨b,hb,hb1,B,hB,hBU,hcenter,havoid⟩ :=
    source_embedded_arc_initial_strip f hf U hU hfU
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval 0 b hb
  have hcentq (t) : B (t,⟨0,by norm_num⟩) = f (q t) := by
    rw [hcenter]
    apply congrArg f
    apply Subtype.ext
    simpa using (hqval t).symm
  refine ⟨b,hb,hb1,⟨⟨B,hB,hBU,?_,?_,?_,havoid⟩⟩⟩
  · rw [hcentq,hq0]
  · rw [hcentq,hq1]
  · have hh : (fun t => B (t,⟨0,by norm_num⟩)) = f ∘ q := funext hcentq
    rw [hh,range_comp,hqrange]
/-- Extend an already constructed actual prefix strip across one chart. The
compatible strips are produced by normalization and exterior-whisker geometry;
the extra terminal margin restores avoidance of the whole original arc. -/
theorem source_extend_arc_prefix_strip
    {S : Type} [TopologicalSpace S] [T2Space S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U)
    (b c d : Interval) (hbc : (b:ℝ) < c) (hcd : (c:ℝ) ≤ d)
    (hmargin : (c:ℝ) < d ∨ d = 1)
    (B : SourceArcPrefixStrip f U b)
    (e : OpenPartialHomeomorph S Plane) (hchart : f '' Icc b d ⊆ e.source) :
    Nonempty (SourceArcPrefixStrip f U c) := by
  classical
  have hbd : (b:ℝ) < d := hbc.trans_le hcd
  obtain ⟨q,hq,hq0,hq1,hqrange,hqval⟩ := source_affine_subinterval b d hbd
  let Q : C(Interval,S) := f.comp q
  have hQ : IsEmbedding Q := hf.comp hq
  have hQstart : Q 0 = B.map (1,⟨0,by norm_num⟩) := by
    change f (q 0) = _
    rw [hq0,B.target]
  have hQmeet : range Q ∩ range B.map = {Q 0} := by
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,z,hz⟩
      have hz0 := (B.avoids z).mp (hz ▸ mem_range_self (q t))
      have hez : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz0)
      have hzcent : B.map z ∈ f '' Icc 0 b := by
        rw [← B.center_range]
        exact ⟨z.1,by rw [hez]⟩
      obtain ⟨s,hs,hes⟩ := hzcent
      have hsqt : s = q t := hf.injective (hes.trans hz)
      have hqt : b ≤ q t := (hqrange ▸ mem_range_self t).1
      have heqb : q t = b := le_antisymm (hsqt ▸ hs.2) hqt
      change Q t = Q 0
      change f (q t) = f (q 0)
      rw [heqb,hq0]
    · intro hx
      have he : x = Q 0 := hx
      rw [he]
      exact ⟨mem_range_self (0:Interval),⟨(1,⟨0,by norm_num⟩),hQstart.symm⟩⟩
  have hQe : range Q ⊆ e.source := by
    change range (f ∘ q) ⊆ e.source
    rw [range_comp,hqrange]
    exact hchart
  obtain ⟨L,R,hL,hR,hLc,hRc,hLB,hRU,hseam,hmeet⟩ :=
    source_attach_chart_arc_to_surface_strip B.map B.embedded Q hQ hQstart hQmeet
      e hQe U hU B.image_subset (by rintro x ⟨t,rfl⟩; exact hfU (mem_range_self (q t)))
  have hLcenter : range (fun t => L (t,⟨0,by norm_num⟩)) = f '' Icc 0 b := by
    have hh : (fun t => L (t,⟨0,by norm_num⟩)) =
        (fun t => B.map (t,⟨0,by norm_num⟩)) := funext hLc
    rw [hh,B.center_range]
  let A : Set S := f '' Icc 0 d
  have hLA (z) : L z ∈ A ↔ (z.2:ℝ) = 0 := by
    constructor
    · intro hz
      obtain ⟨v,hv⟩ := hLB (mem_range_self z)
      have hv0 : (v.2:ℝ) = 0 := (B.avoids v).mp
        (hv ▸ image_subset_range _ _ hz)
      have he : v = (v.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hv0)
      have hh : L z = L (v.1,⟨0,by norm_num⟩) := by
        rw [hLc,← he]
        exact hv.symm
      exact congrArg (fun z : Interval × Width => (z.2:ℝ)) (hL.injective hh)
    · intro hz0
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz0)
      rw [he]
      exact image_mono (Icc_subset_Icc le_rfl (show b ≤ d from hbd.le))
        (hLcenter ▸ mem_range_self z.1)
  have hRA (z) : R z ∈ A ↔ (z.2:ℝ) = 0 := by
    constructor
    · rintro ⟨s,hs,he⟩
      by_cases hsb : s ≤ b
      · have hsL : f s ∈ range (fun t => L (t,⟨0,by norm_num⟩)) := by
          rw [hLcenter]
          exact ⟨s,⟨hs.1,hsb⟩,rfl⟩
        obtain ⟨t,ht⟩ := hsL
        have hm : R z ∈ range L ∩ range R :=
          ⟨⟨(t,⟨0,by norm_num⟩),ht.trans he⟩,mem_range_self z⟩
        rw [hmeet] at hm
        obtain ⟨w,hw⟩ := hm
        have hw0 : (w:ℝ) = 0 := by
          have hh := hL.injective (hw.trans (ht.trans he).symm)
          exact congrArg (fun z : Interval × Width => (z.2:ℝ)) hh
        have hzEq : z = (0,w) := hR.injective (hw.symm.trans (hseam w))
        simpa only [hzEq] using hw0
      · have hsbd : s ∈ Icc b d := ⟨(lt_of_not_ge hsb).le,hs.2⟩
        obtain ⟨t,ht⟩ := (hqrange.symm ▸ hsbd : s ∈ range q)
        have hh : R (t,⟨0,by norm_num⟩) = R z := by
          rw [hRc]
          change f (q t) = R z
          rw [ht,he]
        have hzEq := hR.injective hh
        exact (congrArg (fun z : Interval × Width => (z.2:ℝ)) hzEq).symm
    · intro hz0
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz0)
      rw [he,hRc]
      refine ⟨q z.1,?_,rfl⟩
      exact ⟨(show (0:Interval) ≤ b from b.property.1).trans
        (hqrange ▸ mem_range_self z.1).1,(hqrange ▸ mem_range_self z.1).2⟩
  let r : ℝ := ((c:ℝ)-b)/((d:ℝ)-b)
  have hr : 0 < r ∧ r ≤ 1 :=
    ⟨div_pos (sub_pos.mpr hbc) (sub_pos.mpr hbd),
      (div_le_one (sub_pos.mpr hbd)).mpr (by linarith)⟩
  let k : Interval × Width → Interval × Width := fun z =>
    (⟨r*(z.1:ℝ),⟨mul_nonneg hr.1.le z.1.property.1,
      (mul_le_mul_of_nonneg_left z.1.property.2 hr.1.le).trans (by simpa using hr.2)⟩⟩,z.2)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Prod.ext
    · exact Subtype.ext (mul_left_cancel₀ hr.1.ne' (congrArg (fun z => (z.1:ℝ)) he))
    · simpa only [k] using congrArg Prod.snd he
  let R' := R ∘ k
  have hR' : IsEmbedding R' := ((hR.continuous.comp hkc).isClosedEmbedding
    (hR.injective.comp hki)).isEmbedding
  have hkzero (w) : k (0,w) = (0,w) := by
    apply Prod.ext
    · exact Subtype.ext (mul_zero _)
    · rfl
  have hseam' (w) : L (1,w) = R' (0,w) := by
    change L (1,w) = R (k (0,w))
    rw [hkzero,hseam]
  have hmeet' : range L ∩ range R' = range (fun w => L (1,w)) := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ (range_comp_subset_range _ _)).trans hmeet.le
    · rintro x ⟨w,rfl⟩
      exact ⟨mem_range_self (1,w),⟨(0,w),(hseam' w).symm⟩⟩
  obtain ⟨qc,hqc,hqc0,hqc1,hqcrange,hqcval⟩ := source_affine_subinterval b c hbc
  have hR'c (t) : R' (t,⟨0,by norm_num⟩) = f (qc t) := by
    change R (k (t,⟨0,by norm_num⟩)) = _
    rw [hRc]
    apply congrArg f
    apply Subtype.ext
    rw [hqval,hqcval]
    change (b:ℝ)+((d:ℝ)-b)*(r*(t:ℝ)) = (b:ℝ)+((c:ℝ)-b)*(t:ℝ)
    dsimp [r]
    field_simp [sub_ne_zero.mpr hbd.ne']
    <;> ring
  have hR'center : range (fun t => R' (t,⟨0,by norm_num⟩)) = f '' Icc b c := by
    have hh : (fun t => R' (t,⟨0,by norm_num⟩)) = f ∘ qc := funext hR'c
    rw [hh,range_comp,hqcrange]
  obtain ⟨G,hG,hGU,hG0,hG1,hGcent,hGA⟩ :=
    source_glue_strips_with_center_carrier L R' hL hR' hseam' hmeet' A U
      (hLB.trans B.image_subset) ((range_comp_subset_range _ _).trans hRU)
      hLA (fun z => hRA (k z))
  have hGsource : G (0,⟨0,by norm_num⟩) = f 0 :=
    hG0.trans ((hLc 0).trans B.source)
  have hGtarget : G (1,⟨0,by norm_num⟩) = f c := by
    rw [hG1,hR'c,hqc1]
  have hGcenter : range (fun t => G (t,⟨0,by norm_num⟩)) = f '' Icc 0 c := by
    rw [hGcent,hLcenter,hR'center,← image_union,Icc_union_Icc_eq_Icc
      (show (0:Interval) ≤ b from b.property.1) (show b ≤ c from hbc.le)]
  rcases hmargin with hmargin | hd1
  · let Tail := f '' Icc d 1
    have hTail : IsClosed Tail := (isCompact_Icc.image f.continuous).isClosed
    have hGUt (t) : G (t,⟨0,by norm_num⟩) ∈ U \ Tail := by
      refine ⟨hGU ⟨(t,⟨0,by norm_num⟩),rfl⟩,?_⟩
      have hc := hGcenter ▸ mem_range_self t
      obtain ⟨s,hs,hes⟩ := hc
      rintro ⟨u,hu,he⟩
      have hEq : u = s := hf.injective (he.trans hes.symm)
      have hsd : d ≤ s := hEq ▸ hu.1
      have hsc : s ≤ c := hs.2
      exact not_le_of_gt hmargin (show (d:ℝ) ≤ c from hsd.trans hsc)
    obtain ⟨ρ,hρ,N,hN,hNU,hNC,hNcent⟩ :=
      source_shrink_embedded_strip_in_open G hG (U \ Tail) (hU.sdiff hTail) hGUt
    refine ⟨⟨N,hN,fun x hx => (hNU hx).1,?_,?_,?_,?_⟩⟩
    · rw [hNcent,hGsource]
    · rw [hNcent,hGtarget]
    · have hh : (fun t => N (t,⟨0,by norm_num⟩)) =
          (fun t => G (t,⟨0,by norm_num⟩)) := funext hNcent
      rw [hh,hGcenter]
    · intro z
      constructor
      · rintro ⟨s,hs⟩
        have hsD : s ≤ d := by
          by_contra hn
          exact (hNU (mem_range_self z)).2 ⟨s,⟨(lt_of_not_ge hn).le,s.property.2⟩,hs⟩
        have hzA : N z ∈ A := ⟨s,⟨s.property.1,hsD⟩,hs⟩
        rw [hNC] at hzA
        have hh := (hGA _).mp hzA
        change ρ*(z.2:ℝ) = 0 at hh
        exact (mul_eq_zero.mp hh).resolve_left hρ.1.ne'
      · intro hz
        have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz)
        rw [he,hNcent]
        exact image_subset_range _ _ (hGcenter ▸ mem_range_self z.1)
  · have hAfull : A = range f := by
      change f '' Icc 0 d = range f
      rw [hd1,← unitInterval.univ_eq_Icc,image_univ]
    refine ⟨⟨G,hG,hGU,hGsource,hGtarget,hGcenter,?_⟩⟩
    intro z
    rw [← hAfull]
    exact hGA z

end CurveComplex
#print axioms CurveComplex.source_affine_subinterval
#print axioms CurveComplex.source_exists_initial_arc_prefix_strip

#print axioms CurveComplex.source_extend_arc_prefix_strip
