import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualWholeArcInChart
import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision

namespace CurveComplex
open Set Topology Schoenflies

/-- Simultaneous open separation of every disjoint pair of compact members of
an arbitrary finite family. It requires only Hausdorffness. -/
theorem source_finite_compact_open_separation
    {S K : Type*} [TopologicalSpace S] [T2Space S] [Fintype K]
    (C : K → Set S) (hC : ∀ k, IsCompact (C k)) :
    ∃ V : K → Set S, (∀ k, IsOpen (V k) ∧ C k ⊆ V k) ∧
      ∀ i j, Disjoint (C i) (C j) → Disjoint (V i) (V j) := by
  classical
  have hex (i j : K) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ C i ⊆ A ∧ C j ⊆ B ∧
      (Disjoint (C i) (C j) → Disjoint A B) := by
    by_cases hd : Disjoint (C i) (C j)
    · obtain ⟨A,B,hA,hB,hCA,hCB,hAB⟩ :=
        SeparatedNhds.of_isCompact_isCompact (hC i) (hC j) hd
      exact ⟨A,B,hA,hB,hCA,hCB,fun _ => hAB⟩
    · exact ⟨univ,univ,isOpen_univ,isOpen_univ,subset_univ _,subset_univ _,
        fun h => (hd h).elim⟩
  choose A B hA hB hCA hCB hAB using hex
  let V : K → Set S := fun i => ⋂ j, A i j ∩ B j i
  refine ⟨V,?_,?_⟩
  · intro i
    exact ⟨isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i)),
      fun x hx => mem_iInter.mpr (fun j => ⟨hCA i j hx,hCB j i hx⟩)⟩
  · intro i j hd
    exact (hAB i j hd).mono
      (fun x hx => ((mem_iInter.mp hx) j).1)
      (fun x hx => ((mem_iInter.mp hx) i).2)

/-- Construct chart-contained compact strips on every member of an equal-mesh
subdivision of an actual embedded surface interval, inside the prescribed open
set. Every nonincident pair of strips is disjoint. No charts or strips are
supplied. Adjacent strips have the same exact center at their common endpoint;
compatibility of their whole transverse seams is not asserted here. -/
theorem source_embedded_arc_finite_chart_strips
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Plane S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ n : ℕ, ∃ hn : 0 < n,
      ∃ q : Fin n → C(Interval,Interval),
      ∃ e : Fin n → OpenPartialHomeomorph S Plane,
      ∃ B : Fin n → Interval × Icc (-1:ℝ) 1 → S,
        (∀ k t, (q k t : ℝ) = ((k.val:ℝ)+(t:ℝ))/n) ∧
        (∀ k, IsEmbedding (q k)) ∧
        (∀ k, range (f ∘ q k) ⊆ (e k).source) ∧
        (∀ k, IsEmbedding (B k)) ∧
        (∀ k t, B k (t,⟨0,by norm_num⟩) = f (q k t)) ∧
        (∀ k, range (B k) ⊆ U ∩ (e k).source) ∧
        (∀ i j, i.val+1 < j.val → Disjoint (range (B i)) (range (B j))) ∧
        range f = ⋃ k, range (f ∘ q k) := by
  classical
  let V : S → Set S := fun x => U ∩ (chartAt Plane x).source
  have hV (x) : IsOpen (V x) := hU.inter (chartAt Plane x).open_source
  have hcov (t : Interval) : ∃ x, f t ∈ V x :=
    ⟨f t,hfU (mem_range_self t),mem_chart_source _ _⟩
  obtain ⟨n,hn,c,hc⟩ := position_interval_subdivision f V hV hcov
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let q : Fin n → C(Interval,Interval) := fun k =>
    ⟨fun t => ⟨((k.val:ℝ)+(t:ℝ))/n,by
      constructor
      · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) hnR.le
      · apply (div_le_one hnR).mpr
        have hk : (k.val:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt
        linarith [t.property.2]⟩,by fun_prop⟩
  have hqi (k : Fin n) : Function.Injective (q k) := by
    intro t u he
    have he' := congrArg Subtype.val he
    change ((k.val:ℝ)+(t:ℝ))/n = ((k.val:ℝ)+(u:ℝ))/n at he'
    have he'' := (div_left_inj' hnR.ne').mp he'
    apply Subtype.ext
    linarith
  have hqemb (k) : IsEmbedding (q k) :=
    ((q k).continuous.isClosedEmbedding (hqi k)).isEmbedding
  let g : Fin n → C(Interval,S) := fun k => f.comp (q k)
  let e : Fin n → OpenPartialHomeomorph S Plane := fun k => chartAt Plane (c k)
  have hgV (k : Fin n) : range (g k) ⊆ V (c k) := by
    rintro x ⟨t,rfl⟩
    apply hc k (q k t)
    · change (k.val:ℝ)/n ≤ ((k.val:ℝ)+(t:ℝ))/n
      exact div_le_div_of_nonneg_right (by linarith [t.property.1]) hnR.le
    · change ((k.val:ℝ)+(t:ℝ))/n ≤ (k.val+1:ℝ)/n
      exact div_le_div_of_nonneg_right (by linarith [t.property.2]) hnR.le
  have hgc (k) : IsCompact (range (g k)) := isCompact_range (g k).continuous
  obtain ⟨O,hO,hOdis⟩ := source_finite_compact_open_separation (fun k => range (g k)) hgc
  have hmake (k : Fin n) : ∃ B : Interval × Icc (-1:ℝ) 1 → S,
      IsEmbedding B ∧ (∀ t, B (t,⟨0,by norm_num⟩) = g k t) ∧
      range B ⊆ (U ∩ O k) ∩ (e k).source := by
    obtain ⟨B,hB,hcent,hBU,havoid⟩ := source_whole_arc_strip_in_chart
      (e k) (g k) (hf.comp (hqemb k))
      (fun x hx => (hgV k hx).2) (U ∩ O k) (hU.inter (hO k).1)
      (fun x hx => ⟨(hgV k hx).1,(hO k).2 hx⟩)
    exact ⟨B,hB,hcent,hBU⟩
  choose B hB hcent hBU using hmake
  refine ⟨n,hn,q,e,B,fun _ _ => rfl,hqemb,?_,hB,hcent,?_,?_,?_⟩
  · exact fun k x hx => (hgV k hx).2
  · exact fun k x hx => ⟨(hBU k hx).1.1,(hBU k hx).2⟩
  · intro i j hij
    have hdis : Disjoint (range (g i)) (range (g j)) := by
      rw [disjoint_left]
      rintro x ⟨t,rfl⟩ ⟨u,hu⟩
      have heq := hf.injective hu
      have heq' := congrArg Subtype.val heq
      change ((j.val:ℝ)+(u:ℝ))/n = ((i.val:ℝ)+(t:ℝ))/n at heq'
      have h := (div_left_inj' hnR.ne').mp heq'
      have hijR : (i.val:ℝ)+1 < j.val := by exact_mod_cast hij
      linarith [t.property.2,u.property.1]
    exact (hOdis i j hdis).mono
      (fun x hx => (hBU i hx).1.2) (fun x hx => (hBU j hx).1.2)
  · have hmeshCover (s : Interval) : ∃ k : Fin n, ∃ t : Interval, q k t = s := by
      by_cases hs : (s:ℝ) = 1
      · let k : Fin n := ⟨n-1,Nat.sub_lt hn (by decide)⟩
        let t : Interval := ⟨1,by norm_num⟩
        refine ⟨k,t,Subtype.ext ?_⟩
        have hk : ((n-1:ℕ):ℝ)+1 = n := by
          exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ n by omega))
        change (((n-1:ℕ):ℝ)+1)/n = (s:ℝ)
        rw [hk,div_self hnR.ne',hs]
      · have hs1 : (s:ℝ) < 1 := lt_of_le_of_ne s.property.2 hs
        let k : Fin n := ⟨⌊(n:ℝ)*s⌋₊,
          (Nat.floor_lt (mul_nonneg hnR.le s.property.1)).mpr (by nlinarith)⟩
        let t : Interval := ⟨(n:ℝ)*s-k.val,by
          constructor
          · exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg hnR.le s.property.1))
          · have hh := Nat.lt_floor_add_one ((n:ℝ)*s)
            change (n:ℝ)*s-(⌊(n:ℝ)*s⌋₊:ℝ) ≤ 1
            linarith⟩
        refine ⟨k,t,Subtype.ext ?_⟩
        change ((k.val:ℝ)+((n:ℝ)*s-k.val))/n = (s:ℝ)
        field_simp
        ring
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      obtain ⟨k,u,hu⟩ := hmeshCover t
      exact mem_iUnion.mpr ⟨k,u,congrArg f hu⟩
    · rintro hx
      obtain ⟨k,t,rfl⟩ := mem_iUnion.mp hx
      exact mem_range_self _

end CurveComplex
#print axioms CurveComplex.source_finite_compact_open_separation
#print axioms CurveComplex.source_embedded_arc_finite_chart_strips
