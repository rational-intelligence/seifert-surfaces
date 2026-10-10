import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchSquares

namespace CurveComplex
open Set Topology Schoenflies

section CornerGermHelpers
open unitInterval Metric

/-- An embedded scalar interval beginning at zero occupies exactly one half
of a sufficiently short interval about zero. -/
theorem source_scalar_interval_endpoint_germ
    (f : C(I,ℝ)) (hf : Function.Injective f) (h0 : f 0 = 0) :
    ∃ sgn δ : ℝ, (sgn = 1 ∨ sgn = -1) ∧ 0 < δ ∧
      ∀ z : ℝ, |z| < δ → (z ∈ Set.range f ↔ 0 ≤ sgn*z) := by
  have h01 : (0 : I) < 1 := by norm_num
  have hI : Set.Icc (0:I) 1 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact ⟨t.property.1,t.property.2⟩
  have hr : f '' Set.Icc (0:I) 1 = Set.range f := by rw [hI]; exact Set.image_univ
  rcases f.continuous.strictMono_of_inj_boundedOrder' hf with hm | hm
  · have h1 : 0 < f 1 := by simpa [h0] using hm h01
    have he : Set.range f = Set.Icc 0 (f 1) := by
      rw [← hr,f.continuous.continuousOn.image_Icc_of_monotoneOn h01.le (hm.monotone.monotoneOn _),h0]
    refine ⟨1,f 1,Or.inl rfl,h1,?_⟩
    intro z hz
    rw [he,Set.mem_Icc,one_mul]
    constructor
    · exact And.left
    · intro hz0; exact ⟨hz0,(le_abs_self z).trans hz.le⟩
  · have h1 : f 1 < 0 := by simpa [h0] using hm h01
    have he : Set.range f = Set.Icc (f 1) 0 := by
      rw [← hr,f.continuous.continuousOn.image_Icc_of_antitoneOn h01.le (hm.antitone.antitoneOn _),h0]
    refine ⟨-1,-f 1,Or.inr rfl,by linarith,?_⟩
    intro z hz
    rw [he,Set.mem_Icc]
    constructor
    · intro hz0; nlinarith [hz0.2]
    · intro hz0
      have hh := neg_abs_le z
      exact ⟨by linarith,by nlinarith⟩

/-- The actual endpoint germ of an embedded arc already lying on a chart axis.
The discarded tail is excluded by a genuine open neighborhood. -/
theorem source_chart_axis_endpoint_germ
    {S : Type} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (f : C(I,S))
    (hf : IsEmbedding f) (hp : f 0 ∈ E.source) (h0 : E (f 0) = 0)
    (j : Fin 2)
    (haxis : ∀ t : I, f t ∈ E.source → ∀ l : Fin 2, l ≠ j → E (f t) l = 0) :
    ∃ sgn : ℝ, ∃ W : Set S, (sgn = 1 ∨ sgn = -1) ∧ IsOpen W ∧
      f 0 ∈ W ∧ W ⊆ E.source ∧
      ∀ x ∈ W, x ∈ Set.range f ↔
        (∀ l : Fin 2, l ≠ j → E x l = 0) ∧ 0 ≤ sgn * E x j := by
  classical
  let p : Path (f 0) (f 1) := { toContinuousMap := f, source' := rfl, target' := rfl }
  have hpre : p.extend ⁻¹' E.source ∈ 𝓝 (0:ℝ) := by
    apply p.extend.continuous.continuousAt.preimage_mem_nhds
    apply E.open_source.mem_nhds
    rw [show p.extend (0:ℝ) = p 0 by simp]
    exact hp
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let r : ℝ := min ε 1 / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; have := min_le_left ε (1:ℝ); linarith
  have hr1 : r < 1 := by dsimp [r]; have := min_le_right ε (1:ℝ); linarith
  let rI : I := ⟨r,hr.le,hr1.le⟩
  let qpar : I → I := fun t => ⟨r*(t:ℝ),by
    constructor
    · exact mul_nonneg hr.le t.property.1
    · nlinarith [t.property.2]⟩
  have hqpar : Continuous qpar := by fun_prop
  have hqpari : Function.Injective qpar := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    change r*(t:ℝ) = r*(u:ℝ) at hh
    exact mul_left_cancel₀ (ne_of_gt hr) hh
  let q : C(I,S) := ⟨f ∘ qpar,f.continuous.comp hqpar⟩
  have hqi : Function.Injective q := hf.injective.comp hqpari
  have hqe (t : I) : q t ∈ E.source := by
    have hbound : |r*(t:ℝ)| < ε := by
      rw [abs_of_nonneg (mul_nonneg hr.le t.property.1)]
      nlinarith [t.property.2]
    have hmem := hεsub (show r*(t:ℝ) ∈ ball (0:ℝ) ε by simpa [Real.dist_eq] using hbound)
    change p.extend ((qpar t):ℝ) ∈ E.source at hmem
    rw [p.extend_extends' (qpar t)] at hmem
    exact hmem
  have hq0 : q 0 = f 0 := by
    change f (qpar 0) = f 0
    congr 1
    apply Subtype.ext
    simp [qpar]
  let g : C(I,ℝ) := ⟨fun t => E (q t) j,by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hc : Continuous (fun z : Plane => z j) := by fun_prop
    exact hc.continuousAt.comp
      ((E.continuousAt (hqe t)).comp q.continuous.continuousAt)⟩
  have hgi : Function.Injective g := by
    intro t u he
    apply hqi
    apply E.injOn (hqe t) (hqe u)
    ext l
    by_cases hl : l = j
    · subst l; exact he
    · change E (f (qpar t)) l = E (f (qpar u)) l
      rw [haxis (qpar t) (hqe t) l hl,haxis (qpar u) (hqe u) l hl]
  have hg0 : g 0 = 0 := by change E (q 0) j = 0; rw [hq0,h0]; rfl
  obtain ⟨sgn,δ,hsgn,hδ,hgerm⟩ := source_scalar_interval_endpoint_germ g hgi hg0
  let T := f '' Icc rI (1:I)
  have hTc : IsClosed T := (isCompact_Icc.image f.continuous).isClosed
  have hpT : f 0 ∉ T := by
    rintro ⟨t,ht,he⟩
    have heq : t = 0 := hf.injective he
    have hh : r ≤ (t:ℝ) := ht.1
    rw [heq] at hh
    exact (not_le_of_gt hr) hh
  let V : Set Plane := {z | |z j| < δ}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  let W := (E.source ∩ E ⁻¹' V) \ T
  have hW : IsOpen W := (E.isOpen_inter_preimage hV).sdiff hTc
  have hpW : f 0 ∈ W := by
    refine ⟨⟨hp,?_⟩,hpT⟩
    change |E (f 0) j| < δ
    rw [h0]; simpa using hδ
  refine ⟨sgn,W,hsgn,hW,hpW,fun x hx => hx.1.1,?_⟩
  intro x hx
  have hxE : x ∈ E.source := hx.1.1
  have hxδ : |E x j| < δ := hx.1.2
  constructor
  · rintro ⟨t,rfl⟩
    have htr : (t:ℝ) < r := by
      by_contra hn
      exact hx.2 ⟨t,⟨le_of_not_gt hn,t.property.2⟩,rfl⟩
    let u : I := ⟨(t:ℝ)/r,by
      constructor
      · exact div_nonneg t.property.1 hr.le
      · exact (div_le_one hr).mpr htr.le⟩
    have hqt : qpar u = t := by
      apply Subtype.ext
      change r*((t:ℝ)/r) = t
      field_simp
    refine ⟨haxis t hxE,?_⟩
    apply (hgerm (E (f t) j) hxδ).mp
    refine ⟨u,?_⟩
    change E (f (qpar u)) j = E (f t) j
    rw [hqt]
  · rintro ⟨hxl,hxz⟩
    obtain ⟨u,hu⟩ := (hgerm (E x j) hxδ).mpr hxz
    have he : E (q u) = E x := by
      ext l
      by_cases hl : l = j
      · subst l; exact hu
      · change E (f (qpar u)) l = E x l
        rw [haxis (qpar u) (hqe u) l hl,hxl l hl]
    exact ⟨qpar u,E.injOn (hqe u) hxE he⟩

/-- Two actual embedded endpoint germs on transverse axes can be independently
normalized to the positive L, preserving the original source axes. -/
theorem source_two_axis_positive_corner_square
    {S : Type} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (f g : C(I,S))
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hp : f 0 ∈ E.source) (hpq : g 0 = f 0) (h0 : E (f 0) = 0)
    (hfv : ∀ t : I, f t ∈ E.source → E (f t) 0 = 0)
    (hgh : ∀ t : I, g t ∈ E.source → E (g t) 1 = 0) :
    ∃ F : OpenPartialHomeomorph S Plane,
      f 0 ∈ F.source ∧ F (f 0) = 0 ∧ F.source ⊆ E.source ∧
      Plane.closedSquare 0 1 ⊆ F.target ∧
      (∀ x, F x 0 = 0 ↔ E x 0 = 0) ∧
      (∀ x, F x 1 = 0 ↔ E x 1 = 0) ∧
      (∀ x ∈ F.source, x ∈ Set.range f ∪ Set.range g ↔
        (F x 0 = 0 ∧ 0 ≤ F x 1) ∨ (0 ≤ F x 0 ∧ F x 1 = 0)) := by
  have hfa : ∀ t : I, f t ∈ E.source → ∀ l : Fin 2, l ≠ 1 → E (f t) l = 0 := by
    intro t ht l hl
    fin_cases l
    · exact hfv t ht
    · exact (hl rfl).elim
  have hga : ∀ t : I, g t ∈ E.source → ∀ l : Fin 2, l ≠ 0 → E (g t) l = 0 := by
    intro t ht l hl
    fin_cases l
    · exact (hl rfl).elim
    · exact hgh t ht
  obtain ⟨sy,U,hsy,hU,hpU,hUE,hfU⟩ := source_chart_axis_endpoint_germ E f hf hp h0 1 hfa
  obtain ⟨sx,V,hsx,hV,hpV,hVE,hgV⟩ := source_chart_axis_endpoint_germ E g hg
    (hpq.symm ▸ hp) (by rw [hpq]; exact h0) 0 hga
  have hsxne : sx ≠ 0 := by rcases hsx with rfl | rfl <;> norm_num
  have hsyne : sy ≠ 0 := by rcases hsy with rfl | rfl <;> norm_num
  have hsx2 : sx*sx = 1 := by rcases hsx with rfl | rfl <;> norm_num
  have hsy2 : sy*sy = 1 := by rcases hsy with rfl | rfl <;> norm_num
  let L : Plane ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (sx*z 0,sy*z 1)
      invFun := fun z => Plane.mk (sx*z.1) (sy*z.2)
      left_inv := by
        intro z
        ext l
        fin_cases l
        · change sx*(sx*z 0) = z 0; rw [← mul_assoc,hsx2,one_mul]
        · change sy*(sy*z 1) = z 1; rw [← mul_assoc,hsy2,one_mul]
      right_inv := by
        intro z
        apply Prod.ext
        · change sx*(sx*z.1) = z.1; rw [← mul_assoc,hsx2,one_mul]
        · change sy*(sy*z.2) = z.2; rw [← mul_assoc,hsy2,one_mul] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let R := E.restr (U ∩ V)
  have hRs : R.source = E.source ∩ (U ∩ V) := by simp [R,(hU.inter hV).interior_eq]
  let H := R.trans L.toOpenPartialHomeomorph
  have hHs : H.source = R.source := by simp [H]
  have hpH : f 0 ∈ H.source := by
    rw [hHs,hRs]
    exact ⟨hp,hpU,hpq ▸ hpV⟩
  have hH0 : H (f 0) = (0,0) := by
    change (sx*E (f 0) 0,sy*E (f 0) 1) = (0,0)
    rw [h0]; simp
  obtain ⟨F,δ,hδ,hFs,hsquare,hF0,hcoords⟩ := source_crossing_chart_unit_square H (f 0) hpH hH0
  have hc0 (x : S) : F x 0 = sx*E x 0/δ := (hcoords x).1
  have hc1 (x : S) : F x 1 = sy*E x 1/δ := (hcoords x).2
  have hz0 (x : S) : F x 0 = 0 ↔ E x 0 = 0 := by rw [hc0]; simp [hsxne,ne_of_gt hδ]
  have hz1 (x : S) : F x 1 = 0 ↔ E x 1 = 0 := by rw [hc1]; simp [hsyne,ne_of_gt hδ]
  have hn0 (x : S) : 0 ≤ F x 0 ↔ 0 ≤ sx*E x 0 := by rw [hc0,le_div_iff₀ hδ,zero_mul]
  have hn1 (x : S) : 0 ≤ F x 1 ↔ 0 ≤ sy*E x 1 := by rw [hc1,le_div_iff₀ hδ,zero_mul]
  refine ⟨F,hFs.symm ▸ hpH,hF0,?_,hsquare,hz0,hz1,?_⟩
  · intro x hx
    rw [hFs,hHs,hRs] at hx
    exact hx.1
  · intro x hx
    rw [hFs,hHs,hRs] at hx
    have hff : x ∈ Set.range f ↔ E x 0 = 0 ∧ 0 ≤ sy*E x 1 := by
      rw [hfU x hx.2.1]
      constructor
      · intro hh; exact ⟨hh.1 0 (by decide),hh.2⟩
      · rintro ⟨hh,hs⟩
        refine ⟨?_,hs⟩
        intro l hl
        fin_cases l
        · exact hh
        · exact (hl rfl).elim
    have hgg : x ∈ Set.range g ↔ 0 ≤ sx*E x 0 ∧ E x 1 = 0 := by
      rw [hgV x hx.2.2]
      constructor
      · intro hh; exact ⟨hh.2,hh.1 1 (by decide)⟩
      · rintro ⟨hs,hh⟩
        refine ⟨?_,hs⟩
        intro l hl
        fin_cases l
        · exact (hl rfl).elim
        · exact hh
    rw [Set.mem_union,hff,hgg,hz0,hz1,hn0,hn1]

end CornerGermHelpers

/-- Construct the actual normalized one-sided corner model of either endpoint
of either raw first-return surgery branch. Both coordinate signs are chosen by
the producer. It avoids the opposite corner and every retained crossing. -/
theorem source_first_return_corner_square
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S] [ClosedSurface S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b)
    (i k : Bool) :
    let p := if k then D.finish else D.start
    let q := if k then D.start else D.finish
    ∃ E : OpenPartialHomeomorph S Plane,
      p ∈ E.source ∧ E p = 0 ∧ q ∉ E.source ∧
      Plane.closedSquare 0 1 ⊆ E.target ∧
      Disjoint E.source (source_surgery_retained_crossings B i) ∧
      (∀ x ∈ E.source, x ∈ a.image ↔ E x 0 = 0) ∧
      (∀ x ∈ E.source, x ∈ b.image ↔ E x 1 = 0) ∧
      (∀ x ∈ E.source, x ∈ (B.boundary i).image ↔
        (E x 0 = 0 ∧ 0 ≤ E x 1) ∨ (0 ≤ E x 0 ∧ E x 1 = 0)) := by
  classical
  let p := if k then D.finish else D.start
  let q := if k then D.start else D.finish
  have hpold : p ∈ a.image ∩ b.image := by
    cases k
    · exact D.start_mem
    · exact D.finish_mem
  have hpq : p ≠ q := by
    cases k
    · exact D.distinct
    · exact D.distinct.symm
  let R := source_surgery_retained_crossings B i
  have hRc : IsClosed R := (source_surgery_closing_crossings_budget D B ht i).1.isClosed
  have hpR : p ∉ R := by
    intro hh
    have hn := hh.2
    cases k
    · exact hn (by simp [p])
    · exact hn (by simp [p])
  let W := ({q} : Set S)ᶜ ∩ Rᶜ
  have hW : IsOpen W := isClosed_singleton.isOpen_compl.inter hRc.isOpen_compl
  have hpW : p ∈ W := ⟨hpq,hpR⟩
  obtain ⟨A,hpA,hAW,hA0,haA,hbA⟩ := source_crossing_open_partial_chart (ht.2 p hpold) W hW hpW
  obtain ⟨E,δ,hδ,hEs,hsquare,hE0,hcoords⟩ := source_crossing_chart_unit_square A p hpA hA0
  have hpE : p ∈ E.source := hEs.symm ▸ hpA
  have haE (x : S) (hx : x ∈ E.source) : x ∈ a.image ↔ E x 0 = 0 := by
    rw [(hcoords x).1]
    simpa [ne_of_gt hδ] using haA x (hEs ▸ hx)
  have hbE (x : S) (hx : x ∈ E.source) : x ∈ b.image ↔ E x 1 = 0 := by
    rw [(hcoords x).2]
    simpa [ne_of_gt hδ] using hbA x (hEs ▸ hx)
  let rev : C(unitInterval,unitInterval) := ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
  let f : C(unitInterval,S) := if k then D.first.comp rev else D.first
  let g : C(unitInterval,S) := if k then (B.closing i).comp rev else B.closing i
  have hf : IsEmbedding f := by
    cases k
    · exact D.first_embedded
    · exact D.first_embedded.comp unitInterval.symmHomeomorph.isEmbedding
  have hg : IsEmbedding g := by
    cases k
    · exact B.closing_embedded i
    · exact (B.closing_embedded i).comp unitInterval.symmHomeomorph.isEmbedding
  have hf0 : f 0 = p := by cases k <;> simp [f,rev,p,D.first_zero,D.first_one]
  have hg0 : g 0 = p := by cases k <;> simp [g,rev,p,B.closing_zero,B.closing_one]
  have hfr : Set.range f = Set.range D.first := by
    cases k
    · rfl
    · change Set.range (D.first ∘ unitInterval.symmHomeomorph) = _
      exact unitInterval.symmHomeomorph.surjective.range_comp D.first
  have hgr : Set.range g = Set.range (B.closing i) := by
    cases k
    · rfl
    · change Set.range ((B.closing i) ∘ unitInterval.symmHomeomorph) = _
      exact unitInterval.symmHomeomorph.surjective.range_comp (B.closing i)
  have hgs : Set.range g ⊆ b.image := by
    rw [hgr,← B.closing_cover]
    cases i
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hfv (t : unitInterval) (htE : f t ∈ E.source) : E (f t) 0 = 0 :=
    (haE (f t) htE).mp (D.first_subset (hfr ▸ Set.mem_range_self t))
  have hgh (t : unitInterval) (htE : g t ∈ E.source) : E (g t) 1 = 0 :=
    (hbE (g t) htE).mp (hgs (Set.mem_range_self t))
  obtain ⟨F,hpF,hF0,hFE,hFsquare,hFaxis0,hFaxis1,hbranch⟩ :=
    source_two_axis_positive_corner_square E f g hf hg (hf0.symm ▸ hpE)
      (hg0.trans hf0.symm) (by rw [hf0]; exact hE0) hfv hgh
  have hFW : F.source ⊆ W := fun x hx => hAW (hEs ▸ hFE hx)
  have hpF' : p ∈ F.source := hf0 ▸ hpF
  have hF0' : F p = 0 := by rw [← hf0]; exact hF0
  refine ⟨F,hpF',hF0',?_,hFsquare,?_,?_,?_,?_⟩
  · intro hq
    exact (hFW hq).1 rfl
  · apply Set.disjoint_left.mpr
    intro x hx hr
    exact (hFW hx).2 hr
  · intro x hx
    rw [hFaxis0]
    exact haE x (hFE hx)
  · intro x hx
    rw [hFaxis1]
    exact hbE x (hFE hx)
  · intro x hx
    rw [B.boundary_image,← hfr,← hgr]
    exact hbranch x hx

end CurveComplex
