import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing
namespace CurveComplex
open Set Topology Schoenflies Metric

/-- Construct the initial whole closed strip of an actual arc, including its
first endpoint, with every nonzero transverse point avoiding the WHOLE original
arc. No supplied strip or chart-contained-arc hypothesis is needed. -/
theorem source_embedded_arc_initial_strip
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ b : Interval, 0 < (b:ℝ) ∧ (b:ℝ) < 1 ∧
      ∃ E : Interval × Icc (-1:ℝ) 1 → S,
        IsEmbedding E ∧ range E ⊆ U ∧
        (∀ t, E (t,⟨0,by norm_num⟩) =
          f ⟨(b:ℝ)*(t:ℝ),⟨mul_nonneg b.property.1 t.property.1,
            (mul_le_mul_of_nonneg_left t.property.2 b.property.1).trans
              (by simpa using b.property.2)⟩⟩) ∧
        (∀ z, E z ∈ range f ↔ (z.2:ℝ) = 0) := by
  let e := chartAt Plane (f 0)
  have hpre : IsOpen (f ⁻¹' e.source) := e.open_source.preimage f.continuous
  have hzero : (0:Interval) ∈ f ⁻¹' e.source := mem_chart_source _ _
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hpre.mem_nhds hzero)
  let d : ℝ := min (r/2) (1/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by
    have hh := min_le_right (r/2) (1/2:ℝ); dsimp [d]; linarith
  have hdr : d < r := by
    have hh := min_le_left (r/2) (1/2:ℝ); dsimp [d]; linarith
  let q : C(Interval,Interval) :=
    ⟨fun t => ⟨d*(t:ℝ),⟨mul_nonneg hd.le t.property.1,
      (mul_le_mul_of_nonneg_left t.property.2 hd.le).trans (by simpa using hd1.le)⟩⟩,
      by fun_prop⟩
  have hqi : Function.Injective q := by
    intro s t he
    exact Subtype.ext (mul_left_cancel₀ hd.ne' (congrArg Subtype.val he))
  let g : C(Interval,S) := f.comp q
  have hg : IsEmbedding g := hf.comp ((q.continuous.isClosedEmbedding hqi).isEmbedding)
  have hgsource : range g ⊆ e.source := by
    rintro x ⟨t,rfl⟩
    apply hball
    rw [mem_ball,Subtype.dist_eq,Real.dist_eq]
    change |d*(t:ℝ)-0| < r
    rw [sub_zero,abs_of_nonneg (mul_nonneg hd.le t.property.1)]
    exact (mul_le_mul_of_nonneg_left t.property.2 hd.le).trans_lt
      (by simpa using hdr)
  obtain ⟨B,hB,hcenter,hBU,havoid⟩ := source_whole_arc_strip_in_chart
    e g hg hgsource U hU (fun x hx => hfU (range_comp_subset_range _ _ hx))
  let a : Interval → Interval := fun t => ⟨(t:ℝ)/2,by
    constructor <;> linarith [t.property.1,t.property.2]⟩
  let k : Interval × Icc (-1:ℝ) 1 → Interval × Icc (-1:ℝ) 1 :=
    fun z => (a z.1,z.2)
  have hkc : Continuous k := by dsimp [k,a]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Prod.ext
    · apply Subtype.ext
      have hh := congrArg (fun z => (z.1:ℝ)) he
      change (z.1:ℝ)/2 = (w.1:ℝ)/2 at hh
      linarith
    · simpa [k] using congrArg Prod.snd he
  let C := B ∘ k
  have hC : IsEmbedding C := ((hB.continuous.comp hkc).isClosedEmbedding
    (hB.injective.comp hki)).isEmbedding
  let F : Set S := f '' Icc (⟨d,⟨hd.le,hd1.le⟩⟩:Interval) 1
  have hF : IsClosed F := (isCompact_Icc.image f.continuous).isClosed
  have hCF (t : Interval) : C (t,⟨0,by norm_num⟩) ∈ U \ F := by
    refine ⟨(hBU (mem_range_self (k (t,⟨0,by norm_num⟩)))).1,?_⟩
    change B (a t,⟨0,by norm_num⟩) ∉ F
    rw [hcenter]
    rintro ⟨s,hs,he⟩
    have heq := hf.injective he
    have hh := congrArg Subtype.val heq
    change (s:ℝ) = d*((t:ℝ)/2) at hh
    have hs0 : d ≤ (s:ℝ) := hs.1
    nlinarith [t.property.2]
  obtain ⟨ρ,hρ,N,hN,hNU,hNC,hNcent⟩ :=
    source_shrink_embedded_strip_in_open C hC (U \ F) (hU.sdiff hF) hCF
  let b : Interval := ⟨d/2,by constructor <;> linarith⟩
  refine ⟨b,by dsimp [b]; linarith,by dsimp [b]; linarith,N,hN,
    fun x hx => (hNU hx).1,?_,?_⟩
  · intro t
    rw [hNcent]
    change B (a t,⟨0,by norm_num⟩) = _
    rw [hcenter]
    apply congrArg f
    apply Subtype.ext
    change d*((t:ℝ)/2) = d/2*(t:ℝ)
    ring
  · intro z
    constructor
    · rintro ⟨s,hs⟩
      have hsD : (s:ℝ) < d := by
        by_contra hn
        exact (hNU (mem_range_self z)).2 ⟨s,⟨not_lt.mp hn,s.property.2⟩,hs⟩
      let u : Interval := ⟨(s:ℝ)/d,⟨div_nonneg s.property.1 hd.le,
        (div_le_one hd).mpr hsD.le⟩⟩
      have hqu : q u = s := by
        apply Subtype.ext
        change d*((s:ℝ)/d) = (s:ℝ)
        field_simp
      have hNg : N z ∈ range g := by
        refine ⟨u,?_⟩
        change f (q u) = N z
        rw [hqu,hs]
      rw [hNC] at hNg
      have hzero := (havoid (k (z.1,⟨ρ*(z.2:ℝ),by
        constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩))).mp hNg
      change ρ*(z.2:ℝ) = 0 at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hρ.1.ne'
    · intro hz
      have hw : z.2 = ⟨0,by norm_num⟩ := Subtype.ext hz
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl hw
      rw [he,hNcent]
      change B (a z.1,⟨0,by norm_num⟩) ∈ range f
      rw [hcenter]
      exact mem_range_self _
end CurveComplex
#print axioms CurveComplex.source_embedded_arc_initial_strip
