import CurveComplexGenusTwo.Topology.BandGlobalGluing.OrderedBandSubdivision

open Set Topology
namespace CurveComplex

/-- The center transverse slice of an actual embedded rectangle is a proper
crosscut: exactly its two transverse endpoints lie on the ambient frontier. -/
theorem embedded_rectangle_transverse_proper
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    {δ : ℝ} (hδ : 0 < δ)
    (B : Icc (1/3 : ℝ) (2/3) × Icc (-δ) δ → S) (hB : IsEmbedding B) :
    B ((⟨1/2,by norm_num⟩ : Icc (1/3 : ℝ) (2/3)),
        ⟨-δ,by constructor <;> linarith⟩) ∈ frontier (Set.range B) ∧
    B ((⟨1/2,by norm_num⟩ : Icc (1/3 : ℝ) (2/3)),
        ⟨δ,by constructor <;> linarith⟩) ∈ frontier (Set.range B) ∧
    ∀ w : Icc (-δ) δ, -δ < (w : ℝ) → (w : ℝ) < δ →
      B ((⟨1/2,by norm_num⟩ : Icc (1/3 : ℝ) (2/3)),w) ∈
        interior (Set.range B) := by
  classical
  let R := Icc (1/3 : ℝ) (2/3) × Icc (-δ) δ
  let g : R → Schoenflies.Plane := fun z => Schoenflies.Plane.mk z.1 z.2
  let K : Set Schoenflies.Plane := Set.range g
  have hgc : Continuous g := by dsimp [g,R]; fun_prop
  have hK : IsCompact K := isCompact_range hgc
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcoord (z : K) : z.val 0 ∈ Icc (1/3 : ℝ) (2/3) ∧
      z.val 1 ∈ Icc (-δ) δ := by
    obtain ⟨a,ha⟩ := z.property
    rw [← ha]
    exact ⟨a.1.property,a.2.property⟩
  let k : K → R := fun z => (⟨z.val 0,(hcoord z).1⟩,⟨z.val 1,(hcoord z).2⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    apply Subtype.ext
    ext i
    fin_cases i
    · exact congrArg (fun a : R => (a.1 : ℝ)) he
    · exact congrArg (fun a : R => (a.2 : ℝ)) he
  have hk : IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  let f : K → S := B ∘ k
  have hf : IsEmbedding f := hB.comp hk
  have hkg (a : R) : k ⟨g a,Set.mem_range_self a⟩ = a := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  have hrange : Set.range f = Set.range B := by
    ext v
    constructor
    · rintro ⟨z,rfl⟩; exact Set.mem_range_self _
    · rintro ⟨a,rfl⟩
      refine ⟨⟨g a,Set.mem_range_self a⟩,?_⟩
      change B (k _) = B a
      rw [hkg]
  have hinterior (a : R) : B a ∈ interior (Set.range B) ↔ g a ∈ interior K := by
    have hh := embedded_planar_region_interior_iff_probe K f hf
      ⟨g a,Set.mem_range_self a⟩
    simpa only [f,Function.comp_apply,hkg,hrange] using hh
  have hboundary (a : R) (ha : (a.2 : ℝ) = -δ ∨ (a.2 : ℝ) = δ) :
      g a ∈ K ∧ g a ∉ interior K := by
    refine ⟨Set.mem_range_self _,?_⟩
    intro hi
    let q : ℝ → Schoenflies.Plane := fun t => Schoenflies.Plane.mk a.1 t
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hpre : q ⁻¹' interior K ∈ 𝓝 (a.2 : ℝ) :=
      (isOpen_interior.preimage hq).mem_nhds hi
    obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hpre
    rcases ha with ha | ha
    · have ht : (a.2 : ℝ)-ε/2 ∈ Metric.ball (a.2 : ℝ) ε := by
        rw [Metric.mem_ball,Real.dist_eq,abs_lt]
        constructor <;> linarith
      have hm := interior_subset (hsub ht)
      obtain ⟨v,hv⟩ := hm
      have hh := congrArg (fun z : Schoenflies.Plane => z 1) hv
      change (v.2 : ℝ) = (a.2 : ℝ)-ε/2 at hh
      linarith [v.2.property.1]
    · have ht : (a.2 : ℝ)+ε/2 ∈ Metric.ball (a.2 : ℝ) ε := by
        rw [Metric.mem_ball,Real.dist_eq,abs_lt]
        constructor <;> linarith
      have hm := interior_subset (hsub ht)
      obtain ⟨v,hv⟩ := hm
      have hh := congrArg (fun z : Schoenflies.Plane => z 1) hv
      change (v.2 : ℝ) = (a.2 : ℝ)+ε/2 at hh
      linarith [v.2.property.2]
  have hfront (a : R) (ha : (a.2 : ℝ) = -δ ∨ (a.2 : ℝ) = δ) :
      B a ∈ frontier (Set.range B) := by
    rw [(isCompact_range hB.continuous).isClosed.frontier_eq]
    exact ⟨Set.mem_range_self _,fun hi => (hboundary a ha).2 ((hinterior a).mp hi)⟩
  refine ⟨hfront _ (Or.inl rfl),hfront _ (Or.inr rfl),?_⟩
  intro w hw0 hw1
  apply (hinterior _).mpr
  let V : Set Schoenflies.Plane := {z | z 0 ∈ Ioo (1/3 : ℝ) (2/3) ∧ z 1 ∈ Ioo (-δ) δ}
  have hV : IsOpen V := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hVK : V ⊆ K := by
    intro z hz
    refine ⟨(⟨z 0,⟨hz.1.1.le,hz.1.2.le⟩⟩,⟨z 1,⟨hz.2.1.le,hz.2.2.le⟩⟩),?_⟩
    ext i
    fin_cases i <;> rfl
  apply hV.subset_interior_iff.mpr hVK
  exact ⟨⟨by norm_num [g],by norm_num [g]⟩,hw0,hw1⟩

#print axioms embedded_rectangle_transverse_proper

end CurveComplex
