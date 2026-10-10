import CurveComplexGenusTwo.Topology.BandGlobalGluing.OrderedBandSubdivision

open Set Topology unitInterval
namespace CurveComplex

/-- An interior embedded-arc point in an open overlap has a genuine rectangular
disk there. Its transverse center slice meets the whole arc exactly once. -/
theorem embedded_arc_overlap_transverse_slice
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m : I) (hm0 : 0 < m) (hm1 : m < 1)
    (U : Set S) (hU : IsOpen U) (hmU : p m ∈ U) :
    ∃ η : ℝ, 0 < η ∧ 0 < (m : ℝ)-η ∧ (m : ℝ)+η < 1 ∧
      ∃ δ : ℝ, ∃ hδ : 0 < δ,
        ∃ B : Icc (1/3 : ℝ) (2/3) × Icc (-δ) δ → S,
          IsEmbedding B ∧ Set.range B ⊆ U ∧
          p m ∈ interior (Set.range B) ∧
          (∀ z : Icc (1/3 : ℝ) (2/3),
            B (z,⟨0,by constructor <;> linarith⟩) =
              p.extend ((m : ℝ)-η+2*η*(z : ℝ))) ∧
          Set.range B ∩ Set.range p =
            Set.range (fun z : Icc (1/3 : ℝ) (2/3) =>
              p.extend ((m : ℝ)-η+2*η*(z : ℝ))) ∧
          IsEmbedding (fun w : Icc (-δ) δ =>
            B ((⟨1/2,by norm_num⟩ : Icc (1/3 : ℝ) (2/3)),w)) ∧
          Set.range (fun w : Icc (-δ) δ =>
            B ((⟨1/2,by norm_num⟩ : Icc (1/3 : ℝ) (2/3)),w)) ∩
              Set.range p = {p m} := by
  obtain ⟨η,hη,hL,hR,δ,hδ,B,hB,hBU,hcenter,hmeet⟩ :=
    Schoenflies.exists_local_rectangular_band_on_surface p hp m hm0 hm1 U hU hmU
  let c : Icc (1/3 : ℝ) (2/3) := ⟨1/2,by norm_num⟩
  let z : Icc (-δ) δ := ⟨0,by constructor <;> linarith⟩
  have hmid : B (c,z) = p m := by
    rw [hcenter]
    have hcalc : (m : ℝ)-η+2*η*(c : ℝ) = (m : ℝ) := by dsimp [c]; ring
    rw [hcalc]
    exact p.extend_extends' m
  refine ⟨η,hη,hL,hR,δ,hδ,B,hB,hBU,?_,hcenter,hmeet,?_,?_⟩
  · rw [← hmid]
    exact local_rectangle_center_interior hδ B hB c (by norm_num [c]) (by norm_num [c])
  · exact hB.comp (isEmbedding_prodMkRight c)
  · ext v
    constructor
    · rintro ⟨⟨w,rfl⟩,hw⟩
      have hm : B (c,w) ∈ Set.range B ∩ Set.range p := ⟨Set.mem_range_self _,hw⟩
      rw [hmeet] at hm
      obtain ⟨u,hu⟩ := hm
      have he : B (u,z) = B (c,w) := (hcenter u).trans hu
      have hec : u = c := congrArg Prod.fst (hB.injective he)
      subst u
      exact Set.mem_singleton_iff.mpr (he.symm.trans hmid)
    · intro hv
      have he : v = p m := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨⟨z,hmid⟩,Set.mem_range_self _⟩

#print axioms embedded_arc_overlap_transverse_slice

end CurveComplex
