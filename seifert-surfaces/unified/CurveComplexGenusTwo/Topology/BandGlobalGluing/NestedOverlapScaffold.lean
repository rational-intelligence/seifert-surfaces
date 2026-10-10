import CurveComplexGenusTwo.Topology.BandGlobalGluing.OverlapCrosscutScaffold
import CurveComplexGenusTwo.Topology.BandGlobalGluing.TransverseProperScaffold

open Set Topology unitInterval
namespace CurveComplex

/-- Construct nested genuine overlap supports from the actual arc. The outer
support avoids the earlier/later arc tails; the contracted inner disk lies
strictly inside the outer disk and preserves the exact center parametrization. -/
theorem embedded_arc_nested_overlap_rectangles
    {S : Type*} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (l m r : I) (hlm : l < m) (hmr : m < r)
    (U : Set S) (hU : IsOpen U) (hmU : p m ∈ U) :
    ∃ η : ℝ, 0 < η ∧ 0 < (m : ℝ)-η ∧ (m : ℝ)+η < 1 ∧
      ∃ δ : ℝ, ∃ hδ : 0 < δ,
        ∃ B C : Icc (1/3 : ℝ) (2/3) × Icc (-δ) δ → S,
          IsEmbedding B ∧ IsEmbedding C ∧ Set.range B ⊆ U ∧
          Set.range C ⊆ interior (Set.range B) ∧
          Disjoint (Set.range B) (p '' (Iic l ∪ Ici r)) ∧
          (∀ z : Icc (1/3 : ℝ) (2/3),
            B (z,⟨0,by constructor <;> linarith⟩) =
              p.extend ((m : ℝ)-η+2*η*(z : ℝ))) ∧
          (∀ z : Icc (1/3 : ℝ) (2/3),
            C (z,⟨0,by constructor <;> linarith⟩) =
              p.extend ((m : ℝ)-η/2+η*(z : ℝ))) ∧
          p m ∈ interior (Set.range C) := by
  classical
  let T : Set I := Iic l ∪ Ici r
  let K : Set S := p '' T
  have hK : IsClosed K :=
    ((isClosed_Iic.union isClosed_Ici).isCompact.image p.continuous).isClosed
  have hmK : p m ∉ K := by
    rintro ⟨t,ht,he⟩
    have het : t = m := hp.injective he
    subst t
    rcases ht with ht | ht
    · exact (not_le_of_gt hlm) ht
    · exact (not_le_of_gt hmr) ht
  let V := U \ K
  have hV : IsOpen V := hU.sdiff hK
  have hmV : p m ∈ V := ⟨hmU,hmK⟩
  have hm0 : 0 < m := lt_of_le_of_lt l.property.1 hlm
  have hm1 : m < 1 := lt_of_lt_of_le hmr r.property.2
  obtain ⟨η,hη,hL,hR,δ,hδ,B,hB,hBV,hpoint,hcenter,hmeet,htrans,hsingle⟩ :=
    embedded_arc_overlap_transverse_slice p hp m hm0 hm1 V hV hmV
  have hinside (t : Icc (1/3:ℝ) (2/3)) (ht0 : (1/3:ℝ) < t)
      (ht1 : (t:ℝ) < 2/3) (w : Icc (-δ) δ)
      (hw0 : -δ < (w:ℝ)) (hw1 : (w:ℝ) < δ) :
      B (t,w) ∈ interior (Set.range B) := by
    let f : Schoenflies.Plane → S := fun z =>
      B (projIcc (1/3) (2/3) (by norm_num) (z 0),
         projIcc (-δ) δ (by linarith) (z 1))
    let V : Set Schoenflies.Plane :=
      {z | z 0 ∈ Ioo (1/3:ℝ) (2/3) ∧ z 1 ∈ Ioo (-δ) δ}
    have hV : IsOpen V := (isOpen_Ioo.preimage (by fun_prop)).inter
      (isOpen_Ioo.preimage (by fun_prop))
    have hf : Continuous f := hB.continuous.comp
      ((continuous_projIcc.comp (by fun_prop)).prodMk
        (continuous_projIcc.comp (by fun_prop)))
    have hi : InjOn f V := by
      intro z hz w hw he
      have hh := hB.injective he
      have h0 := congrArg (fun q : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ => (q.1 : ℝ)) hh
      have h1 := congrArg (fun q : Icc (1/3:ℝ) (2/3) × Icc (-δ) δ => (q.2 : ℝ)) hh
      simp only [projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num)
        ⟨hz.1.1.le,hz.1.2.le⟩,
        projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num)
        ⟨hw.1.1.le,hw.1.2.le⟩] at h0
      simp only [projIcc_of_mem (show -δ ≤ δ by linarith)
        ⟨hz.2.1.le,hz.2.2.le⟩,
        projIcc_of_mem (show -δ ≤ δ by linarith)
        ⟨hw.2.1.le,hw.2.2.le⟩] at h1
      ext i
      fin_cases i
      · exact h0
      · exact h1
    have hopen : IsOpen (f '' V) :=
      surface_invariance_of_domain_probe f V hV hf.continuousOn hi
    have hsub : f '' V ⊆ Set.range B := by
      rintro z ⟨w,hw,rfl⟩
      exact Set.mem_range_self _
    apply (hopen.subset_interior_iff.mpr hsub)
    refine ⟨Schoenflies.Plane.mk t w,⟨⟨ht0,ht1⟩,hw0,hw1⟩,?_⟩
    simp [f,projIcc_of_mem (show (1/3:ℝ) ≤ 2/3 by norm_num) t.property,
      projIcc_of_mem (show -δ ≤ δ by linarith) w.property]
  let R := Icc (1/3:ℝ) (2/3) × Icc (-δ) δ
  let k : R → R := fun a =>
    (⟨1/4+(a.1:ℝ)/2,by constructor <;> linarith [a.1.property.1,a.1.property.2]⟩,
     ⟨(a.2:ℝ)/2,by constructor <;> linarith [a.2.property.1,a.2.property.2]⟩)
  have hkc : Continuous k := by dsimp [k,R]; fun_prop
  have hki : Function.Injective k := by
    intro a b he
    apply Prod.ext <;> apply Subtype.ext
    · have hh := congrArg (fun z : R => (z.1:ℝ)) he
      dsimp [k] at hh
      linarith
    · have hh := congrArg (fun z : R => (z.2:ℝ)) he
      dsimp [k] at hh
      linarith
  have hk : IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
  let C : R → S := B ∘ k
  have hC : IsEmbedding C := hB.comp hk
  have hsub : Set.range C ⊆ interior (Set.range B) := by
    rintro z ⟨a,rfl⟩
    apply hinside
    · dsimp [k]
      linarith [a.1.property.1]
    · dsimp [k]
      linarith [a.1.property.2]
    · dsimp [k]
      linarith [a.2.property.1]
    · dsimp [k]
      linarith [a.2.property.2]
  have hCcenter (z : Icc (1/3:ℝ) (2/3)) :
      C (z,⟨0,by constructor <;> linarith⟩) =
        p.extend ((m:ℝ)-η/2+η*(z:ℝ)) := by
    change B (⟨1/4+(z:ℝ)/2,_⟩,⟨0/2,_⟩) = _
    have he0 : (⟨0/2,by constructor <;> linarith⟩ : Icc (-δ) δ) = ⟨0,by constructor <;> linarith⟩ := by
      apply Subtype.ext
      norm_num
    rw [he0,hcenter]
    congr 1
    ring
  have hCm : C ((⟨1/2,by norm_num⟩ : Icc (1/3:ℝ) (2/3)),
      ⟨0,by constructor <;> linarith⟩) = p m := by
    rw [hCcenter]
    have he : (m:ℝ)-η/2+η*(1/2:ℝ) = (m:ℝ) := by ring
    rw [he,p.extend_extends']
  refine ⟨η,hη,hL,hR,δ,hδ,B,C,hB,hC,?_,hsub,?_,hcenter,hCcenter,?_⟩
  · intro z hz
    exact (hBV hz).1
  · apply Set.disjoint_left.mpr
    intro z hz hk
    exact (hBV hz).2 hk
  · rw [← hCm]
    exact local_rectangle_center_interior hδ C hC ⟨1/2,by norm_num⟩
      (by norm_num) (by norm_num)

#print axioms embedded_arc_nested_overlap_rectangles

end CurveComplex
