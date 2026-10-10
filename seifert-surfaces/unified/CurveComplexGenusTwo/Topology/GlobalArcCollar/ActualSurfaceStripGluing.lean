import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualWholeArcInChart

namespace CurveComplex
open Set Topology unitInterval

/-- Glue two actual surface strips with their exact common seam. The output
is an embedded whole strip with the union image and exact ports. This is
geometric gluing in the original surface, with no planar ambient assumption. -/
theorem source_glue_two_surface_strips
    {S W : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace W] [CompactSpace W]
    (L R : Interval × W → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ w, L (0,w) = R (0,w))
    (hmeet : Set.range L ∩ Set.range R = Set.range (fun w => L (0,w))) :
    ∃ F : Interval × W → S, IsEmbedding F ∧
      (∀ w, F (0,w) = L (1,w)) ∧
      (∀ w, F (1,w) = R (1,w)) ∧
      (∀ w, F (⟨1/2,by norm_num⟩,w) = L (0,w)) ∧
      Set.range F = Set.range L ∪ Set.range R ∧
      ∀ z, ∃ t : Interval, F z = L (t,z.2) ∨ F z = R (t,z.2) := by
  let kl (z : Interval × W) : Interval × W :=
    (projIcc 0 1 zero_le_one (1-2*(z.1:ℝ)),z.2)
  let kr (z : Interval × W) : Interval × W :=
    (projIcc 0 1 zero_le_one (2*(z.1:ℝ)-1),z.2)
  let F : Interval × W → S :=
    fun z => if (z.1:ℝ) ≤ 1/2 then L (kl z) else R (kr z)
  have hklc : Continuous kl := by dsimp [kl]; fun_prop
  have hkrc : Continuous kr := by dsimp [kr]; fun_prop
  have hfc : Continuous F := by
    apply continuous_if_le (by fun_prop) continuous_const
      (hL.continuous.comp hklc).continuousOn (hR.continuous.comp hkrc).continuousOn
    intro z hz
    have hl : kl z = (0,z.2) := by
      apply Prod.ext
      · apply Subtype.ext
        simp [kl,hz]
      · rfl
    have hr : kr z = (0,z.2) := by
      apply Prod.ext
      · apply Subtype.ext
        simp [kr,hz]
      · rfl
    change L (kl z) = R (kr z)
    rw [hl,hr,hseam]
  have hleft (z : Interval × W) (hz : (z.1:ℝ) ≤ 1/2) :
      ((kl z).1:ℝ) = 1-2*(z.1:ℝ) := by
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one
      (show 1-2*(z.1:ℝ) ∈ I from ⟨by linarith,by linarith [z.1.property.1]⟩))
  have hright (z : Interval × W) (hz : 1/2 ≤ (z.1:ℝ)) :
      ((kr z).1:ℝ) = 2*(z.1:ℝ)-1 := by
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one
      (show 2*(z.1:ℝ)-1 ∈ I from ⟨by linarith,by linarith [z.1.property.2]⟩))
  have hfi : Function.Injective F := by
    intro z w he
    dsimp only [F] at he
    split_ifs at he with hz hw hw
    · have hh := hL.injective he
      apply Prod.ext
      · apply Subtype.ext
        have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) hh
        rw [hleft z hz,hleft w hw] at h1
        linarith
      · simpa [kl] using congrArg Prod.snd hh
    · have hm : L (kl z) ∈ Set.range L ∩ Set.range R :=
        ⟨Set.mem_range_self _,⟨kr w,he.symm⟩⟩
      rw [hmeet] at hm
      obtain ⟨u,hu⟩ := hm
      have hr : R (kr w) = R (0,u) := he.symm.trans (hu.symm.trans (hseam u))
      have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) (hR.injective hr)
      rw [hright w (by linarith)] at h1
      norm_num at h1
      exfalso
      linarith
    · have hm : L (kl w) ∈ Set.range L ∩ Set.range R :=
        ⟨Set.mem_range_self _,⟨kr z,he⟩⟩
      rw [hmeet] at hm
      obtain ⟨u,hu⟩ := hm
      have hr : R (kr z) = R (0,u) := he.trans (hu.symm.trans (hseam u))
      have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) (hR.injective hr)
      rw [hright z (by linarith)] at h1
      norm_num at h1
      exfalso
      linarith
    · have hh := hR.injective he
      apply Prod.ext
      · apply Subtype.ext
        have h1 := congrArg (fun q : Interval × W => (q.1:ℝ)) hh
        rw [hright z (by linarith),hright w (by linarith)] at h1
        linarith
      · simpa [kr] using congrArg Prod.snd hh
  refine ⟨F,(hfc.isClosedEmbedding hfi).isEmbedding,?_,?_,?_,?_,?_⟩
  · intro w
    simp [F,kl]
  · intro w
    norm_num [F,kr]
  · intro w
    simp [F,kl]
  · ext x
    constructor
    · rintro ⟨z,rfl⟩
      dsimp only [F]
      split_ifs
      · exact Or.inl (Set.mem_range_self _)
      · exact Or.inr (Set.mem_range_self _)
    · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
      · let t : Interval := ⟨(1-(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
        have ht : (t:ℝ) ≤ 1/2 := by dsimp [t]; linarith [z.1.property.1]
        refine ⟨(t,z.2),?_⟩
        rw [show F (t,z.2) = L (kl (t,z.2)) from ite_eq_left ht]
        apply congrArg L
        apply Prod.ext
        · apply Subtype.ext
          rw [hleft _ ht]
          dsimp [t]
          ring
        · rfl
      · let t : Interval := ⟨(1+(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
        by_cases hz0 : z.1 = 0
        · have hz : z = (0,z.2) := Prod.ext hz0 rfl
          refine ⟨(⟨1/2,by norm_num⟩,z.2),?_⟩
          rw [hz]
          norm_num [F,kl,hseam]
        · have ht : 1/2 < (t:ℝ) := by
            have hp : 0 < z.1 := lt_of_le_of_ne z.1.property.1 (fun h => hz0 h.symm)
            have hp' : (0:ℝ) < z.1 := hp
            dsimp [t]
            linarith
          refine ⟨(t,z.2),?_⟩
          rw [show F (t,z.2) = R (kr (t,z.2)) from ite_eq_right (not_le.mpr ht)]
          apply congrArg R
          apply Prod.ext
          · apply Subtype.ext
            rw [hright _ (by linarith)]
            dsimp [t]
            ring
          · rfl
  · intro z
    dsimp only [F]
    split_ifs
    · exact ⟨(kl z).1,Or.inl rfl⟩
    · exact ⟨(kr z).1,Or.inr rfl⟩

end CurveComplex

#print axioms CurveComplex.source_glue_two_surface_strips
