import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripExtension
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
namespace CurveComplex
open Set Topology Schoenflies unitInterval
private abbrev Width := Icc (-1:ℝ) 1

/-- The existing geometric seam glue preserves the exact center carrier and
whole-original-arc avoidance. Endpoint parametrization is preserved. -/
theorem source_glue_strips_with_center_carrier
    {S : Type} [TopologicalSpace S] [T2Space S]
    (L R : Interval × Width → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ w, L (1,w) = R (0,w))
    (hmeet : range L ∩ range R = range (fun w => L (1,w)))
    (A U : Set S) (hLU : range L ⊆ U) (hRU : range R ⊆ U)
    (hLA : ∀ z, L z ∈ A ↔ (z.2:ℝ) = 0)
    (hRA : ∀ z, R z ∈ A ↔ (z.2:ℝ) = 0) :
    ∃ F : Interval × Width → S,
      IsEmbedding F ∧ range F ⊆ U ∧
      F (0,⟨0,by norm_num⟩) = L (0,⟨0,by norm_num⟩) ∧
      F (1,⟨0,by norm_num⟩) = R (1,⟨0,by norm_num⟩) ∧
      range (fun t => F (t,⟨0,by norm_num⟩)) =
        range (fun t => L (t,⟨0,by norm_num⟩)) ∪
        range (fun t => R (t,⟨0,by norm_num⟩)) ∧
      (∀ z, F z ∈ A ↔ (z.2:ℝ) = 0) := by
  let rev : Interval × Width → Interval × Width := fun z => (unitInterval.symm z.1,z.2)
  have hrevc : Continuous rev := by dsimp [rev]; fun_prop
  have hrevi : Function.Injective rev := by
    intro z w he
    exact Prod.ext (unitInterval.symm_involutive.injective (congrArg Prod.fst he))
      (by simpa [rev] using congrArg Prod.snd he)
  let L' := L ∘ rev
  have hL' : IsEmbedding L' := ((hL.continuous.comp hrevc).isClosedEmbedding
    (hL.injective.comp hrevi)).isEmbedding
  have hL'range : range L' = range L := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact mem_range_self _
    · rintro ⟨z,rfl⟩
      refine ⟨rev z,?_⟩
      simp [L',rev]
  have hL'zero (w) : L' (0,w) = L (1,w) := by simp [L',rev]
  have hL'one (w) : L' (1,w) = L (0,w) := by simp [L',rev]
  have hmeet' : range L' ∩ range R = range (fun w => L' (0,w)) := by
    simp only [hL'range,hL'zero,hmeet]
  obtain ⟨F,hF,hfirst,hlast,hmid,hFrange,htrack⟩ :=
    source_glue_two_surface_strips L' R hL' hR
      (fun w => (hL'zero w).trans (hseam w)) hmeet'
  have hFA (z) : F z ∈ A ↔ (z.2:ℝ) = 0 := by
    obtain ⟨t,ht | ht⟩ := htrack z
    · rw [ht]
      exact hLA (rev (t,z.2))
    · rw [ht]
      exact hRA (t,z.2)
  have hFU : range F ⊆ U := by
    rw [hFrange,hL'range]
    exact union_subset hLU hRU
  refine ⟨F,hF,hFU,(hfirst _).trans (hL'one _),hlast _,?_,hFA⟩
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      obtain ⟨u,hu | hu⟩ := htrack (t,⟨0,by norm_num⟩)
      · exact Or.inl ⟨unitInterval.symm u,hu.symm⟩
      · exact Or.inr ⟨u,hu.symm⟩
    · intro hx
      have hxA : x ∈ A := by
        rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
        · exact (hLA _).mpr rfl
        · exact (hRA _).mpr rfl
      have hxF : x ∈ range F := by
        rw [hFrange,hL'range]
        rcases hx with ⟨t,rfl⟩ | ⟨t,rfl⟩
        · exact Or.inl (mem_range_self _)
        · exact Or.inr (mem_range_self _)
      obtain ⟨z,hz⟩ := hxF
      have hz0 : (z.2:ℝ) = 0 := (hFA z).mp (hz ▸ hxA)
      refine ⟨z.1,?_⟩
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz0)
      change F (z.1,⟨0,by norm_num⟩) = x
      rw [← he]
      exact hz
end CurveComplex
#print axioms CurveComplex.source_glue_strips_with_center_carrier
