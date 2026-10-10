import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

def seamHalfstrip (h : ℝ) : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) h
def seamFullstrip (h : ℝ) : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-h) h
def seamReflect (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

/-- Two continuous embedded closed halfstrips with a common clock and no
intersection away from their boundaries glue to an embedded open strip. -/
theorem seam_halfstrip_glue
    {X : Type*} [TopologicalSpace X] (h : ℝ) (hh : 0 < h)
    (f g : ℝ × ℝ → X)
    (hf : ContinuousOn f (seamHalfstrip h)) (hg : ContinuousOn g (seamHalfstrip h))
    (hfi : InjOn f (seamHalfstrip h)) (hgi : InjOn g (seamHalfstrip h))
    (hfg : ∀ t ∈ Ioo (-1 : ℝ) 1, f (t, 0) = g (t, 0))
    (hcross : ∀ z ∈ seamHalfstrip h, ∀ w ∈ seamHalfstrip h,
      f z = g w → z.2 = 0 ∧ w.2 = 0 ∧ z.1 = w.1) :
    let glue := fun z : ℝ × ℝ => if 0 ≤ z.2 then f z else g (seamReflect z)
    ContinuousOn glue (seamFullstrip h) ∧ InjOn glue (seamFullstrip h) ∧
      glue '' seamFullstrip h = f '' seamHalfstrip h ∪ g '' seamHalfstrip h := by
  dsimp only
  classical
  let Z := seamFullstrip h
  let H := seamHalfstrip h
  let glue := fun z : ℝ × ℝ => if 0 ≤ z.2 then f z else g (seamReflect z)
  have hpos {z : ℝ × ℝ} (hz : z ∈ Z) (hzn : 0 ≤ z.2) : z ∈ H := ⟨hz.1, hzn, hz.2.2⟩
  have hneg {z : ℝ × ℝ} (hz : z ∈ Z) (hzn : z.2 ≤ 0) : seamReflect z ∈ H :=
    ⟨hz.1, neg_nonneg.mpr hzn, by dsimp [seamReflect]; linarith [hz.2.1]⟩
  have hrefl : Continuous seamReflect := by unfold seamReflect; fun_prop
  have hglue : ContinuousOn glue Z := by
    apply ContinuousOn.if
    · intro z hz
      have he := frontier_le_subset_eq (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℝ)))
        continuous_snd hz.2
      change 0 = z.2 at he
      have hz0 : z = (z.1, 0) := Prod.ext rfl he.symm
      rw [hz0]
      simpa [seamReflect] using hfg z.1 hz.1.1
    · apply hf.mono
      intro z hz
      apply hpos hz.1
      have hcl := (isClosed_le (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℝ)))
        continuous_snd).closure_eq
      rw [hcl] at hz
      exact hz.2
    · apply hg.comp hrefl.continuousOn
      intro z hz
      apply hneg hz.1
      have hcl : closure {z : ℝ × ℝ | ¬0 ≤ z.2} ⊆ {z : ℝ × ℝ | z.2 ≤ 0} := by
        simpa only [not_le] using closure_lt_subset_le continuous_snd
          (continuous_const : Continuous (fun _ : ℝ × ℝ => (0 : ℝ)))
      exact hcl hz.2
  have hinj : InjOn glue Z := by
    intro z hz w hw he
    by_cases hzp : 0 ≤ z.2 <;> by_cases hwp : 0 ≤ w.2
    · exact hfi (hpos hz hzp) (hpos hw hwp) (by simpa [glue, hzp, hwp] using he)
    · have hc := hcross z (hpos hz hzp) (seamReflect w)
        (hneg hw (le_of_lt (lt_of_not_ge hwp))) (by simpa [glue, hzp, hwp] using he)
      exact (hwp (by dsimp [seamReflect] at hc; linarith [hc.2.1])).elim
    · have hc := hcross w (hpos hw hwp) (seamReflect z)
        (hneg hz (le_of_lt (lt_of_not_ge hzp))) (by simpa [glue, hzp, hwp] using he.symm)
      exact (hzp (by dsimp [seamReflect] at hc; linarith [hc.2.1])).elim
    · have hr := hgi (hneg hz (le_of_lt (lt_of_not_ge hzp)))
        (hneg hw (le_of_lt (lt_of_not_ge hwp))) (by simpa [glue, hzp, hwp] using he)
      have h1 := congrArg Prod.fst hr
      have h2 := congrArg Prod.snd hr
      exact Prod.ext h1 (by dsimp [seamReflect] at h2; linarith)
  refine ⟨hglue, hinj, ?_⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    by_cases hp : 0 ≤ z.2
    · exact Or.inl ⟨z, hpos hz hp, by simp [glue, hp]⟩
    · exact Or.inr ⟨seamReflect z, hneg hz (le_of_lt (lt_of_not_ge hp)), by simp [glue, hp]⟩
  · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · refine ⟨z, ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, ?_⟩
      simp [glue, hz.2.1]
    · by_cases he : z.2 = 0
      · refine ⟨z, ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩, ?_⟩
        have hz0 : z = (z.1, 0) := Prod.ext rfl he
        rw [hz0]
        simpa [glue] using hfg z.1 hz.1
      · have hzpos : 0 < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm he)
        refine ⟨seamReflect z, ⟨hz.1, ?_, ?_⟩, ?_⟩
        · dsimp [seamReflect]; linarith [hz.2.2]
        · dsimp [seamReflect]; linarith
        · simp [glue, seamReflect, not_le.mpr (neg_neg_of_pos hzpos)]

/-- Native surface invariance of domain makes the exact union of any two
such halfstrips an open source neighbourhood. -/
theorem native_two_halfstrip_union_open
    (S : CompactOrientedSurface) (h : ℝ) (hh : 0 < h) (f g : ℝ × ℝ → S)
    (hf : ContinuousOn f (seamHalfstrip h)) (hg : ContinuousOn g (seamHalfstrip h))
    (hfi : InjOn f (seamHalfstrip h)) (hgi : InjOn g (seamHalfstrip h))
    (hfg : ∀ t ∈ Ioo (-1 : ℝ) 1, f (t, 0) = g (t, 0))
    (hcross : ∀ z ∈ seamHalfstrip h, ∀ w ∈ seamHalfstrip h,
      f z = g w → z.2 = 0 ∧ w.2 = 0 ∧ z.1 = w.1) :
    IsOpen (f '' seamHalfstrip h ∪ g '' seamHalfstrip h) := by
  classical
  obtain ⟨hc, hi, heq⟩ := seam_halfstrip_glue h hh f g hf hg hfi hgi hfg hcross
  let glue := fun z : ℝ × ℝ => if 0 ≤ z.2 then f z else g (seamReflect z)
  let L : Euc 2 ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp [Euc])
  let V := L ⁻¹' seamFullstrip h
  have hV : IsOpen V := (isOpen_Ioo.prod isOpen_Ioo).preimage L.continuous
  have hfV : Continuous (fun z : V => glue (L z)) :=
    (hc.comp L.continuous.continuousOn (fun _ hz => hz)).domRestrict
  have hiV : Function.Injective (fun z : V => glue (L z)) := by
    intro z w he
    exact Subtype.ext (L.injective (hi z.property w.property he))
  have hopen := DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
    (𝓡∂ 2) hV (fun z : V => glue (L z)) hfV hiV
  have hr : range (fun z : V => glue (L z)) = glue '' seamFullstrip h := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨L z, z.property, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨L.symm z, by change L (L.symm z) ∈ seamFullstrip h; simpa using hz⟩,
        by simp⟩
  rwa [hr, heq] at hopen

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
