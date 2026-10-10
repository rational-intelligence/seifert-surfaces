import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Constructions

noncomputable section
open Set Topology Function MeasureTheory
open scoped ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487

variable {E M : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Preimages under a map continuous on a measurable piece are measurable there. -/
theorem measurableSet_piece_preimage {f : E → M} {s : Set E} {t : Set M}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hf : ContinuousOn f s) :
    MeasurableSet (s ∩ f ⁻¹' t) := by
  have hpre : MeasurableSet ((s.domRestrict f) ⁻¹' t) :=
    (continuousOn_iff_continuous_domRestrict.mp hf).measurable ht
  have him := (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr hpre
  convert him using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists, exists_and_right]
  aesop

/-- Exact image intersection, independently of any parameter choice. -/
theorem image_common_piece (f g : E → M) (s t : Set E) :
    f '' (s ∩ f ⁻¹' (g '' t)) = g '' (t ∩ g ⁻¹' (f '' s)) := by
  ext z
  simp only [mem_image, mem_inter_iff, mem_preimage]
  aesop

/-- Countable measurable common refinement gives equality of the extended
 integrals once each actual common-image pair is transported. -/
theorem tsum_lintegral_common_refinement [PolishSpace E] [T2Space M]
    (μ : Measure E) (f g : ℕ → E → M) (s t : ℕ → Set E)
    (hs : ∀ i, MeasurableSet (s i)) (ht : ∀ j, MeasurableSet (t j))
    (hfc : ∀ i, ContinuousOn (f i) (s i)) (hgc : ∀ j, ContinuousOn (g j) (t j))
    (hfi : ∀ i, InjOn (f i) (s i)) (hgi : ∀ j, InjOn (g j) (t j))
    (hfs : Pairwise (fun i j => Disjoint (f i '' s i) (f j '' s j)))
    (hgt : Pairwise (fun i j => Disjoint (g i '' t i) (g j '' t j)))
    (hcover : (⋃ i, f i '' s i) = ⋃ j, g j '' t j)
    (a b : ℕ → E → ℝ≥0∞)
    (hpair : ∀ i j, (∫⁻ x in s i ∩ f i ⁻¹' (g j '' t j), a i x ∂μ) =
      ∫⁻ y in t j ∩ g j ⁻¹' (f i '' s i), b j y ∂μ) :
    (∑' i, ∫⁻ x in s i, a i x ∂μ) = ∑' j, ∫⁻ y in t j, b j y ∂μ := by
  have hrow : ∀ i, (∫⁻ x in s i, a i x ∂μ) =
      ∑' j, ∫⁻ x in s i ∩ f i ⁻¹' (g j '' t j), a i x ∂μ := by
    intro i
    have hpieces : ∀ j, MeasurableSet (s i ∩ f i ⁻¹' (g j '' t j)) := fun j =>
      measurableSet_piece_preimage (hs i)
        ((ht j).image_of_continuousOn_injOn (hgc j) (hgi j)) (hfc i)
    have hdis : Pairwise (fun j k => Disjoint
        (s i ∩ f i ⁻¹' (g j '' t j)) (s i ∩ f i ⁻¹' (g k '' t k))) := by
      intro j k hjk
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp (hgt hjk) hx.2 hy.2
    have hset : (⋃ j, s i ∩ f i ⁻¹' (g j '' t j)) = s i := by
      apply Subset.antisymm
      · exact iUnion_subset fun j => inter_subset_left
      · intro x hx
        have himg : f i x ∈ ⋃ j, g j '' t j := by
          rw [← hcover]
          exact mem_iUnion.mpr ⟨i, mem_image_of_mem (f i) hx⟩
        obtain ⟨j, hj⟩ := mem_iUnion.mp himg
        exact mem_iUnion.mpr ⟨j, hx, hj⟩
    simpa only [hset] using lintegral_iUnion (μ := μ) hpieces hdis (a i)
  have hcol : ∀ j, (∫⁻ y in t j, b j y ∂μ) =
      ∑' i, ∫⁻ y in t j ∩ g j ⁻¹' (f i '' s i), b j y ∂μ := by
    intro j
    have hpieces : ∀ i, MeasurableSet (t j ∩ g j ⁻¹' (f i '' s i)) := fun i =>
      measurableSet_piece_preimage (ht j)
        ((hs i).image_of_continuousOn_injOn (hfc i) (hfi i)) (hgc j)
    have hdis : Pairwise (fun i k => Disjoint
        (t j ∩ g j ⁻¹' (f i '' s i)) (t j ∩ g j ⁻¹' (f k '' s k))) := by
      intro i k hik
      apply Set.disjoint_left.mpr
      intro y hy hz
      exact Set.disjoint_left.mp (hfs hik) hy.2 hz.2
    have hset : (⋃ i, t j ∩ g j ⁻¹' (f i '' s i)) = t j := by
      apply Subset.antisymm
      · exact iUnion_subset fun i => inter_subset_left
      · intro y hy
        have himg : g j y ∈ ⋃ i, f i '' s i := by
          rw [hcover]
          exact mem_iUnion.mpr ⟨j, mem_image_of_mem (g j) hy⟩
        obtain ⟨i, hi⟩ := mem_iUnion.mp himg
        exact mem_iUnion.mpr ⟨i, hy, hi⟩
    simpa only [hset] using lintegral_iUnion (μ := μ) hpieces hdis (b j)
  calc
    (∑' i, ∫⁻ x in s i, a i x ∂μ) =
        ∑' i, ∑' j, ∫⁻ x in s i ∩ f i ⁻¹' (g j '' t j), a i x ∂μ := tsum_congr hrow
    _ = ∑' i, ∑' j, ∫⁻ y in t j ∩ g j ⁻¹' (f i '' s i), b j y ∂μ := by
      apply tsum_congr
      intro i
      exact tsum_congr (hpair i)
    _ = ∑' j, ∑' i, ∫⁻ y in t j ∩ g j ⁻¹' (f i '' s i), b j y ∂μ := ENNReal.tsum_comm
    _ = ∑' j, ∫⁻ y in t j, b j y ∂μ := tsum_congr fun j => (hcol j).symm

end SeifertSurfaces.OriginalEndpoints.Section5.NativeAreaV487
