import Section5GeometricDefinitions
import MetricAreaAnalysis.Assembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

private theorem coordinate_image_recover {S : CompactOrientedSurface.{0}}
    (f : S → M) (p : S) (A : Set S) (hA : A ⊆ (extChartAt (𝓡∂ 2) p).source) :
    (f ∘ (extChartAt (𝓡∂ 2) p).symm) '' ((extChartAt (𝓡∂ 2) p) '' A) = f '' A := by
  ext y
  constructor
  · rintro ⟨z, ⟨x,hx,rfl⟩,rfl⟩
    simpa only [Function.comp_apply, (extChartAt (𝓡∂ 2) p).left_inv (hA hx)] using
      mem_image_of_mem f hx
  · rintro ⟨x,hx,rfl⟩
    exact ⟨extChartAt (𝓡∂ 2) p x, ⟨x,hx,rfl⟩,
      congrArg f ((extChartAt (𝓡∂ 2) p).left_inv (hA hx))⟩

private def imageAtlasCenter {S : CompactOrientedSurface.{0}} [Nonempty S]
    (P : ChartPartition S) (i : ℕ) : S :=
  if h : i < P.count then P.center ⟨i,h⟩ else Classical.choice ‹Nonempty S›

/-- An actual finite partition supplies a countable image atlas. Indices
outside the finite partition retain regular charts and have empty pieces. -/
def neatImageAtlas {S : CompactOrientedSurface.{0}} [Nonempty S]
    (f : NeatEmbedding S M) (P : ChartPartition S) : ImageAreaAtlas f.image where
  map i := f.toFun ∘ (extChartAt (𝓡∂ 2) (imageAtlasCenter P i)).symm
  chartDomain i := (extChartAt (𝓡∂ 2) (imageAtlasCenter P i)).target
  piece i := if h : i < P.count then
    (extChartAt (𝓡∂ 2) (imageAtlasCenter P i)) '' P.piece ⟨i,h⟩ else ∅
  piece_measurable i := by
    split_ifs with h
    · simp only [imageAtlasCenter, dif_pos h]
      exact AreaAnalysis.extChart_image_measurable _ _ (P.measurable ⟨i,h⟩) (P.subordinate ⟨i,h⟩)
    · exact MeasurableSet.empty
  subordinate i := by
    split_ifs with h
    · simp only [imageAtlasCenter, dif_pos h]
      exact ((extChartAt (𝓡∂ 2) (P.center ⟨i,h⟩)).mapsTo.mono
        (P.subordinate ⟨i,h⟩) (Subset.refl _)).image_subset
    · exact empty_subset _
  c2 i :=
    (f.smoothEmbedding.isImmersion.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm (imageAtlasCenter P i))).of_le (by norm_num)
  chart_embedding i := by
    let e : PartialHomeomorph S E2 := {
      toPartialEquiv := extChartAt (𝓡∂ 2) (imageAtlasCenter P i)
      continuousOn_toFun := continuousOn_extChartAt _
      continuousOn_invFun := continuousOn_extChartAt_symm _ }
    exact f.smoothEmbedding.isEmbedding.comp e.symm.isEmbedding_restrict
  immersion i x hx := coordinateDifferential_injective (ProperSmoothEmbedding.ofNeat f)
    (imageAtlasCenter P i) hx
  partition := by
    intro i j hij
    split_ifs with hi hj
    · simp only [imageAtlasCenter, dif_pos hi, dif_pos hj]
      rw [coordinate_image_recover _ _ _ (P.subordinate _),
        coordinate_image_recover _ _ _ (P.subordinate _)]
      exact (P.disjoint (show (⟨i,hi⟩ : Fin P.count) ≠ ⟨j,hj⟩ from fun h => hij (congrArg Fin.val h))).image
        (f.smoothEmbedding.isEmbedding.injective.injOn (s := univ)) (subset_univ _) (subset_univ _)
    · simp
    · simp
    · simp
  covers := by
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      split_ifs at hi with h
      · simp only [imageAtlasCenter, dif_pos h] at hi
        rw [coordinate_image_recover _ _ _ (P.subordinate _)] at hi
        exact image_subset_range _ _ hi
      · simpa using hi
    · rintro ⟨x,rfl⟩
      have hx : x ∈ ⋃ i, P.piece i := by rw [P.covers]; trivial
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      apply mem_iUnion.mpr
      refine ⟨i.val, ?_⟩
      simp only [dif_pos i.isLt, imageAtlasCenter]
      rw [coordinate_image_recover _ _ _ (P.subordinate _)]
      exact mem_image_of_mem _ hi


theorem neatImageAtlas_density {S : CompactOrientedSurface.{0}} [Nonempty S]
    (g : SmoothMetric M) (f : NeatEmbedding S M) (P : ChartPartition S) (i : ℕ) (y : E2) :
    Real.sqrt (Matrix.det ((neatImageAtlas f P).gram g i y)) =
      coordinateAreaDensity g f.toFun (imageAtlasCenter P i) y := by
  rfl

theorem neatImageAtlas_valid {S : CompactOrientedSurface.{0}} [Nonempty S]
    (g : SmoothMetric M) (f : NeatEmbedding S M) (P : ChartPartition S) :
    (neatImageAtlas f P).Valid g := by
  intro i
  simp_rw [neatImageAtlas_density]
  by_cases h : i < P.count
  · change AEMeasurable (fun y => ENNReal.ofReal
      (coordinateAreaDensity g f.toFun (imageAtlasCenter P i) y))
      (volume.restrict (if h : i < P.count then
        (extChartAt (𝓡∂ 2) (imageAtlasCenter P i)) '' P.piece ⟨i,h⟩ else ∅))
    simp only [dif_pos h, imageAtlasCenter]
    exact (coordinateDensity_integrable_via_chartCover g (ProperSmoothEmbedding.ofNeat f) P
      ⟨i,h⟩).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  · have hp : (neatImageAtlas f P).piece i = ∅ := by simp [neatImageAtlas, h]
    rw [hp]
    simp

theorem neatImageAtlas_area {S : CompactOrientedSurface.{0}} [Nonempty S]
    (g : SmoothMetric M) (f : NeatEmbedding S M) (P : ChartPartition S) :
    (neatImageAtlas f P).area g = ENNReal.ofReal (partitionArea g f.toFun P) := by
  unfold ImageAreaAtlas.area
  rw [tsum_eq_sum (s := Finset.range P.count) (fun i hi => by
    have h : ¬ i < P.count := by simpa using hi
    have hp : (neatImageAtlas f P).piece i = ∅ := by simp [neatImageAtlas, h]
    rw [hp]
    simp)]
  rw [← Fin.sum_univ_eq_sum_range]
  have hi (i : Fin P.count) :
      (∫⁻ y in (neatImageAtlas f P).piece i.val,
        ENNReal.ofReal (Real.sqrt (Matrix.det ((neatImageAtlas f P).gram g i.val y)))) =
      ENNReal.ofReal (∫ y in (extChartAt (𝓡∂ 2) (P.center i)) '' P.piece i,
        coordinateAreaDensity g f.toFun (P.center i) y) := by
    simp_rw [neatImageAtlas_density]
    change (∫⁻ y in (if h : i.val < P.count then
      (extChartAt (𝓡∂ 2) (imageAtlasCenter P i.val)) '' P.piece ⟨i.val,h⟩ else ∅),
      ENNReal.ofReal (coordinateAreaDensity g f.toFun (imageAtlasCenter P i.val) y)) = _
    simp only [dif_pos i.isLt, imageAtlasCenter]
    exact (ofReal_integral_eq_lintegral_ofReal
      (coordinateDensity_integrable_via_chartCover g (ProperSmoothEmbedding.ofNeat f) P i)
      (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _))).symm
  simp_rw [hi]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _)))).symm

#print axioms neatImageAtlas_valid
#print axioms neatImageAtlas_area

theorem neat_image_has_exact_area_atlas {S : CompactOrientedSurface.{0}} [Nonempty S]
    (g : SmoothMetric M) (f : NeatEmbedding S M) :
    ∃ A : ImageAreaAtlas f.image, A.Valid g ∧ A.area g = ENNReal.ofReal (area g f.toFun) := by
  exact ⟨neatImageAtlas f (canonicalPartition S),
    neatImageAtlas_valid g f (canonicalPartition S),
    neatImageAtlas_area g f (canonicalPartition S)⟩

/-- Exact lower-interface area bridge once chart independence is paid. This is
only an internal assembly theorem; no additional premise is added to 5.5. -/
theorem image_area_neat_of_atlas_independence {S : CompactOrientedSurface.{0}} [Nonempty S]
    (g : SmoothMetric M) (f : NeatEmbedding S M)
    (hcharts : ∀ A B : ImageAreaAtlas f.image, A.Valid g → B.Valid g → A.area g = B.area g) :
    imageArea g f.image = area g f.toFun := by
  obtain ⟨A,hA,harea⟩ := neat_image_has_exact_area_atlas g f
  have hset : {a : ℝ≥0∞ | ∃ B : ImageAreaAtlas f.image, B.Valid g ∧ a = B.area g} =
      {ENNReal.ofReal (area g f.toFun)} := by
    ext a
    constructor
    · rintro ⟨B,hB,rfl⟩
      exact (hcharts B A hB hA).trans harea
    · intro ha
      exact ⟨A,hA,(mem_singleton_iff.mp ha).trans harea.symm⟩
  have hnonempty : f.image ≠ ∅ := (Set.range_nonempty f.toFun).ne_empty
  unfold imageArea extendedImageArea
  rw [if_neg hnonempty, hset, sInf_singleton, ENNReal.toReal_ofReal]
  exact area_nonnegative g (ProperSmoothEmbedding.ofNeat f)

#print axioms neat_image_has_exact_area_atlas
#print axioms image_area_neat_of_atlas_independence

theorem empty_image_atlas_area (g : SmoothMetric M) (A : ImageAreaAtlas (∅ : Set M)) :
    A.area g = 0 := by
  have hp : ∀ i, A.piece i = ∅ := by
    intro i
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem : A.map i x ∈ ⋃ j, A.map j '' A.piece j :=
      mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩
    rw [A.covers] at hmem
    exact hmem
  simp [ImageAreaAtlas.area, hp]

theorem image_area_empty (g : SmoothMetric M) : imageArea g (∅ : Set M) = 0 := by
  simp [imageArea, extendedImageArea]

theorem image_area_neat_bridge_assembly {S : CompactOrientedSurface.{0}}
    (g : SmoothMetric M) (f : NeatEmbedding S M)
    (hcharts : ∀ A B : ImageAreaAtlas f.image, A.Valid g → B.Valid g → A.area g = B.area g) :
    imageArea g f.image = area g f.toFun := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    letI := h
    have himg : f.image = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨x,_⟩
      exact isEmptyElim x
    rw [himg, image_area_empty]
    unfold area partitionArea
    symm
    apply Finset.sum_eq_zero
    intro i hi
    exact isEmptyElim ((canonicalPartition S).center i)
  | inr h =>
    letI := h
    exact image_area_neat_of_atlas_independence g f hcharts

#print axioms image_area_empty
#print axioms image_area_neat_bridge_assembly
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
