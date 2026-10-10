import MetricAreaAnalysis.CompactIntegrability

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v
set_option maxSynthPendingDepth 3

/- H13: common refinement uses the actual two partition families. -/
theorem commonPiece_measurable {S : CompactOrientedSurface.{u}} (P Q : ChartPartition S)
    (i : Fin P.count) (j : Fin Q.count) : MeasurableSet (commonPiece P Q i j) := by
  exact (P.measurable i).inter (Q.measurable j)

theorem commonPiece_subordinate {S : CompactOrientedSurface.{u}} (P Q : ChartPartition S)
    (i : Fin P.count) (j : Fin Q.count) :
    commonPiece P Q i j ⊆ (surfaceChart (P.center i)).source ∩
      (surfaceChart (Q.center j)).source := by
  intro x hx
  exact ⟨P.subordinate i hx.1, Q.subordinate j hx.2⟩

theorem commonPiece_disjoint {S : CompactOrientedSurface.{u}} (P Q : ChartPartition S) :
    Pairwise (fun a b : Fin P.count × Fin Q.count =>
      Disjoint (commonPiece P Q a.1 a.2) (commonPiece P Q b.1 b.2)) := by
  intro a b hab
  by_cases hi : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun hj => hab (Prod.ext hi hj)
    exact (Q.disjoint hj).mono inter_subset_right inter_subset_right
  · exact (P.disjoint hi).mono inter_subset_left inter_subset_left

theorem commonPiece_covers {S : CompactOrientedSurface.{u}} (P Q : ChartPartition S) :
    (⋃ i, ⋃ j, commonPiece P Q i j) = univ := by
  apply Subset.antisymm (subset_univ _)
  intro x _
  have hxP : x ∈ ⋃ i, P.piece i := by rw [P.covers]; trivial
  have hxQ : x ∈ ⋃ j, Q.piece j := by rw [Q.covers]; trivial
  rcases mem_iUnion.mp hxP with ⟨i, hi⟩
  rcases mem_iUnion.mp hxQ with ⟨j, hj⟩
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hi, hj⟩⟩

theorem commonPiece_chart_image_union {S : CompactOrientedSurface.{u}}
    (P Q : ChartPartition S) (i : Fin P.count) :
    (surfaceChart (P.center i)) '' P.piece i =
      ⋃ j, (surfaceChart (P.center i)) '' commonPiece P Q i j := by
  have heq : P.piece i = ⋃ j, commonPiece P Q i j := by
    apply Subset.antisymm
    · intro x hx
      have hxQ : x ∈ ⋃ j, Q.piece j := by rw [Q.covers]; trivial
      rcases mem_iUnion.mp hxQ with ⟨j, hj⟩
      exact mem_iUnion.mpr ⟨j, hx, hj⟩
    · intro x hx
      rcases mem_iUnion.mp hx with ⟨j, hj⟩
      exact hj.1
  rw [heq, image_iUnion]

/- H15a: intrinsic boundary is characterized in any actual chart containing x. -/
theorem surface_boundary_coordinate {S : CompactOrientedSurface.{u}} (p x : S)
    (hx : x ∈ (surfaceChart p).source) :
    x ∈ S.boundary ↔ surfaceChart p x 0 = 0 := by
  have hx' : x ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
    simpa only [surfaceChart, extChartAt_source] using hx
  have hinter : (𝓡∂ 2).IsInteriorPoint x ↔ 0 < surfaceChart p x 0 := by
    rw [(𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p) hx']
    constructor
    · intro h
      have h' := (chartAt (EuclideanHalfSpace 2) p).interior_extend_target_subset_interior_range h
      simpa only [surfaceChart, extChartAt, OpenPartialHomeomorph.extend_coe,
        Function.comp_apply, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
        using h'
    · intro h
      apply (chartAt (EuclideanHalfSpace 2) p).mem_interior_extend_target
        ((chartAt (EuclideanHalfSpace 2) p).map_source hx')
      simpa only [surfaceChart, extChartAt, OpenPartialHomeomorph.extend_coe,
        Function.comp_apply, interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq]
        using h
  have hnonneg : 0 ≤ surfaceChart p x 0 := by
    have h := (surfaceChart p).mapsTo hx
    have h' := extChartAt_target_subset_range (I := 𝓡∂ 2) p h
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using h'
  change (𝓡∂ 2).IsBoundaryPoint x ↔ _
  rw [(𝓡∂ 2).isBoundaryPoint_iff_not_isInteriorPoint, hinter]
  constructor <;> intro h <;> linarith

theorem surface_interior_coordinate {S : CompactOrientedSurface.{u}} (p x : S)
    (hx : x ∈ (surfaceChart p).source) :
    x ∈ (S.boundary)ᶜ ↔ 0 < surfaceChart p x 0 := by
  have hnonneg : 0 ≤ surfaceChart p x 0 := by
    have h := (surfaceChart p).mapsTo hx
    have h' := extChartAt_target_subset_range (I := 𝓡∂ 2) p h
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using h'
  simp only [mem_compl_iff, surface_boundary_coordinate p x hx]
  constructor
  · intro h
    by_contra hnot
    apply h
    linarith
  · exact fun h => ne_of_gt h

/- H15b: Euclidean nullness, rather than a postulated source-surface measure. -/
theorem chartTarget_boundary_null {S : CompactOrientedSurface.{u}} (p : S) :
    (volume : Measure (Euc 2))
      ((surfaceChart p).target ∩ frontier (range (𝓡∂ 2))) = 0 := by
  have hker : (LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 2))) ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ∈
        LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 2)) := by
      rw [h]
      trivial
    have hbad : (1 : ℝ) = 0 := by simpa using hmem
    exact one_ne_zero hbad
  have hnull := Measure.addHaar_submodule (volume : Measure (Euc 2))
    (LinearMap.ker (EuclideanSpace.projₗ (𝕜 := ℝ) (0 : Fin 2))) hker
  apply measure_mono_null _ hnull
  intro y hy
  change y 0 = 0
  have h := hy.2
  rw [frontier_range_modelWithCornersEuclideanHalfSpace] at h
  exact h.symm

theorem extChart_boundary_image_null {S : CompactOrientedSurface.{u}} (p : S) (s : Set S)
    (hsub : s ⊆ (surfaceChart p).source) :
    (volume : Measure (Euc 2)) ((surfaceChart p) '' (s ∩ S.boundary)) = 0 := by
  apply measure_mono_null _ (chartTarget_boundary_null p)
  rintro y ⟨x, hx, rfl⟩
  refine ⟨(surfaceChart p).mapsTo (hsub hx.1), ?_⟩
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  exact ((surface_boundary_coordinate p x (hsub hx.1)).mp hx.2).symm

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/- H14: both orders of the actual finite coordinate sums. -/
theorem partitionArea_pairwise_sum (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (P Q : ChartPartition S) :
    partitionArea g F P =
      ∑ i : Fin P.count, ∑ j : Fin Q.count,
        coordinateIntegral g F (P.center i) (commonPiece P Q i j) ∧
    partitionArea g F Q =
      ∑ j : Fin Q.count, ∑ i : Fin P.count,
        coordinateIntegral g F (Q.center j) (commonPiece P Q i j) := by
  have hrow (P Q : ChartPartition S) (i : Fin P.count) :
      coordinateIntegral g F (P.center i) (P.piece i) =
        ∑ j : Fin Q.count, coordinateIntegral g F (P.center i) (commonPiece P Q i j) := by
    unfold coordinateIntegral
    rw [commonPiece_chart_image_union P Q i]
    apply integral_iUnion_fintype
    · intro j
      exact extChart_image_measurable (P.center i) _ (commonPiece_measurable P Q i j)
        ((commonPiece_subordinate P Q i j).trans inter_subset_left)
    · intro j l hjl
      change Disjoint ((surfaceChart (P.center i)) '' commonPiece P Q i j)
        ((surfaceChart (P.center i)) '' commonPiece P Q i l)
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have hxs := P.subordinate i hx.1
      have hzs := P.subordinate i hz.1
      have hxz := (surfaceChart (P.center i)).injOn hxs hzs (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (Q.disjoint hjl) hx.2 hz.2
    · intro j
      exact coordinateDensity_integrable_measurableChartSubset g F hF (P.center i) _
        (commonPiece_measurable P Q i j)
        ((commonPiece_subordinate P Q i j).trans inter_subset_left)
  constructor
  · unfold partitionArea
    exact Finset.sum_congr rfl (fun i _ => hrow P Q i)
  · unfold partitionArea
    apply Finset.sum_congr rfl
    intro j _
    simpa only [coordinateIntegral, commonPiece, inter_comm] using hrow Q P j

/- H16: removing boundary affects the set of integration, not the density. -/
theorem coordinateDensity_integral_remove_boundary (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (p : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source) :
    coordinateIntegral g F p s = coordinateIntegral g F p (s \ S.boundary) := by
  have hdecomp : s = (s \ S.boundary) ∪ (s ∩ S.boundary) := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter_iff]
    tauto
  have hae : (surfaceChart p) '' s =ᵐ[volume]
      (surfaceChart p) '' (s \ S.boundary) := by
    calc
      (surfaceChart p) '' s =
          (surfaceChart p) '' (s \ S.boundary) ∪
            (surfaceChart p) '' (s ∩ S.boundary) := by
        rw [← image_union, ← hdecomp]
      _ =ᵐ[volume] (surfaceChart p) '' (s \ S.boundary) :=
        union_ae_eq_left_of_ae_eq_empty
          (ae_eq_empty.mpr (extChart_boundary_image_null p s hsub))
  exact setIntegral_congr_set hae

theorem coordinateIntegrable_remove_boundary (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (F : S → M) (p : S) (s : Set S)
    (hsub : s ⊆ (surfaceChart p).source) :
    IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' s) ↔
      IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' (s \ S.boundary)) := by
  have hdecomp : s = (s \ S.boundary) ∪ (s ∩ S.boundary) := by
    ext x
    simp only [mem_union, mem_sdiff, mem_inter_iff]
    tauto
  have hae : (surfaceChart p) '' s =ᵐ[volume]
      (surfaceChart p) '' (s \ S.boundary) := by
    calc
      (surfaceChart p) '' s =
          (surfaceChart p) '' (s \ S.boundary) ∪
            (surfaceChart p) '' (s ∩ S.boundary) := by
        rw [← image_union, ← hdecomp]
      _ =ᵐ[volume] (surfaceChart p) '' (s \ S.boundary) :=
        union_ae_eq_left_of_ae_eq_empty
          (ae_eq_empty.mpr (extChart_boundary_image_null p s hsub))
  exact integrableOn_congr_set_ae hae

/- H17: strict positivity is confined to a genuine ball inside the chart target. -/
theorem coordinateBall_integral_pos (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (f : ProperSmoothEmbedding S M) (p : S) (z : Euc 2) (r : ℝ)
    (hr : 0 < r) (hball : Metric.closedBall z r ⊆ (surfaceChart p).target) :
    0 < ∫ y in Metric.ball z r, coordinateAreaDensity g f.toFun p y := by
  have hcontinuous := (coordinateAreaDensity_continuous g f.toFun f.smooth p).mono hball
  have hintegrable := (hcontinuous.integrableOn_compact (μ := volume)
    (isCompact_closedBall z r)).mono_set
    Metric.ball_subset_closedBall
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _)) hintegrable).mpr
  have hsupp : Function.support (coordinateAreaDensity g f.toFun p) ∩ Metric.ball z r =
      Metric.ball z r := by
    apply inter_eq_right.mpr
    intro y hy
    exact (coordinateAreaDensity_pos g f p (hball (Metric.ball_subset_closedBall hy))).ne'
  change 0 < volume (Function.support (coordinateAreaDensity g f.toFun p) ∩ Metric.ball z r)
  rw [hsupp]
  exact Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hr)

/- H18: no partition piece is asserted to have nonempty interior. -/
theorem coordinateSubset_integral_le_partitionArea (g : SmoothMetric M)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M)
    (P : ChartPartition S) (p : S) (s : Set S)
    (hs : MeasurableSet s) (hsub : s ⊆ (surfaceChart p).source) :
    coordinateIntegral g f.toFun p s ≤ partitionArea g f.toFun P := by
  have heq : s = ⋃ i, s ∩ P.piece i := by
    apply Subset.antisymm
    · intro x hx
      have hxP : x ∈ ⋃ i, P.piece i := by rw [P.covers]; trivial
      rcases mem_iUnion.mp hxP with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨i, hx, hi⟩
    · intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      exact hi.1
  have hsum : coordinateIntegral g f.toFun p s =
      ∑ i, coordinateIntegral g f.toFun p (s ∩ P.piece i) := by
    unfold coordinateIntegral
    conv_lhs => rw [heq, image_iUnion]
    apply integral_iUnion_fintype
    · intro i
      exact extChart_image_measurable p _ (hs.inter (P.measurable i))
        (inter_subset_left.trans hsub)
    · intro i j hij
      change Disjoint ((surfaceChart p) '' (s ∩ P.piece i))
        ((surfaceChart p) '' (s ∩ P.piece j))
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have hxz := (surfaceChart p).injOn (hsub hx.1) (hsub hz.1) (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (P.disjoint hij) hx.2 hz.2
    · intro i
      exact coordinateDensity_integrable_measurableChartSubset g f.toFun f.smooth p _
        (hs.inter (P.measurable i)) (inter_subset_left.trans hsub)
  rw [hsum]
  unfold partitionArea
  apply Finset.sum_le_sum
  intro i _
  have hover : s ∩ P.piece i ⊆ (surfaceChart p).source ∩
      (surfaceChart (P.center i)).source := fun x hx =>
    ⟨hsub hx.1, P.subordinate i hx.2⟩
  rw [coordinateIntegral_overlap g f.toFun f.smooth p (P.center i) _
    (hs.inter (P.measurable i)) hover]
  apply setIntegral_mono_set
    (coordinateDensity_integrable_measurableChartSubset g f.toFun f.smooth (P.center i)
      (P.piece i) (P.measurable i) (P.subordinate i))
    (Filter.Eventually.of_forall (fun y => Real.sqrt_nonneg _))
  exact (image_mono inter_subset_right).eventuallySubset

end SeifertSurfaces.MetricFoundations.AreaAnalysis
