import B1ActualCompactGraphVariation_v475
import MetricAreaAnalysis.Assembly

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.MetricFoundations.AreaAnalysis
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Local equality cancels actual chart densities, including the dependent
transport between the two equal ambient tangent fibers. -/
theorem native_coordinate_density_of_local_equality_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F H : S → M) (p : S) (y : Euc 2) (hy : y ∈ (surfaceChart p).target)
    (heq : F =ᶠ[𝓝 ((surfaceChart p).symm y)] H) :
    coordinateAreaDensity g F p y = coordinateAreaDensity g H p y := by
  let e := surfaceChart p
  have hf : (F ∘ e.symm) =ᶠ[𝓝[e.target] y] (H ∘ e.symm) :=
    (continuousOn_extChartAt_symm p y hy).tendsto.eventually heq
  have hx : F (e.symm y) = H (e.symm y) := heq.self_of_nhds
  have hd := hf.mfderivWithin_eq (I := 𝓘(ℝ,Euc 2)) (I' := 𝓡∂ 3) hx
  have hpair (a b : TangentSpace (𝓡∂ 3) (H (e.symm y))) :
      g.inner (F (e.symm y))
        (tangentSpaceCast (𝓡∂ 3) (H (e.symm y)) (F (e.symm y)) a)
        (tangentSpaceCast (𝓡∂ 3) (H (e.symm y)) (F (e.symm y)) b) =
      g.inner (H (e.symm y)) a b := by
    rw [hx]
    rfl
  unfold coordinateAreaDensity
  congr 2
  ext i j
  change g.inner (F (e.symm y))
      (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 3) (F ∘ e.symm) e.target y
        ((tangentSpaceCastModel 𝓘(ℝ,Euc 2) y).symm (EuclideanSpace.single i 1)))
      (mfderivWithin 𝓘(ℝ,Euc 2) (𝓡∂ 3) (F ∘ e.symm) e.target y
        ((tangentSpaceCastModel 𝓘(ℝ,Euc 2) y).symm (EuclideanSpace.single j 1))) = _
  rw [hd]
  exact hpair _ _

/-- Every coordinate cell in the unchanged open part of the original source
has zero area change. -/
theorem native_coordinate_integral_of_local_equality_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F H : S → M) (p : S) (A : Set S) (hA : MeasurableSet A)
    (hAp : A ⊆ (surfaceChart p).source)
    (heq : ∀ x ∈ A, F =ᶠ[𝓝 x] H) :
    coordinateIntegral g F p A = coordinateIntegral g H p A := by
  unfold coordinateIntegral
  apply setIntegral_congr_fun (extChart_image_measurable p A hA hAp)
  rintro y ⟨x,hx,rfl⟩
  have hy := (surfaceChart p).map_source (hAp hx)
  apply native_coordinate_density_of_local_equality_v475 g F H p _ hy
  rw [(surfaceChart p).left_inv (hAp hx)]
  exact heq x hx

/-- A source region contained in one chart can be split out of the literal
finite chart-partition area, without asserting that partition cells are open. -/
theorem native_partition_area_local_split_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (P : ChartPartition S) (p : S) (A : Set S) (hA : MeasurableSet A)
    (hAp : A ⊆ (surfaceChart p).source) :
    partitionArea g F P = coordinateIntegral g F p A +
      ∑ i, coordinateIntegral g F (P.center i) (P.piece i \ A) := by
  have hcover : A = ⋃ i, A ∩ P.piece i := by
    ext x
    constructor
    · intro hx
      have hP : x ∈ ⋃ i, P.piece i := by rw [P.covers]; trivial
      obtain ⟨i,hi⟩ := mem_iUnion.mp hP
      exact mem_iUnion.mpr ⟨i,hx,hi⟩
    · intro hx
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact hi.1
  have hsum : coordinateIntegral g F p A =
      ∑ i, coordinateIntegral g F p (A ∩ P.piece i) := by
    unfold coordinateIntegral
    conv_lhs => rw [hcover,image_iUnion]
    apply integral_iUnion_fintype
    · intro i
      exact extChart_image_measurable p _ (hA.inter (P.measurable i))
        (inter_subset_left.trans hAp)
    · intro i j hij
      change Disjoint ((surfaceChart p) '' (A ∩ P.piece i))
        ((surfaceChart p) '' (A ∩ P.piece j))
      rw [Set.disjoint_left]
      rintro y ⟨x,hx,hxy⟩ ⟨z,hz,hzy⟩
      have he : x = z := (surfaceChart p).injOn (hAp hx.1) (hAp hz.1) (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (P.disjoint hij) hx.2 hz.2
    · intro i
      exact coordinateDensity_integrable_measurableChartSubset g F hF p _
        (hA.inter (P.measurable i)) (inter_subset_left.trans hAp)
  have hsplit (i : Fin P.count) :
      coordinateIntegral g F (P.center i) (P.piece i) =
        coordinateIntegral g F (P.center i) (A ∩ P.piece i) +
        coordinateIntegral g F (P.center i) (P.piece i \ A) := by
    let c := surfaceChart (P.center i)
    have hm : MeasurableSet (c '' (P.piece i \ A)) :=
      extChart_image_measurable _ _ ((P.measurable i).diff hA) (sdiff_subset.trans (P.subordinate i))
    have hcov : P.piece i = (A ∩ P.piece i) ∪ (P.piece i \ A) := by
      ext x
      simp only [mem_union,mem_inter_iff,Set.mem_sdiff]
      tauto
    have hdisj : Disjoint (c '' (A ∩ P.piece i)) (c '' (P.piece i \ A)) := by
      rw [Set.disjoint_left]
      rintro y ⟨x,hx,hxy⟩ ⟨z,hz,hzy⟩
      have he : x = z := c.injOn (P.subordinate i hx.2) (P.subordinate i hz.1) (hxy.trans hzy.symm)
      subst z
      exact hz.2 hx.1
    have hi₁ := coordinateDensity_integrable_measurableChartSubset g F hF (P.center i) _
      (hA.inter (P.measurable i)) (inter_subset_right.trans (P.subordinate i))
    have hi₂ := coordinateDensity_integrable_measurableChartSubset g F hF (P.center i) _
      ((P.measurable i).diff hA) (sdiff_subset.trans (P.subordinate i))
    unfold coordinateIntegral
    conv_lhs => rw [hcov,image_union]
    exact setIntegral_union hdisj hm hi₁ hi₂
  have hover (i : Fin P.count) : coordinateIntegral g F (P.center i) (A ∩ P.piece i) =
      coordinateIntegral g F p (A ∩ P.piece i) := by
    exact (coordinateIntegral_overlap g F hF p (P.center i) _ (hA.inter (P.measurable i))
      (fun x hx => ⟨hAp hx.1,P.subordinate i hx.2⟩)).symm
  change (∑ i, coordinateIntegral g F (P.center i) (P.piece i)) = _
  simp_rw [hsplit,hover]
  rw [Finset.sum_add_distrib,← hsum]

/-- The exact geometric area change of two smooth source maps agreeing off a
closed local support is the area change on that support in a single chart. -/
theorem native_actual_area_change_localization_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F H : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (p : S) (A : Set S) (hA : IsClosed A) (hAp : A ⊆ (surfaceChart p).source)
    (heq : EqOn F H Aᶜ) :
    area g H - area g F = coordinateIntegral g H p A - coordinateIntegral g F p A := by
  letI : BorelSpace S := ⟨rfl⟩
  have hl : ∀ x ∈ Aᶜ, F =ᶠ[𝓝 x] H := fun x hx =>
    Filter.eventuallyEq_of_mem (hA.isOpen_compl.mem_nhds hx) heq
  have hc (i : Fin (canonicalPartition S).count) :
      coordinateIntegral g F ((canonicalPartition S).center i) ((canonicalPartition S).piece i \ A) =
      coordinateIntegral g H ((canonicalPartition S).center i) ((canonicalPartition S).piece i \ A) :=
    native_coordinate_integral_of_local_equality_v475 g F H _ _
      (((canonicalPartition S).measurable i).diff hA.measurableSet)
      (sdiff_subset.trans ((canonicalPartition S).subordinate i)) (fun x hx => hl x hx.2)
  unfold area
  rw [native_partition_area_local_split_v475 g H hH _ p A hA.measurableSet hAp,
    native_partition_area_local_split_v475 g F hF _ p A hA.measurableSet hAp]
  simp_rw [hc]
  ring

#print axioms native_coordinate_density_of_local_equality_v475
#print axioms native_coordinate_integral_of_local_equality_v475
#print axioms native_partition_area_local_split_v475
#print axioms native_actual_area_change_localization_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
