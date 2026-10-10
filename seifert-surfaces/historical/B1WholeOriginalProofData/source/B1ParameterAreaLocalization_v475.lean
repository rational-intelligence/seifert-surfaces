import B1ParametricAreaTransport_v475
import B1ActualGraphParameters_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem native_parametric_density_of_local_equality_v475
    (g : SmoothMetric M) (F H : Euc 2 → M) (x : Euc 2)
    (heq : F =ᶠ[𝓝 x] H) :
    native_parametric_density_v475 g F x = native_parametric_density_v475 g H x := by
  have hx : F x = H x := heq.self_of_nhds
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ,Euc 2)) (I' := 𝓡∂ 3)
  have hpair (a b : TangentSpace (𝓡∂ 3) (H x)) :
      g.inner (F x) (tangentSpaceCast (𝓡∂ 3) (H x) (F x) a)
        (tangentSpaceCast (𝓡∂ 3) (H x) (F x) b) = g.inner (H x) a b := by
    rw [hx]
    rfl
  unfold native_parametric_density_v475
  congr 2
  ext i j
  rw [hd]
  exact hpair _ _

/-- Actual local area transport along a recovered smooth parameter, with the
source support compactly contained in one original surface chart. -/
theorem native_parameter_area_change_v475
    (g : SmoothMetric M) {S : CompactOrientedSurface.{u}}
    (F H : S → M) (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F)
    (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (p : S) (q : Euc 2 → S) (O A : Set (Euc 2))
    (hO : IsOpen O) (hA : IsCompact A) (hAO : A ⊆ O)
    (hq : ContMDiffOn 𝓘(ℝ,Euc 2) (𝓡∂ 2) ∞ q O)
    (hqs : MapsTo q O (surfaceChart p).source)
    (hqi : ∀ x ∈ O, q x ∉ S.boundary) (hqinj : InjOn q O)
    (heq : EqOn F H (q '' A)ᶜ) :
    area g H - area g F =
      (∫ x in A, native_parametric_density_v475 g (H ∘ q) x) -
      (∫ x in A, native_parametric_density_v475 g (F ∘ q) x) := by
  letI : BorelSpace S := ⟨rfl⟩
  let c : Euc 2 → Euc 2 := surfaceChart p ∘ q
  have hc : ContDiffOn ℝ ∞ c O :=
    ((contMDiffOn_extChartAt (I := 𝓡∂ 2) (x := p)).comp hq
      (fun x hx => by simpa only [extChartAt_source, Set.mem_preimage] using hqs hx)).contDiffOn
  have hct : MapsTo c O (interior (surfaceChart p).target) := by
    intro x hx
    exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p)
      (by simpa only [extChartAt_source, Set.mem_preimage] using hqs hx)).mp
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mpr (hqi x hx))
  have hcA : InjOn c A := by
    intro x hx y hy hxy
    exact hqinj (hAO hx) (hAO hy)
      ((surfaceChart p).injOn (hqs (hAO hx)) (hqs (hAO hy)) hxy)
  have hqA : IsCompact (q '' A) := hA.image_of_continuousOn (hq.continuousOn.mono hAO)
  have hqAp : q '' A ⊆ (surfaceChart p).source := image_subset_iff.mpr (fun x hx => hqs (hAO hx))
  have hintegral (L : S → M) (hL : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ L) :
      coordinateIntegral g L p (q '' A) = ∫ x in A, native_parametric_density_v475 g (L ∘ q) x := by
    unfold coordinateIntegral
    rw [image_image]
    change (∫ y in c '' A, coordinateAreaDensity g L p y) = _
    rw [native_parameter_coordinate_integral_v475 g L hL p c O A hO hA.measurableSet hAO hc hct hcA]
    apply setIntegral_congr_fun hA.measurableSet
    intro x hx
    apply native_parametric_density_of_local_equality_v475
    apply Filter.eventuallyEq_of_mem (hO.mem_nhds (hAO hx))
    intro y hy
    change L ((surfaceChart p).symm ((surfaceChart p) (q y))) = L (q y)
    rw [(surfaceChart p).left_inv (hqs hy)]
  rw [native_actual_area_change_localization_v475 g F H hF hH p (q '' A)
    hqA.isClosed hqAp heq,hintegral H hH,hintegral F hF]

#print axioms native_parametric_density_of_local_equality_v475
#print axioms native_parameter_area_change_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
