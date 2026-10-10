import A5NativeProjectionFiber

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The literal C1 chart transition factors the within derivative of a map
on a closed native piece. Consequently its tangent range is chart-independent. -/
theorem sector_chart_tangent_range_le
    (B : CompactSectorPiece) (f : B → Euc 3)
    (i j : Fin B.count) (y : B)
    (hi : y ∈ (B.chart i).map.source) (hj : y ∈ (B.chart j).map.source)
    (hf : ContDiffWithinAt ℝ 1 (f ∘ (B.chart j).map.symm)
      (B.chart j).map.target ((B.chart j).map y)) :
    (fderivWithin ℝ (f ∘ (B.chart i).map.symm)
      (B.chart i).map.target ((B.chart i).map y)).toLinearMap.range ≤
    (fderivWithin ℝ (f ∘ (B.chart j).map.symm)
      (B.chart j).map.target ((B.chart j).map y)).toLinearMap.range := by
  let ci := (B.chart i).map
  let cj := (B.chart j).map
  let T := cj ∘ ci.symm
  let O := ci.target ∩ ci.symm ⁻¹' cj.source
  have hxi : ci y ∈ ci.target := ci.map_source hi
  have hO : O ∈ 𝓝[ci.target] (ci y) := by
    apply inter_mem self_mem_nhdsWithin
    have hcont := ci.symm.continuousOn (ci y) hxi
    apply hcont.preimage_mem_nhdsWithin
    simpa only [ci.left_inv hi] using (B.chart j).source_open.mem_nhds hj
  have hxO : ci y ∈ O := ⟨hxi, by change ci.symm (ci y) ∈ cj.source; rwa [ci.left_inv hi]⟩
  have hT : ContDiffWithinAt ℝ 1 T ci.target (ci y) :=
    (B.transition_c1 i j (ci y) hxO).mono_of_mem_nhdsWithin hO
  have hTy : T (ci y) = cj y := by dsimp [T]; rw [ci.left_inv hi]
  have hm : ∀ᶠ z in 𝓝[ci.target] (ci y), T z ∈ cj.target := by
    filter_upwards [hO] with z hz
    exact cj.map_source hz.2
  have ht : Tendsto T (𝓝[ci.target] (ci y)) (𝓝[cj.target] (T (ci y))) :=
    tendsto_nhdsWithin_iff.mpr ⟨hT.continuousWithinAt, hm⟩
  have hfj : HasFDerivWithinAt (f ∘ cj.symm)
      (fderivWithin ℝ (f ∘ cj.symm) cj.target (cj y)) cj.target (T (ci y)) :=
    hTy.symm ▸ (hf.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hd := hfj.comp_of_tendsto (ci y)
    (hT.differentiableWithinAt (by norm_num)).hasFDerivWithinAt ht
  have he : (f ∘ ci.symm) =ᶠ[𝓝[ci.target] (ci y)] ((f ∘ cj.symm) ∘ T) := by
    filter_upwards [hO] with z hz
    change f (ci.symm z) = f (cj.symm (cj (ci.symm z)))
    rw [cj.left_inv hz.2]
  have hyEq : (f ∘ ci.symm) (ci y) = ((f ∘ cj.symm) ∘ T) (ci y) := by
    change f (ci.symm (ci y)) = f (cj.symm (cj (ci.symm (ci y))))
    rw [ci.left_inv hi, cj.left_inv hj]
  have hu : UniqueDiffWithinAt ℝ ci.target (ci y) := by
    change UniqueDiffWithinAt ℝ (B.chart i).map.target (ci y)
    rw [(B.chart i).target_eq]
    exact (B.chart i).model.uniqueDiffOn_domain _ (by
      simpa only [← (B.chart i).target_eq] using hxi)
  have hder := (hd.congr_of_eventuallyEq he hyEq).fderivWithin hu
  intro z hz
  obtain ⟨v, hv⟩ := hz
  refine ⟨(fderivWithin ℝ T ci.target (ci y)) v, ?_⟩
  have hh := congrArg (fun D : Euc 2 →L[ℝ] Euc 3 => D v) hder
  exact hh.symm.trans hv

theorem sector_chart_tangent_ranges_eq
    (B : CompactSectorPiece) (f : B → Euc 3)
    (i j : Fin B.count) (y : B)
    (hi : y ∈ (B.chart i).map.source) (hj : y ∈ (B.chart j).map.source)
    (hfi : ContDiffWithinAt ℝ 1 (f ∘ (B.chart i).map.symm)
      (B.chart i).map.target ((B.chart i).map y))
    (hfj : ContDiffWithinAt ℝ 1 (f ∘ (B.chart j).map.symm)
      (B.chart j).map.target ((B.chart j).map y)) :
    (fderivWithin ℝ (f ∘ (B.chart i).map.symm)
      (B.chart i).map.target ((B.chart i).map y)).toLinearMap.range =
    (fderivWithin ℝ (f ∘ (B.chart j).map.symm)
      (B.chart j).map.target ((B.chart j).map y)).toLinearMap.range :=
  le_antisymm (sector_chart_tangent_range_le B f i j y hi hj hfj)
    (sector_chart_tangent_range_le B f j i y hj hi hfi)

/-- Transversality depends on the actual tangent range, independently of the
chosen rank-two parametrization. -/
theorem projection_bijective_of_equal_tangent_ranges
    (D₁ D₂ : Euc 2 →L[ℝ] Euc 3) (P : Euc 3 →L[ℝ] Euc 2)
    (hr : D₁.toLinearMap.range = D₂.toLinearMap.range)
    (hD₂ : Function.Injective D₂) (hP : Function.Bijective (P.comp D₁)) :
    Function.Bijective (P.comp D₂) := by
  have hinj : Function.Injective (P.comp D₂) := by
    intro v w he
    have hv : D₂ v ∈ D₁.toLinearMap.range := hr ▸ (show D₂ v ∈ D₂.toLinearMap.range from ⟨v, rfl⟩)
    have hw : D₂ w ∈ D₁.toLinearMap.range := hr ▸ (show D₂ w ∈ D₂.toLinearMap.range from ⟨w, rfl⟩)
    obtain ⟨a, ha⟩ := hv
    obtain ⟨b, hb⟩ := hw
    change D₁ a = D₂ v at ha
    change D₁ b = D₂ w at hb
    have hab : a = b := hP.1 (by change P (D₁ a) = P (D₁ b); rw [ha, hb]; exact he)
    apply hD₂
    rw [← ha, ← hb, hab]
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

/-- The within-tangent range of one actual whole native piece agrees in any
two of its actual charts containing the same piece point. -/
theorem native_piece_tangent_ranges_eq
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j k : Fin (F.domain i).count) (y : F.domain i)
    (hj : y ∈ ((F.domain i).chart j).map.source)
    (hk : y ∈ ((F.domain i).chart k).map.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map (F.parametrization i y)) ∈ c.chart.source) :
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target (((F.domain i).chart j).map y)).toLinearMap.range =
    (fderivWithin ℝ (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) k)
      ((F.domain i).chart k).map.target (((F.domain i).chart k).map y)).toLinearMap.range := by
  have hreg (l : Fin (F.domain i).count) (hl : y ∈ ((F.domain i).chart l).map.source) :=
    native_piece_chart_C1_rank_at E F i l (((F.domain i).chart l).map y)
      (((F.domain i).chart l).map.map_source hl) c (by
        dsimp [sectorCoordinateMap]
        rw [((F.domain i).chart l).map.left_inv hl]
        exact hc)
  exact sector_chart_tangent_ranges_eq (F.domain i)
    (c.chart ∘ E.toSphere ∘ F.map ∘ F.parametrization i) j k y hj hk
    (hreg j hj).1 (hreg k hk).1

/-- Transversality constructed using one native chart transfers to the
actual chart selected by the seam/conormal data. -/
theorem native_projection_transverse_change_chart
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j k : Fin (F.domain i).count) (y : F.domain i)
    (hj : y ∈ ((F.domain i).chart j).map.source)
    (hk : y ∈ ((F.domain i).chart k).map.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map (F.parametrization i y)) ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target (((F.domain i).chart j).map y)))) :
    Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) k)
      ((F.domain i).chart k).map.target (((F.domain i).chart k).map y))) := by
  apply projection_bijective_of_equal_tangent_ranges _ _ P
    (native_piece_tangent_ranges_eq E F i j k y hj hk c hc) _ hP
  exact (native_piece_chart_C1_rank_at E F i k (((F.domain i).chart k).map y)
    (((F.domain i).chart k).map.map_source hk) c (by
      dsimp [sectorCoordinateMap]
      rw [((F.domain i).chart k).map.left_inv hk]
      exact hc)).2

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
