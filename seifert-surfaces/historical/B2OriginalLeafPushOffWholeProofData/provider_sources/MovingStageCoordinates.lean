import MovingChartExtension

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- The actual immersion charts carry a linear left inverse whose normal
coordinate is positive. This exposes the data needed for the moving inverse,
rather than supplying an independent retraction premise. -/
theorem neat_exists_boundary_coordinates (f : NeatEmbedding S M)
    (x : S) (hx : x ∈ S.boundary) :
    ∃ (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
      (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
      (A : Euc 2 →L[ℝ] Euc 3) (R : Euc 3 →L[ℝ] Euc 2) (a : ℝ),
      c ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S ∧
      d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M ∧
      x ∈ c.source ∧ f.toFun x ∈ d.source ∧ 0 < a ∧
      Function.LeftInverse R A ∧ (∀ w, A w 0 = a * w 0) ∧
      (∀ w, R w 0 = w 0 / a) ∧
      (∀ y ∈ c.source, f.toFun y ∈ d.source ∧
        (d.extend (𝓡∂ 3)) (f.toFun y) = A ((c.extend (𝓡∂ 2)) y)) := by
  let h := f.smoothEmbedding.isImmersion.isImmersionAt x
  let c := h.domChart
  let d := h.codChart
  let A : Euc 2 →L[ℝ] Euc 3 := h.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Euc 2) h.complement)
  let q : Euc 2 := (c.extend (𝓡∂ 2)) x
  let D : Set (Euc 2) := (c.extend (𝓡∂ 2)).target
  have hxC : x ∈ c.source := h.mem_domChart_source
  have hfxD : f.toFun x ∈ d.source := h.mem_codChart_source
  have hc := h.domChart_mem_maximalAtlas
  have hd := h.codChart_mem_maximalAtlas
  have hread (y : S) (hy : y ∈ c.source) :
      (d.extend (𝓡∂ 3)) (f.toFun y) = A ((c.extend (𝓡∂ 2)) y) := by
    have hh := h.writtenInCharts ((c.extend (𝓡∂ 2)).map_source (by simpa using hy))
    change (d.extend (𝓡∂ 3)) (f.toFun ((c.extend (𝓡∂ 2)).symm
      ((c.extend (𝓡∂ 2)) y))) = A ((c.extend (𝓡∂ 2)) y) at hh
    rwa [(c.extend (𝓡∂ 2)).left_inv
      (show y ∈ (c.extend (𝓡∂ 2)).source by simpa using hy)] at hh
  have hqD : q ∈ D := (c.extend (𝓡∂ 2)).map_source (by simpa using hxC)
  have hqH : q ∈ range (𝓡∂ 2) := by exact mem_range_self (c x)
  have hq0 : q 0 = 0 := (chart_boundary_normal_iff c hc hxC).mp hx
  have hAq : A q 0 = 0 := by
    rw [← hread x hxC]
    exact (chart_boundary_normal_iff d hd hfxD).mp (by
      change x ∈ f.toFun ⁻¹' (𝓡∂ 3).boundary M
      rwa [f.boundary_preimage])
  have hDn : D ∈ 𝓝[range (𝓡∂ 2)] q := by
    rw [← c.map_extend_nhds hxC]
    change (c.extend (𝓡∂ 2)).target ∈ Filter.map (c.extend (𝓡∂ 2)) (𝓝 x)
    rw [c.extend_target_eq_image_source]
    exact Filter.image_mem_map (c.open_source.mem_nhds hxC)
  have hmap (w : Euc 2) (hw : w ∈ D) : 0 ≤ A w 0 := by
    have h := h.map_target_subset_target (mem_image_of_mem _ hw)
    have hh : A w ∈ range (𝓡∂ 3) := by
      have ht := h.1
      change A w ∈ (𝓡∂ 3).target at ht
      simpa only [ModelWithCorners.target_eq] using ht
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hh
  have hb (w : Euc 2) (hw : w ∈ D) : A w 0 = 0 ↔ w 0 = 0 := by
    let y : S := (c.extend (𝓡∂ 2)).symm w
    have hy : y ∈ c.source := by
      have ht := (c.extend (𝓡∂ 2)).map_target hw
      change y ∈ (c.extend (𝓡∂ 2)).source at ht
      simpa only [OpenPartialHomeomorph.extend_source] using ht
    have he : (c.extend (𝓡∂ 2)) y = w := (c.extend (𝓡∂ 2)).right_inv hw
    have hfy : f.toFun y ∈ d.source := h.source_subset_preimage_source hy
    rw [← he, ← hread y hy]
    change (𝓡∂ 3) (d (f.toFun y)) 0 = 0 ↔ (𝓡∂ 2) (c y) 0 = 0
    rw [← chart_boundary_normal_iff d hd hfy, ← chart_boundary_normal_iff c hc hy]
    change y ∈ f.toFun ⁻¹' (𝓡∂ 3).boundary M ↔ y ∈ S.boundary
    rw [f.boundary_preimage]
  have hpos : ∃ w ∈ D, 0 < w 0 := by
    obtain ⟨W,hWo,hqW,hWD⟩ := mem_nhdsWithin.mp hDn
    have hqcl : q ∈ closure (interior (range (𝓡∂ 2))) := by
      rw [← (𝓡∂ 2).range_eq_closure_interior]
      exact hqH
    obtain ⟨w,hwW,hwint⟩ := mem_closure_iff.mp hqcl W hWo hqW
    refine ⟨w,hWD ⟨hwW,interior_subset hwint⟩,?_⟩
    simpa only [interior_range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hwint
  obtain ⟨a,ha,hAn⟩ := linear_slice_normal_positive A hqH hq0 hDn hAq hmap hb hpos
  have hAi : Function.Injective A := h.equiv.injective.comp LinearMap.inl_injective
  obtain ⟨R,hRA,hRn⟩ := exists_boundary_compatible_leftInverse A hAi a ha.ne' hAn
  refine ⟨c,d,A,R,a,hc,hd,hxC,hfxD,ha,hRA,hAn,hRn,?_⟩
  intro y hy
  exact ⟨h.source_subset_preimage_source hy,hread y hy⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
