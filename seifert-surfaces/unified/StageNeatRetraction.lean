import LinearNeatVelocity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

/-- Boundary coordinates are preserved by every smooth atlas chart, including
those supplied by the actual immersion normal form. -/
theorem chart_boundary_normal_iff {n : ℕ} [NeZero n] {N : Type*}
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace n) N]
    [IsManifold (𝓡∂ n) ∞ N]
    (e : OpenPartialHomeomorph N (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ N) {y : N} (hy : y ∈ e.source) :
    y ∈ (𝓡∂ n).boundary N ↔ (𝓡∂ n) (e y) 0 = 0 := by
  let d : PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) N (EuclideanHalfSpace n) ∞ := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have h := (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ d hy).isBoundaryPoint_iff (by simp)
  change (𝓡∂ n).IsBoundaryPoint y ↔ (𝓡∂ n) (e y) 0 = 0
  rw [h, ModelWithCorners.isBoundaryPoint_iff,
    frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (𝓡∂ n) (e y) 0 ↔ (𝓡∂ n) (e y) 0 = 0
  exact eq_comm

/-- A linear slice which maps a relative neighbourhood of a boundary point
neatly into a halfspace has a positive boundary normal factor. -/
theorem linear_slice_normal_positive (A : Euc 2 →L[ℝ] Euc 3)
    {D : Set (Euc 2)} {q : Euc 2} (hq : q ∈ range (𝓡∂ 2)) (hq0 : q 0 = 0)
    (hD : D ∈ 𝓝[range (𝓡∂ 2)] q) (hAq : A q 0 = 0)
    (hmap : ∀ w ∈ D, 0 ≤ A w 0)
    (hboundary : ∀ w ∈ D, A w 0 = 0 ↔ w 0 = 0)
    (hpositive : ∃ w ∈ D, 0 < w 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ w, A w 0 = a * w 0 := by
  let L : Euc 2 →L[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).comp A
  have hmin : IsLocalMinOn (fun z => L z) (range (𝓡∂ 2)) q := by
    filter_upwards [hD] with z hz
    change A q 0 ≤ A z 0
    rw [hAq]
    exact hmap z hz
  have hnonneg (w : Euc 2) (hw : 0 ≤ w 0) : 0 ≤ L w := by
    have h := hmin.fderivWithin_nonneg
      (mem_posTangentConeAt_of_segment_subset ((𝓡∂ 2).convex_range.segment_subset hq
        (by rw [range_modelWithCornersEuclideanHalfSpace]
            change 0 ≤ (q+w) 0
            simpa only [PiLp.add_apply, hq0, zero_add] using hw)))
    rwa [L.hasFDerivAt.hasFDerivWithinAt.fderivWithin ((𝓡∂ 2).uniqueDiffOn _ hq)] at h
  have hker (w : Euc 2) (hw : w 0 = 0) : L w = 0 := by
    apply le_antisymm
    · have h := hnonneg (-w) (by simp [hw])
      simpa only [map_neg, neg_nonneg] using h
    · exact hnonneg w (by simp [hw])
  let u : Euc 2 := EuclideanSpace.single 0 1
  have hu : u 0 = 1 := by simp [u]
  have hfactor (w : Euc 2) : L w = L u * w 0 := by
    have h := hker (w - w 0 • u) (by simp [hu])
    simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero, mul_comm] using h
  have hne : L u ≠ 0 := by
    intro hzero
    obtain ⟨w,hw,hw0⟩ := hpositive
    have hz : A w 0 = 0 := by change L w = 0; rw [hfactor, hzero, zero_mul]
    exact hw0.ne' ((hboundary w hw).mp hz)
  refine ⟨L u, lt_of_le_of_ne (hnonneg u (by rw [hu]; norm_num)) hne.symm, ?_⟩
  exact hfactor

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Actual neat embeddings admit a smooth local retraction at every boundary
point. The construction uses their supplied nonlinear immersion charts. -/
theorem neat_exists_boundary_local_retraction (f : NeatEmbedding S M)
    (x : S) (hx : x ∈ S.boundary) :
    ∃ U : Set M, IsOpen U ∧ f.toFun x ∈ U ∧ ∃ r : M → S,
      ContMDiffOn (𝓡∂ 3) (𝓡∂ 2) ∞ r U ∧
      (∀ y, f.toFun y ∈ U → r (f.toFun y) = y) ∧
      (∀ y ∈ U, y ∈ (𝓡∂ 3).boundary M → r y ∈ S.boundary) := by
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
  let P := linearHalfspaceRetraction R a ha hRn
  have hP : ContMDiff (𝓡∂ 3) (𝓡∂ 2) ∞ P :=
    linearHalfspaceRetraction_contMDiff R a ha hRn
  let U₀ : Set M := d.source ∩ (fun y => P (d y)) ⁻¹' c.target
  have hU₀ : IsOpen U₀ :=
    (hP.continuous.comp_continuousOn
      (contMDiffOn_of_mem_maximalAtlas hd).continuousOn).isOpen_inter_preimage
        d.open_source c.open_target
  have hPx : P (d (f.toFun x)) = c x := by
    apply (𝓡∂ 2).injective
    rw [linearHalfspaceRetraction_read, show (𝓡∂ 3) (d (f.toFun x)) = A q from hread x hxC, hRA]
    rfl
  have hxU₀ : f.toFun x ∈ U₀ := ⟨hfxD, by
    change P (d (f.toFun x)) ∈ c.target
    rw [hPx]
    exact c.map_source hxC⟩
  let r : M → S := fun y => c.symm (P (d y))
  have hr : ContMDiffOn (𝓡∂ 3) (𝓡∂ 2) ∞ r U₀ :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      (hP.comp_contMDiffOn ((contMDiffOn_of_mem_maximalAtlas hd).mono inter_subset_left))
      inter_subset_right
  have hfix (y : S) (hy : y ∈ c.source) : r (f.toFun y) = y := by
    have hPy : P (d (f.toFun y)) = c y := by
      apply (𝓡∂ 2).injective
      rw [linearHalfspaceRetraction_read]
      change R ((d.extend (𝓡∂ 3)) (f.toFun y)) = (c.extend (𝓡∂ 2)) y
      rw [hread y hy, hRA]
    exact (congrArg c.symm hPy).trans (c.left_inv hy)
  obtain ⟨W,hW,hWeq⟩ := f.smoothEmbedding.isEmbedding.isInducing.isOpen_iff.mp c.open_source
  let U : Set M := U₀ ∩ W
  refine ⟨U,hU₀.inter hW,⟨hxU₀,?_⟩,r,hr.mono inter_subset_left,?_,?_⟩
  · change x ∈ f.toFun ⁻¹' W
    rw [hWeq]
    exact hxC
  · intro y hy
    exact hfix y (by rw [← hWeq]; exact hy.2)
  · intro y hy hyb
    have hcy : r y ∈ c.source := c.map_target hy.1.2
    apply (chart_boundary_normal_iff c hc hcy).mpr
    have hdb : (𝓡∂ 3) (d y) 0 = 0 := (chart_boundary_normal_iff d hd hy.1.1).mp hyb
    change (𝓡∂ 2) (c (c.symm (P (d y)))) 0 = 0
    rw [c.right_inv hy.1.2]
    exact linearHalfspaceRetraction_boundary R a ha hRn (d y) hdb

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
