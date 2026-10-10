import MovingBoundaryRetraction

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

theorem neat_exists_coordinates (f : NeatEmbedding S M) (x : S) :
    ∃ (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
      (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
      (A : Euc 2 →L[ℝ] Euc 3) (R : Euc 3 →L[ℝ] Euc 2),
      c ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S ∧
      d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M ∧
      x ∈ c.source ∧ f.toFun x ∈ d.source ∧ Function.LeftInverse R A ∧
      (∀ y ∈ c.source, f.toFun y ∈ d.source ∧
        (d.extend (𝓡∂ 3)) (f.toFun y) = A ((c.extend (𝓡∂ 2)) y)) := by
  let h := f.smoothEmbedding.isImmersion.isImmersionAt x
  let c := h.domChart
  let d := h.codChart
  let A : Euc 2 →L[ℝ] Euc 3 := h.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Euc 2) h.complement)
  let R : Euc 3 →L[ℝ] Euc 2 := (ContinuousLinearMap.fst ℝ (Euc 2) h.complement).comp
    h.equiv.symm.toContinuousLinearMap
  refine ⟨c,d,A,R,h.domChart_mem_maximalAtlas,h.codChart_mem_maximalAtlas,
    h.mem_domChart_source,h.mem_codChart_source,?_,?_⟩
  · intro w
    simp [R,A]
  · intro y hy
    refine ⟨h.source_subset_preimage_source hy,?_⟩
    have hh := h.writtenInCharts ((c.extend (𝓡∂ 2)).map_source (by simpa using hy))
    change (d.extend (𝓡∂ 3)) (f.toFun ((c.extend (𝓡∂ 2)).symm
      ((c.extend (𝓡∂ 2)) y))) = A ((c.extend (𝓡∂ 2)) y) at hh
    rwa [(c.extend (𝓡∂ 2)).left_inv
      (show y ∈ (c.extend (𝓡∂ 2)).source by simpa using hy)] at hh

/-- Actual Euclidean moving inverse at any source point; the interior
retraction will use the open positive-normal part of its target. -/
theorem normal_exists_moving_inverse (F : SmoothNormalIsotopy S M f g)
    (t : Time) (x : S) :
    ∃ (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
      (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
      (R : Euc 3 →L[ℝ] Euc 2)
      (U : Set (ℝ × Euc 2)) (G : ℝ × Euc 2 → Euc 3)
      (e : OpenPartialHomeomorph (ℝ × Euc 2) (ℝ × Euc 2)),
      c ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ S ∧
      d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M ∧
      x ∈ c.source ∧ (F.stage t).toFun x ∈ d.source ∧ IsOpen U ∧
      ((t : ℝ), (c.extend (𝓡∂ 2)) x) ∈ U ∧ ContDiff ℝ ∞ G ∧
      (∀ q ∈ U, q.1 ∈ Icc 0 1 → q.2 ∈ range (𝓡∂ 2) →
        q.2 ∈ (c.extend (𝓡∂ 2)).target ∧
        (F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
          ((c.extend (𝓡∂ 2)).symm q.2) ∈ d.source ∧
        G q = (d.extend (𝓡∂ 3))
          ((F.stage (projIcc 0 1 (by norm_num) q.1)).toFun
            ((c.extend (𝓡∂ 2)).symm q.2))) ∧
      ((t : ℝ), (c.extend (𝓡∂ 2)) x) ∈ e.source ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q, e q = (q.1, R (G q))) ∧
      (∀ q ∈ e.target, (e.symm q).1 = q.1) := by
  obtain ⟨c,d,A,R,hc,hd,hxc,hfxd,hRA,hread⟩ := neat_exists_coordinates (F.stage t) x
  obtain ⟨U,hU,hqU,G,hG,hGeq⟩ := normal_exists_local_chart_extension F c hc d hd t x hxc hfxd
  let u : Euc 2 := (c.extend (𝓡∂ 2)) x
  let h : ℝ × Euc 2 → Euc 2 := fun q => R (G q)
  have hh : ContDiff ℝ ∞ h := R.contDiff.comp hG
  have htime : projIcc 0 1 (by norm_num) (t : ℝ) = t :=
    Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) t.property])
  have hslice : (fun b => h ((t : ℝ),b)) =ᶠ[𝓝[range (𝓡∂ 2)] u] id := by
    have hnear : ∀ᶠ b in 𝓝[range (𝓡∂ 2)] u, ((t : ℝ),b) ∈ U :=
      mem_nhdsWithin_of_mem_nhds ((continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (hU.mem_nhds hqU))
    filter_upwards [hnear,self_mem_nhdsWithin] with b hbU hb
    have he := hGeq ((t : ℝ),b) hbU t.property hb
    have hcb : (c.extend (𝓡∂ 2)).symm b ∈ c.source := by
      have hy := (c.extend (𝓡∂ 2)).map_target he.1
      simpa only [OpenPartialHomeomorph.extend_source] using hy
    dsimp [h]
    rw [he.2.2,htime,(hread _ hcb).2,(c.extend (𝓡∂ 2)).right_inv he.1,hRA]
  have hsmooth : ContDiff ℝ ∞ (fun b => h ((t : ℝ),b)) :=
    hh.comp (contDiff_const.prodMk contDiff_id)
  have hderSlice : fderiv ℝ (fun b => h ((t : ℝ),b)) u = ContinuousLinearMap.id ℝ (Euc 2) := by
    have hu : u ∈ range (𝓡∂ 2) := mem_range_self (c x)
    have hud := (𝓡∂ 2).uniqueDiffOn u hu
    rw [← fderivWithin_eq_fderiv hud (hsmooth.differentiable (by simp)).differentiableAt,
      hslice.fderivWithin_eq (hslice.eq_of_nhdsWithin hu)]
    exact hasFDerivAt_id u |>.hasFDerivWithinAt.fderivWithin hud
  have hvertical : ∀ b, fderiv ℝ h ((t : ℝ),u) (0,b) = b := by
    have hl : HasFDerivAt (fun b : Euc 2 => ((t : ℝ),b))
        (ContinuousLinearMap.inr ℝ ℝ (Euc 2)) u := by
      exact (hasFDerivAt_const (t : ℝ) u).prodMk (hasFDerivAt_id u)
    have hd := ((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).comp u hl
    have heq := hd.fderiv
    change fderiv ℝ (fun b => h ((t : ℝ),b)) u = _ at heq
    rw [hderSlice] at heq
    intro b
    have hb := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L b) heq
    exact hb.symm
  obtain ⟨e,hqe,heU,he,hei,hemap,heinv⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_preserving_vector_parameter hh.contDiffOn hU hqU
      (ContinuousLinearEquiv.refl ℝ (Euc 2)) hvertical
  refine ⟨c,d,R,U,G,e,hc,hd,hxc,hfxd,hU,hqU,hG,hGeq,hqe,heU,he,hei,hemap,?_⟩
  intro q hq
  exact (heinv q hq).1

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
