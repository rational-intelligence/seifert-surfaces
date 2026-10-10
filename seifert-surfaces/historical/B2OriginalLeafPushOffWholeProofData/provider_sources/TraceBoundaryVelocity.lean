import TracePreparations

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
universe u v
noncomputable section

theorem halfspace_atlas_boundary_interior {n : ℕ} [NeZero n]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) ∞ M]
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ n) ∞ M) (x : M) (hx : x ∈ e.source) :
    (x ∈ (𝓡∂ n).boundary M ↔ ((𝓡∂ n) (e x)) 0 = 0) ∧
    (x ∈ (𝓡∂ n).interior M ↔ 0 < ((𝓡∂ n) (e x)) 0) := by
  let e' : PartialDiffeomorph (𝓡∂ n) (𝓡∂ n) M (EuclideanHalfSpace n) ∞ :=
    { __ := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
  have hd : IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ e x :=
    ⟨e', hx, fun _ _ => rfl⟩
  have hb := hd.isBoundaryPoint_iff (by simp)
  have hi := hd.isInteriorPoint_iff (by simp)
  constructor
  · simpa [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint,
      extChartAt, frontier_range_modelWithCornersEuclideanHalfSpace, eq_comm, e'] using hb
  · simpa [ModelWithCorners.interior, ModelWithCorners.IsInteriorPoint,
      extChartAt, interior_range_modelWithCornersEuclideanHalfSpace, e'] using hi



/-- The velocity of any smooth curve lying in the ambient boundary has zero
normal coordinate, including at the endpoints of the time interval. -/
theorem boundary_curve_inward_zero {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (c : Time → M)
    (hc : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ c)
    (hb : ∀ s, c s ∈ (𝓡∂ 3).boundary M) (t : Time)
    (v : TangentSpace (𝓡∂ 1) t) :
    inwardCoordinate (c t) (mfderiv (𝓡∂ 1) (𝓡∂ 3) c t v) = 0 := by
  let e := chartAt (EuclideanHalfSpace 3) (c t)
  let q : Time → ℝ := fun s => ((extChartAt (𝓡∂ 3) (c t)) (c s)) 0
  have he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas (I := 𝓡∂ 3) (n := ∞) _
  have hmem : ∀ᶠ s in 𝓝 t, c s ∈ e.source :=
    hc.continuous.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds (mem_chart_source _ _))
  have hzero : q =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [hmem] with s hs
    exact (halfspace_atlas_boundary_interior e he (c s) hs).1.mp (hb s)
  have hdq : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) q t = 0 := by
    rw [hzero.mfderiv_eq, mfderiv_const]
    simp
  have hchart := mfderiv_comp t
    (mdifferentiableAt_extChartAt (I := 𝓡∂ 3) (mem_chart_source _ (c t)))
    (hc.mdifferentiableAt (by simp))
  have hproj := mfderiv_comp t
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt)
    ((mdifferentiableAt_extChartAt (I := 𝓡∂ 3) (mem_chart_source _ (c t))).comp t
      (hc.mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hproj
  have hq : q = (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)) ∘
      ((extChartAt (𝓡∂ 3) (c t)) ∘ c) := rfl
  rw [← hq, hdq, hchart] at hproj
  have hv := congrArg (fun A : TangentSpace (𝓡∂ 1) t →L[ℝ] ℝ => A v) hproj
  exact hv.symm

/-- The actual normal-isotopy track has boundary-tangent time velocity. -/
theorem normal_boundary_velocity {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}
    (F : SmoothNormalIsotopy S M f g) (x : S) (hx : x ∈ S.boundary)
    (t : Time) (v : TangentSpace (𝓡∂ 1) t) :
    inwardCoordinate ((F.stage t).toFun x)
      (mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun s => (F.stage s).toFun x) t v) = 0 := by
  apply boundary_curve_inward_zero
    (fun s => (F.stage s).toFun x)
    (F.smooth_family.comp (contMDiff_id.prodMk contMDiff_const))
  intro s
  change x ∈ (F.stage s).toFun ⁻¹' (𝓡∂ 3).boundary M
  rw [(F.stage s).boundary_preimage]
  exact hx

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
