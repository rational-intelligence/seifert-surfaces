import MovingTangentVelocity

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] {f g : NeatEmbedding S M}

/-- Joint local tangent velocity extending the prescribed moving trace, with
actual ambient tangency, constructed from the original isotopy. -/
theorem normal_exists_local_tangent_velocity
    (F : SmoothNormalIsotopy S M f g) (p : Time × S) :
    ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
      ∃ Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2,
        ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
          (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) U ∧
        (∀ q, normalTrace F q ∈ U → Y (normalTrace F q) = traceVelocity F q) ∧
        ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0 := by
  let d := chartAt (EuclideanHalfSpace 3) ((F.stage p.1).toFun p.2)
  have hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas _
  obtain ⟨U,hU,hpU,hUd,V,hV,hVagree,hVb⟩ := normal_exists_moving_chart_velocity F p d hd
    (mem_chart_source _ _)
  obtain ⟨Y,hY,hYchart,hYb⟩ := chart_velocity_lift d hd hUd hV
  refine ⟨U,hU,hpU,Y,hY,?_,fun q hq hb => hYb q hq hb (hVb q hq hb)⟩
  intro q hq
  apply (isInvertible_mfderiv_extend
    (IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) hd)
    (hUd hq).2).injective
  have hy := hYchart (normalTrace F q) hq
  rw [hVagree q hq] at hy
  exact hy

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
