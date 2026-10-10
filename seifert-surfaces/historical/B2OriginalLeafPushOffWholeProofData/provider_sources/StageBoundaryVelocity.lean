import TraceChartVelocity

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

/-- At each boundary point of each original stage, the actual prescribed time
velocity has a smooth local coordinate extension tangent to the ambient
boundary. The local retraction is constructed from the original neat data. -/
theorem normal_stage_exists_boundary_velocity_extension
    (F : SmoothNormalIsotopy S M f g) (t : Time) (x : S) (hx : x ∈ S.boundary)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (hfx : (F.stage t).toFun x ∈ d.source) :
    ∃ U : Set M, IsOpen U ∧ (F.stage t).toFun x ∈ U ∧ U ⊆ d.source ∧
      ∃ V : M → Euc 3, ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ V U ∧
        (∀ y, (F.stage t).toFun y ∈ U → V ((F.stage t).toFun y) =
          traceChartVelocity F d (t,y)) ∧
        ∀ y ∈ U, y ∈ (𝓡∂ 3).boundary M → V y 0 = 0 := by
  obtain ⟨U₀,hU₀,hxU₀,r,hr,hfix,hboundary⟩ :=
    neat_exists_boundary_local_retraction (F.stage t) x hx
  let a : M → M := fun y => (F.stage t).toFun (r y)
  have ha : ContinuousOn a U₀ :=
    (F.stage t).smoothEmbedding.isEmbedding.continuous.comp_continuousOn hr.continuousOn
  let U : Set M := (U₀ ∩ a ⁻¹' d.source) ∩ d.source
  have hU : IsOpen U := (ha.isOpen_inter_preimage hU₀ d.open_source).inter d.open_source
  have hxU : (F.stage t).toFun x ∈ U := by
    refine ⟨⟨hxU₀,?_⟩,hfx⟩
    change (F.stage t).toFun (r ((F.stage t).toFun x)) ∈ d.source
    rw [hfix x hxU₀]
    exact hfx
  let V : M → Euc 3 := fun y => traceChartVelocity F d (t,r y)
  have hV : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, Euc 3) ∞ V U :=
    (traceChartVelocity_contMDiffOn F d hd).comp
      (contMDiffOn_const.prodMk (hr.mono (inter_subset_left.trans inter_subset_left)))
      (fun y hy => hy.1.2)
  refine ⟨U,hU,hxU,inter_subset_right,V,hV,?_,?_⟩
  · intro y hy
    change traceChartVelocity F d (t,r ((F.stage t).toFun y)) = _
    rw [hfix y hy.1.1]
  · intro y hy hyb
    exact traceChartVelocity_boundary F d hd (t,r y) hy.1.2
      (hboundary y hy.1.1 hyb)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
