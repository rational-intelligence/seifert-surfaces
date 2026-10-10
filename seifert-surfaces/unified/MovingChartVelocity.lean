import MovingInteriorRetraction

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] {f g : NeatEmbedding S M}

/-- At every point of the actual moving trace there is a jointly smooth local
retraction, preserving boundary points. Both source strata are constructed. -/
theorem normal_exists_moving_retraction (F : SmoothNormalIsotopy S M f g)
    (p : Time × S) :
    ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
      ∃ r : Time × M → S,
        ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 2) ∞ r U ∧
        (∀ q, normalTrace F q ∈ U → r (normalTrace F q) = q.2) ∧
        ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → r q ∈ S.boundary := by
  by_cases hp : p.2 ∈ S.boundary
  · exact normal_exists_moving_boundary_retraction F p hp
  · exact normal_exists_moving_interior_retraction F p hp

/-- The prescribed velocity of the moving family extends smoothly in any
chosen ambient chart and has zero normal component on its boundary. -/
theorem normal_exists_moving_chart_velocity
    (F : SmoothNormalIsotopy S M f g) (p : Time × S)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (hfx : (F.stage p.1).toFun p.2 ∈ d.source) :
    ∃ U : Set (Time × M), IsOpen U ∧ normalTrace F p ∈ U ∧
      U ⊆ univ ×ˢ d.source ∧ ∃ V : Time × M → Euc 3,
        ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞ V U ∧
        (∀ q, normalTrace F q ∈ U → V (normalTrace F q) = traceChartVelocity F d q) ∧
        ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → V q 0 = 0 := by
  obtain ⟨U₀,hU₀,hpU₀,r,hr,hfix,hboundary⟩ := normal_exists_moving_retraction F p
  let a : Time × M → M := fun q => (F.stage q.1).toFun (r q)
  have ha : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ a U₀ :=
    F.smooth_family.comp_contMDiffOn (contMDiffOn_fst.prodMk hr)
  let U : Set (Time × M) := (U₀ ∩ a ⁻¹' d.source) ∩ (univ ×ˢ d.source)
  have hU : IsOpen U := (ha.continuousOn.isOpen_inter_preimage hU₀ d.open_source).inter
    (isOpen_univ.prod d.open_source)
  have hpU : normalTrace F p ∈ U := by
    refine ⟨⟨hpU₀,?_⟩,mem_univ _,hfx⟩
    change (F.stage p.1).toFun (r (normalTrace F p)) ∈ d.source
    rw [hfix p hpU₀]
    exact hfx
  let V : Time × M → Euc 3 := fun q => traceChartVelocity F d (q.1,r q)
  have hV : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞ V U :=
    (traceChartVelocity_contMDiffOn F d hd).comp
      (contMDiffOn_fst.prodMk (hr.mono (inter_subset_left.trans inter_subset_left)))
      (fun q hq => hq.1.2)
  refine ⟨U,hU,hpU,inter_subset_right,V,hV,?_,?_⟩
  · intro q hq
    change traceChartVelocity F d (q.1,r (normalTrace F q)) = _
    rw [hfix q hq.1.1]
  · intro q hq hqb
    exact traceChartVelocity_boundary F d hd (q.1,r q) hq.1.2
      (hboundary q hq.1.1 hqb)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
