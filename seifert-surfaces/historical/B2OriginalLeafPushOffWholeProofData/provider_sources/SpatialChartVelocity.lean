import CompactSpatialVelocity
import ChartForwardBoundaryDifferential

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

def spatialChartVelocity
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3)) (q : Time × M) : Euc 3 :=
  mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) q.2 (Y q)

theorem spatialChartVelocity_contMDiffOn
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M) :
    ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞
      (spatialChartVelocity Y d) (univ ×ˢ d.source) := by
  have htm := (d.contMDiffOn_extend hd).contMDiffOn_tangentMapWithin
    (m := (⊤ : ℕ∞)) (by simp) d.open_source.uniqueMDiffOn
  have hcomp : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3).tangent ∞
      (fun q => tangentMapWithin (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) d.source
        (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) (univ ×ˢ d.source) :=
    htm.comp hY.contMDiffOn (fun q hq => hq.2)
  have hread := (contMDiff_snd_tangentBundle_modelSpace (Euc 3) 𝓘(ℝ,Euc 3)).comp_contMDiffOn hcomp
  apply hread.congr
  intro q hq
  symm
  change mfderivWithin (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) d.source
    q.2 (Y q) = spatialChartVelocity Y d q
  rw [mfderivWithin_of_mem_nhds (d.open_source.mem_nhds hq.2)]
  rfl

theorem spatialChartVelocity_boundary
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (q : Time × M) (hq : q.2 ∈ d.source) (hqb : q.2 ∈ (𝓡∂ 3).boundary M) :
    spatialChartVelocity Y d q 0 = 0 :=
  chart_forward_boundary_differential d hd hq hqb (Y q) (hYb q hqb)

theorem spatialChartVelocity_model_contMDiffOn
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M) :
    ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞
      (fun q : Time × EuclideanHalfSpace 3 => spatialChartVelocity Y d (q.1,d.symm q.2))
      (univ ×ˢ d.target) := by
  exact (spatialChartVelocity_contMDiffOn Y hY d hd).comp
    (contMDiffOn_fst.prodMk
      ((contMDiffOn_symm_of_mem_maximalAtlas hd).comp contMDiffOn_snd (fun q hq => hq.2)))
    (fun q hq => ⟨mem_univ _,d.map_target hq.2⟩)

theorem spatialChartVelocity_model_boundary
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (t : Time) (z : EuclideanHalfSpace 3) (hz : z ∈ d.target) (hzb : (𝓡∂ 3) z 0 = 0) :
    spatialChartVelocity Y d (t,d.symm z) 0 = 0 := by
  apply spatialChartVelocity_boundary Y hYb d hd _ (d.map_target hz)
  apply (chart_boundary_normal_iff d hd (d.map_target hz)).mpr
  change (𝓡∂ 3) (d (d.symm z)) 0 = 0
  rw [d.right_inv hz]
  exact hzb

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
