import SpatialFlowDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

/-- Integrating one short interval gives an ambient isotopy whose endpoint is
the actual time-dependent flow from `s` to `t`. -/
theorem spatial_flow_ambient_segment
    {Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2}
    {a b : ℝ} {Φ : ℝ → ℝ → M → M} (hΦ : SpatialFlowOn Y a b Φ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ∃ H : SmoothAmbientIsotopy M, ∀ x, H.stage 1 x = Φ s t x := by
  let l : Time → ℝ := fun u => (1 - (u : ℝ)) * s + (u : ℝ) * t
  have hl : ContMDiff (𝓡∂ 1) 𝓘(ℝ,ℝ) ∞ l :=
    ((contMDiff_const.sub contMDiff_subtypeVal_Icc).mul contMDiff_const).add
      (contMDiff_subtypeVal_Icc.mul contMDiff_const)
  have hlC (u : Time) : l u ∈ Icc a b := by
    dsimp only [l]
    constructor
    · nlinarith [u.property.1,u.property.2,hs.1,ht.1,
        mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hs.1),
        mul_nonneg u.property.1 (sub_nonneg.mpr ht.1)]
    · nlinarith [u.property.1,u.property.2,hs.2,ht.2,
        mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr hs.2),
        mul_nonneg u.property.1 (sub_nonneg.mpr ht.2)]
  have hl0 : l 0 = s := by dsimp [l]; norm_num
  have hl1 : l 1 = t := by dsimp [l]; norm_num
  have hp : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3))
      ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) ∞
      (fun q : Time × M => ((s,l q.1),q.2)) :=
    (contMDiff_const.prodMk (hl.comp contMDiff_fst)).prodMk contMDiff_snd
  let H : SmoothAmbientIsotopy M :=
    { stage := fun u => spatialFlowDiffeomorph hΦ hs (hlC u)
      smooth_family := hΦ.1.comp_contMDiff hp (fun q => ⟨⟨hs,hlC q.1⟩,mem_univ q.2⟩)
      initial := by
        intro x
        change Φ s (l 0) x = x
        rw [hl0]
        exact hΦ.2.1 s hs x
      boundary_setwise := fun u => (spatialFlowDiffeomorph hΦ hs (hlC u)).image_boundary (by simp) }
  refine ⟨H,?_⟩
  intro x
  change Φ s (l 1) x = Φ s t x
  rw [hl1]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
