import CompactSpatialFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

omit [T2Space M] in
theorem spatialFlowOn_space_smooth
    {Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2}
    {a b : ℝ} {Φ : ℝ → ℝ → M → M} (hΦ : SpatialFlowOn Y a b Φ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ (Φ s t) := by
  have hp : ContMDiff (𝓡∂ 3) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) ∞
      (fun x : M => ((s,t),x)) := contMDiff_const.prodMk contMDiff_id
  exact contMDiffOn_univ.mp (hΦ.1.comp hp.contMDiffOn (fun x _ => ⟨⟨hs,ht⟩,mem_univ x⟩))

omit [T2Space M] in
def spatialFlowDiffeomorph
    {Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2}
    {a b : ℝ} {Φ : ℝ → ℝ → M → M} (hΦ : SpatialFlowOn Y a b Φ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞ :=
  { toEquiv :=
      { toFun := Φ s t
        invFun := Φ t s
        left_inv := hΦ.2.2.1 s hs t ht
        right_inv := hΦ.2.2.1 t ht s hs }
    contMDiff_toFun := spatialFlowOn_space_smooth hΦ hs ht
    contMDiff_invFun := spatialFlowOn_space_smooth hΦ ht hs }

omit [T2Space M] in
theorem spatialFlowDiffeomorph_apply
    {Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2}
    {a b : ℝ} {Φ : ℝ → ℝ → M → M} (hΦ : SpatialFlowOn Y a b Φ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : M) :
    spatialFlowDiffeomorph hΦ hs ht x = Φ s t x := rfl

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
