import Section5BoundaryChartCoordinateV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Topology Function Filter Manifold
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
open SeifertSurfaces.Foundations
universe u v
variable {S : Type u} [TopologicalSpace S] [ChartedSpace (Euc 1) S]
  [IsManifold (𝓡 1) ∞ S]
  {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem boundary_curve_isImmersion {f : S → M}
    (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f)
    (hboundary : ∀ x, f x ∈ (𝓡∂ 3).boundary M)
    (hinj : ∀ x, Injective (mfderiv (𝓡 1) (𝓡∂ 3) f x)) :
    IsImmersion (𝓡 1) (𝓡∂ 3) ∞ f := by
  refine ⟨Euc 2,inferInstance,inferInstance,?_⟩
  intro x
  let c := chartAt (Euc 1) x
  let d := chartAt (EuclideanHalfSpace 3) (f x)
  let a := extChartAt (𝓡 1) x x
  let g : Euc 1 → Euc 3 :=
    (extChartAt (𝓡∂ 3) (f x)) ∘ f ∘ (extChartAt (𝓡 1) x).symm
  let W := f ⁻¹' d.source
  let U := c.target ∩ c.symm ⁻¹' W
  have hW : IsOpen W := d.open_source.preimage hf.continuous
  have hU : IsOpen U := c.isOpen_inter_preimage_symm hW
  have ha : a ∈ U := by
    refine ⟨c.map_source (mem_chart_source _ _),?_⟩
    change f (c.symm (c x)) ∈ d.source
    rw [c.left_inv (mem_chart_source _ _)]
    exact mem_chart_source _ _
  have hg : ContDiffOn ℝ ∞ g U := by
    have hc : ContMDiffOn (𝓡 1) (𝓡 1) ∞ c.symm U :=
      (contMDiffOn_chart_symm (I := 𝓡 1) (n := ∞) (x := x)).mono inter_subset_left
    have hd : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ,Euc 3) ∞
        (extChartAt (𝓡∂ 3) (f x)) d.source := contMDiffOn_extChartAt
    exact (hd.comp (hf.comp_contMDiffOn hc) (fun _ h => h.2)).contDiffOn
  have hzero : ∀ z ∈ U, g z 0 = 0 := by
    intro z hz
    exact (chart_boundary_coordinate_iff (f x) (f (c.symm z)) hz.2).mp
      (hboundary (c.symm z))
  let L : Euc 1 →L[ℝ] Euc 3 :=
    (tangentSpaceCastModel (𝓡∂ 3) (f x)).toContinuousLinearMap.comp
      ((mfderiv (𝓡 1) (𝓡∂ 3) f x).comp
        (tangentSpaceCastModel (𝓡 1) x).symm.toContinuousLinearMap)
  have hL : Injective L :=
    (tangentSpaceCastModel (𝓡∂ 3) (f x)).injective.comp
      ((hinj x).comp (tangentSpaceCastModel (𝓡 1) x).symm.injective)
  have hd : HasFDerivAt g L a := by
    have hd := (hf.mdifferentiableAt (by simp) (x := x)).hasMFDerivAt.2
    rw [(𝓡 1).range_eq_univ,hasFDerivWithinAt_univ] at hd
    exact hd
  obtain ⟨β,hβa,hβ,hβi,himage,hgraph⟩ :=
    boundary_curve_local_straightening hU hg hzero ha hd hL
  exact boundary_curve_immersion_of_straightening hf x g (EventuallyEq.rfl)
    β hβ hβi himage hgraph

theorem boundary_curve_isSmoothEmbedding {f : S → M}
    (hf : ContMDiff (𝓡 1) (𝓡∂ 3) ∞ f)
    (hboundary : ∀ x, f x ∈ (𝓡∂ 3).boundary M)
    (hinj : ∀ x, Injective (mfderiv (𝓡 1) (𝓡∂ 3) f x))
    (hembed : IsEmbedding f) :
    IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ f :=
  ⟨boundary_curve_isImmersion hf hboundary hinj,hembed⟩

#print axioms boundary_curve_isSmoothEmbedding
end SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
