import Section5CommonRealHeightsV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem same_embedded_circle_diffeomorph (f g : Circle → E.Carrier)
    (hf : IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ f)
    (hg : IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ g)
    (he : range f = range g) :
    ∃ rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞, ∀ z, g (rho z) = f z := by
  classical
  have hfg (z) : ∃ w, g w = f z := by
    have hz : f z ∈ range g := by rw [← he]; exact mem_range_self z
    exact hz
  have hgf (z) : ∃ w, f w = g z := by
    have hz : g z ∈ range f := by rw [he]; exact mem_range_self z
    exact hz
  choose rho hrho using hfg
  choose sigma hsigma using hgf
  have hgr : g ∘ rho = f := funext hrho
  have hfs : f ∘ sigma = g := funext hsigma
  have hrc : Continuous rho := hg.isEmbedding.continuous_iff.mpr (hgr ▸ hf.contMDiff.continuous)
  have hsc : Continuous sigma := hf.isEmbedding.continuous_iff.mpr (hfs ▸ hg.contMDiff.continuous)
  have hrs : ContMDiff (𝓡 1) (𝓡 1) ∞ rho :=
    (ContMDiff.iff_comp_isImmersion hg.isImmersion).mpr ⟨hrc,hgr ▸ hf.contMDiff⟩
  have hss : ContMDiff (𝓡 1) (𝓡 1) ∞ sigma :=
    (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr ⟨hsc,hfs ▸ hg.contMDiff⟩
  have hleft : LeftInverse sigma rho := by
    intro z
    exact hf.isEmbedding.injective ((hsigma (rho z)).trans (hrho z))
  have hright : RightInverse sigma rho := by
    intro z
    exact hg.isEmbedding.injective ((hrho (sigma z)).trans (hsigma z))
  exact ⟨⟨⟨rho,sigma,hleft,hright⟩,hrs,hss⟩,hrho⟩

/-- Actual unit-arclength parametrization differs from the original longitude
coordinate by one smooth circle diffeomorphism. -/
theorem unit_leaf_parameter_diffeomorph (g : SmoothMetric E.Carrier)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ∃ rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞,
      ∀ z, J.torus (a,rho z) = longitudeUnitParameter g J a z := by
  have hh := longitude_leaf_regular J a
  have hgam : IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) ∞ (fun z => J.torus (a,z)) :=
    SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488.boundary_curve_isSmoothEmbedding
      hh.1 (fun z => J.torus_lands_boundary (a,z)) hh.2.2 hh.2.1
  exact same_embedded_circle_diffeomorph (longitudeUnitParameter g J a) (fun z => J.torus (a,z))
    (longitude_unit_parameter_smoothEmbedding g J a) hgam (longitude_unit_parameter_image g J a)

#print axioms same_embedded_circle_diffeomorph
#print axioms unit_leaf_parameter_diffeomorph
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
