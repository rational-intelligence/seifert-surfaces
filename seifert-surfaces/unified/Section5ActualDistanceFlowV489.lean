import Section5MetricCompatibleFlowV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Original geometric data produces one actual distance collar and a compatible
ambient longitude flow; the flow preserves the actual distance on this collar. -/
theorem actual_distance_compatible_leaf_flow (G : A7.SourceGeometry E) (J : LongitudeFoliation.{0} E) :
    ∃ U : Set E.Carrier, IsOpen U ∧ (𝓡∂ 3).boundary E.Carrier ⊆ U ∧
    ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r ∧
    ∃ b : ℝ, 0 < b ∧ ∃ V : TopologicalSpace.Opens E.Carrier,
    ∃ C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞,
    ∃ m : ((Circle × Circle) × Time) → E.Carrier,
    ∃ Phi : B1SourceFoliationFlow J,
      ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ m ∧
      (∀ q : longitudeProductStrip, m q.val = (C q : E.Carrier)) ∧
      (∀ p : Circle × Circle, m (p,0) = J.torus p) ∧
      (∀ q, m q ∈ U ∧ r (m q) = b*(q.2 : ℝ)) ∧
      ((V : Set E.Carrier) ⊆ U) ∧ (𝓡∂ 3).boundary E.Carrier ⊆ V ∧
      Phi.labels = longitudeLabelFlow ∧
      (∀ t : ℝ, ∀ q : longitudeProductStrip,
        Phi.ambient t (C q : E.Carrier) = (C (longitudeStripFlow t q) : E.Carrier)) ∧
      (∀ t : ℝ, ∀ x ∈ V, Phi.ambient t x ∈ V ∧ r (Phi.ambient t x) = r x) := by
  obtain ⟨U,hU,hb,r,hr,b,hbpos,V,C,m,hm,hmc,hmb,hmr,hVU,hbV⟩ := actual_metric_longitude_collar G J
  obtain ⟨Phi,hlabels,hflow⟩ := metric_collar_compatible_ambient_flow J V C m hm hmc hmb
  refine ⟨U,hU,hb,r,hr,b,hbpos,V,C,m,Phi,hm,hmc,hmb,hmr,hVU,hbV,hlabels,hflow,?_⟩
  intro t x hx
  let q := C.symm ⟨x,hx⟩
  have hqx : (C q : E.Carrier) = x := congrArg Subtype.val (C.apply_symm_apply ⟨x,hx⟩)
  have hrC (q : longitudeProductStrip) : r (C q : E.Carrier) = b*(q.val.2 : ℝ) :=
    (congrArg r (hmc q)).symm.trans (hmr q.val).2
  have heq : Phi.ambient t x = (C (longitudeStripFlow t q) : E.Carrier) := by
    rw [← hqx]
    exact hflow t q
  refine ⟨heq ▸ (C (longitudeStripFlow t q)).property,?_⟩
  rw [heq,← hqx,hrC,hrC]
  rfl

#print axioms actual_distance_compatible_leaf_flow
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
