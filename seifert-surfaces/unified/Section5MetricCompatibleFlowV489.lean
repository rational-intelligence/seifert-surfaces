import Section5MetricLongitudeCollarV489
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

/-- Extend the longitude flow through this specific collar. The returned
ambient flow is exactly conjugate to the product flow in the supplied collar. -/
theorem metric_collar_compatible_ambient_flow (J : LongitudeFoliation.{0} E)
    (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (m : ((Circle × Circle) × Time) → E.Carrier)
    (hm : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ m)
    (hmc : ∀ q : longitudeProductStrip, m q.val = (C q : E.Carrier))
    (hmb : ∀ p : Circle × Circle, m (p,0) = J.torus p) :
    ∃ Phi : B1SourceFoliationFlow J,
      Phi.labels = longitudeLabelFlow ∧
      ∀ t : ℝ, ∀ q : longitudeProductStrip,
        Phi.ambient t (C q : E.Carrier) = (C (longitudeStripFlow t q) : E.Carrier) := by
  let A : Set E.Carrier := m '' {q : (Circle × Circle) × Time | (q.2 : ℝ) ≤ 1/2}
  have hA : IsCompact A :=
    (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const).isCompact.image hm.continuous
  have hAV : A ⊆ V := by
    rintro x ⟨p,hp,rfl⟩
    let q : longitudeProductStrip := ⟨p,by
      change (p.2 : ℝ) < 1
      change (p.2 : ℝ) ≤ 1/2 at hp
      linarith⟩
    rw [hmc q]
    exact (C q).property
  let F : Flow ℝ V := conjugateFlow C.toHomeomorph longitudeStripFlow
  have hF : ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun p : ℝ × V => F p.1 p.2) :=
    conjugate_flow_smooth C longitudeStripFlow longitude_strip_flow_smooth
  have hcoord (t : ℝ) (q : longitudeProductStrip) : F t (C q) = C (longitudeStripFlow t q) :=
    conjugate_flow_coordinates C.toHomeomorph longitudeStripFlow t q
  have hfixed (t : ℝ) (x : V) (hx : (x : E.Carrier) ∉ A) : F t x = x := by
    let q := C.symm x
    have hq : 1/2 ≤ (q.val.2 : ℝ) := by
      by_contra h
      have hlt : (q.val.2 : ℝ) < 1/2 := lt_of_not_ge h
      apply hx
      refine ⟨q.val,hlt.le,?_⟩
      rw [hmc q]
      exact congrArg Subtype.val (C.apply_symm_apply x)
    change C (longitudeStripFlow t q) = x
    rw [longitude_strip_flow_fixed t q hq]
    exact C.apply_symm_apply x
  let ambient : Flow ℝ E.Carrier := extendOpenFlow V F hF hA.isClosed hAV hfixed
  have hambient : ContMDiff (𝓘(ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : ℝ × E.Carrier => ambient p.1 p.2) :=
    extend_open_flow_smooth V F hF hA.isClosed hAV hfixed
  have hformula (t : ℝ) (q : longitudeProductStrip) :
      ambient t (C q : E.Carrier) = (C (longitudeStripFlow t q) : E.Carrier) := by
    change extendOpenFlowMap V F t (C q : E.Carrier) = _
    rw [extend_open_flow_map_inside,hcoord]
  have hboundary (t : ℝ) (p : Circle × Circle) :
      ambient t (J.torus p) = J.torus (longitudeLabelFlow t p.1,p.2) := by
    have hcb (p : Circle × Circle) : (C (longitudeBoundarySection p) : E.Carrier) = J.torus p :=
      (hmc (longitudeBoundarySection p)).symm.trans (hmb p)
    rw [← hcb p,hformula,longitude_strip_flow_boundary,hcb]
  have hleaf (t : ℝ) (a : Circle) : ambient t '' J.leaf a = J.leaf (longitudeLabelFlow t a) := by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨z,(hboundary t (a,z)).symm⟩
    · rintro ⟨z,rfl⟩
      exact ⟨J.torus (a,z),⟨z,rfl⟩,hboundary t (a,z)⟩
  exact ⟨{
    ambient := ambient
    labels := longitudeLabelFlow
    ambient_smooth := hambient
    labels_smooth := longitude_label_flow_smooth
    leaf_image := hleaf
    labels_transverse := longitude_label_flow_transverse },rfl,hformula⟩

#print axioms metric_collar_compatible_ambient_flow
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
