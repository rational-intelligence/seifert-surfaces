import Section5CommonLeafRegularParameterV488
import Section5CommonLeafLabelFlowV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

def longitudeBoundaryHomeomorph (J : LongitudeFoliation.{0} E) :
    (Circle × Circle) ≃ₜ ((𝓡∂ 3).boundary E.Carrier) := by
  have he : IsEmbedding J.boundaryLift :=
    IsEmbedding.subtypeVal.of_comp_iff.mp J.smoothEmbedding.isEmbedding
  apply he.toHomeomorphOfSurjective
  intro p
  have hp : (p : E.Carrier) ∈ range J.torus := J.covers_boundary.symm ▸ p.property
  obtain ⟨q,hq⟩ := hp
  exact ⟨q,Subtype.ext hq⟩

theorem longitude_boundary_homeomorph_apply (J : LongitudeFoliation.{0} E)
    (p : Circle × Circle) : longitudeBoundaryHomeomorph J p = J.boundaryLift p := rfl

def longitudeTorusFlow : Flow ℝ (Circle × Circle) where
  toFun t p := (longitudeLabelFlow t p.1,p.2)
  cont' := (longitudeLabelFlow.continuous continuous_fst continuous_snd.fst).prodMk
    continuous_snd.snd
  map_add' t u p := by simp only [Flow.map_add]
  map_zero' p := by simp only [Flow.map_zero_apply]

def longitudeBoundaryFlow (J : LongitudeFoliation.{0} E) :
    Flow ℝ ((𝓡∂ 3).boundary E.Carrier) where
  toFun t p := longitudeBoundaryHomeomorph J
    (longitudeTorusFlow t ((longitudeBoundaryHomeomorph J).symm p))
  cont' := (longitudeBoundaryHomeomorph J).continuous.comp
    (longitudeTorusFlow.continuous continuous_fst
      ((longitudeBoundaryHomeomorph J).symm.continuous.comp continuous_snd))
  map_add' t u p := by simp only [Homeomorph.symm_apply_apply,Flow.map_add]
  map_zero' p := by simp only [Flow.map_zero_apply,Homeomorph.apply_symm_apply]

theorem longitude_boundary_flow_parameter (J : LongitudeFoliation.{0} E)
    (t : ℝ) (p : Circle × Circle) :
    longitudeBoundaryFlow J t (J.boundaryLift p) =
      J.boundaryLift (longitudeLabelFlow t p.1,p.2) := by
  change longitudeBoundaryHomeomorph J
    (longitudeTorusFlow t ((longitudeBoundaryHomeomorph J).symm
      (longitudeBoundaryHomeomorph J p))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem longitude_boundary_flow_parameter_smooth (J : LongitudeFoliation.{0} E) :
    ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓡∂ 3) ∞
      (fun p : ℝ × (Circle × Circle) =>
        (longitudeBoundaryFlow J p.1 (J.boundaryLift p.2) : E.Carrier)) := by
  have heq : (fun p : ℝ × (Circle × Circle) =>
        (longitudeBoundaryFlow J p.1 (J.boundaryLift p.2) : E.Carrier)) =
      (fun p : ℝ × (Circle × Circle) => J.torus (longitudeLabelFlow p.1 p.2.1,p.2.2)) := by
    funext p
    rw [longitude_boundary_flow_parameter]
    rfl
  rw [heq]
  exact J.smoothEmbedding.contMDiff.comp
    ((longitude_label_flow_smooth.comp
      (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
        (contMDiff_snd.comp contMDiff_snd))

theorem longitude_boundary_flow_leaf_image (J : LongitudeFoliation.{0} E)
    (t : ℝ) (a : Circle) :
    longitudeBoundaryFlow J t '' {p : (𝓡∂ 3).boundary E.Carrier | (p : E.Carrier) ∈ J.leaf a} =
      {p : (𝓡∂ 3).boundary E.Carrier | (p : E.Carrier) ∈ J.leaf (longitudeLabelFlow t a)} := by
  ext p
  constructor
  · rintro ⟨q,⟨z,hz⟩,rfl⟩
    have hq : q = J.boundaryLift (a,z) := Subtype.ext hz.symm
    rw [hq,longitude_boundary_flow_parameter]
    exact ⟨z,rfl⟩
  · rintro ⟨z,hz⟩
    refine ⟨J.boundaryLift (a,z), ⟨z,rfl⟩, ?_⟩
    rw [longitude_boundary_flow_parameter]
    exact Subtype.ext hz

#print axioms longitude_boundary_flow_parameter_smooth
#print axioms longitude_boundary_flow_leaf_image
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
