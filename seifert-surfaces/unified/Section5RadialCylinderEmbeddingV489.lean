import Section5RadialCylinderRescalingV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

def radialCylinderClosedRescaling (R : ℝ) (p : halfCylinder R 1) :
    Circle × (Time × Icc (-1:ℝ) 1) :=
  (p.val.1,projIcc 0 1 (by norm_num) (p.val.2.1/R),
    ⟨p.val.2.2,abs_le.mp p.property.2.le⟩)

theorem radial_cylinder_closed_rescaling_embedding {R : ℝ} (hR : 0 < R) :
    IsEmbedding (radialCylinderClosedRescaling R) := by
  let L : Circle × (Time × Icc (-1:ℝ) 1) → Circle × (ℝ × ℝ) :=
    fun p => (p.1,R*(p.2.1:ℝ),(p.2.2:ℝ))
  have hc : Continuous (radialCylinderClosedRescaling R) := by
    apply continuous_subtype_val.fst.prodMk
    apply (continuous_projIcc.comp
      (continuous_subtype_val.snd.fst.div_const R)).prodMk
    exact continuous_subtype_val.snd.snd.subtype_mk _
  have hL : Continuous L := continuous_fst.prodMk
    ((continuous_const.mul (continuous_subtype_val.comp continuous_snd.fst)).prodMk
      (continuous_subtype_val.comp continuous_snd.snd))
  have he : L ∘ radialCylinderClosedRescaling R = Subtype.val := by
    funext p
    change (p.val.1,R*((radialCylinderRescaling R p.val).2.1:ℝ),p.val.2.2) = p.val
    rw [radial_cylinder_rescaling_value hR p.property,mul_div_cancel₀ _ hR.ne']
  exact IsEmbedding.of_comp hc hL (he.symm ▸ IsEmbedding.subtypeVal)

#print axioms radial_cylinder_closed_rescaling_embedding
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
