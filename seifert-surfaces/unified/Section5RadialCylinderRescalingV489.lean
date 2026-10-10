import Section5StraightenedTimeGraphsV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

/-- Real distance is rescaled to the actual interval coordinate. -/
def radialCylinderRescaling (R : ℝ) (p : Circle × (ℝ × ℝ)) : Circle × (Time × ℝ) :=
  (p.1,projIcc 0 1 (by norm_num) (p.2.1/R),p.2.2)

theorem half_cylinder_unique {R eta : ℝ} (hR : 0 < R) :
    UniqueMDiffOn ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) (halfCylinder R eta) := by
  have h := (uniqueMDiffOn_univ (I:=𝓡 1) (M:=Circle)).prod
    ((uniqueDiffOn_Icc hR).uniqueMDiffOn.prod
      ((isOpen_lt (continuous_abs : Continuous (abs : ℝ → ℝ)) (continuous_const (y:=eta))).uniqueMDiffOn (I:=𝓘(ℝ))))
  convert h using 1
  ext p
  simp only [halfCylinder,mem_setOf_eq,mem_prod,mem_univ,true_and]

theorem radial_cylinder_rescaling_smooth {R eta : ℝ} (hR : 0 < R) :
    ContMDiffOn ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ)))
      ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) ∞ (radialCylinderRescaling R) (halfCylinder R eta) := by
  apply contMDiff_fst.contMDiffOn.prodMk
  apply (contMDiffOn_projIcc.comp ((contMDiff_snd.fst.div_const R).contMDiffOn) ?_).prodMk
    contMDiff_snd.snd.contMDiffOn
  intro p hp
  exact ⟨div_nonneg hp.1.1 hR.le,(div_le_one hR).mpr hp.1.2⟩

theorem radial_cylinder_rescaling_value {R eta : ℝ} (hR : 0 < R)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ halfCylinder R eta) :
    ((radialCylinderRescaling R p).2.1:ℝ) = p.2.1/R := by
  exact congrArg Subtype.val (projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    ⟨div_nonneg hp.1.1 hR.le,(div_le_one hR).mpr hp.1.2⟩)

/-- The real-distance rescaling has full rank including both endpoints. -/
theorem radial_cylinder_rescaling_differential_injective {R eta : ℝ} (hR : 0 < R)
    (p : Circle × (ℝ × ℝ)) (hp : p ∈ halfCylinder R eta) :
    Injective (mfderivWithin ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ)))
      ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) (radialCylinderRescaling R) (halfCylinder R eta) p) := by
  let L : Circle × (Time × ℝ) → Circle × (ℝ × ℝ) := fun q => (q.1,R*(q.2.1:ℝ),q.2.2)
  have hL : ContMDiff ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
      ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) ∞ L :=
    contMDiff_fst.prodMk ((contMDiff_const.mul
      (contMDiff_subtypeVal_Icc.comp contMDiff_snd.fst)).prodMk contMDiff_snd.snd)
  have heq : EqOn (L ∘ radialCylinderRescaling R) id (halfCylinder R eta) := by
    intro x hx
    change (x.1,R*((radialCylinderRescaling R x).2.1:ℝ),x.2.2) = x
    rw [radial_cylinder_rescaling_value hR hx,mul_div_cancel₀ _ hR.ne']
  have hder := mfderivWithin_congr_of_mem
    (I:=((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ)))) (I':=((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ)))) heq hp
  rw [mfderiv_comp_mfderivWithin p (hL.mdifferentiableAt (by simp))
    ((radial_cylinder_rescaling_smooth hR p hp).mdifferentiableWithinAt (by simp))
    (half_cylinder_unique hR p hp),mfderivWithin_id (half_cylinder_unique hR p hp)] at hder
  intro v w hvw
  have hh := congrArg (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
    ((𝓡 1).prod (𝓘(ℝ).prod 𝓘(ℝ))) L (radialCylinderRescaling R p)) hvw
  change ((mfderiv _ _ L _).comp (mfderivWithin _ _ _ _ _)) v =
    ((mfderiv _ _ L _).comp (mfderivWithin _ _ _ _ _)) w at hh
  rw [hder] at hh
  exact hh

#print axioms half_cylinder_unique
#print axioms radial_cylinder_rescaling_smooth
#print axioms radial_cylinder_rescaling_value
#print axioms radial_cylinder_rescaling_differential_injective
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
