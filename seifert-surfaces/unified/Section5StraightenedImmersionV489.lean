import Section5StraightenedRankV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

theorem straightened_strip_differential_injective (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (p : Circle × (Time × ℝ)) :
    Injective (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (straightenedStripPoint a rho FB d hd hd1) p) := by
  let R : longitudeProductStrip → Circle × (ℝ × Circle) := fun q =>
    (rho.symm q.val.1.2,((q.val.2:ℝ)/d,
      longitudeLabelFlow (-FB (q.val.1.2,(q.val.2:ℝ))) q.val.1.1))
  have ht : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
      (fun q : longitudeProductStrip => (q.val.2:ℝ)) :=
    contMDiff_subtypeVal_Icc.comp contMDiff_subtype_val.snd
  have hbase : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡 1) ∞
      (fun q : longitudeProductStrip => q.val.1.2) := contMDiff_subtype_val.fst.snd
  have hR : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
      ((𝓡 1).prod (𝓘(ℝ).prod (𝓡 1))) ∞ R :=
    (rho.symm.contMDiff.comp hbase).prodMk ((ht.div_const d).prodMk
      (longitude_label_flow_smooth.comp
        ((hFB.comp (hbase.prodMk ht)).neg.prodMk contMDiff_subtype_val.fst.fst)))
  have heq : R ∘ straightenedStripPoint a rho FB d hd hd1 =
      fun q : Circle × (Time × ℝ) => (q.1,((q.2.1:ℝ),longitudeLabelFlow q.2.2 a)) := by
    funext q
    change (rho.symm (rho q.1),(d*(q.2.1:ℝ)/d,
      longitudeLabelFlow (-FB (rho q.1,d*(q.2.1:ℝ)))
        (longitudeLabelFlow q.2.2 (longitudeLabelFlow (FB (rho q.1,d*(q.2.1:ℝ))) a)))) = _
    rw [rho.symm_apply_apply,mul_div_cancel_left₀ _ hd.ne',← Flow.map_add,← Flow.map_add]
    congr 2
    congr 1
    ring
  have hi := straightened_reference_rank a p
  rw [← heq,mfderiv_comp p (hR.mdifferentiableAt (by simp))
    ((straightened_strip_smooth a rho FB hFB d hd hd1).mdifferentiableAt (by simp))] at hi
  intro v w hvw
  apply hi
  exact congrArg (mfderiv (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1))
    ((𝓡 1).prod (𝓘(ℝ).prod (𝓡 1))) R (straightenedStripPoint a rho FB d hd hd1 p)) hvw

#print axioms straightened_strip_differential_injective
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
