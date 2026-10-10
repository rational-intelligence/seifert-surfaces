import Section5UnitLeafDiffeomorphV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

/-- The exact strip coordinates which take B to the zero graph. -/
def straightenedStripPoint (a : Circle) (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (d : ℝ) (hd : 0 < d) (hd1 : d < 1)
    (p : Circle × (Time × ℝ)) : longitudeProductStrip :=
  ⟨((longitudeLabelFlow p.2.2 (longitudeLabelFlow (FB (rho p.1,d*(p.2.1:ℝ))) a),rho p.1),
    ⟨d*(p.2.1:ℝ),mul_nonneg hd.le p.2.1.property.1,
      (mul_le_mul_of_nonneg_left p.2.1.property.2 hd.le).trans (by simpa using hd1.le)⟩),
    (mul_le_mul_of_nonneg_left p.2.1.property.2 hd.le).trans_lt (by simpa using hd1)⟩

theorem straightened_strip_smooth (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    ContMDiff ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
      (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) ∞ (straightenedStripPoint a rho FB d hd hd1) := by
  apply (ContMDiff.subtypeVal_comp_iff longitudeProductStrip _).mp
  have hs : ContMDiff ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) (𝓡 1) ∞
      (fun p : Circle × (Time × ℝ) => rho p.1) := rho.contMDiff.comp contMDiff_fst
  have ht : ContMDiff ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) 𝓘(ℝ) ∞
      (fun p : Circle × (Time × ℝ) => d*(p.2.1:ℝ)) :=
    contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd.fst)
  have hb := longitude_label_flow_smooth.comp ((hFB.comp (hs.prodMk ht)).prodMk (contMDiff_const (c:=a)))
  apply ((longitude_label_flow_smooth.comp (contMDiff_snd.snd.prodMk hb)).prodMk hs).prodMk
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  exact ⟨ht.continuous.subtype_mk _,ht⟩

theorem straightened_strip_injective (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    InjOn (straightenedStripPoint a rho FB d hd hd1)
      {p : Circle × (Time × ℝ) | |p.2.2| ≤ 1} := by
  intro p hp q hq he
  have hcoord := congrArg Subtype.val he
  have hs : p.1 = q.1 := rho.injective (congrArg (fun x : (Circle × Circle) × Time => x.1.2) hcoord)
  have ht : p.2.1 = q.2.1 := by
    apply Subtype.ext
    exact mul_left_cancel₀ hd.ne' (congrArg (fun x : (Circle × Circle) × Time => (x.2:ℝ)) hcoord)
  have hy : p.2.2 = q.2.2 := by
    have hh := congrArg (fun x : (Circle × Circle) × Time => x.1.1) hcoord
    change Circle.exp p.2.2 * _ = Circle.exp q.2.2 * _ at hh
    rw [hs,ht] at hh
    have hexp : Circle.exp p.2.2 = Circle.exp q.2.2 := mul_right_cancel hh
    exact Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three])
      (abs_le.mp hp) (abs_le.mp hq) hexp
  exact Prod.ext hs (Prod.ext ht hy)

/-- A compact closed slab gives the topological embedding needed for every
smaller open transverse width. -/
theorem straightened_strip_closed_embedding (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    IsEmbedding (fun p : Circle × (Time × Icc (-1:ℝ) 1) =>
      straightenedStripPoint a rho FB d hd hd1 (p.1,p.2.1,p.2.2.val)) := by
  have hc : Continuous (fun p : Circle × (Time × Icc (-1:ℝ) 1) =>
      straightenedStripPoint a rho FB d hd hd1 (p.1,p.2.1,p.2.2.val)) :=
    (straightened_strip_smooth a rho FB hFB d hd hd1).continuous.comp
      (continuous_fst.prodMk (continuous_snd.fst.prodMk (continuous_subtype_val.comp continuous_snd.snd)))
  apply (hc.isClosedEmbedding ?_).isEmbedding
  intro p q he
  have hi := straightened_strip_injective a rho FB d hd hd1
    (abs_le.mpr p.2.2.property) (abs_le.mpr q.2.2.property) he
  apply Prod.ext
  · exact congrArg (fun x : Circle × (Time × ℝ) => x.1) hi
  · apply Prod.ext
    · exact congrArg (fun x : Circle × (Time × ℝ) => x.2.1) hi
    · exact Subtype.ext (congrArg (fun x : Circle × (Time × ℝ) => x.2.2) hi)

#print axioms straightened_strip_smooth
#print axioms straightened_strip_injective
#print axioms straightened_strip_closed_embedding
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
