import Section5StraightenedImmersionV489
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

def straightenedTimeCollar (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (p : Circle × (Time × ℝ)) : E.Carrier :=
  C (straightenedStripPoint a rho FB d hd hd1 p)

theorem straightened_time_collar_smooth (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞) :
    ContMDiff ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) (𝓡∂ 3) ∞
      (straightenedTimeCollar a rho FB d hd hd1 V C) :=
  contMDiff_subtype_val.comp (C.contMDiff.comp (straightened_strip_smooth a rho FB hFB d hd hd1))

theorem straightened_time_collar_differential_injective (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (p : Circle × (Time × ℝ)) :
    Injective (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) (𝓡∂ 3)
      (straightenedTimeCollar a rho FB d hd hd1 V C) p) := by
  let q := straightenedStripPoint a rho FB d hd hd1
  have hq := straightened_strip_smooth a rho FB hFB d hd hd1
  have hinc := (Manifold.IsSmoothEmbedding.of_opens (I:=𝓡∂ 3) (n:=∞) V).isImmersion.mfderiv_injective (by simp) (C (q p))
  have hC : Injective (mfderiv (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) C (q p)) := by
    exact (C.mfderivToContinuousLinearEquiv (by simp) (q p)).injective
  change Injective (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ))) (𝓡∂ 3)
    (Subtype.val ∘ (C ∘ q)) p)
  rw [mfderiv_comp p (contMDiff_subtype_val.mdifferentiableAt (n:=∞) (by simp))
    ((C.contMDiff.comp hq).mdifferentiableAt (by simp)),
    mfderiv_comp p (C.contMDiff.mdifferentiableAt (by simp)) (hq.mdifferentiableAt (by simp))]
  exact hinc.comp (hC.comp (straightened_strip_differential_injective a rho FB hFB d hd hd1 p))

theorem straightened_time_collar_closed_embedding (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (FB : Circle × ℝ → ℝ) (hFB : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞) :
    IsEmbedding (fun p : Circle × (Time × Icc (-1:ℝ) 1) =>
      straightenedTimeCollar a rho FB d hd hd1 V C (p.1,p.2.1,p.2.2.val)) :=
  IsEmbedding.subtypeVal.comp (C.toHomeomorph.isEmbedding.comp
    (straightened_strip_closed_embedding a rho FB hFB d hd hd1))

theorem straightened_time_collar_flow (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (hsmall : d ≤ 1/4) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (J : LongitudeFoliation.{0} E) (Phi : B1SourceFoliationFlow J)
    (hflow : ∀ y : ℝ, ∀ q : longitudeProductStrip,
      Phi.ambient y (C q : E.Carrier) = (C (longitudeStripFlow y q) : E.Carrier))
    (s : Circle) (t : Time) (y : ℝ) :
    straightenedTimeCollar a rho FB d hd hd1 V C (s,t,y) =
      Phi.ambient y (straightenedTimeCollar a rho FB d hd hd1 V C (s,t,0)) := by
  simp only [straightenedTimeCollar]
  rw [hflow]
  apply congrArg (fun q : longitudeProductStrip => (C q : E.Carrier))
  apply Subtype.ext
  rw [longitude_strip_flow_small_time y _ (by
    change d*(t:ℝ) ≤ 1/4
    exact (mul_le_mul_of_nonneg_left t.property.2 hd.le).trans (by simpa using hsmall))]
  change ((longitudeLabelFlow y (longitudeLabelFlow (FB (rho s,d*(t:ℝ))) a),rho s),_) =
    ((longitudeLabelFlow y (longitudeLabelFlow 0 (longitudeLabelFlow (FB (rho s,d*(t:ℝ))) a)),rho s),_)
  rw [Flow.map_zero_apply]
  rfl

#print axioms straightened_time_collar_smooth
#print axioms straightened_time_collar_differential_injective
#print axioms straightened_time_collar_closed_embedding
#print axioms straightened_time_collar_flow
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
