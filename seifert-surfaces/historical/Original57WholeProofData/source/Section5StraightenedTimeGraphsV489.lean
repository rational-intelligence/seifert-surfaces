import Section5StraightenedTimeCollarV489
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

theorem longitude_label_flow_eq_iff (a : Circle) (u v : ℝ)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1) :
    longitudeLabelFlow u a = longitudeLabelFlow v a ↔ u = v := by
  constructor
  · intro h
    change Circle.exp u * a = Circle.exp v * a at h
    exact Circle.exp_injOn_Icc (by linarith [Real.pi_gt_three])
      (abs_le.mp hu) (abs_le.mp hv) (mul_right_cancel h)
  · rintro rfl
    rfl

/-- Exact graph membership in the B-straightened collar. -/
theorem straightened_time_collar_mem_iff (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FA FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (X : Set E.Carrier)
    (hX : ∀ q : longitudeProductStrip, (q.val.2:ℝ) ≤ d →
      ((C q : E.Carrier) ∈ X ↔ q.val.1.1 = longitudeLabelFlow (FA (q.val.1.2,(q.val.2:ℝ))) a))
    (hsmall : ∀ z : Circle, ∀ t : Time, (t:ℝ) ≤ d → |FA (z,(t:ℝ))-FB (z,(t:ℝ))| ≤ 1)
    (p : Circle × (Time × ℝ)) (hp : |p.2.2| ≤ 1) :
    straightenedTimeCollar a rho FB d hd hd1 V C p ∈ X ↔
      p.2.2 = FA (rho p.1,d*(p.2.1:ℝ))-FB (rho p.1,d*(p.2.1:ℝ)) := by
  let q := straightenedStripPoint a rho FB d hd hd1 p
  have ht : (q.val.2:ℝ) ≤ d := by
    exact (mul_le_mul_of_nonneg_left p.2.1.property.2 hd.le).trans_eq (mul_one d)
  change (C q : E.Carrier) ∈ X ↔ _
  rw [hX q ht]
  change longitudeLabelFlow p.2.2 (longitudeLabelFlow (FB (rho p.1,d*(p.2.1:ℝ))) a) =
    longitudeLabelFlow (FA (rho p.1,d*(p.2.1:ℝ))) a ↔ _
  have he : longitudeLabelFlow (FA (rho p.1,d*(p.2.1:ℝ))-FB (rho p.1,d*(p.2.1:ℝ)))
      (longitudeLabelFlow (FB (rho p.1,d*(p.2.1:ℝ))) a) =
      longitudeLabelFlow (FA (rho p.1,d*(p.2.1:ℝ))) a := by
    rw [← Flow.map_add,sub_add_cancel]
  rw [← he]
  exact longitude_label_flow_eq_iff _ _ _ hp (hsmall (rho p.1) q.val.2 ht)

/-- The actual metric radial coordinate along the straightened collar. -/
theorem straightened_time_collar_radial (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (r : E.Carrier → ℝ) (b : ℝ)
    (hCr : ∀ q : longitudeProductStrip, r (C q) = b*(q.val.2:ℝ))
    (p : Circle × (Time × ℝ)) :
    r (straightenedTimeCollar a rho FB d hd hd1 V C p) = (b*d)*(p.2.1:ℝ) := by
  rw [straightenedTimeCollar,hCr]
  change b*(d*(p.2.1:ℝ)) = _
  ring

/-- Straightening fixes the common boundary pointwise in the chosen unit parameter. -/
theorem straightened_time_collar_leaf (a : Circle)
    (rho : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞) (FB : Circle × ℝ → ℝ)
    (hFB0 : ∀ z, FB (z,0) = 0)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) (V : TopologicalSpace.Opens E.Carrier)
    (C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞)
    (J : LongitudeFoliation.{0} E)
    (hC0 : ∀ p : Circle × Circle, (C ⟨(p,0),by change ((0 : Time) : ℝ) < 1; norm_num⟩ : E.Carrier) = J.torus p)
    (s : Circle) :
    straightenedTimeCollar a rho FB d hd hd1 V C (s,0,0) = J.torus (a,rho s) := by
  change (C _ : E.Carrier) = _
  convert hC0 (a,rho s) using 1
  congr 2
  apply Subtype.ext
  simp [straightenedStripPoint,hFB0,Flow.map_zero_apply]

#print axioms longitude_label_flow_eq_iff
#print axioms straightened_time_collar_mem_iff
#print axioms straightened_time_collar_radial
#print axioms straightened_time_collar_leaf
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
