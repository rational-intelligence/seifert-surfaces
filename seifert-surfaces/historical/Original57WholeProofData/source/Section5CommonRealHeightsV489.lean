import Section5SurfaceHeightExtensionV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

/-- Both actual graph heights have compatible smooth real lifts; their
literal difference is the parameter of the already constructed ambient flow. -/
theorem common_circle_graphs_real_pair (a : Circle) (hA hB : Circle × Time → Circle)
    {d : ℝ} (hd : 0 < d)
    (hA_smooth : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ hA {p | (p.2:ℝ) ≤ d})
    (hB_smooth : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ hB {p | (p.2:ℝ) ≤ d})
    (hzero : ∀ z, hA (z,0) = a ∧ hB (z,0) = a) {eta : ℝ} (heta : 0 < eta) :
    ∃ e : ℝ, 0 < e ∧ e < d ∧ e < 1 ∧ ∃ FA FB : Circle × ℝ → ℝ,
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FA ∧
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ FB ∧
      (∀ z, FA (z,0) = 0 ∧ FB (z,0) = 0) ∧
      (∀ z : Circle, ∀ t : Time, (t:ℝ) ≤ e →
        longitudeLabelFlow (FA (z,(t:ℝ))) a = hA (z,t) ∧
        longitudeLabelFlow (FB (z,(t:ℝ))) a = hB (z,t) ∧
        longitudeLabelFlow (FA (z,(t:ℝ))-FB (z,(t:ℝ))) (hB (z,t)) = hA (z,t) ∧
        |FA (z,(t:ℝ))-FB (z,(t:ℝ))| < eta ∧
        |FA (z,(t:ℝ))| < eta/2 ∧ |FB (z,(t:ℝ))| < eta/2) := by
  obtain ⟨eA,heA,heAd,heA1,FA,hFA,hFA0,hFAe⟩ :=
    circle_graph_smooth_real_height a hA hd hA_smooth (fun z => (hzero z).1) (half_pos heta)
  obtain ⟨eB,heB,heBd,heB1,FB,hFB,hFB0,hFBe⟩ :=
    circle_graph_smooth_real_height a hB hd hB_smooth (fun z => (hzero z).2) (half_pos heta)
  let e := min eA eB
  refine ⟨e,lt_min heA heB,(min_le_left _ _).trans_lt heAd,
    (min_le_left _ _).trans_lt heA1,FA,FB,hFA,hFB,fun z => ⟨hFA0 z,hFB0 z⟩,?_⟩
  intro z t ht
  have hA := hFAe z t (ht.trans (min_le_left _ _))
  have hB := hFBe z t (ht.trans (min_le_right _ _))
  refine ⟨hA.1,hB.1,?_,?_,hA.2,hB.2⟩
  · rw [← hB.1,← Flow.map_add]
    convert hA.1 using 1
    congr 1
    ring
  · exact (abs_sub _ _).trans_lt (by linarith [hA.2,hB.2])

/-- The actual cutoff flow is the unmodified transverse longitude flow on
the entire common graph cylinder. -/
theorem longitude_strip_flow_small_time (y : ℝ) (p : longitudeProductStrip)
    (hp : (p.val.2:ℝ) ≤ 1/4) :
    (longitudeStripFlow y p).val = ((longitudeLabelFlow y p.val.1.1,p.val.1.2),p.val.2) := by
  have hc : longitudeRadialCutoff (p.val.2:ℝ) = 1 := by
    apply longitudeRadialCutoff.one_of_mem_closedBall
    change dist (p.val.2:ℝ) 0 ≤ 1/4
    rw [Real.dist_eq,sub_zero,abs_of_nonneg p.val.2.property.1]
    exact hp
  change ((longitudeLabelFlow (longitudeRadialCutoff (p.val.2:ℝ)*y) p.val.1.1,p.val.1.2),p.val.2) = _
  rw [hc,one_mul]

#print axioms common_circle_graphs_real_pair
#print axioms longitude_strip_flow_small_time
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
