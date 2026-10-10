import Section5ActualCommonGraphsV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
noncomputable section

/-- A smooth logarithm of actual longitude labels near any initial leaf. -/
theorem longitude_label_local_log (a : Circle) :
    ∃ O : Set Circle, IsOpen O ∧ a ∈ O ∧ ∃ theta : Circle → ℝ,
      ContMDiffOn (𝓡 1) 𝓘(ℝ) ∞ theta O ∧ theta a = 0 ∧
      (∀ z, longitudeLabelFlow (theta z) a = z) := by
  let rot : Circle → Circle := fun z => z*a⁻¹
  let theta : Circle → ℝ := fun z => (Complex.log (rot z : ℂ)).im
  let O : Set Circle := (fun z => (rot z : ℂ)) ⁻¹' Complex.slitPlane
  haveI : Fact (Module.finrank ℝ ℂ = 1+1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ,ℂ) ∞ (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have hrot : ContMDiff (𝓡 1) (𝓡 1) ∞ rot := contMDiff_id.mul contMDiff_const
  have hO : IsOpen O := Complex.isOpen_slitPlane.preimage (hcoe.comp hrot).continuous
  have ha : a ∈ O := by simp [O,rot]
  have htheta : ContMDiffOn (𝓡 1) 𝓘(ℝ) ∞ theta O := by
    intro z hz
    have hl := (Complex.contDiffAt_log hz (n:=∞)).restrict_scalars ℝ
    exact (Complex.imCLM.contDiff.contMDiff.contMDiffAt.comp z
      (hl.contMDiffAt.comp z (hcoe.comp hrot).contMDiffAt)).contMDiffWithinAt
  refine ⟨O,hO,ha,theta,htheta,?_,?_⟩
  · simp [theta,rot]
  · intro z
    change Circle.exp (Complex.log (rot z : ℂ)).im * a = z
    rw [Complex.log_im,Circle.exp_arg]
    simp [rot,mul_assoc]

/-- A circle-valued graph which starts on one leaf lifts smoothly to a small
real height, uniformly over the whole boundary circle. -/
theorem circle_graph_real_height (a : Circle) (h : Circle × Time → Circle)
    {d : ℝ} (hd : 0 < d)
    (hh : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ h {p | (p.2:ℝ) ≤ d})
    (hzero : ∀ z, h (z,0) = a) {eta : ℝ} (heta : 0 < eta) :
    ∃ e : ℝ, 0 < e ∧ e < d ∧ e < 1 ∧ ∃ f : Circle × Time → ℝ,
      ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ) ∞ f {p | (p.2:ℝ) ≤ e} ∧
      (∀ z, f (z,0) = 0) ∧
      (∀ p, longitudeLabelFlow (f p) a = h p) ∧
      (∀ p, (p.2:ℝ) ≤ e → |f p| < eta) := by
  obtain ⟨O,hO,ha,theta,htheta,htheta0,hexp⟩ := longitude_label_local_log a
  let Q : Set (Circle × Time) := {p | (p.2:ℝ) < d}
  have hQ : IsOpen Q := isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const
  have hQQ : Q ⊆ {p : Circle × Time | (p.2:ℝ) ≤ d} := by
    intro p hp
    exact (show (p.2:ℝ) < d from hp).le
  let R := Q ∩ h ⁻¹' O
  have hR : IsOpen R := (hh.continuousOn.mono hQQ).isOpen_inter_preimage hQ hO
  let f := theta ∘ h
  have hf : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ) ∞ f R :=
    htheta.comp (hh.mono (inter_subset_left.trans hQQ)) (fun _ hp => hp.2)
  let N := R ∩ f ⁻¹' Ioo (-eta) eta
  have hN : IsOpen N := hf.continuousOn.isOpen_inter_preimage hR isOpen_Ioo
  have hf0 (z) : f (z,0) = 0 := by simp only [f,comp_apply,hzero,htheta0]
  have hN0 (z) : (z,0) ∈ N := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · exact hd
    · change h (z,0) ∈ O
      rw [hzero]
      exact ha
    · change f (z,0) ∈ Ioo (-eta) eta
      rw [hf0]
      exact ⟨neg_neg_of_pos heta,heta⟩
  obtain ⟨e₀,he₀,he₀one,he₀N⟩ := compact_boundary_uniform_strip hN hN0
  let e := min e₀ (d/2)
  have he : 0 < e := lt_min he₀ (half_pos hd)
  have heN (p : Circle × Time) (hp : (p.2:ℝ) ≤ e) : p ∈ N :=
    he₀N p.1 p.2 (hp.trans (min_le_left _ _))
  refine ⟨e,he,(min_le_right _ _).trans_lt (half_lt_self hd),
    (min_le_left _ _).trans_lt he₀one,f,hf.mono (fun p hp => (heN p hp).1),hf0,
    fun p => hexp (h p),?_⟩
  intro p hp
  exact abs_lt.mpr (heN p hp).2

#print axioms longitude_label_local_log
#print axioms circle_graph_real_height
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
