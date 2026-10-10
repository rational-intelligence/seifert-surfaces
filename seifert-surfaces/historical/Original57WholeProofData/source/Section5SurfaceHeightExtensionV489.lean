import Section5LongitudeLocalLogV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

/-- Extend an actual smooth graph height through the boundary without
changing it anywhere on the chosen closed radial cylinder. -/
theorem surface_height_real_extension (f : Circle × Time → ℝ) {d : ℝ}
    (hd : d < 1)
    (hf : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ) ∞ f {p | (p.2:ℝ) ≤ d}) :
    ∃ F : Circle × ℝ → ℝ, ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ F ∧
      ∀ z : Circle, ∀ t : Time, (t:ℝ) ≤ d → F (z,(t:ℝ)) = f (z,t) := by
  let Q : ℝ × Circle → Circle × Time := fun q => (q.2,projIcc 0 1 (by norm_num) q.1)
  have hQ : ContMDiffOn (𝓘(ℝ).prod (𝓡 1)) ((𝓡 1).prod (𝓡∂ 1)) ∞ Q
      (Icc (0:ℝ) d ×ˢ univ) := by
    exact contMDiff_snd.contMDiffOn.prodMk
      (contMDiffOn_projIcc.comp contMDiff_fst.contMDiffOn
        (fun q hq => ⟨hq.1.1,hq.1.2.trans hd.le⟩))
  have hmaps : MapsTo Q (Icc (0:ℝ) d ×ˢ univ) {p : Circle × Time | (p.2:ℝ) ≤ d} := by
    intro q hq
    change (projIcc 0 1 (by norm_num) q.1 : ℝ) ≤ d
    simpa only [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) ⟨hq.1.1,hq.1.2.trans hd.le⟩] using hq.1.2
  obtain ⟨F,hF,hFe⟩ := Manifold.exists_contMDiff_extension_Icc (hf.comp hQ hmaps)
  refine ⟨fun p => F (p.2,p.1),hF.comp (contMDiff_snd.prodMk contMDiff_fst),?_⟩
  intro z t ht
  have he := hFe (show ((t:ℝ),z) ∈ Icc (0:ℝ) d ×ˢ univ from ⟨⟨t.property.1,ht⟩,mem_univ z⟩)
  have hproj : projIcc 0 1 (by norm_num) (t:ℝ) = t :=
    Subtype.ext (by simp [projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) t.property])
  simpa only [comp_apply,Q,hproj] using he

/-- Real graph heights are actual flow parameters, smooth through r = 0. -/
theorem circle_graph_smooth_real_height (a : Circle) (h : Circle × Time → Circle)
    {d : ℝ} (hd : 0 < d)
    (hh : ContMDiffOn ((𝓡 1).prod (𝓡∂ 1)) (𝓡 1) ∞ h {p | (p.2:ℝ) ≤ d})
    (hzero : ∀ z, h (z,0) = a) {eta : ℝ} (heta : 0 < eta) :
    ∃ e : ℝ, 0 < e ∧ e < d ∧ e < 1 ∧ ∃ F : Circle × ℝ → ℝ,
      ContMDiff ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) ∞ F ∧
      (∀ z, F (z,0) = 0) ∧
      (∀ z : Circle, ∀ t : Time, (t:ℝ) ≤ e →
        longitudeLabelFlow (F (z,(t:ℝ))) a = h (z,t) ∧ |F (z,(t:ℝ))| < eta) := by
  obtain ⟨e,he,hed,he1,f,hf,hf0,hfe,hfb⟩ := circle_graph_real_height a h hd hh hzero heta
  obtain ⟨F,hF,hFe⟩ := surface_height_real_extension f he1 hf
  refine ⟨e,he,hed,he1,F,hF,?_,?_⟩
  · intro z
    exact (hFe z 0 he.le).trans (hf0 z)
  · intro z t ht
    rw [hFe z t ht]
    exact ⟨hfe (z,t),hfb (z,t) ht⟩

#print axioms surface_height_real_extension
#print axioms circle_graph_smooth_real_height
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
