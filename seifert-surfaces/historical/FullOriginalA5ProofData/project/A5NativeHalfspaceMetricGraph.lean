import A5NativeHalfspaceGraphExtension

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
universe u

/-- The literal C1 section on a closed half-disc constructs a native metric
graph. The auxiliary extension is used only to obtain the ambient jet tube;
the actual graph on the original half-disc is preserved exactly. -/
theorem native_metric_graph_of_C1_halfspace_section
    {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ,E3) ∞ N]
    (h : AmbientMetric N) (c : SmoothAmbientChart N)
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → E3)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (hchart : MapsTo f (closedHalfDisc ρ) c.chart.target)
    (P : E3 →L[ℝ] E2) (height : E3 →L[ℝ] ℝ)
    (hsep : Function.Injective (fun z => (P z,height z)))
    (hsection : ∀ z ∈ closedHalfDisc ρ, P (f z) = z) :
    ∃ G : NativeMetricGraph h,
      G.coordinates = c ∧ G.origin = f 0 ∧
      (∀ v, P (G.plane v) = v ∧ height (G.plane v) = 0) ∧
      P G.normal = 0 ∧ height G.normal = 1 ∧ G.height 0 = 0 ∧
      (∀ (z : E2), z ∈ Metric.closedBall 0 (2 * G.radius) → z ∈ Metric.ball 0 ρ) ∧
      ∀ z ∈ closedHalfDisc (2 * G.radius),
        graphMap G.origin G.plane G.normal G.height z = f z := by
  let A : E3 →L[ℝ] E2 × ℝ := P.prod height
  have hA : Function.Bijective A := by
    refine ⟨hsep,?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) (by simp [E2,E3,Module.finrank_prod])).mp hsep
  let L : E3 ≃L[ℝ] E2 × ℝ := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  obtain ⟨g,hg,he⟩ := C1_closed_halfdisc_local_extension ρ hρ f hf
  let f' : E2 → E3 := fun z => L.symm (z,height (g z))
  have hf' : ContDiffAt ℝ 1 f' 0 :=
    L.symm.contDiff.contDiffAt.comp 0
      (contDiffAt_id.prodMk (height.contDiff.contDiffAt.comp 0 hg))
  have hsection' (z : E2) : P (f' z) = z :=
    congrArg Prod.fst (L.apply_symm_apply (z,height (g z)))
  have hz : (0 : E2) ∈ closedHalfDisc ρ := ⟨Metric.mem_closedBall_self hρ.le,by simp⟩
  have hfe : f' =ᶠ[𝓝[closedHalfDisc ρ] (0 : E2)] f := by
    filter_upwards [he,self_mem_nhdsWithin] with z hez hzs
    apply L.injective
    change L (L.symm (z,height (g z))) = L (f z)
    rw [L.apply_symm_apply]
    apply Prod.ext
    · exact (hsection z hzs).symm
    · exact congrArg height hez
  have hfzero : f' 0 = f 0 := hfe.eq_of_nhdsWithin hz
  obtain ⟨ε,hε,hεeq⟩ := Metric.mem_nhdsWithin_iff.mp hfe
  obtain ⟨V,hV,hVf⟩ := hf'.contDiffOn (m := 1) le_rfl (by norm_num)
  have hfc : f' ⁻¹' c.chart.target ∈ 𝓝 (0 : E2) :=
    hf'.continuousAt.preimage_mem_nhds
      (c.chart.open_target.mem_nhds (hfzero.symm ▸ hchart hz))
  obtain ⟨U,hUsub,hU,hzero⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem hV hfc) (Metric.ball_mem_nhds (0 : E2) (lt_min hρ hε)))
  have hUf : ContDiffOn ℝ 1 f' U := hVf.mono (fun z hz => (hUsub hz).1.1)
  have hUc : MapsTo f' U c.chart.target := fun z hz => (hUsub hz).1.2
  obtain ⟨G,hGc,hGo,hGp,hGn,hGh,hGzero,hGmap⟩ :=
    native_metric_graph_of_C1_section h c U hU 0 hzero f' hUf hUc P height hsep
      (fun z _ => hsection' z)
  refine ⟨G,hGc,hGo.trans hfzero,hGp,hGn,hGh,hGzero,?_,?_⟩
  · intro z hzG
    have hzU : z ∈ U := by simpa only [zero_add] using (hGmap z hzG).1
    exact Metric.ball_subset_ball (min_le_left _ _) (hUsub hzU).2
  · intro z hzG
    have hzU : z ∈ U := by simpa only [zero_add] using (hGmap z hzG.1).1
    have hzρ : z ∈ closedHalfDisc ρ :=
      ⟨Metric.mem_closedBall.mpr ((Metric.mem_ball.mp (hUsub hzU).2).trans_le
        (min_le_left _ _)).le,hzG.2⟩
    have hze : f' z = f z := hεeq
      ⟨Metric.ball_subset_ball (min_le_right _ _) (hUsub hzU).2,hzρ⟩
    have hh : graphMap G.origin G.plane G.normal G.height z = f' z := by
      simpa only [zero_add] using (hGmap z hzG.1).2
    exact hh.trans hze

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
