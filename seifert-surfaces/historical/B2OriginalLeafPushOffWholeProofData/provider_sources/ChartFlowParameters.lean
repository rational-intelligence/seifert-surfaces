import LocalSpatialVelocity

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

theorem chartPatch_real_parameters_contMDiff
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (D : ℝ × ℝ → Diffeomorph (𝓡∂ 3) (𝓡∂ 3)
      (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞)
    (hD : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : (ℝ × ℝ) × EuclideanHalfSpace 3 => D p.1 p.2))
    {K : Set (EuclideanHalfSpace 3)} (hK : IsCompact K) (hKt : K ⊆ e.target)
    (hfix : ∀ t z, z ∉ K → D t z = z) :
    ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : (ℝ × ℝ) × M => chartPatch e (D p.1) p.2) := by
  have hei := contMDiffOn_symm_of_mem_maximalAtlas he
  have hKi : IsCompact (e.symm '' K) :=
    hK.image_of_continuousOn (hei.continuousOn.mono hKt)
  intro q
  by_cases hq : q.2 ∈ e.source
  · have hmap := diffeomorph_mapsTo_of_fixed_outside (D q.1) hKt (hfix q.1)
    have hc : ContMDiffAt ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
        (fun r : (ℝ × ℝ) × M => e r.2) q :=
      ((contMDiffOn_of_mem_maximalAtlas he).contMDiffAt
        (e.open_source.mem_nhds hq)).comp q contMDiffAt_snd
    have hfun := hD.contMDiffAt.comp q (contMDiffAt_fst.prodMk hc)
    have hi := (hei.contMDiffAt
      (e.open_target.mem_nhds (hmap (e.map_source hq)))).comp q hfun
    apply hi.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hq)] with r hr
    exact chartPatch_of_mem e _ hr
  · have hqK : q.2 ∉ e.symm '' K := by
      rintro ⟨z,hz,heq⟩
      exact hq (heq ▸ e.map_target (hKt hz))
    apply contMDiffAt_snd.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      (hKi.isClosed.isOpen_compl.mem_nhds hqK)] with r hr
    exact chartPatch_eq_of_notMem_image e _ (hfix r.1) hr

def chartRealFlow
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0) (s t : ℝ) (x : M) : M :=
  chartPatch e (halfspaceFlow hV hs hb s t) x

theorem chartRealFlow_contMDiff
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) :
    ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : (ℝ × ℝ) × M => chartRealFlow e hV hs hb q.1.1 q.1.2 q.2) := by
  apply chartPatch_real_parameters_contMDiff e he
    (fun q => halfspaceFlow hV hs hb q.1 q.2) (halfspaceFlow_contMDiff hV hs hb)
    (halfspaceSpatialSupport_isCompact hs) hlocal
  intro q z hz
  apply (𝓡∂ 3).injective
  rw [halfspaceFlow_apply]
  exact (Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs q.1 q.2).1 hz

theorem chartRealFlow_refl
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0) (s : ℝ) (x : M) :
    chartRealFlow e hV hs hb s s x = x := by
  unfold chartRealFlow
  rw [halfspaceFlow_refl]
  by_cases hx : x ∈ e.source
  · rw [chartPatch_of_mem e _ hx]
    exact e.left_inv hx
  · exact chartPatch_of_notMem e _ hx

theorem chartRealFlow_leftInverse
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) :
    Function.LeftInverse (chartRealFlow e hV hs hb t s) (chartRealFlow e hV hs hb s t) := by
  have hmap : MapsTo (halfspaceFlow hV hs hb s t) e.target e.target := by
    apply diffeomorph_mapsTo_of_fixed_outside _ hlocal
    intro z hz
    apply (𝓡∂ 3).injective
    rw [halfspaceFlow_apply]
    exact (Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs s t).1 hz
  change Function.LeftInverse (chartPatch e (halfspaceFlow hV hs hb t s))
    (chartPatch e (halfspaceFlow hV hs hb s t))
  exact chartPatch_leftInverse e (halfspaceFlow hV hs hb s t) hmap

theorem chartRealFlow_mapsTo
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) :
    MapsTo (chartRealFlow e hV hs hb s t) e.source e.source := by
  intro x hx
  rw [chartRealFlow,chartPatch_of_mem e _ hx]
  apply e.map_target
  apply diffeomorph_mapsTo_of_fixed_outside _ hlocal _ (e.map_source hx)
  intro z hz
  apply (𝓡∂ 3).injective
  rw [halfspaceFlow_apply]
  exact (Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs s t).1 hz

theorem halfspaceFlow_trans
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0) (s t u : ℝ)
    (z : EuclideanHalfSpace 3) :
    halfspaceFlow hV hs hb t u (halfspaceFlow hV hs hb s t z) =
      halfspaceFlow hV hs hb s u z := by
  apply (𝓡∂ 3).injective
  rw [halfspaceFlow_apply,halfspaceFlow_apply,halfspaceFlow_apply]
  exact congrArg (fun D : Diffeomorph 𝓘(ℝ,Euc 3) 𝓘(ℝ,Euc 3) (Euc 3) (Euc 3) ∞ =>
    D ((𝓡∂ 3) z)) (Diffeomorph.timeDependentFlow_trans V hV hs s t u)

theorem chartRealFlow_trans
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t u : ℝ) (x : M) :
    chartRealFlow e hV hs hb t u (chartRealFlow e hV hs hb s t x) =
      chartRealFlow e hV hs hb s u x := by
  by_cases hx : x ∈ e.source
  · have hfx := chartRealFlow_mapsTo e hV hs hb hlocal s t hx
    unfold chartRealFlow at hfx ⊢
    rw [chartPatch_of_mem e _ hfx,chartPatch_of_mem e _ hx,chartPatch_of_mem e _ hx]
    have hz : halfspaceFlow hV hs hb s t (e x) ∈ e.target := by
      rw [chartPatch_of_mem e _ hx] at hfx
      have hinv := (chartRealFlow_mapsTo e hV hs hb hlocal t s) hfx
      apply diffeomorph_mapsTo_of_fixed_outside _ hlocal _ (e.map_source hx)
      intro z hz
      apply (𝓡∂ 3).injective
      rw [halfspaceFlow_apply]
      exact (Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs s t).1 hz
    rw [e.right_inv hz,halfspaceFlow_trans]
  · simp only [chartRealFlow,chartPatch_of_notMem e _ hx]

theorem chartRealFlow_coordinates
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) {x : M} (hx : x ∈ e.source) :
    (e.extend (𝓡∂ 3)) (chartRealFlow e hV hs hb s t x) =
      Diffeomorph.timeDependentFlow V hV hs s t ((e.extend (𝓡∂ 3)) x) := by
  have hz : halfspaceFlow hV hs hb s t (e x) ∈ e.target := by
    apply diffeomorph_mapsTo_of_fixed_outside _ hlocal _ (e.map_source hx)
    intro z hz
    apply (𝓡∂ 3).injective
    rw [halfspaceFlow_apply]
    exact (Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport V hV hs s t).1 hz
  change (𝓡∂ 3) (e (chartPatch e (halfspaceFlow hV hs hb s t) x)) = _
  rw [chartPatch_of_mem e _ hx,e.right_inv hz,halfspaceFlow_apply]
  rfl

theorem chartRealFlow_coordinate_derivative
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) {x : M} (hx : x ∈ e.source) :
    HasDerivAt (fun u => (e.extend (𝓡∂ 3)) (chartRealFlow e hV hs hb s u x))
      (V (t,(e.extend (𝓡∂ 3)) (chartRealFlow e hV hs hb s t x))) t := by
  have hf : (fun u => (e.extend (𝓡∂ 3)) (chartRealFlow e hV hs hb s u x)) =
      (fun u => Diffeomorph.timeDependentFlow V hV hs s u ((e.extend (𝓡∂ 3)) x)) :=
    funext (fun u => chartRealFlow_coordinates e hV hs hb hlocal s u hx)
  rw [hf]
  rw [chartRealFlow_coordinates e hV hs hb hlocal s t hx]
  exact Diffeomorph.isIntegralCurve_timeDependentFlow V hV hs s ((e.extend (𝓡∂ 3)) x) t

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
