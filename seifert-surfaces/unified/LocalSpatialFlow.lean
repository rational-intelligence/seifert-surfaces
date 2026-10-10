import ChartFlowTangentEquation

set_option autoImplicit false

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

set_option maxHeartbeats 1000000 in
def chartRealDiffeomorph
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞ :=
  { toEquiv :=
      { toFun := chartRealFlow e hV hs hb s t
        invFun := chartRealFlow e hV hs hb t s
        left_inv := chartRealFlow_leftInverse e hV hs hb hlocal s t
        right_inv := chartRealFlow_leftInverse e hV hs hb hlocal t s }
    contMDiff_toFun := by
      have hp : ContMDiff (𝓡∂ 3) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) ∞
          (fun x : M => ((s,t),x)) := contMDiff_const.prodMk contMDiff_id
      exact (chartRealFlow_contMDiff e he hV hs hb hlocal).comp hp
    contMDiff_invFun := by
      have hp : ContMDiff (𝓡∂ 3) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) ∞
          (fun x : M => ((t,s),x)) := contMDiff_const.prodMk contMDiff_id
      exact (chartRealFlow_contMDiff e he hV hs hb hlocal).comp hp }

theorem chartRealDiffeomorph_apply
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {V : ℝ × Euc 3 → Euc 3} (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t z, z 0 = 0 → V (t,z) 0 = 0)
    (hlocal : halfspaceSpatialSupport V ⊆ e.target) (s t : ℝ) (x : M) :
    chartRealDiffeomorph e he hV hs hb hlocal s t x = chartRealFlow e hV hs hb s t x := rfl

set_option maxHeartbeats 1000000 in
theorem exists_local_spatial_flow
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (p : Time × M) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s t x, Φ t s (Φ s t x) = x) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s t, ∃ D : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞, ∀ x, D x = Φ s t x) ∧
      ∃ A : Set ((Time × Time) × M), IsOpen A ∧ ((p.1,p.1),p.2) ∈ A ∧
        ∀ q ∈ A, HasMFDerivAt 𝓘(ℝ,ℝ) (𝓡∂ 3)
          (fun u => Φ (q.1.1 : ℝ) u q.2) (q.1.2 : ℝ)
          ((ContinuousLinearMap.id ℝ ℝ).smulRight
            (Y (q.1.2,Φ (q.1.1 : ℝ) (q.1.2 : ℝ) q.2))) := by
  obtain ⟨d,hd,U,hU,hpU,hUd,V,hV,hVs,hVb,hlocal,hVU⟩ :=
    exists_local_compact_spatial_chart_velocity Y hY hYb p
  let Φ := chartRealFlow d hV hVs hVb
  have hΦ : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) :=
    chartRealFlow_contMDiff d hd hV hVs hVb hlocal
  let Ψ : (Time × Time) × M → Time × M := fun q =>
    (q.1.2,chartRealFlow d hV hVs hVb (q.1.1 : ℝ) (q.1.2 : ℝ) q.2)
  have hp : Continuous (fun q : (Time × Time) × M =>
      (((q.1.1 : ℝ),(q.1.2 : ℝ)),q.2)) :=
    ((continuous_subtype_val.comp continuous_fst.fst).prodMk
      (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd
  have hπ : Continuous (fun q : (Time × Time) × M => q.1.2) :=
    continuous_fst.snd
  have hΨ : Continuous Ψ := hπ.prodMk
    ((chartRealFlow_contMDiff d hd hV hVs hVb hlocal).continuous.comp hp)
  let A := Ψ ⁻¹' U ∩ (univ ×ˢ d.source)
  have hA : IsOpen A := (hU.preimage hΨ).inter (isOpen_univ.prod d.open_source)
  have hpA : ((p.1,p.1),p.2) ∈ A := by
    refine ⟨?_,mem_univ _,(hUd hpU).2⟩
    change (p.1,chartRealFlow d hV hVs hVb (p.1 : ℝ) (p.1 : ℝ) p.2) ∈ U
    rw [chartRealFlow_refl]
    exact hpU
  refine ⟨Φ,hΦ,?_,?_,?_,?_,A,hA,hpA,?_⟩
  · exact fun s x => chartRealFlow_refl d hV hVs hVb s x
  · exact fun s t x => chartRealFlow_leftInverse d hV hVs hVb hlocal s t x
  · exact fun s t u x => chartRealFlow_trans d hV hVs hVb hlocal s t u x
  · exact fun s t => ⟨chartRealDiffeomorph d hd hV hVs hVb hlocal s t,fun _ => rfl⟩
  · intro q hq
    simpa only [Φ, Ψ] using
      (chartRealFlow_hasMFDerivAt d hd hV hVs hVb hlocal _ _ hq.2.2
        (Y (q.1.2, chartRealFlow d hV hVs hVb (q.1.1 : ℝ) (q.1.2 : ℝ) q.2))
        (hVU (q.1.2, chartRealFlow d hV hVs hVb (q.1.1 : ℝ) (q.1.2 : ℝ) q.2) hq.1))

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
