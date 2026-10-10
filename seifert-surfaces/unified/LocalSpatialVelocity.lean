import SpatialChartVelocity
import BoundaryCompatibleChartFlow
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M]

theorem exists_global_model_chart_velocity
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (z : EuclideanHalfSpace 3) (hz : z ∈ d.target) :
    ∃ W : Time × EuclideanHalfSpace 3 → Euc 3,
      ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ W ∧
      (∀ t z, (𝓡∂ 3) z 0 = 0 → W (t,z) 0 = 0) ∧
      ∃ A : Set (EuclideanHalfSpace 3), IsOpen A ∧ z ∈ A ∧ A ⊆ d.target ∧
        ∀ t z, z ∈ A → W (t,z) = spatialChartVelocity Y d (t,d.symm z) := by
  letI : T2Space (EuclideanHalfSpace 3) :=
    inferInstanceAs (T2Space {z : Euc 3 // 0 ≤ z 0})
  obtain ⟨β,hβtrue,hβs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡∂ 3) z).mem_iff.mp
    (d.open_target.mem_nhds hz)
  let W : Time × EuclideanHalfSpace 3 → Euc 3 := fun q =>
    β q.2 • spatialChartVelocity Y d (q.1,d.symm q.2)
  have hW : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ W := by
    intro q
    by_cases hq : q.2 ∈ tsupport β
    · exact (β.contMDiff.comp contMDiff_snd).contMDiffAt.smul
        ((spatialChartVelocity_model_contMDiffOn Y hY d hd).contMDiffAt
          ((isOpen_univ.prod d.open_target).mem_nhds ⟨mem_univ _,hβs hq⟩))
    · have heq : W =ᶠ[𝓝 q] fun _ => (0 : Euc 3) := by
        have hβ0 := notMem_tsupport_iff_eventuallyEq.mp hq
        filter_upwards [hβ0.comp_tendsto continuous_snd.continuousAt] with p hp
        change β p.2 = 0 at hp
        simp only [W,hp,zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq heq
  have hWb (t : Time) (w : EuclideanHalfSpace 3) (hw : (𝓡∂ 3) w 0 = 0) : W (t,w) 0 = 0 := by
    by_cases hws : w ∈ tsupport β
    · simp only [W,PiLp.smul_apply,
        spatialChartVelocity_model_boundary Y hYb d hd t w (hβs hws) hw,
        smul_eq_mul,mul_zero]
    · rw [show W (t,w) = 0 by simp [W,image_eq_zero_of_notMem_tsupport hws]]
      rfl
  obtain ⟨A,hAeq,hAo,hzA⟩ := mem_nhds_iff.mp β.eventuallyEq_one
  refine ⟨W,hW,hWb,A ∩ d.target,hAo.inter d.open_target,⟨hzA,hz⟩,inter_subset_right,?_⟩
  intro t w hw
  change β w • _ = _
  have hβone : β w = 1 := hAeq hw.1
  rw [hβone,one_smul]

/-- Every point has a compact Euclidean representative of the same global
spatial field, valid on a relative open neighbourhood of that point. -/
theorem exists_local_compact_spatial_chart_velocity
    (Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2)
    (hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)))
    (hYb : ∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (Y q) = 0)
    (p : Time × M) :
    ∃ d : OpenPartialHomeomorph M (EuclideanHalfSpace 3),
      d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M ∧
      ∃ U : Set (Time × M), IsOpen U ∧ p ∈ U ∧ U ⊆ univ ×ˢ d.source ∧
        ∃ V : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
          (∀ t z, z 0 = 0 → V (t,z) 0 = 0) ∧
          halfspaceSpatialSupport V ⊆ d.target ∧
          ∀ q ∈ U, V ((q.1 : ℝ),(d.extend (𝓡∂ 3)) q.2) = spatialChartVelocity Y d q := by
  let d := chartAt (EuclideanHalfSpace 3) p.2
  have hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M := IsManifold.chart_mem_maximalAtlas _
  have hp : p.2 ∈ d.source := mem_chart_source _ _
  obtain ⟨W,hW,hWb,A,hAo,hzA,hAd,hWA⟩ :=
    exists_global_model_chart_velocity Y hY hYb d hd (d p.2) (d.map_source hp)
  let q₀ : ℝ × Euc 3 := ((p.1 : ℝ),(d.extend (𝓡∂ 3)) p.2)
  let B : Set (ℝ × Euc 3) := univ ×ˢ ((𝓡∂ 3).symm ⁻¹' d.target)
  have hBo : IsOpen B := isOpen_univ.prod (d.open_target.preimage (𝓡∂ 3).continuous_symm)
  have hqB : q₀ ∈ B := by
    refine ⟨mem_univ _,?_⟩
    change (𝓡∂ 3).symm ((𝓡∂ 3) (d p.2)) ∈ d.target
    rw [(𝓡∂ 3).left_inv]
    exact d.map_source hp
  obtain ⟨χ,hχ,hχc,hχone,hχs,hχrange⟩ := DifferentialGeometry.Analysis.exists_bump_compact
    (isCompact_singleton (x := q₀)) hBo (singleton_subset_iff.mpr hqB)
  have hχt : (𝓡∂ 3) ⁻¹' (Prod.snd '' tsupport χ) ⊆ d.target := by
    intro z hz
    obtain ⟨w,hw,heq⟩ := hz
    have hh := (hχs hw).2
    change (𝓡∂ 3).symm w.2 ∈ d.target at hh
    rw [heq,(𝓡∂ 3).left_inv] at hh
    exact hh
  obtain ⟨V,hV,hVc,hVb,hlocal,hVW⟩ :=
    exists_compact_closed_time_chart_velocity d hd W hW hWb χ hχ hχc hχt
  let Ψ : Time × M → ℝ × Euc 3 := fun q => ((q.1 : ℝ),(d.extend (𝓡∂ 3)) q.2)
  have hΨ : ContinuousOn Ψ (univ ×ˢ d.source) :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      ((d.contMDiffOn_extend hd).continuousOn.comp continuous_snd.continuousOn (fun q hq => hq.2))
  have hχone₀ : χ =ᶠ[𝓝 q₀] 1 := by simpa only [nhdsSet_singleton] using hχone
  obtain ⟨C,hCone,hCo,hqC⟩ := mem_nhds_iff.mp hχone₀
  let U := ((univ ×ˢ d.source) ∩ Ψ ⁻¹' C) ∩ (univ ×ˢ (d.source ∩ d ⁻¹' A))
  have hU : IsOpen U :=
    (hΨ.isOpen_inter_preimage (isOpen_univ.prod d.open_source) hCo).inter
      (isOpen_univ.prod (d.continuousOn.isOpen_inter_preimage d.open_source hAo))
  have hpU : p ∈ U := ⟨⟨⟨mem_univ _,hp⟩,hqC⟩,mem_univ _,hp,hzA⟩
  refine ⟨d,hd,U,hU,hpU,(inter_subset_left.trans inter_subset_left),V,hV,hVc,hVb,hlocal,?_⟩
  intro q hq
  have heq := hVW q.1 (d q.2) (hCone hq.1.2)
  change V ((q.1 : ℝ),(𝓡∂ 3) (d q.2)) = _
  rw [heq,hWA q.1 (d q.2) hq.2.2.2,d.left_inv hq.2.2.1]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
