import ChartFlowInstantiation
import TimeBoundaryVelocityExtension

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe v

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
  [T2Space M]

/-- A closed-time chart field with zero boundary normal component produces an
actual ambient isotopy on the manifold. The Euclidean field is repaired and
extended on both time sides before invoking the genuine halfspace flow. -/
theorem exists_compact_closed_time_chart_velocity
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (G : Time × EuclideanHalfSpace 3 → Euc 3)
    (hG : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ G)
    (hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0)
    (χ : ℝ × Euc 3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ)
    (hχtarget : (𝓡∂ 3) ⁻¹' (Prod.snd '' tsupport χ) ⊆ e.target) :
    ∃ V : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      (∀ t z, z 0 = 0 → V (t,z) 0 = 0) ∧
      halfspaceSpatialSupport V ⊆ e.target ∧
      ∀ t : Time, ∀ z, χ ((t : ℝ),(𝓡∂ 3) z) = 1 →
        V ((t : ℝ),(𝓡∂ 3) z) = G (t,z) := by
  obtain ⟨X,hX,hXeq,hXb⟩ := exists_real_boundary_velocity_extension G hG hGb
  obtain ⟨V,hV,hVc,hVs,hVeq,hVb⟩ :=
    exists_contDiff_compact_boundary_velocity_extension
      (fun q : ℝ × EuclideanHalfSpace 3 => X (q.1,(𝓡∂ 3) q.2))
      (by
        have hXmd := hX.contMDiff
        exact hXmd.comp
          (contMDiff_fst.prodMk_space ((𝓡∂ 3).contMDiff.comp contMDiff_snd)))
      (by intro t z hz; exact hXb t ((𝓡∂ 3) z) hz)
      χ hχ hχc
  have hlocal : halfspaceSpatialSupport V ⊆ e.target := by
    intro z hz
    obtain ⟨w, hw, heq⟩ := hz
    exact hχtarget ⟨w,hVs hw,heq⟩
  exact ⟨V,hV,hVc,hVb,hlocal,fun t z hz => (hVeq t z hz).trans (hXeq t z)⟩

theorem exists_boundary_compatible_chart_flow
    (e : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    (G : Time × EuclideanHalfSpace 3 → Euc 3)
    (hG : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ G)
    (hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0)
    (χ : ℝ × Euc 3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ)
    (hχtarget : (𝓡∂ 3) ⁻¹' (Prod.snd '' tsupport χ) ⊆ e.target)
    {γ : ℝ → Euc 3} (hγ : ContinuousOn γ (Icc 0 1))
    (hγ' : ∀ t ∈ Ico 0 1, HasDerivWithinAt γ
      (G (projIcc 0 1 (by norm_num) t,(𝓡∂ 3).symm (γ t))) (Ici t) t)
    (hγhalf : ∀ t ∈ Icc 0 1, γ t ∈ range (𝓡∂ 3))
    (hγchart : (𝓡∂ 3).symm (γ 0) ∈ e.target)
    (hγcutoff : ∀ t ∈ Icc 0 1, χ (t,γ t) = 1) :
    ∃ H : SmoothAmbientIsotopy M, ∀ t : Time,
      H.stage t (e.symm ((𝓡∂ 3).symm (γ 0))) = e.symm ((𝓡∂ 3).symm (γ t)) := by
  obtain ⟨V,hV,hVc,hVb,hlocal,htrace⟩ :=
    exists_compact_closed_time_chart_velocity e he G hG hGb χ hχ hχc hχtarget
  refine ⟨chartCompactFlow e he hV hVc hVb hlocal,?_⟩
  intro t
  apply chartCompactFlow_tracks e he hV hVc hVb hlocal hγ _ hγhalf hγchart t
  intro u hu
  have hucc : u ∈ Icc 0 1 := ⟨hu.1,hu.2.le⟩
  have hp : ((projIcc 0 1 (by norm_num) u : Time) : ℝ) = u := by
    rw [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) hucc]
  have hh := htrace (projIcc 0 1 (by norm_num) u) ((𝓡∂ 3).symm (γ u))
    (by rw [hp,(𝓡∂ 3).right_inv (hγhalf u hucc)]; exact hγcutoff u hucc)
  rw [hp,(𝓡∂ 3).right_inv (hγhalf u hucc)] at hh
  rw [hh]
  exact hγ' u hu

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
