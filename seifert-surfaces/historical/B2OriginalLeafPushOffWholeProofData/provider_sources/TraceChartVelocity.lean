import StageNeatRetraction

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

def traceChartVelocity (F : SmoothNormalIsotopy S M f g)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3)) (p : Time × S) : Euc 3 :=
  mfderiv (𝓡∂ 3) 𝓘(ℝ, Euc 3) (d.extend (𝓡∂ 3)) ((F.stage p.1).toFun p.2)
    (traceVelocity F p)

/-- The actual time velocity, expressed in any immersion chart, is jointly
smooth on the trace portion in that chart. -/
theorem traceChartVelocity_contMDiffOn (F : SmoothNormalIsotopy S M f g)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M) :
    ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 2)) 𝓘(ℝ, Euc 3) ∞
      (traceChartVelocity F d) {p | (F.stage p.1).toFun p.2 ∈ d.source} := by
  have hchart := d.contMDiffOn_extend hd
  have htm := hchart.contMDiffOn_tangentMapWithin (m := (⊤ : ℕ∞)) (by simp)
    d.open_source.uniqueMDiffOn
  have hcomp := htm.comp (traceVelocity_contMDiff F).contMDiffOn
    (fun p hp => hp)
  have hread := (contMDiff_snd_tangentBundle_modelSpace (Euc 3) 𝓘(ℝ, Euc 3)).comp_contMDiffOn hcomp
  apply hread.congr
  intro p hp
  symm
  change mfderivWithin (𝓡∂ 3) 𝓘(ℝ, Euc 3) (d.extend (𝓡∂ 3)) d.source
    ((F.stage p.1).toFun p.2) (traceVelocity F p) = traceChartVelocity F d p
  rw [mfderivWithin_of_mem_nhds (d.open_source.mem_nhds hp)]
  rfl

/-- The chart expression of the original time velocity has zero boundary
normal coordinate in every smooth chart, including at the time endpoints. -/
theorem traceChartVelocity_boundary (F : SmoothNormalIsotopy S M f g)
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M) (p : Time × S)
    (hp : (F.stage p.1).toFun p.2 ∈ d.source) (hpb : p.2 ∈ S.boundary) :
    traceChartVelocity F d p 0 = 0 := by
  let c : Time → M := fun t => (F.stage t).toFun p.2
  let q : Time → ℝ := fun t => (d.extend (𝓡∂ 3)) (c t) 0
  have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ c :=
    F.smooth_family.comp (contMDiff_id.prodMk contMDiff_const)
  have hmem : ∀ᶠ t in 𝓝 p.1, c t ∈ d.source :=
    hc.continuous.continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hp)
  have hzero : q =ᶠ[𝓝 p.1] fun _ => 0 := by
    filter_upwards [hmem] with t ht
    apply (chart_boundary_normal_iff d hd ht).mp
    change p.2 ∈ (F.stage t).toFun ⁻¹' (𝓡∂ 3).boundary M
    rwa [(F.stage t).boundary_preimage]
  have hdq : mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) q p.1 = 0 := by
    rw [hzero.mfderiv_eq, mfderiv_const]
    simp
  have hdc := (d.contMDiffOn_extend hd).mdifferentiableOn (by simp)
    |>.mdifferentiableAt (d.open_source.mem_nhds hp)
  have hchart := mfderiv_comp p.1 hdc (hc.mdifferentiableAt (by simp))
  have hproj := mfderiv_comp p.1
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).differentiableAt.mdifferentiableAt)
    (hdc.comp p.1 (hc.mdifferentiableAt (by simp)))
  rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hproj
  change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) q p.1 = _ at hproj
  rw [hdq, hchart] at hproj
  have hv := congrArg (fun A : TangentSpace (𝓡∂ 1) p.1 →L[ℝ] ℝ => A 1) hproj
  exact hv.symm

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
