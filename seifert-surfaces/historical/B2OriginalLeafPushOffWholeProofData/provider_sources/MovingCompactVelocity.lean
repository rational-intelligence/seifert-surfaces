import MovingPartitionGluing

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SecondCountableTopology M]
  {f g : NeatEmbedding S M}

/-- The actual prescribed moving velocity has one compactly supported smooth
ambient extension, tangent to the spatial boundary. Compactness of the ambient
manifold is not required. -/
theorem normal_exists_compact_tangent_velocity
    (F : SmoothNormalIsotopy S M f g) :
    ∃ K : Set M, IsCompact K ∧
      ∃ X : (q : Time × M) → TangentSpace ((𝓡∂ 1).prod (𝓡∂ 3)) q,
        ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3)).tangent ∞
          (fun q => (⟨q,X q⟩ : TangentBundle ((𝓡∂ 1).prod (𝓡∂ 3)) (Time × M))) ∧
        (∀ q, (X q).1 = 0) ∧
        (∀ p, (X (normalTrace F p)).2 = traceVelocity F p) ∧
        (∀ q, q.2 ∈ (𝓡∂ 3).boundary M → inwardCoordinate q.2 (X q).2 = 0) ∧
        ∀ q, q.2 ∉ K → X q = 0 := by
  obtain ⟨X,hX,hXtime,hXtrace,hXboundary⟩ := normal_exists_global_tangent_velocity F
  obtain ⟨χ,hχ,hχsupp,hχone,hχrange⟩ := normalTrace_exists_compact_cutoff F
  let ρ : Time × M → ℝ := fun q => χ q.2
  have hρ : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,ℝ) ∞ ρ := hχ.comp contMDiff_snd
  let Y : (q : Time × M) → TangentSpace ((𝓡∂ 1).prod (𝓡∂ 3)) q := fun q => ρ q • X q
  have hY : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3)).tangent ∞
      (fun q => (⟨q,Y q⟩ : TangentBundle ((𝓡∂ 1).prod (𝓡∂ 3)) (Time × M))) :=
    hρ.smul_section hX
  refine ⟨tsupport χ,hχsupp,Y,hY,?_,?_,?_,?_⟩
  · intro q
    change ρ q • (X q).1 = 0
    rw [hXtime,smul_zero]
  · intro p
    change χ ((F.stage p.1).toFun p.2) • (X (normalTrace F p)).2 = traceVelocity F p
    rw [hχone,one_smul,hXtrace]
  · intro q hqb
    have hb : (show Euc 3 from (X q).2) 0 = 0 :=
      (inwardCoordinate_eq q.2 (X q).2).symm.trans (hXboundary q hqb)
    apply (inwardCoordinate_eq q.2 (Y q).2).trans
    change (ρ q • (show Euc 3 from (X q).2)) 0 = 0
    rw [PiLp.smul_apply,smul_eq_mul,hb,mul_zero]
  · intro q hq
    change χ q.2 • X q = 0
    rw [image_eq_zero_of_notMem_tsupport hq,zero_smul]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
