import ChartBoundaryDifferential

open scoped Manifold ContDiff
open Set Filter Topology Bundle
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- Transport a smooth local chart velocity to a genuine tangent section. -/
theorem chart_velocity_lift
    (d : OpenPartialHomeomorph M (EuclideanHalfSpace 3))
    (hd : d ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ M)
    {U : Set (Time × M)} (hUd : U ⊆ univ ×ˢ d.source)
    {V : Time × M → Euc 3}
    (hV : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ V U) :
    ∃ Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2,
      ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
        (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) U ∧
      (∀ q ∈ U, mfderiv (𝓡∂ 3) 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)) q.2 (Y q) =
        (NormedSpace.fromTangentSpace ((d.extend (𝓡∂ 3)) q.2)).symm (V q)) ∧
      ∀ q ∈ U, q.2 ∈ (𝓡∂ 3).boundary M → V q 0 = 0 → inwardCoordinate q.2 (Y q) = 0 := by
  let Y : (q : Time × M) → TangentSpace (𝓡∂ 3) q.2 := fun q =>
    (show Euc 3 from mfderivWithin 𝓘(ℝ,Euc 3) (𝓡∂ 3) (d.extend (𝓡∂ 3)).symm
      (d.extend (𝓡∂ 3)).target ((d.extend (𝓡∂ 3)) q.2)
        ((NormedSpace.fromTangentSpace ((d.extend (𝓡∂ 3)) q.2)).symm (V q)))
  have hdi : ContMDiffOn 𝓘(ℝ,Euc 3) (𝓡∂ 3) ∞ (d.extend (𝓡∂ 3)).symm
      (d.extend (𝓡∂ 3)).target := by
    simpa only [d.extend_target'] using contMDiffOn_extend_symm hd
  have hdu : UniqueMDiffOn 𝓘(ℝ,Euc 3) (d.extend (𝓡∂ 3)).target := by
    apply UniqueDiffOn.uniqueMDiffOn
    rw [d.extend_target,inter_comm]
    exact (𝓡∂ 3).uniqueDiffOn.inter (d.open_target.preimage (𝓡∂ 3).continuous_symm)
  have htm := hdi.contMDiffOn_tangentMapWithin (m := (⊤ : ℕ∞)) (by simp) hdu
  have hcoords : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞
      (fun q : Time × M => (d.extend (𝓡∂ 3)) q.2) U :=
    (d.contMDiffOn_extend hd).comp contMDiffOn_snd (fun q hq => (hUd hq).2)
  have harg : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3).tangent ∞
      (fun q : Time × M => (⟨(d.extend (𝓡∂ 3)) q.2,
        (NormedSpace.fromTangentSpace ((d.extend (𝓡∂ 3)) q.2)).symm (V q)⟩ :
          TangentBundle 𝓘(ℝ,Euc 3) (Euc 3))) U :=
    by
      have hp := hcoords.prodMk hV
      rw [chartedSpaceSelf_prod] at hp
      have hb := (tangentBundleModelSpaceDiffeomorph 𝓘(ℝ,Euc 3) (⊤ : ℕ∞)).symm.contMDiff.comp_contMDiffOn
        hp
      apply hb.congr
      intro q hq
      rfl
  have hs := htm.comp harg (fun q hq => (d.extend (𝓡∂ 3)).map_source (by simpa using (hUd hq).2))
  have hY : ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 3)) (𝓡∂ 3).tangent ∞
      (fun q => (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M)) U := by
    apply hs.congr
    intro q hq
    change (⟨q.2,Y q⟩ : TangentBundle (𝓡∂ 3) M) =
      ⟨(d.extend (𝓡∂ 3)).symm ((d.extend (𝓡∂ 3)) q.2),_⟩
    rw [(d.extend (𝓡∂ 3)).left_inv (by simpa using (hUd hq).2)]
    rfl
  have hder (q : Time × M) (hq : q ∈ U) :
      mfderivWithin 𝓘(ℝ,Euc 3) (𝓡∂ 3) (d.extend (𝓡∂ 3)).symm
        (d.extend (𝓡∂ 3)).target ((d.extend (𝓡∂ 3)) q.2) =
      mfderivWithin 𝓘(ℝ,Euc 3) (𝓡∂ 3) (d.extend (𝓡∂ 3)).symm
        (range (𝓡∂ 3)) ((d.extend (𝓡∂ 3)) q.2) := by
    exact (mdifferentiableWithinAt_extend_symm
      (IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) hd)
      ((d.extend (𝓡∂ 3)).map_source (by simpa using (hUd hq).2))).mfderivWithin_mono
      (hdu _ ((d.extend (𝓡∂ 3)).map_source (by simpa using (hUd hq).2)))
      d.extend_target_subset_range
  refine ⟨Y,hY,?_,?_⟩
  · intro q hq
    have h := mfderiv_extend_comp_mfderivWithin_extend_symm'
      (IsManifold.maximalAtlas_subset_of_le (by simp : (1 : ℕ∞ω) ≤ ∞) hd)
      (show q.2 ∈ (d.extend (𝓡∂ 3)).source by simpa using (hUd hq).2)
    have hv := congrArg (fun L => L ((NormedSpace.fromTangentSpace ((d.extend (𝓡∂ 3)) q.2)).symm (V q))) h
    dsimp only [Y]
    rw [hder q hq]
    exact hv
  · intro q hq hqb hv
    rw [inwardCoordinate_eq]
    dsimp only [Y]
    rw [hder q hq]
    exact chart_inverse_boundary_differential d hd (hUd hq).2 hqb (V q) hv

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
