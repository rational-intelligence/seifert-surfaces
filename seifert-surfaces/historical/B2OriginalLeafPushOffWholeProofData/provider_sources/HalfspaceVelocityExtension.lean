import HalfspaceFlow
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section

/-- Extend a smooth half-space field to Euclidean space. Boundary tangency is
retained because the extension agrees on the entire closed half-space. -/
theorem exists_contDiff_boundary_velocity_extension
    (G : ℝ × EuclideanHalfSpace 3 → Euc 3)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞ G)
    (hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0) :
    ∃ X : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ X ∧
      (∀ t z, X (t,(𝓡∂ 3) z) = G (t,z)) ∧
      ∀ t z, z 0 = 0 → X (t,z) 0 = 0 := by
  let f : ℝ × Euc 3 → Euc 3 := fun p => G (p.1, (𝓡∂ 3).symm p.2)
  have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Euc 3))
      (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) ∞
      (fun p : ℝ × Euc 3 => (p.1,(𝓡∂ 3).symm p.2))
      (univ ×ˢ range (𝓡∂ 3)) :=
    contMDiff_fst.contMDiffOn.prodMk
      ((𝓡∂ 3).contMDiffOn_symm.comp contMDiff_snd.contMDiffOn (fun _ hp => hp.2))
  have hf : ContDiffOn ℝ ∞ f (univ ×ˢ range (𝓡∂ 3)) := by
    have hm := hG.comp_contMDiffOn hΨ
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hm
    exact hm.contDiffOn
  let k : ℝ × (ℝ × (Fin 2 → ℝ)) → ℝ × Euc 3 :=
    fun p => (p.2.1, splitAmbient (p.1,p.2.2))
  let j : ℝ × Euc 3 → ℝ × (ℝ × (Fin 2 → ℝ)) :=
    fun p => ((splitAmbient.symm p.2).1, (p.1,(splitAmbient.symm p.2).2))
  have hk : ContDiff ℝ ∞ k :=
    contDiff_snd.fst.prodMk (splitAmbient.contDiff.comp
      (contDiff_fst.prodMk contDiff_snd.snd))
  have hj : ContDiff ℝ ∞ j :=
    (splitAmbient.symm.contDiff.comp contDiff_snd).fst.prodMk
      (contDiff_fst.prodMk (splitAmbient.symm.contDiff.comp contDiff_snd).snd)
  have hkj (p : ℝ × Euc 3) : k (j p) = p := by
    change (p.1,splitAmbient (splitAmbient.symm p.2)) = p
    rw [splitAmbient.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k) (Ici 0 ×ˢ univ) := by
    apply hf.comp hk.contDiffOn
    intro p hp
    refine ⟨mem_univ _,?_⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ splitAmbient (p.1,p.2.2) 0
    rw [splitAmbient_zero]
    exact hp.1
  obtain ⟨Y,hY,hYf⟩ := hread.exists_contDiff_extension_Ici_prod
  refine ⟨Y ∘ j,hY.comp hj,?_,?_⟩
  · intro t z
    have hz : j (t,(𝓡∂ 3) z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × (Fin 2 → ℝ))) := by
      refine ⟨?_,mem_univ _⟩
      change 0 ≤ (splitAmbient.symm ((𝓡∂ 3) z)).1
      rw [← splitAmbient_zero, splitAmbient.apply_symm_apply]
      exact z.property
    change Y (j (t,(𝓡∂ 3) z)) = G (t,z)
    rw [hYf hz]
    change f (k (j (t,(𝓡∂ 3) z))) = G (t,z)
    rw [hkj]
    change G (t,(𝓡∂ 3).symm ((𝓡∂ 3) z)) = G (t,z)
    rw [(𝓡∂ 3).left_inv]
  · intro t z hz
    have hzm : z ∈ range (𝓡∂ 3) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ z 0
      rw [hz]
    have hjz : j (t,z) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × (Fin 2 → ℝ))) := by
      refine ⟨?_,mem_univ _⟩
      change 0 ≤ (splitAmbient.symm z).1
      rw [← splitAmbient_zero, splitAmbient.apply_symm_apply, hz]
    change Y (j (t,z)) 0 = 0
    rw [hYf hjz]
    change f (k (j (t,z))) 0 = 0
    rw [hkj]
    apply hGb t ((𝓡∂ 3).symm z)
    rw [(𝓡∂ 3).right_inv hzm]
    exact hz

/-- A compact cutoff creates the Euclidean field required by the paid flow
provider while preserving boundary tangency and agreement where it equals one. -/
theorem exists_contDiff_compact_boundary_velocity_extension
    (G : ℝ × EuclideanHalfSpace 3 → Euc 3)
    (hG : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞ G)
    (hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0)
    (χ : ℝ × Euc 3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ X : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
      tsupport X ⊆ tsupport χ ∧
      (∀ t z, χ (t,(𝓡∂ 3) z) = 1 → X (t,(𝓡∂ 3) z) = G (t,z)) ∧
      ∀ t z, z 0 = 0 → X (t,z) 0 = 0 := by
  obtain ⟨X,hX,hXe,hXb⟩ := exists_contDiff_boundary_velocity_extension G hG hGb
  refine ⟨fun p => χ p • X p,hχ.smul hX,hχc.smul_right,
    tsupport_smul_subset_left χ X,?_,?_⟩
  · intro t z hχone
    change χ (t,(𝓡∂ 3) z) • X (t,(𝓡∂ 3) z) = G (t,z)
    rw [hχone,one_smul,hXe]
  · intro t z hz
    simp only [PiLp.smul_apply, hXb t z hz, smul_eq_mul, mul_zero]

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
