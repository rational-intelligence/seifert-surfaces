import HalfspaceVelocityExtension
import MovingCornerExtension

open scoped Manifold ContDiff
open Set Filter Topology
namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section

def ambientBoundaryProjection : Euc 3 →L[ℝ] Euc 3 :=
  ContinuousLinearMap.id ℝ (Euc 3) -
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).smulRight (EuclideanSpace.single 0 1)

@[simp] theorem ambientBoundaryProjection_normal (z : Euc 3) :
    ambientBoundaryProjection z 0 = 0 := by
  simp [ambientBoundaryProjection,PiLp.sub_apply,PiLp.smul_apply]

def halfspaceBoundaryProjection (z : EuclideanHalfSpace 3) : EuclideanHalfSpace 3 :=
  (𝓡∂ 3).symm (ambientBoundaryProjection ((𝓡∂ 3) z))

theorem halfspaceBoundaryProjection_contMDiff :
    ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ halfspaceBoundaryProjection := by
  apply (𝓡∂ 3).contMDiffOn_symm.comp_contMDiff
    (ambientBoundaryProjection.contDiff.contMDiff.comp (𝓡∂ 3).contMDiff)
  intro z
  rw [range_modelWithCornersEuclideanHalfSpace]
  change 0 ≤ ambientBoundaryProjection ((𝓡∂ 3) z) 0
  rw [ambientBoundaryProjection_normal]

@[simp] theorem halfspaceBoundaryProjection_normal (z : EuclideanHalfSpace 3) :
    (𝓡∂ 3) (halfspaceBoundaryProjection z) 0 = 0 := by
  rw [halfspaceBoundaryProjection,(𝓡∂ 3).right_inv]
  · exact ambientBoundaryProjection_normal _
  · rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ ambientBoundaryProjection ((𝓡∂ 3) z) 0
    rw [ambientBoundaryProjection_normal]

/-- Extend a closed-time halfspace field in both time and space, and repair
the extended normal component on the boundary hyperplane. The repair vanishes
on the entire original closed-time halfspace. -/
theorem exists_real_boundary_velocity_extension
    (G : Time × EuclideanHalfSpace 3 → Euc 3)
    (hG : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ G)
    (hGb : ∀ t z, (𝓡∂ 3) z 0 = 0 → G (t,z) 0 = 0) :
    ∃ X : ℝ × Euc 3 → Euc 3, ContDiff ℝ ∞ X ∧
      (∀ t : Time, ∀ z, X ((t : ℝ),(𝓡∂ 3) z) = G (t,z)) ∧
      ∀ t z, z 0 = 0 → X (t,z) 0 = 0 := by
  letI : T2Space (EuclideanHalfSpace 3) :=
    inferInstanceAs (T2Space {z : Euc 3 // 0 ≤ z 0})
  letI : SecondCountableTopology (EuclideanHalfSpace 3) :=
    inferInstanceAs (SecondCountableTopology {z : Euc 3 // 0 ≤ z 0})
  letI : LocallyCompactSpace (EuclideanHalfSpace 3) :=
    (𝓡∂ 3).locallyCompactSpace
  letI : SigmaCompactSpace (EuclideanHalfSpace 3) := inferInstance
  let P : ℝ → Time := projIcc 0 1 (by norm_num)
  let g : ℝ × EuclideanHalfSpace 3 → Euc 3 := fun q => G (P q.1,q.2)
  have hP : ContMDiffOn 𝓘(ℝ,ℝ) (𝓡∂ 1) ∞ P (Icc 0 1) := contMDiffOn_projIcc
  have hg : ContMDiffOn (𝓘(ℝ,ℝ).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ g
      (Icc 0 1 ×ˢ univ) := hG.comp_contMDiffOn
    ((hP.comp contMDiffOn_fst (fun _ hq => hq.1)).prodMk contMDiffOn_snd)
  obtain ⟨H,hH,hHeq⟩ := Manifold.exists_contMDiff_extension_Icc_halfspace hg
  let R : ℝ × EuclideanHalfSpace 3 → Euc 3 := fun q => H q -
    (H (q.1,halfspaceBoundaryProjection q.2) 0) • EuclideanSpace.single 0 1
  have hR : ContMDiff (𝓘(ℝ,ℝ).prod (𝓡∂ 3)) 𝓘(ℝ,Euc 3) ∞ R :=
    hH.sub (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.contMDiff.comp
      (hH.comp (contMDiff_fst.prodMk
        (halfspaceBoundaryProjection_contMDiff.comp contMDiff_snd)))).smul contMDiff_const)
  have hRorig (t : Time) (z : EuclideanHalfSpace 3) : R ((t : ℝ),z) = G (t,z) := by
    have hPval : P (t : ℝ) = t := by
      simpa only [P] using projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) t.property
    change H ((t : ℝ),z) - (H ((t : ℝ),halfspaceBoundaryProjection z) 0) • _ = _
    rw [hHeq ⟨t.property,mem_univ _⟩,hHeq ⟨t.property,mem_univ _⟩]
    dsimp only [g]
    rw [hPval,hGb t _ (halfspaceBoundaryProjection_normal z),zero_smul,sub_zero]
  have hRb (t : ℝ) (z : EuclideanHalfSpace 3) (hz : (𝓡∂ 3) z 0 = 0) : R (t,z) 0 = 0 := by
    have hfix : halfspaceBoundaryProjection z = z := by
      apply (𝓡∂ 3).injective
      rw [halfspaceBoundaryProjection,(𝓡∂ 3).right_inv]
      · change ambientBoundaryProjection ((𝓡∂ 3) z) = (𝓡∂ 3) z
        change (𝓡∂ 3) z - ((𝓡∂ 3) z 0) • EuclideanSpace.single 0 1 = (𝓡∂ 3) z
        rw [hz,zero_smul,sub_zero]
      · rw [range_modelWithCornersEuclideanHalfSpace]
        change 0 ≤ ambientBoundaryProjection ((𝓡∂ 3) z) 0
        rw [ambientBoundaryProjection_normal]
    simp [R,hfix,PiLp.sub_apply,PiLp.smul_apply]
  obtain ⟨X,hX,hXeq,hXb⟩ := exists_contDiff_boundary_velocity_extension R hR hRb
  exact ⟨X,hX,fun t z => (hXeq t z).trans (hRorig t z),hXb⟩

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
