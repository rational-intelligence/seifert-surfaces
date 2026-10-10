import B1ActualInteriorSlice_v475
import B1InteriorGraphOfProjection_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The transition between two constructed smooth ambient slice charts is
an actual local Euclidean diffeomorphism. Its restriction to the zero sheet
is a genuine rank-two parametrization on an open planar domain. -/
theorem native_interior_slice_transition_v475
    (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (hΨ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Ψ Ψ.source)
    (hΨi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Ψ.symm Ψ.target) :
    let U := {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source}
    let P := fun z : E2 => Φ (Ψ.symm (z,0))
    IsOpen U ∧ ContDiffOn ℝ ∞ P U ∧ ∀ z ∈ U, Function.Injective (fderiv ℝ P z) := by
  let T := Ψ.target ∩ Ψ.symm ⁻¹' Φ.source
  have hT : IsOpen T := Ψ.continuousOn_symm.isOpen_inter_preimage Ψ.open_target Φ.open_source
  let T' := Φ.target ∩ Φ.symm ⁻¹' Ψ.source
  have hT' : IsOpen T' := Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target Ψ.open_source
  let F : E2 × ℝ → E2 × ℝ := Φ ∘ Ψ.symm
  let G : E2 × ℝ → E2 × ℝ := Ψ ∘ Φ.symm
  have hF : ContDiffOn ℝ ∞ F T := contMDiffOn_iff_contDiffOn.mp
    (hΦ.comp (hΨi.mono inter_subset_left) (fun y hy => hy.2))
  have hG : ContDiffOn ℝ ∞ G T' := contMDiffOn_iff_contDiffOn.mp
    (hΨ.comp (hΦi.mono inter_subset_left) (fun y hy => hy.2))
  let ι : E2 →L[ℝ] (E2 × ℝ) := ContinuousLinearMap.inl ℝ E2 ℝ
  let U := ι ⁻¹' T
  let P := F ∘ ι
  have hU : IsOpen U := hT.preimage ι.continuous
  have hP : ContDiffOn ℝ ∞ P U := hF.comp ι.contDiff.contDiffOn (fun z hz => hz)
  refine ⟨hU,hP,?_⟩
  intro z hz
  have hzT : ι z ∈ T := hz
  have hFz : F (ι z) ∈ T' := by
    refine ⟨Φ.map_source hzT.2,?_⟩
    change Φ.symm (Φ (Ψ.symm (ι z))) ∈ Ψ.source
    rw [Φ.left_inv hzT.2]
    exact Ψ.map_target hzT.1
  have hFd : DifferentiableAt ℝ F (ι z) := (hF.contDiffAt (hT.mem_nhds hzT)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G (F (ι z)) := (hG.contDiffAt (hT'.mem_nhds hFz)).differentiableAt (by simp)
  have hId : (fun w : E2 × ℝ => w) =ᶠ[𝓝 (ι z)] G ∘ F := by
    filter_upwards [hT.mem_nhds hzT] with w hw
    change w=Ψ (Φ.symm (Φ (Ψ.symm w)))
    rw [Φ.left_inv hw.2,Ψ.right_inv hw.1]
  have hchain := (hGd.hasFDerivAt.comp (ι z) hFd.hasFDerivAt).congr_of_eventuallyEq hId
  have hprod : (fderiv ℝ G (F (ι z))).comp (fderiv ℝ F (ι z))=ContinuousLinearMap.id ℝ (E2 × ℝ) :=
    hchain.unique (hasFDerivAt_id (ι z))
  have hFi : Function.Injective (fderiv ℝ F (ι z)) := by
    intro v w h
    have hh := congrArg (fun L : (E2 × ℝ) →L[ℝ] (E2 × ℝ) => L v) hprod
    have hk := congrArg (fun L : (E2 × ℝ) →L[ℝ] (E2 × ℝ) => L w) hprod
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using
      hh.symm.trans ((congrArg (fderiv ℝ G (F (ι z))) h).trans hk)
  change Function.Injective (fderiv ℝ (F ∘ ι) z)
  rw [fderiv_comp z hFd ι.differentiableAt, ι.fderiv]
  exact hFi.comp (fun v w h => show v=w from congrArg Prod.fst h)

#print axioms native_interior_slice_transition_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
