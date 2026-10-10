import A5HalfspaceBoundaryCentering
import A5C1HalfspaceHalfdisc

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- Every regular native C1 half-space image chart at an arbitrary
boundary point has centered Euclidean closed-half-disc coordinates with
the same image and an injective actual within derivative. -/
theorem C1_halfspace_image_centered_halfdisc
    (f : EuclideanHalfSpace 2 → E3) (V : Set (EuclideanHalfSpace 2))
    (hV : IsOpen V) (hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) 1 f V)
    (a : EuclideanHalfSpace 2) (ha : a ∈ V) (hab : ((𝓡∂ 2) a) 0 = 0)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) f a)) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      d.source = univ ∧ d.target = univ ∧ d a = 0 ∧ d.symm 0 = a ∧
      (∀ z, (𝓡∂ 2) (d z) = (𝓡∂ 2) z - (𝓡∂ 2) a) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d.symm d.target ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        MapsTo (d.symm ∘ (𝓡∂ 2).symm) (closedHalfDisc ρ) V ∧
        ContDiffOn ℝ 1 (f ∘ d.symm ∘ (𝓡∂ 2).symm) (closedHalfDisc ρ) ∧
        Function.Injective (fderivWithin ℝ (f ∘ d.symm ∘ (𝓡∂ 2).symm)
          (closedHalfDisc ρ) 0) := by
  obtain ⟨d,hds,hdt,hda,hdf,_,hd,hdi,_,hdii⟩ := smooth_halfspace_boundary_centering a hab
  have hdia : d.symm 0 = a := by rw [← hda,d.left_inv (hds.symm ▸ mem_univ a)]
  have hdc : Continuous d.symm := continuousOn_univ.mp (hdt ▸ hdi.continuousOn)
  let U := d.symm ⁻¹' V
  have hU : IsOpen U := hV.preimage hdc
  have h0U : (0 : EuclideanHalfSpace 2) ∈ U := by change d.symm 0 ∈ V; rwa [hdia]
  have hg : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) 1 (f ∘ d.symm) U :=
    hf.comp ((hdi.of_le (by simp)).mono (fun z _ => hdt.symm ▸ mem_univ z)) (fun _ hz => hz)
  have hgi : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,E3) (f ∘ d.symm) 0) := by
    rw [mfderiv_comp _
      ((hf.contMDiffAt (hV.mem_nhds (hdia.symm ▸ ha))).mdifferentiableAt (by norm_num))
      ((hdi.contMDiffAt (d.open_target.mem_nhds (hdt.symm ▸ mem_univ 0))).mdifferentiableAt (by simp)),
      hdia]
    exact hinj.comp (hdii 0)
  obtain ⟨ρ,hρ,hmap,hreg,hrank⟩ := regular_C1_halfspace_local_halfdisc
    (f ∘ d.symm) U hU h0U hg hgi
  exact ⟨d,hds,hdt,hda,hdia,hdf,hd,hdi,ρ,hρ,hmap,hreg,hrank⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
