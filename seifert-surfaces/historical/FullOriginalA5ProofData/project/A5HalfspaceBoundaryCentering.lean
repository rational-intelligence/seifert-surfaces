import A5HalfspaceCoordinateRestriction

set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates

/-- Tangential translation centers any actual boundary point of the model
half-space. It preserves the full boundary and the differential rank. -/
theorem smooth_halfspace_boundary_centering
    (a : EuclideanHalfSpace 2) (ha : ((𝓡∂ 2) a) 0 = 0) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      d.source = univ ∧ d.target = univ ∧ d a = 0 ∧
      (∀ z, (𝓡∂ 2) (d z) = (𝓡∂ 2) z - (𝓡∂ 2) a) ∧
      (∀ z, (𝓡∂ 2) (d.symm z) = (𝓡∂ 2) z + (𝓡∂ 2) a) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ d.symm d.target ∧
      (∀ z, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) d z)) ∧
      (∀ z, Function.Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm z)) := by
  let e := (Homeomorph.addRight (-(𝓡∂ 2) a)).toOpenPartialHomeomorph
  have hef (z : E2) : e z = z - (𝓡∂ 2) a := rfl
  have hei (z : E2) : e.symm z = z + (𝓡∂ 2) a := by
    change z + -(-(𝓡∂ 2) a) = _
    rw [neg_neg]
  have hec : ContDiffOn ℝ ∞ e e.source :=
    (contDiff_id.sub contDiff_const).contDiffOn
  have heic : ContDiffOn ℝ ∞ e.symm e.target := by
    have hh : ContDiffOn ℝ ∞ (fun z : E2 => z + (𝓡∂ 2) a) e.target :=
      (contDiff_id.add contDiff_const).contDiffOn
    exact hh.congr (fun z _ => hei z)
  obtain ⟨d,hds,hdt,hdf,hdi,hd,hi⟩ := halfspace_coordinate_restriction e ∞ hec heic
    (fun z _ => by rw [hef]; simp only [PiLp.sub_apply,ha,sub_zero])
  have hs : d.source = univ := by rw [hds]; rfl
  have ht : d.target = univ := by rw [hdt]; rfl
  have hdf' (z : EuclideanHalfSpace 2) : (𝓡∂ 2) (d z) = (𝓡∂ 2) z - (𝓡∂ 2) a :=
    (hdf z (hs.symm ▸ mem_univ z)).trans (hef _)
  have hdi' (z : EuclideanHalfSpace 2) : (𝓡∂ 2) (d.symm z) = (𝓡∂ 2) z + (𝓡∂ 2) a :=
    (hdi z (ht.symm ▸ mem_univ z)).trans (hei _)
  have hdm : d.MDifferentiable (𝓡∂ 2) (𝓡∂ 2) :=
    ⟨hd.mdifferentiableOn (by simp),hi.mdifferentiableOn (by simp)⟩
  refine ⟨d,hs,ht,?_,hdf',hdi',hd,hi,fun z => hdm.mfderiv_injective (hs.symm ▸ mem_univ z),
    fun z => hdm.symm.mfderiv_injective (show z ∈ d.target by rw [ht]; trivial)⟩
  apply (𝓡∂ 2).injective
  rw [hdf',sub_self]
  rfl

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
