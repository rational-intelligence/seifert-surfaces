import A5C1BoundaryStraightenedCoordinates

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- The inverse of the constructed relative coordinate change produces a
C1 section over a genuine closed half-disc. Its boundary is the same smooth
longitude, with the tangential coordinate now exactly its curve parameter. -/
theorem C1_straightened_halfspace_section
    (ρ : ℝ) (f : E2 → E3) (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (L : E3 ≃L[ℝ] E2 × ℝ)
    (d : OpenPartialHomeomorph E2 E2)
    (e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2))
    (he0 : (0 : EuclideanHalfSpace 2) ∈ e.source) (hez : e 0 = 0)
    (hemap : ∀ z ∈ e.source, (𝓡∂ 2) z ∈ closedHalfDisc ρ ∧
      (L (f ((𝓡∂ 2) z))).1 ∈ d.source ∧
      (𝓡∂ 2) (e z) = d (L (f ((𝓡∂ 2) z))).1)
    (heb : ∀ z ∈ e.source, ((𝓡∂ 2) (e z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0)
    (hei : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 e.symm e.target)
    (γ : ℝ → E3)
    (hetrace : ∀ z ∈ e.source, ((𝓡∂ 2) z) 0 = 0 →
      f ((𝓡∂ 2) z) = γ (((𝓡∂ 2) (e z)) 1)) :
    let q : E2 → E3 := fun z => L.symm (z,
      (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).2)
    ∃ r : ℝ, 0 < r ∧
      MapsTo (𝓡∂ 2).symm (closedHalfDisc r) e.target ∧
      ContDiffOn ℝ 1 q (closedHalfDisc r) ∧
      (∀ z, (L (q z)).1 = z) ∧
      (∀ z ∈ closedHalfDisc r,
        (𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z)) ∈ closedHalfDisc ρ ∧
        (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).1 ∈ d.source ∧
        q z = L.symm (d (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).1,
          (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).2)) ∧
      (∀ z ∈ closedHalfDisc r, z 0 = 0 →
        q z = L.symm (z,(L (γ (z 1))).2)) := by
  dsimp only
  let q : E2 → E3 := fun z => L.symm (z,
    (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).2)
  have hzero : (0 : EuclideanHalfSpace 2) ∈ e.target := hez ▸ e.map_source he0
  let U := (𝓡∂ 2).symm ⁻¹' e.target
  have hU : IsOpen U := e.open_target.preimage (𝓡∂ 2).continuous_symm
  have hzU : (0 : E2) ∈ U := by
    change (𝓡∂ 2).symm ((𝓡∂ 2) (0 : EuclideanHalfSpace 2)) ∈ e.target
    rwa [ModelWithCorners.left_inv]
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzU)
  let r := R / 2
  have hr : 0 < r := div_pos hR (by norm_num)
  have hmap (z : E2) (hz : z ∈ closedHalfDisc r) : (𝓡∂ 2).symm z ∈ e.target := by
    apply hRU
    apply Metric.mem_ball.mpr
    have hh := Metric.mem_closedBall.mp hz.1
    dsimp [r] at hh
    linarith
  have hright (z : E2) (hz : z ∈ closedHalfDisc r) : (𝓡∂ 2) ((𝓡∂ 2).symm z) = z :=
    (𝓡∂ 2).right_inv (by rw [range_modelWithCornersEuclideanHalfSpace]; exact hz.2)
  have hfhalf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) 1 (f ∘ (𝓡∂ 2)) e.source :=
    hf.contMDiffOn.comp (𝓡∂ 2).contMDiff.contMDiffOn (fun z hz => (hemap z hz).1)
  have hfinv : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) 1 (f ∘ (𝓡∂ 2) ∘ e.symm) e.target :=
    hfhalf.comp hei (fun z hz => e.map_target hz)
  let qhalf : EuclideanHalfSpace 2 → E3 := fun z => L.symm ((𝓡∂ 2) z,
    (L (f ((𝓡∂ 2) (e.symm z)))).2)
  have hqhalf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,E3) 1 qhalf e.target := by
    exact L.symm.contDiff.contMDiff.comp_contMDiffOn
      ((𝓡∂ 2).contMDiff.contMDiffOn.prodMk_space
        (((ContinuousLinearMap.snd ℝ E2 ℝ).comp L.toContinuousLinearMap).contDiff.contMDiff.comp_contMDiffOn hfinv))
  have hqs : ContDiffOn ℝ 1 q (closedHalfDisc r) := by
    have hh := hqhalf.comp
      ((𝓡∂ 2).contMDiffOn_symm.mono
        (show closedHalfDisc r ⊆ range (𝓡∂ 2) from fun z hz => by
          rw [range_modelWithCornersEuclideanHalfSpace]; exact hz.2))
      (fun z hz => hmap z hz)
    apply hh.contDiffOn.congr
    intro z hz
    change L.symm (z,_) = L.symm ((𝓡∂ 2) ((𝓡∂ 2).symm z),_)
    rw [hright z hz]
  refine ⟨r,hr,hmap,hqs,fun z => congrArg Prod.fst (L.apply_symm_apply _),?_,?_⟩
  · intro z hz
    have hy := hemap _ (e.map_target (hmap z hz))
    have heq : z = d (L (f ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))))).1 := by
      simpa only [e.right_inv (hmap z hz),hright z hz] using hy.2.2
    exact ⟨hy.1,hy.2.1,congrArg L.symm (Prod.ext heq rfl)⟩
  · intro z hz hz0
    have hflat : ((𝓡∂ 2) (e.symm ((𝓡∂ 2).symm z))) 0 = 0 := by
      apply (heb _ (e.map_target (hmap z hz))).mp
      rw [e.right_inv (hmap z hz),hright z hz]
      exact hz0
    have hh := hetrace _ (e.map_target (hmap z hz)) hflat
    rw [e.right_inv (hmap z hz),hright z hz] at hh
    change L.symm (z,_) = _
    rw [hh]

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
