import A5LocalHalfspaceSign
import A5HalfspaceCoordinateRestriction

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates

/-- The C1 inverse function theorem with a flat boundary trace produces
actual half-space coordinates. The boundary and the original coordinate
map are preserved; the local side condition is derived from the inward
derivative. -/
theorem C1_halfspace_local_inverse_of_flat_trace
    (Q : E2 → E2) (U : Set E2) (hU : IsOpen U) (hzero : (0 : E2) ∈ U)
    (hQ : ContDiffOn ℝ 1 Q U) (hQzero : Q 0 = 0)
    (htrace : ∀ s : ℝ, s • coordinateVector 2 1 ∈ U →
      Q (s • coordinateVector 2 1) 0 = 0)
    (hrank : Function.Bijective (fderiv ℝ Q 0))
    (hder : 0 < fderiv ℝ (fun z => Q z 0) 0 (coordinateVector 2 0)) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      0 ∈ d.source ∧ d 0 = 0 ∧
      (∀ z ∈ d.source, (𝓡∂ 2) z ∈ U ∧ (𝓡∂ 2) (d z) = Q ((𝓡∂ 2) z)) ∧
      (∀ z ∈ d.source, ((𝓡∂ 2) (d z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 d.symm d.target := by
  have hp : ContDiffOn ℝ 1 (fun z => Q z 0) U :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp_contDiffOn hQ
  obtain ⟨ε,hε,hsgn⟩ := local_halfspace_sign_of_C1_flat_trace
    (fun z => Q z 0) U hU hzero hp htrace hder
  let A : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective (fderiv ℝ Q 0)
    (LinearMap.ker_eq_bot.mpr hrank.1) (LinearMap.range_eq_top.mpr hrank.2)
  have hq0 := hQ.contDiffAt (hU.mem_nhds hzero)
  have hd : HasFDerivAt Q (A : E2 →L[ℝ] E2) 0 :=
    (hq0.differentiableAt (by simp)).hasFDerivAt
  let e₀ := hq0.toOpenPartialHomeomorph Q hd (by simp)
  have he0 : (0 : E2) ∈ e₀.source := hq0.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hi0 : ContDiffAt ℝ 1 e₀.symm (Q 0) := hq0.to_localInverse hd (by simp)
  obtain ⟨V,hV,hVi⟩ := hi0.contDiffOn (m := 1) le_rfl (by norm_num)
  let B : Set E2 := {z | |z 0| < ε ∧ |z 1| < ε}
  have hB : IsOpen B := by
    exact (isOpen_lt (EuclideanSpace.proj 0).continuous.abs continuous_const).inter
      (isOpen_lt (EuclideanSpace.proj 1).continuous.abs continuous_const)
  have hBzero : (0 : E2) ∈ B := by exact ⟨by simpa using hε,by simpa using hε⟩
  have hqV : Q ⁻¹' V ∈ 𝓝 (0 : E2) := hq0.continuousAt.preimage_mem_nhds hV
  obtain ⟨W,hWsub,hW,hWzero⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem (hU.mem_nhds hzero) (hB.mem_nhds hBzero)) hqV)
  let e := e₀.restrOpen W hW
  have hex : (0 : E2) ∈ e.source := ⟨he0,hWzero⟩
  have heQ : (e : E2 → E2) = Q := rfl
  have heU : e.source ⊆ U := fun z hz => (hWsub hz.2).1.1
  have heB : e.source ⊆ B := fun z hz => (hWsub hz.2).1.2
  have hzrep (z : E2) : z 0 • coordinateVector 2 0 + z 1 • coordinateVector 2 1 = z := by
    ext i
    fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
  have hside (z : E2) (hz : z ∈ e.source) : 0 ≤ e z 0 ↔ 0 ≤ z 0 := by
    have hh := (hsgn (z 0) (z 1) (heB hz).1 (heB hz).2).2.1
    rwa [hzrep] at hh
  have hflat (z : E2) (hz : z ∈ e.source) : e z 0 = 0 ↔ z 0 = 0 := by
    have hh := (hsgn (z 0) (z 1) (heB hz).1 (heB hz).2).2.2
    rwa [hzrep] at hh
  have hei : ContDiffOn ℝ 1 e.symm e.target := by
    apply hVi.mono
    intro z hz
    have hzW := (e.map_target hz).2
    have hVQ := (hWsub hzW).2
    change Q (e.symm z) ∈ V at hVQ
    change e (e.symm z) ∈ V at hVQ
    rwa [e.right_inv hz] at hVQ
  obtain ⟨d,hds,hdt,hde,_,hdc,hdci⟩ :=
    halfspace_coordinate_restriction e 1 (hQ.mono heU) hei hside
  have hd0 : (0 : EuclideanHalfSpace 2) ∈ d.source := by rw [hds]; exact hex
  refine ⟨d,hd0,?_,?_,?_,hdc,hdci⟩
  · apply (𝓡∂ 2).injective
    rw [hde 0 hd0]
    exact hQzero
  · intro z hz
    have hze : (𝓡∂ 2) z ∈ e.source := by rwa [hds] at hz
    exact ⟨heU hze,hde z hz⟩
  · intro z hz
    rw [hde z hz]
    exact hflat _ (by rwa [hds] at hz)

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
