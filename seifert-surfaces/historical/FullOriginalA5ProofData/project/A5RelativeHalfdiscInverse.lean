import A5C1HalfspaceInverse
import A5NativeHalfspaceGraphExtension

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- The relative C1 inverse theorem on a closed half-disc constructs
genuine open half-space coordinates of the same map, including exact
boundary preservation. The ambient extension and its side control are
both proved internally. -/
theorem C1_closed_halfdisc_local_inverse
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → E2)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ)) (hfzero : f 0 = 0)
    (htrace : ∀ z ∈ closedHalfDisc ρ, z 0 = 0 → f z 0 = 0)
    (hrank : Function.Bijective (fderivWithin ℝ f (closedHalfDisc ρ) 0))
    (hder : 0 < (fderivWithin ℝ f (closedHalfDisc ρ) 0 (coordinateVector 2 0)) 0) :
    ∃ d : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
      0 ∈ d.source ∧ d 0 = 0 ∧
      (∀ z ∈ d.source, (𝓡∂ 2) z ∈ closedHalfDisc ρ ∧
        (𝓡∂ 2) (d z) = f ((𝓡∂ 2) z)) ∧
      (∀ z ∈ d.source, ((𝓡∂ 2) (d z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0) ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 d d.source ∧
      ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 d.symm d.target := by
  have hz : (0 : E2) ∈ closedHalfDisc ρ := ⟨Metric.mem_closedBall_self hρ.le,by simp⟩
  obtain ⟨g,hg,he⟩ := C1_closed_halfdisc_local_extension ρ hρ f hf
  have hg0 : g 0 = 0 := (he.eq_of_nhdsWithin hz).trans hfzero
  have hud := closedHalfDisc_uniqueDiffOn hρ 0 hz
  have hdg : fderiv ℝ g 0 = fderivWithin ℝ f (closedHalfDisc ρ) 0 := by
    rw [← fderivWithin_eq_fderiv hud (hg.differentiableAt (by norm_num))]
    exact he.fderivWithin_eq_of_mem hz
  obtain ⟨ε,hε,hεeq⟩ := Metric.mem_nhdsWithin_iff.mp he
  obtain ⟨V,hV,hVg⟩ := hg.contDiffOn (m := 1) le_rfl (by norm_num)
  obtain ⟨U,hUsub,hU,hzero⟩ := mem_nhds_iff.mp
    (inter_mem hV (Metric.ball_mem_nhds (0 : E2) (lt_min hρ hε)))
  have hUg : ContDiffOn ℝ 1 g U := hVg.mono (fun z hz => (hUsub hz).1)
  have hUH (z : E2) (hzU : z ∈ U) (hzside : 0 ≤ z 0) : z ∈ closedHalfDisc ρ :=
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball (min_le_left _ _) (hUsub hzU).2),hzside⟩
  have hUeq (z : E2) (hzU : z ∈ U) (hzside : 0 ≤ z 0) : g z = f z :=
    hεeq ⟨Metric.ball_subset_ball (min_le_right _ _) (hUsub hzU).2,hUH z hzU hzside⟩
  have hgt (s : ℝ) (hs : s • coordinateVector 2 1 ∈ U) :
      g (s • coordinateVector 2 1) 0 = 0 := by
    have hs0 : (s • coordinateVector 2 1) 0 = 0 := by
      simp [coordinateVector,EuclideanSpace.single]
    rw [hUeq _ hs hs0.ge]
    exact htrace _ (hUH _ hs hs0.ge) hs0
  have hgder : 0 < fderiv ℝ (fun z => g z 0) 0 (coordinateVector 2 0) := by
    let π := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
    have hd := π.hasFDerivAt.comp 0 (hg.differentiableAt (by norm_num)).hasFDerivAt
    have heval := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 0)) hd.fderiv
    change fderiv ℝ (fun z => g z 0) 0 (coordinateVector 2 0) =
      (fderiv ℝ g 0 (coordinateVector 2 0)) 0 at heval
    rw [heval,hdg]
    exact hder
  obtain ⟨d,hd0,hdz,hdmap,hdb,hdc,hdi⟩ :=
    C1_halfspace_local_inverse_of_flat_trace g U hU hzero hUg hg0 hgt
      (by rwa [hdg]) hgder
  refine ⟨d,hd0,hdz,?_,hdb,hdc,hdi⟩
  intro z hzD
  have hzU := (hdmap z hzD).1
  exact ⟨hUH _ hzU z.property,(hdmap z hzD).2.trans (hUeq _ hzU z.property)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
