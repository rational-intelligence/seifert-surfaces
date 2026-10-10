import A5NormalizedBoundaryStraightener
import A5RelativeHalfdiscInverse

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity

/-- Straightening the actual smooth boundary trace of a regular C1 image
produces C1 half-space coordinates with the exact same trace. The sign of
the inward coordinate is derived from the normalized native derivative. -/
theorem C1_halfdisc_straightened_boundary_coordinates
    (ρ : ℝ) (hρ : 0 < ρ) (f : E2 → E3)
    (hf : ContDiffOn ℝ 1 f (closedHalfDisc ρ))
    (P : E3 →L[ℝ] E2)
    (hP : ∀ v, P (fderivWithin ℝ f (closedHalfDisc ρ) 0 v) = v)
    (γ : ℝ → E3) (I : Set ℝ) (hI : IsOpen I) (hI0 : (0 : ℝ) ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (hγ0 : γ 0 = f 0)
    (a : ℝ) (ha : a ≠ 0)
    (hdγ : HasDerivAt γ
      (fderivWithin ℝ f (closedHalfDisc ρ) 0 (a • coordinateVector 2 1)) 0)
    (hcover : ∀ J ∈ 𝓝 (0 : ℝ), ∀ᶠ z in 𝓝[closedHalfDisc ρ] (0 : E2),
      z 0 = 0 → ∃ t ∈ J, f z = γ t) :
    ∃ d : OpenPartialHomeomorph E2 E2,
      P (f 0) ∈ d.source ∧ d (P (f 0)) = 0 ∧
      (∀ z, d.symm z = P (γ (z 1)) + z 0 • coordinateVector 2 0) ∧
      ContDiffOn ℝ ∞ d d.source ∧ ContDiffOn ℝ ∞ d.symm d.target ∧
      ∃ e : OpenPartialHomeomorph (EuclideanHalfSpace 2) (EuclideanHalfSpace 2),
        0 ∈ e.source ∧ e 0 = 0 ∧
        (∀ z ∈ e.source, (𝓡∂ 2) z ∈ closedHalfDisc ρ ∧
          P (f ((𝓡∂ 2) z)) ∈ d.source ∧
          (𝓡∂ 2) (e z) = d (P (f ((𝓡∂ 2) z)))) ∧
        (∀ z ∈ e.source, ((𝓡∂ 2) (e z)) 0 = 0 ↔ ((𝓡∂ 2) z) 0 = 0) ∧
        ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 e e.source ∧
        ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) 1 e.symm e.target ∧
        (∀ z ∈ e.source, ((𝓡∂ 2) z) 0 = 0 →
          ((𝓡∂ 2) (e z)) 1 ∈ I ∧
          f ((𝓡∂ 2) z) = γ (((𝓡∂ 2) (e z)) 1)) := by
  have hzρ : (0 : E2) ∈ closedHalfDisc ρ :=
    ⟨Metric.mem_closedBall_self hρ.le,by simp⟩
  let D := fderivWithin ℝ f (closedHalfDisc ρ) 0
  have hpg : HasDerivAt (P ∘ γ) (a • coordinateVector 2 1) 0 := by
    simpa only [hP] using P.hasFDerivAt.comp_hasDerivAt 0 hdγ
  obtain ⟨d,hds,hdzero,hdinv,hdI,hd,hdi,hdr,_,hdin,ε,hε,hclock⟩ :=
    smooth_boundary_straightener_preserves_inward_jet (P ∘ γ) I hI hI0
      (P.contDiff.comp_contDiffOn hγ) a ha hpg
  have hds' : P (f 0) ∈ d.source := by simpa only [Function.comp_apply,hγ0] using hds
  have hdz' : d (P (f 0)) = 0 := by simpa only [Function.comp_apply,hγ0] using hdzero
  have hdj : fderiv ℝ d (P (f 0)) (coordinateVector 2 0) = coordinateVector 2 0 := by
    simpa only [Function.comp_apply,hγ0] using hdin
  have hnear : ∀ᶠ z in 𝓝[closedHalfDisc ρ] (0 : E2),
      P (f z) ∈ d.source ∧
      (z 0 = 0 → ∃ t ∈ I ∩ Ioo (-ε) ε, f z = γ t) := by
    have hh : ∀ᶠ z in 𝓝[closedHalfDisc ρ] (0 : E2), P (f z) ∈ d.source :=
      (P.continuous.continuousAt.comp_continuousWithinAt (hf.continuousOn 0 hzρ)).preimage_mem_nhdsWithin
        (d.open_source.mem_nhds hds')
    exact hh.and
      (hcover (I ∩ Ioo (-ε) ε) (inter_mem (hI.mem_nhds hI0) (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε)))
  obtain ⟨δ,hδ,hδnear⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let r := min ρ δ / 2
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min hρ hδ) (by norm_num)
  have hrρ : r ≤ ρ := by dsimp [r]; linarith [min_le_left ρ δ,lt_min hρ hδ]
  have hrδ : r < δ := by dsimp [r]; linarith [min_le_right ρ δ,lt_min hρ hδ]
  have hsub : closedHalfDisc r ⊆ closedHalfDisc ρ := closedHalfDisc_mono hrρ
  have hlocal (z : E2) (hz : z ∈ closedHalfDisc r) :
      P (f z) ∈ d.source ∧
      (z 0 = 0 → ∃ t ∈ I ∩ Ioo (-ε) ε, f z = γ t) :=
    hδnear ⟨Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hz.1).trans_lt hrδ),hsub hz⟩
  let ψ : E2 → E2 := d ∘ P ∘ f
  have hψ : ContDiffOn ℝ 1 ψ (closedHalfDisc r) :=
    (hd.of_le (by simp)).comp (P.contDiff.comp_contDiffOn (hf.mono hsub))
      (fun z hz => (hlocal z hz).1)
  have hψzero : ψ 0 = 0 := hdz'
  have htrace (z : E2) (hz : z ∈ closedHalfDisc r) (hz0 : z 0 = 0) : ψ z 0 = 0 := by
    obtain ⟨t,ht,hzt⟩ := (hlocal z hz).2 hz0
    have hdt := (hclock t ht.2).2
    simp only [Function.comp_apply] at hdt
    change d (P (f z)) 0 = 0
    rw [hzt,hdt]
    simp [coordinateVector,EuclideanSpace.single]
  have hPD : P.comp D = ContinuousLinearMap.id ℝ E2 := by
    apply ContinuousLinearMap.ext
    intro z
    exact hP z
  have hfD : HasFDerivWithinAt f D (closedHalfDisc r) 0 :=
    ((hf.differentiableOn (by norm_num) 0 hzρ).hasFDerivWithinAt).mono hsub
  have hψD : HasFDerivWithinAt ψ (fderiv ℝ d (P (f 0))) (closedHalfDisc r) 0 := by
    have hh := ((hd.contDiffAt (d.open_source.mem_nhds hds')).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasFDerivWithinAt 0 (P.hasFDerivAt.comp_hasFDerivWithinAt 0 hfD)
    simpa only [hPD,ContinuousLinearMap.comp_id] using hh
  have hψder : fderivWithin ℝ ψ (closedHalfDisc r) 0 = fderiv ℝ d (P (f 0)) :=
    hψD.fderivWithin (closedHalfDisc_uniqueDiffOn hr 0 ⟨Metric.mem_closedBall_self hr.le,by simp⟩)
  obtain ⟨e,he0,hez,hemap,heb,he,hei⟩ :=
    C1_closed_halfdisc_local_inverse r hr ψ hψ hψzero htrace
      (by rw [hψder]; exact hdr _ hds')
      (by rw [hψder,hdj]; simp [coordinateVector,EuclideanSpace.single])
  refine ⟨d,hds',hdz',hdinv,hd,hdi,e,he0,hez,?_,heb,he,hei,?_⟩
  · intro z hz
    exact ⟨hsub (hemap z hz).1,(hlocal _ (hemap z hz).1).1,(hemap z hz).2⟩
  · intro z hz hz0
    obtain ⟨t,ht,hzt⟩ := (hlocal _ (hemap z hz).1).2 hz0
    have heqt : (𝓡∂ 2) (e z) = t • coordinateVector 2 1 := by
      rw [(hemap z hz).2]
      change d (P (f ((𝓡∂ 2) z))) = _
      rw [hzt]
      exact (hclock t ht.2).2
    have het : ((𝓡∂ 2) (e z)) 1 = t := by
      rw [heqt]
      simp [coordinateVector,EuclideanSpace.single]
    exact ⟨het.symm ▸ ht.1,het.symm ▸ hzt⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
