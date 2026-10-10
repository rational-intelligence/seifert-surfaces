import A7StandardPlaneV464
import A7BoundaryCompletionV464
import A7HalfSpaceRestrictionV464
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function Filter
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

def straighteningChart (e : OpenPartialHomeomorph (E2 × ℝ) E3) :
    OpenPartialHomeomorph E3 E3 :=
  e.symm.trans standardPlaneEquiv.toHomeomorph.toOpenPartialHomeomorph

theorem local_normal_extension {g : E2 → E3} (hg : ContDiff ℝ ∞ g)
    {a : E2} {L : E2 →L[ℝ] E3} (hd : HasFDerivAt g L a)
    (n : E3) (A : (E2 × ℝ) ≃L[ℝ] E3)
    (hA : ∀ q, A q = L q.1 + q.2 • n) :
    ∃ e : OpenPartialHomeomorph (E2 × ℝ) E3,
      (a,0) ∈ e.source ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ q, e q = g q.1 + q.2 • n) := by
  let Ψ : E2 × ℝ → E3 := fun q => g q.1 + q.2 • n
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (hg.comp contDiff_fst).add (contDiff_snd.smul contDiff_const)
  let N : E2 × ℝ →L[ℝ] E3 := (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight n
  have hdΨ : HasFDerivAt Ψ A.toContinuousLinearMap (a,0) := by
    have h := (hd.comp (a,(0:ℝ)) hasFDerivAt_fst).add (N.hasFDerivAt (x := (a,(0:ℝ))))
    have he : L.comp (ContinuousLinearMap.fst ℝ E2 ℝ) + N = A := by
      apply ContinuousLinearMap.ext
      intro q
      exact (hA q).symm
    rwa [he] at h
  obtain ⟨e,hea,_,he,hei,heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hΨ.contDiffOn isOpen_univ (mem_univ _) hdΨ
  exact ⟨e,hea,he,hei,heq⟩

theorem straighteningChart_smooth
    (e : OpenPartialHomeomorph (E2 × ℝ) E3)
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target) :
    ContDiffOn ℝ ∞ (straighteningChart e) (straighteningChart e).source ∧
      ContDiffOn ℝ ∞ (straighteningChart e).symm (straighteningChart e).target := by
  constructor
  · exact standardPlaneEquiv.contDiff.comp_contDiffOn (hei.mono inter_subset_left)
  · exact he.comp standardPlaneEquiv.symm.contDiff.contDiffOn (fun _ h => h.2)

theorem straighteningChart_graph
    {g : E2 → E3} {a : E2} {n : E3}
    (e : OpenPartialHomeomorph (E2 × ℝ) E3) (hae : (a,0) ∈ e.source)
    (heq : ∀ q, e q = g q.1 + q.2 • n) :
    g a ∈ (straighteningChart e).source ∧
      straighteningChart e (g a) = standardPlaneEquiv (a,0) ∧
      ∀ᶠ z : E2 in 𝓝 a, g z ∈ (straighteningChart e).source ∧
        straighteningChart e (g z) = standardPlaneEquiv (z,0) := by
  have hzero (z : E2) : e (z,0) = g z := by simp [heq]
  have hg (z : E2) (hz : (z,0) ∈ e.source) :
      g z ∈ (straighteningChart e).source ∧
      straighteningChart e (g z) = standardPlaneEquiv (z,0) := by
    refine ⟨⟨hzero z ▸ e.map_source hz,mem_univ _⟩,?_⟩
    change standardPlaneEquiv (e.symm (g z)) = standardPlaneEquiv (z,0)
    rw [←hzero z,e.left_inv hz]
  refine ⟨(hg a hae).1,(hg a hae).2,?_⟩
  have hz : ∀ᶠ z : E2 in 𝓝 a, (z,(0:ℝ)) ∈ e.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hae)
  filter_upwards [hz] with z hz
  exact hg z hz

theorem straighteningChart_boundary_halfspace
    {g : E2 → E3} {a : E2} {n : E3}
    (e : OpenPartialHomeomorph (E2 × ℝ) E3) (hae : (a,0) ∈ e.source)
    (heq : ∀ q, e q = g q.1 + q.2 • n) (hn : n 0 = 0)
    (hsign : ∀ᶠ z : E2 in 𝓝 a, 0 ≤ g z 0 ↔ 0 ≤ z 0) :
    ∀ᶠ y : E3 in 𝓝 (g a),
      0 ≤ straighteningChart e y 0 ↔ 0 ≤ y 0 := by
  have hea : e (a,0) = g a := by simp [heq]
  have hga : g a ∈ e.target := hea ▸ e.map_source hae
  have hei : Tendsto e.symm (𝓝 (g a)) (𝓝 (a,0)) := by
    have ht := (e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hga)).tendsto
    simpa only [←hea,e.left_inv hae] using ht
  have hp := (continuous_fst.tendsto (a,(0:ℝ))).comp hei
  filter_upwards [hp.eventually hsign,e.open_target.mem_nhds hga] with y hy hyt
  have he : e (e.symm y) = y := e.right_inv hyt
  have hy0 : y 0 = g (e.symm y).1 0 := by
    calc
      y 0 = e (e.symm y) 0 := congrArg (fun z : E3 => z 0) he.symm
      _ = g (e.symm y).1 0 := by
        rw [heq]
        simp only [PiLp.add_apply,PiLp.smul_apply,hn,smul_zero,add_zero]
  change 0 ≤ standardPlaneEquiv (e.symm y) 0 ↔ 0 ≤ y 0
  rw [standardPlaneEquiv_zero,hy0]
  exact hy.symm

theorem restrict_halfspace_straightening
    {β : OpenPartialHomeomorph E3 E3} {b : E3} (hb : b ∈ β.source)
    (hβ : ContDiffOn ℝ ∞ β β.source) (hβi : ContDiffOn ℝ ∞ β.symm β.target)
    (hh : ∀ᶠ y : E3 in 𝓝 b, 0 ≤ β y 0 ↔ 0 ≤ y 0) :
    ∃ γ : OpenPartialHomeomorph E3 E3,
      b ∈ γ.source ∧ ContDiffOn ℝ ∞ γ γ.source ∧
      ContDiffOn ℝ ∞ γ.symm γ.target ∧
      γ.IsImage (range (𝓡∂ 3)) (range (𝓡∂ 3)) ∧
      (∀ y, γ y = β y) := by
  obtain ⟨W,hW,hWo,hbW⟩ := mem_nhds_iff.mp hh
  let γ := β.restrOpen W hWo
  refine ⟨γ,⟨hb,hbW⟩,hβ.mono inter_subset_left,
    hβi.mono inter_subset_left,?_,fun _ => rfl⟩
  intro y hy
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact hW hy.2

end SeifertSurfaces.OriginalEndpoints.A7Support
