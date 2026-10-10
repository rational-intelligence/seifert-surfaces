import A7PlaneAlgebraV464
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace SeifertSurfaces.OriginalEndpoints.A7Support
open SeifertSurfaces.AppendixACoordinates

/-- A chart which straightens the actual smooth extension while retaining its
first-order coordinates and the original source parametrization. -/
theorem euclidean_straightening {g : E2 → E3} (hg : ContDiff ℝ ∞ g)
    (a : E2) {L : E2 →L[ℝ] E3} (hd : HasFDerivAt g L a)
    (n : E3) (A : (E2 × ℝ) ≃L[ℝ] E3)
    (hA : ∀ q, A q = L q.1 + q.2 • n) :
    ∃ β : OpenPartialHomeomorph E3 E3,
      g a ∈ β.source ∧ ContDiffOn ℝ ∞ β β.source ∧
      ContDiffOn ℝ ∞ β.symm β.target ∧ β (g a) = g a ∧
      HasFDerivAt β (ContinuousLinearMap.id ℝ E3) (g a) ∧
      ∀ᶠ z : E2 in 𝓝 0, g (a+z) ∈ β.source ∧
        β (g (a+z)) = g a + L z := by
  let Ψ : E2 × ℝ → E3 := fun q => g (a+q.1) + q.2 • n
  have hΨ : ContDiff ℝ ∞ Ψ :=
    (hg.comp (contDiff_const.add contDiff_fst)).add (contDiff_snd.smul contDiff_const)
  let N : E2 × ℝ →L[ℝ] E3 := (ContinuousLinearMap.snd ℝ E2 ℝ).smulRight n
  have hdΨ : HasFDerivAt Ψ A.toContinuousLinearMap (0,0) := by
    have ht : HasFDerivAt (fun q : E2 × ℝ => a+q.1)
        (ContinuousLinearMap.fst ℝ E2 ℝ) (0,0) := by
      convert (by simpa only [zero_add] using
        ((hasFDerivAt_const (𝕜 := ℝ) (E := E2 × ℝ) a ((0:E2),(0:ℝ))).add
          (hasFDerivAt_fst (𝕜 := ℝ) (p := ((0:E2),(0:ℝ)))))) using 1 <;> rfl
    have hd0 : HasFDerivAt g L (a+(0:E2)) := by simpa using hd
    have h := (hd0.comp ((0:E2),(0:ℝ)) ht).add (N.hasFDerivAt (x := ((0:E2),(0:ℝ))))
    have he : L.comp (ContinuousLinearMap.fst ℝ E2 ℝ) + N = A := by
      apply ContinuousLinearMap.ext
      intro q
      exact (hA q).symm
    rwa [he] at h
  obtain ⟨e,he0,_,he,hei,heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hΨ.contDiffOn isOpen_univ (mem_univ _) hdΨ
  have hezero : e (0,0) = g a := by simp [heq,Ψ]
  have hga : g a ∈ e.target := hezero ▸ e.map_source he0
  let γ : OpenPartialHomeomorph (E2 × ℝ) E3 :=
    A.toHomeomorph.toOpenPartialHomeomorph.trans
      (Homeomorph.addLeft (g a)).toOpenPartialHomeomorph
  let β : OpenPartialHomeomorph E3 E3 := e.symm.trans γ
  have hβ : ContDiffOn ℝ ∞ β β.source := by
    change ContDiffOn ℝ ∞ (fun y => g a + A (e.symm y)) β.source
    exact contDiff_const.contDiffOn.add (A.contDiff.comp_contDiffOn
      (hei.mono inter_subset_left))
  have hβi : ContDiffOn ℝ ∞ β.symm β.target := by
    change ContDiffOn ℝ ∞ (fun y => e (A.symm (-g a + y))) β.target
    apply he.comp
      (A.symm.contDiff.comp (contDiff_const.add contDiff_id)).contDiffOn
    intro y hy
    exact hy.2
  have hβp : β (g a) = g a := by
    change g a + A (e.symm (g a)) = g a
    rw [← hezero, e.left_inv he0]
    simp
  have hdep : HasFDerivAt e A.toContinuousLinearMap (0,0) := by
    simpa only [show (fun q => e q) = Ψ from funext heq] using hdΨ
  have heiD : HasFDerivAt e.symm A.symm.toContinuousLinearMap (g a) := by
    apply e.hasFDerivAt_symm hga
    rwa [← hezero,e.left_inv he0]
  have hdβ : HasFDerivAt β (ContinuousLinearMap.id ℝ E3) (g a) := by
    have h := (hasFDerivAt_const (g a) (g a)).add (A.hasFDerivAt.comp (g a) heiD)
    have hid : A.toContinuousLinearMap.comp A.symm.toContinuousLinearMap =
        ContinuousLinearMap.id ℝ E3 := by ext v; simp
    convert (by simpa only [hid,zero_add] using h) using 1 <;> rfl
  refine ⟨β,⟨hga,by simp [γ]⟩,hβ,hβi,hβp,hdβ,?_⟩
  have hz : ∀ᶠ z : E2 in 𝓝 0, (z,(0:ℝ)) ∈ e.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds he0)
  filter_upwards [hz] with z hze
  have hez : e (z,0) = g (a+z) := by simp [heq,Ψ]
  refine ⟨⟨hez ▸ e.map_source hze,by simp [γ]⟩,?_⟩
  change g a + A (e.symm (g (a+z))) = g a + L z
  rw [← hez,e.left_inv hze,hA]
  simp

end SeifertSurfaces.OriginalEndpoints.A7Support
