import A5RelativeImageTangent
import A5ManifoldHalfspaceCancellation

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- A smooth regular half-space parametrization has an ordinary smooth
Euclidean extension with the SAME actual boundary tangent differential. -/
theorem regular_halfspace_coordinate_extension
    (f : EuclideanHalfSpace 2 → Euc 3) (V : Set (EuclideanHalfSpace 2))
    (hV : IsOpen V) (hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) ∞ f V)
    (z : EuclideanHalfSpace 2) (hz : z ∈ V)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f z)) :
    ∃ G : Euc 2 → Euc 3, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[range (𝓡∂ 2)] ((𝓡∂ 2) z)] f ∘ (𝓡∂ 2).symm ∧
      Function.Injective (fderiv ℝ G ((𝓡∂ 2) z)) := by
  let U := (𝓡∂ 2).symm ⁻¹' V
  have hU : IsOpen U := hV.preimage (𝓡∂ 2).continuous_symm
  have hzU : (𝓡∂ 2) z ∈ U := by simpa only [U,mem_preimage,ModelWithCorners.left_inv] using hz
  have hs : ContDiffOn ℝ ∞ (f ∘ (𝓡∂ 2).symm) (U ∩ range (𝓡∂ 2)) :=
    (hf.comp ((𝓡∂ 2).contMDiffOn_symm.mono inter_subset_right)
      (fun y hy => hy.1)).contDiffOn
  obtain ⟨G,hG,he⟩ := SeifertSurfaces.OriginalEndpoints.A7Support.exists_contDiff_extension_halfspace_local
    hU hs hzU
  have hfd := ((hf.contMDiffAt (hV.mem_nhds hz)).mdifferentiableAt (by simp)).hasMFDerivAt.2
  change HasFDerivWithinAt (f ∘ (𝓡∂ 2).symm)
    ((tangentSpaceCastModel 𝓘(ℝ,Euc 3) (f z)).toContinuousLinearMap.comp
      ((mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f z).comp
        (tangentSpaceCastModel (𝓡∂ 2) z).symm.toContinuousLinearMap))
    (range (𝓡∂ 2)) ((𝓡∂ 2) z) at hfd
  have hu := (𝓡∂ 2).uniqueDiffOn ((𝓡∂ 2) z) (mem_range_self z)
  have hde : fderiv ℝ G ((𝓡∂ 2) z) =
      ((tangentSpaceCastModel 𝓘(ℝ,Euc 3) (f z)).toContinuousLinearMap.comp
        ((mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f z).comp
          (tangentSpaceCastModel (𝓡∂ 2) z).symm.toContinuousLinearMap)) := by
    rw [← fderivWithin_eq_fderiv hu (hG.differentiable (by simp) _)]
    rw [he.fderivWithin_eq_of_mem (mem_range_self z),hfd.fderivWithin hu]
  refine ⟨G,hG,he,?_⟩
  rw [hde]
  exact (tangentSpaceCastModel 𝓘(ℝ,Euc 3) (f z)).injective.comp
    (hinj.comp (tangentSpaceCastModel (𝓡∂ 2) z).symm.injective)

/-- Continuous relative lifts into a regular smooth half-space image preserve
the actual tangent range of any native rank-two closed-sector immersion. -/
theorem relative_tangent_range_of_halfspace_image_lift
    (g : Euc 2 → Euc 3) (f : EuclideanHalfSpace 2 → Euc 3)
    (q : Euc 2 → EuclideanHalfSpace 2) (A : Set (Euc 2)) (x : Euc 2)
    (hx : x ∈ A) (hA : UniqueDiffWithinAt ℝ A x)
    (D : Euc 2 →L[ℝ] Euc 3) (hg : HasFDerivWithinAt g D A x)
    (hD : Function.Injective D)
    (V : Set (EuclideanHalfSpace 2)) (hV : IsOpen V)
    (hf : ContMDiffOn (𝓡∂ 2) 𝓘(ℝ,Euc 3) ∞ f V)
    (hqV : q x ∈ V)
    (hinj : Function.Injective (mfderiv (𝓡∂ 2) 𝓘(ℝ,Euc 3) f (q x)))
    (hq : ContinuousWithinAt q A x)
    (heq : f ∘ q =ᶠ[𝓝[A] x] g) (hp : f (q x) = g x) :
    D.toLinearMap.range =
      (fderivWithin ℝ (f ∘ (𝓡∂ 2).symm) (range (𝓡∂ 2)) ((𝓡∂ 2) (q x))).toLinearMap.range := by
  obtain ⟨G,hG,hGeq,hGi⟩ := regular_halfspace_coordinate_extension f V hV hf (q x) hqV hinj
  let p : Euc 2 → Euc 2 := (𝓡∂ 2) ∘ q
  have hpc : ContinuousWithinAt p A x := (𝓡∂ 2).continuousAt.comp_continuousWithinAt hq
  have hpt : Tendsto p (𝓝[A] x) (𝓝[range (𝓡∂ 2)] (p x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpc,Filter.Eventually.of_forall fun y => mem_range_self _⟩
  have he : G ∘ p =ᶠ[𝓝[A] x] g := by
    have hh := (hGeq.comp_tendsto hpt).trans
      (show (f ∘ (𝓡∂ 2).symm) ∘ p =ᶠ[𝓝[A] x] f ∘ q from
        Filter.Eventually.of_forall fun y => by simp only [p,Function.comp_apply,ModelWithCorners.left_inv])
    exact hh.trans heq
  have hep : G (p x) = g x := by
    have hh := hGeq.eq_of_nhdsWithin (mem_range_self (q x))
    simpa only [p,Function.comp_apply,ModelWithCorners.left_inv,hp] using hh
  have hrange := relative_tangent_range_of_continuous_image_lift g G p A x hx hA D
    (fderiv ℝ G (p x)) hg hD (hG.differentiable (by simp) _).hasFDerivAt hGi hpc he hep
  have hu := (𝓡∂ 2).uniqueDiffOn (p x) (mem_range_self (q x))
  have hde : fderiv ℝ G (p x) =
      fderivWithin ℝ (f ∘ (𝓡∂ 2).symm) (range (𝓡∂ 2)) ((𝓡∂ 2) (q x)) := by
    rw [← fderivWithin_eq_fderiv hu (hG.differentiable (by simp) _)]
    exact hGeq.fderivWithin_eq_of_mem (mem_range_self (q x))
  rwa [hde] at hrange

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
