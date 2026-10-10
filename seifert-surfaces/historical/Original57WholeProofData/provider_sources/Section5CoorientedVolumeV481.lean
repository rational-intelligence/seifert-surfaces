import Section5GeometricDefinitions
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

def coorientedSphereForm (f n : S → Euc 4) (x : S) :
    TangentSpace (𝓡∂ 2) x [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (((EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det.curryLeft (f x)).curryLeft (n x)).compLinearMap
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f x).toLinearMap

/-- The actual contraction of the ambient determinant has smooth coefficients
in every native halfspace chart; this supplies the regularity needed by the
one-sided collar orientation construction. -/
theorem cooriented_sphere_form_smooth (f n : S → Euc 4)
    (hf : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ f)
    (hn : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ n) (p : S) :
    ContDiffOn ℝ ∞
      (fun y : Euc 2 => coorientedSphereForm f n ((extChartAt (𝓡∂ 2) p).symm y)
        (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
          (extChartAt (𝓡∂ 2) p).target y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1))))
      (extChartAt (𝓡∂ 2) p).target := by
  let e := extChartAt (𝓡∂ 2) p
  let F : Euc 2 → Euc 4 := f ∘ e.symm
  let N : Euc 2 → Euc 4 := n ∘ e.symm
  have hF : ContDiffOn ℝ ∞ F e.target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hN : ContDiffOn ℝ ∞ N e.target :=
    (hn.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hdF : ContDiffOn ℝ ∞ (fderivWithin ℝ F e.target) e.target :=
    hF.fderivWithin (uniqueDiffOn_extChartAt_target p) (by simp)
  let V : Euc 2 → Fin 4 → Euc 4 := fun y =>
    Fin.cons (F y) (Fin.cons (N y) (fun i => fderivWithin ℝ F e.target y (EuclideanSpace.single i 1)))
  have hV : ∀ i : Fin 4, ContDiffOn ℝ ∞ (fun y => V y i) e.target := by
    intro i
    refine Fin.cases hF (fun j => ?_) i
    exact Fin.cases hN (fun k => hdF.clm_apply contDiffOn_const) j
  have hdet : ContDiffOn ℝ ∞
      (fun y => (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det (V y)) e.target := by
    simp only [Module.Basis.det_apply, Matrix.det_apply]
    apply ContDiffOn.sum
    intro σ hσ
    simp only [Units.smul_def, zsmul_eq_mul]
    apply contDiffOn_const.mul
    apply contDiffOn_prod
    intro i hi
    exact (EuclideanSpace.proj (σ i)).contDiff.comp_contDiffOn (hV i)
  apply hdet.congr
  intro y hy
  have hchain := mfderiv_comp_mfderivWithin y (hf.mdifferentiableAt (by simp))
    ((contMDiffOn_extChartAt_symm (n := (∞ : ℕ∞ω)) p y hy).mdifferentiableWithinAt (by simp))
    ((uniqueDiffOn_extChartAt_target p y hy).uniqueMDiffWithinAt)
  have hvec (i : Fin 2) :
      mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f (e.symm y)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1))) =
        fderivWithin ℝ F e.target y (EuclideanSpace.single i 1) := by
    rw [mfderivWithin_eq_fderivWithin] at hchain
    have h := congrArg (fun L => L ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm
      (EuclideanSpace.single i 1))) hchain
    change fderivWithin ℝ F e.target y (EuclideanSpace.single i 1) =
      mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f (e.symm y)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1))) at h
    exact h.symm
  change (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det
    (Matrix.vecCons (f (e.symm y)) (Matrix.vecCons (n (e.symm y))
      (fun i => mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 4) f (e.symm y)
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target y
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1)))))) = _
  simp_rw [hvec]
  rfl

/-- A nowhere-zero contracted determinant gives the required literal smooth
orientation, with no replacement of the existing surface atlas. -/
theorem cooriented_sphere_volume_orientation (f n : S → Euc 4)
    (hf : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ f)
    (hn : ContMDiff (𝓡∂ 2) 𝓘(ℝ, Euc 4) ∞ n)
    (hvol : ∀ x, coorientedSphereForm f n x ≠ 0) :
    Nonempty (SmoothVolumeOrientation (𝓡∂ 2) S) := by
  exact ⟨{form := coorientedSphereForm f n
          nowhere_zero := hvol
          smooth_coefficients := cooriented_sphere_form_smooth f n hf hn}⟩

#print axioms cooriented_sphere_form_smooth
#print axioms cooriented_sphere_volume_orientation
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
