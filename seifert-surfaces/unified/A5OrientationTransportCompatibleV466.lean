import GeometricCategory
import ExternalTransportContracts

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
universe u v

/- Mechanical namespace relocation of the paid CutHelpers transport proof.
No proof logic changed; its original import tree collides with the native topological provider. -/
def a5InverseTransportedForm {S : Type u} {Q : Type v}
    [TopologicalSpace S] [TopologicalSpace Q]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (EuclideanHalfSpace 2) Q]
    (d : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S Q ∞) (omega : SmoothVolumeOrientation (𝓡∂ 2) S)
    (y : Q) : TangentSpace (𝓡∂ 2) y [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  (omega.form (d.symm y)).compLinearMap
    (mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm y).toLinearMap

theorem a5_smooth_volume_orientation_diffeomorph_transport {S : Type u} {Q : Type v}
    [TopologicalSpace S] [TopologicalSpace Q]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (EuclideanHalfSpace 2) Q]
    [IsManifold (𝓡∂ 2) ∞ S] [IsManifold (𝓡∂ 2) ∞ Q]
    (d : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S Q ∞) (omega : SmoothVolumeOrientation (𝓡∂ 2) S) :
    ∃ omegaQ : SmoothVolumeOrientation (𝓡∂ 2) Q,
      omegaQ.form = a5InverseTransportedForm d omega ∧
      ∀ x (w : Fin 2 → TangentSpace (𝓡∂ 2) x),
        omegaQ.form (d x) (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) d x (w i)) = omega.form x w := by
  classical
  let form := a5InverseTransportedForm d omega
  have hsmooth : ∀ p : Q,
      ContDiffOn ℝ ∞
        (fun y : Euc 2 => form ((extChartAt (𝓡∂ 2) p).symm y)
          (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) (extChartAt (𝓡∂ 2) p).symm
            (extChartAt (𝓡∂ 2) p).target y
            ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm (EuclideanSpace.single i 1))))
        (extChartAt (𝓡∂ 2) p).target := by
    intro p y hy
    let e := extChartAt (𝓡∂ 2) p
    let g : Euc 2 → S := d.symm ∘ e.symm
    let x : S := g y
    let f := extChartAt (𝓡∂ 2) x
    let k : Euc 2 → Euc 2 := f ∘ g
    let A (z : Euc 2) : Euc 2 [⋀^Fin 2]→ₗ[ℝ] ℝ :=
      (omega.form (f.symm z)).compLinearMap
        (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) f.symm f.target z).toLinearMap
    let coeff : Euc 2 → ℝ := fun z => A z (fun i => EuclideanSpace.single i 1)
    let jac : Euc 2 → ℝ := fun z => Matrix.det (fun i j : Fin 2 =>
      (fderivWithin ℝ k e.target z (EuclideanSpace.single j 1)) i)
    have hg : ContMDiffOn 𝓘(ℝ, Euc 2) (𝓡∂ 2) ∞ g e.target :=
      d.symm.contMDiff.comp_contMDiffOn (contMDiffOn_extChartAt_symm p)
    have hgy : ContinuousWithinAt g e.target y := hg.continuousOn y hy
    have hx : g y ∈ f.source := by
      exact mem_extChartAt_source x
    have hk : ContDiffWithinAt ℝ ∞ k e.target y :=
      ((contMDiffAt_extChartAt (I := 𝓡∂ 2) (n := (∞ : ℕ∞ω)) (x := x)).comp_contMDiffWithinAt y
        (hg y hy)).contDiffWithinAt
    let W : Set (Euc 2) := e.target ∩ g ⁻¹' f.source
    have hW : W ∈ nhdsWithin y e.target := Filter.inter_mem self_mem_nhdsWithin
      (hgy.preimage_mem_nhdsWithin (isOpen_extChartAt_source (I := 𝓡∂ 2) x |>.mem_nhds hx))
    have hmaps : MapsTo k W f.target := fun z hz => f.map_source hz.2
    have hcoeff : ContDiffWithinAt ℝ ∞ (coeff ∘ k) e.target y := by
      have hfcoeff : ContDiffWithinAt ℝ ∞ coeff f.target (k y) :=
        omega.smooth_coefficients x (k y) (f.map_source hx)
      exact (hfcoeff.comp y (hk.mono Set.inter_subset_left) hmaps).mono_of_mem_nhdsWithin hW
    have hder := hk.fderivWithin_right (uniqueDiffOn_extChartAt_target p)
      (m := (∞ : ℕ∞ω)) (by simp) hy
    have hentry (i j : Fin 2) : ContDiffWithinAt ℝ ∞
        (fun z => (fderivWithin ℝ k e.target z (EuclideanSpace.single j 1)) i) e.target y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp_contDiffWithinAt y
        (hder.clm_apply (contDiffWithinAt_const (c := EuclideanSpace.single j (1 : ℝ))))
    have hjac : ContDiffWithinAt ℝ ∞ jac e.target y := by
      set_option backward.isDefEq.respectTransparency false in
        dsimp [jac]
        simp only [Matrix.det_fin_two]
        exact ((hentry 0 0).mul (hentry 1 1)).sub ((hentry 0 1).mul (hentry 1 0))
    apply (hcoeff.mul hjac).congr_of_eventuallyEq_of_mem ?_ hy
    filter_upwards [hW] with z hz
    have hzf : k z ∈ f.target := hmaps hz
    have hzg : f.symm (k z) = g z := f.left_inv hz.2
    have hde : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target z :=
      (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡∂ 2) hz.1).mono
        (extChartAt_target_subset_range p)
    have hdu : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) e.target z :=
      (uniqueDiffOn_extChartAt_target p z hz.1).uniqueMDiffWithinAt
    have hc1 := mfderiv_comp_mfderivWithin z
      (d.symm.contMDiff.mdifferentiableAt (by simp)) hde hdu
    have hdg := (hg z hz.1).mdifferentiableWithinAt (by simp)
    have hdf : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, Euc 2) f (g z) :=
      mdifferentiableAt_extChartAt (x := x) (by
        have hsrc : g z ∈ f.source := hz.2
        simpa only [f, extChartAt_source] using hsrc)
    have hc2 := mfderiv_comp_mfderivWithin z hdf hdg hdu
    rw [mfderivWithin_eq_fderivWithin] at hc2
    have hmono := (mdifferentiableWithinAt_extChartAt_symm (I := 𝓡∂ 2) hzf).mfderivWithin_mono
      ((uniqueDiffOn_extChartAt_target x (k z) hzf).uniqueMDiffWithinAt)
      (extChartAt_target_subset_range x)
    have hleft := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓡∂ 2) hzf
    rw [← hmono, hzg] at hleft
    have hvec (i : Fin 2) :
        mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm (e.symm z)
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target z (EuclideanSpace.single i 1)) =
        mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) f.symm f.target (k z)
          (fderivWithin ℝ k e.target z (EuclideanSpace.single i 1)) := by
      have hh1 := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L (EuclideanSpace.single i 1)) hc1
      have hh2 := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L (EuclideanSpace.single i 1)) hc2
      have hh3 := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 =>
        L (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) g e.target z (EuclideanSpace.single i 1))) hleft
      dsimp [k, g] at hh1 hh2
      change mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) g e.target z (EuclideanSpace.single i 1) = _ at hh1
      change fderivWithin ℝ k e.target z (EuclideanSpace.single i 1) =
        mfderiv (𝓡∂ 2) 𝓘(ℝ, Euc 2) f (g z)
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) g e.target z (EuclideanSpace.single i 1)) at hh2
      rw [hh2]
      exact hh1.symm.trans hh3.symm
    have heval : form (e.symm z)
        (fun i => mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target z
          ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) z).symm (EuclideanSpace.single i 1))) =
        A (k z) (fun i => fderivWithin ℝ k e.target z (EuclideanSpace.single i 1)) := by
      change omega.form (g z) (fun i =>
        mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm (e.symm z)
          (mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) e.symm e.target z (EuclideanSpace.single i 1))) =
        omega.form (f.symm (k z)) (fun i =>
          mfderivWithin 𝓘(ℝ, Euc 2) (𝓡∂ 2) f.symm f.target (k z)
            (fderivWithin ℝ k e.target z (EuclideanSpace.single i 1)))
      rw [hzg]
      congr 1
      funext i
      exact hvec i
    rw [heval]
    have ha := AlternatingMap.eq_smul_basis_det (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (A (k z))
    rw [ha, AlternatingMap.smul_apply, smul_eq_mul, Module.Basis.det_apply]
    have hb : ⇑(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
        (fun i => EuclideanSpace.single i (1 : ℝ)) := by
      funext i
      exact EuclideanSpace.basisFun_apply (Fin 2) ℝ i
    have hA : (A (k z)) ⇑(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis = coeff (k z) := by
      rw [hb]
    rw [hA]
    congr 1
  let omegaQ : SmoothVolumeOrientation (𝓡∂ 2) Q := {
    form := form
    nowhere_zero := by
      intro y hz
      apply omega.nowhere_zero (d.symm y)
      have hinj := AlternatingMap.compLinearMap_injective (N := ℝ) (ι := Fin 2)
        (mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm y).toLinearMap
        (d.symm.mfderivToContinuousLinearEquiv (by simp) y).surjective
      apply hinj
      simpa only [form, a5InverseTransportedForm, AlternatingMap.zero_compLinearMap] using hz
    smooth_coefficients := hsmooth }
  refine ⟨omegaQ, rfl, ?_⟩
  intro x w
  have hcomp : d.symm ∘ d = (id : S → S) := by funext x; exact d.symm_apply_apply x
  have hder := mfderiv_comp x
    (d.symm.contMDiff.mdifferentiableAt (by simp))
    (d.contMDiff.mdifferentiableAt (by simp))
  rw [hcomp, mfderiv_id] at hder
  have hval (v : TangentSpace (𝓡∂ 2) x) :
      mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm (d x)
        (mfderiv (𝓡∂ 2) (𝓡∂ 2) d x v) = v :=
    (congrArg (fun L => L v) hder).symm
  change omega.form (d.symm (d x))
    (fun i => mfderiv (𝓡∂ 2) (𝓡∂ 2) d.symm (d x)
      (mfderiv (𝓡∂ 2) (𝓡∂ 2) d x (w i))) = omega.form x w
  set_option backward.isDefEq.respectTransparency false in
    rw [d.symm_apply_apply]
  congr 1
  funext i
  exact hval (w i)

#print axioms a5_smooth_volume_orientation_diffeomorph_transport
end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.GlobalSmoothSource
