import TraceBoundaryVelocity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open scoped Manifold ContDiff
open Set Topology Bundle

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

theorem timeOne_contMDiff :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1).tangent ∞
      (fun t : Time => (⟨t, (1 : TangentSpace (𝓡∂ 1) t)⟩ : TangentBundle (𝓡∂ 1) Time)) := by
  let P : ℝ → Time := Set.projIcc 0 1 (by norm_num)
  have hP : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ P (Icc 0 1) := contMDiffOn_projIcc
  have hTP := hP.contMDiffOn_tangentMapWithin (m := (⊤ : ℕ∞)) (by simp)
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)).uniqueMDiffOn
  have hunitR : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun r : ℝ => (⟨r, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have hunit := hunitR.comp (contMDiff_subtypeVal_Icc (x := 0) (y := 1))
  have h := hTP.comp_contMDiff hunit (fun t => t.property)
  apply h.congr
  intro t
  change (⟨t, (1 : TangentSpace (𝓡∂ 1) t)⟩ : TangentBundle (𝓡∂ 1) Time) =
    ⟨P t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡∂ 1) P (Icc 0 1) t 1⟩
  dsimp only [P]
  rw [mfderivWithin_projIcc_one t.property, projIcc_of_mem (by norm_num) t.property]

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] {f g : NeatEmbedding S M}

def traceVelocity (F : SmoothNormalIsotopy S M f g) (p : Time × S) :
    TangentSpace (𝓡∂ 3) ((F.stage p.1).toFun p.2) :=
  mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => (F.stage t).toFun p.2) p.1 1

omit [IsManifold (𝓡∂ 3) ∞ M] in
theorem traceVelocity_eq (F : SmoothNormalIsotopy S M f g) (p : Time × S) :
    traceVelocity F p =
      mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3)
        (fun q : Time × S => (F.stage q.1).toFun q.2) p
        ((1 : TangentSpace (𝓡∂ 1) p.1),0) := by
  have hc := mfderiv_comp p.1 (F.smooth_family.mdifferentiableAt (by simp) (x := p))
    (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  change mfderiv (𝓡∂ 1) (𝓡∂ 3) (fun t => (F.stage t).toFun p.2) p.1 =
    (mfderiv ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3)
      (fun q : Time × S => (F.stage q.1).toFun q.2) p).comp
      (mfderiv (𝓡∂ 1) ((𝓡∂ 1).prod (𝓡∂ 2)) (fun t : Time => (t,p.2)) p.1) at hc
  rw [mfderiv_prod_left] at hc
  exact congrArg (fun A => A (1 : TangentSpace (𝓡∂ 1) p.1)) hc

theorem traceVelocity_contMDiff (F : SmoothNormalIsotopy S M f g) :
    ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3).tangent ∞
      (fun p : Time × S => (⟨(F.stage p.1).toFun p.2, traceVelocity F p⟩ :
        TangentBundle (𝓡∂ 3) M)) := by
  have harg : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2))
      ((𝓡∂ 1).prod (𝓡∂ 2)).tangent ∞
      (fun p : Time × S => (⟨p, ((1 : TangentSpace (𝓡∂ 1) p.1),0)⟩ :
        TangentBundle ((𝓡∂ 1).prod (𝓡∂ 2)) (Time × S))) := by
    exact contMDiff_equivTangentBundleProd_symm.comp
      ((timeOne_contMDiff.comp contMDiff_fst).prodMk
        ((contMDiff_zeroSection ℝ (TangentSpace (𝓡∂ 2))).comp contMDiff_snd))
  have h := (F.smooth_family.contMDiff_tangentMap (m := (⊤ : ℕ∞)) (by simp)).comp harg
  apply h.congr
  intro p
  exact congrArg (fun w => (⟨(F.stage p.1).toFun p.2,w⟩ : TangentBundle (𝓡∂ 3) M))
    (traceVelocity_eq F p)

theorem traceVelocity_boundary (F : SmoothNormalIsotopy S M f g)
    (p : Time × S) (hp : p.2 ∈ S.boundary) :
    inwardCoordinate ((F.stage p.1).toFun p.2) (traceVelocity F p) = 0 :=
  normal_boundary_velocity F p.2 hp p.1 1

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
