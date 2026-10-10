import Foundations
import BoundaryFlow

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section

/-- Split off the inward coordinate of the ambient model. -/
def splitAmbient : (ℝ × (Fin 2 → ℝ)) ≃L[ℝ] Euc 3 :=
  (Fin.consEquivL ℝ (fun _ : Fin 3 => ℝ)).trans
    (EuclideanSpace.equiv (Fin 3) ℝ).symm

@[simp] theorem splitAmbient_zero (q : ℝ × (Fin 2 → ℝ)) :
    splitAmbient q 0 = q.1 := by simp [splitAmbient]

def conjugateField (V : ℝ × Euc 3 → Euc 3) (p : ℝ × (ℝ × (Fin 2 → ℝ))) :
    ℝ × (Fin 2 → ℝ) := splitAmbient.symm (V (p.1, splitAmbient p.2))

theorem conjugateField_contDiff {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (conjugateField V) :=
  splitAmbient.symm.contDiff.comp
    (hV.comp (contDiff_fst.prodMk (splitAmbient.contDiff.comp contDiff_snd)))

theorem conjugateField_hasCompactSupport {V : ℝ × Euc 3 → Euc 3}
    (hs : HasCompactSupport V) : HasCompactSupport (conjugateField V) := by
  exact (hs.comp_isClosedEmbedding
    (IsClosedEmbedding.id.prodMap splitAmbient.toHomeomorph.isClosedEmbedding)).comp_left
      (g := splitAmbient.symm) (map_zero _)

theorem timeDependentFlow_conjugate {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (s t : ℝ) (x : ℝ × (Fin 2 → ℝ)) :
    splitAmbient (Diffeomorph.timeDependentFlow (conjugateField V)
      (conjugateField_contDiff hV) (conjugateField_hasCompactSupport hs) s t x) =
      Diffeomorph.timeDependentFlow V hV hs s t (splitAmbient x) := by
  let W := conjugateField V
  have hW := conjugateField_contDiff hV
  have hWs := conjugateField_hasCompactSupport hs
  let γ : ℝ → Euc 3 := fun u => splitAmbient (Diffeomorph.timeDependentFlow W hW hWs s u x)
  have hγ : IsIntegralCurve γ (fun u q => V (u, q)) := by
    intro u
    have hd := splitAmbient.hasFDerivAt.comp_hasDerivAt u
      (Diffeomorph.isIntegralCurve_timeDependentFlow W hW hWs s x u)
    simpa only [γ, W, conjugateField, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, Function.comp_def] using hd
  have he := Diffeomorph.timeDependentFlow_apply_eq_of_isIntegralCurve V hV hs hγ s t
  have hstart : γ s = splitAmbient x := by
    simp only [γ, Diffeomorph.timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq]
  rw [hstart] at he
  exact he.symm

theorem eucFlow_boundary_iff {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) (x : Euc 3) :
    Diffeomorph.timeDependentFlow V hV hs s t x 0 = 0 ↔ x 0 = 0 := by
  have hWb : ∀ t z, (conjugateField V (t, (0, z))).1 = 0 := by
    intro t z
    change (splitAmbient.symm (V (t, splitAmbient (0,z)))).1 = 0
    rw [← splitAmbient_zero, splitAmbient.apply_symm_apply]
    exact hb t _ (splitAmbient_zero _)
  have h := timeDependentFlow_boundary_iff (conjugateField_contDiff hV)
    (conjugateField_hasCompactSupport hs) hWb s t (splitAmbient.symm x)
  rw [← splitAmbient_zero, timeDependentFlow_conjugate hV hs,
    splitAmbient.apply_symm_apply, ← splitAmbient_zero, splitAmbient.apply_symm_apply] at h
  exact h

theorem eucFlow_nonneg_iff {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) (x : Euc 3) :
    0 ≤ Diffeomorph.timeDependentFlow V hV hs s t x 0 ↔ 0 ≤ x 0 := by
  have hWb : ∀ t z, (conjugateField V (t, (0, z))).1 = 0 := by
    intro t z
    change (splitAmbient.symm (V (t, splitAmbient (0,z)))).1 = 0
    rw [← splitAmbient_zero, splitAmbient.apply_symm_apply]
    exact hb t _ (splitAmbient_zero _)
  have h := timeDependentFlow_nonneg_iff (conjugateField_contDiff hV)
    (conjugateField_hasCompactSupport hs) hWb s t (splitAmbient.symm x)
  rw [← splitAmbient_zero, timeDependentFlow_conjugate hV hs,
    splitAmbient.apply_symm_apply, ← splitAmbient_zero, splitAmbient.apply_symm_apply] at h
  exact h

/-- The restriction of the genuine Euclidean flow to the half-space model. -/
def halfspaceFlow {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) :
    Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (EuclideanHalfSpace 3) (EuclideanHalfSpace 3) ∞ := by
  let D := Diffeomorph.timeDependentFlow V hV hs s t
  let Di := Diffeomorph.timeDependentFlow V hV hs t s
  have hD : MapsTo D (range (𝓡∂ 3)) (range (𝓡∂ 3)) := by
    intro x hx
    rw [range_modelWithCornersEuclideanHalfSpace] at hx ⊢
    exact (eucFlow_nonneg_iff hV hs hb s t x).mpr hx
  have hDi : MapsTo Di (range (𝓡∂ 3)) (range (𝓡∂ 3)) := by
    intro x hx
    rw [range_modelWithCornersEuclideanHalfSpace] at hx ⊢
    exact (eucFlow_nonneg_iff hV hs hb t s x).mpr hx
  let A := fun x : EuclideanHalfSpace 3 => (𝓡∂ 3).symm (D ((𝓡∂ 3) x))
  let Ai := fun x : EuclideanHalfSpace 3 => (𝓡∂ 3).symm (Di ((𝓡∂ 3) x))
  have hA : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ A :=
    (𝓡∂ 3).contMDiffOn_symm.comp_contMDiff
      (D.contMDiff.comp (𝓡∂ 3).contMDiff) (fun x => hD (mem_range_self x))
  have hAi : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ Ai :=
    (𝓡∂ 3).contMDiffOn_symm.comp_contMDiff
      (Di.contMDiff.comp (𝓡∂ 3).contMDiff) (fun x => hDi (mem_range_self x))
  refine
    { toEquiv :=
        { toFun := A
          invFun := Ai
          left_inv := ?_
          right_inv := ?_ }
      contMDiff_toFun := hA
      contMDiff_invFun := hAi }
  · intro x
    change (𝓡∂ 3).symm (Di ((𝓡∂ 3) ((𝓡∂ 3).symm (D ((𝓡∂ 3) x))))) = x
    rw [(𝓡∂ 3).right_inv (hD (mem_range_self x)),
      show Di = D.symm from (Diffeomorph.timeDependentFlow_symm V hV hs s t).symm,
      D.symm_apply_apply, (𝓡∂ 3).left_inv]
  · intro x
    change (𝓡∂ 3).symm (D ((𝓡∂ 3) ((𝓡∂ 3).symm (Di ((𝓡∂ 3) x))))) = x
    rw [(𝓡∂ 3).right_inv (hDi (mem_range_self x)),
      show Di = D.symm from (Diffeomorph.timeDependentFlow_symm V hV hs s t).symm,
      D.apply_symm_apply, (𝓡∂ 3).left_inv]

theorem halfspaceFlow_apply {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) (x : EuclideanHalfSpace 3) :
    (𝓡∂ 3) (halfspaceFlow hV hs hb s t x) =
      Diffeomorph.timeDependentFlow V hV hs s t ((𝓡∂ 3) x) := by
  apply (𝓡∂ 3).right_inv
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact (eucFlow_nonneg_iff hV hs hb s t _).mpr x.property

theorem halfspaceFlow_contMDiff {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡∂ 3)) (𝓡∂ 3) ∞
      (fun p : (ℝ × ℝ) × EuclideanHalfSpace 3 => halfspaceFlow hV hs hb p.1.1 p.1.2 p.2) := by
  have hD : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (𝓡∂ 3)) 𝓘(ℝ, Euc 3) ∞
      (fun p : (ℝ × ℝ) × EuclideanHalfSpace 3 =>
        Diffeomorph.timeDependentFlow V hV hs p.1.1 p.1.2 ((𝓡∂ 3) p.2)) :=
    (Diffeomorph.contDiff_timeDependentFlow V hV hs).contMDiff.comp
      (contMDiff_fst.fst.prodMk_space
        (contMDiff_fst.snd.prodMk_space ((𝓡∂ 3).contMDiff.comp contMDiff_snd)))
  apply (𝓡∂ 3).contMDiffOn_symm.comp_contMDiff hD
  intro p
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact (eucFlow_nonneg_iff hV hs hb p.1.1 p.1.2 _).mpr p.2.property

theorem halfspaceFlow_refl {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s : ℝ) :
    halfspaceFlow hV hs hb s s = Diffeomorph.refl (𝓡∂ 3) (EuclideanHalfSpace 3) ∞ := by
  apply Diffeomorph.ext
  intro x
  apply (𝓡∂ 3).injective
  rw [halfspaceFlow_apply, Diffeomorph.timeDependentFlow_refl]
  rfl

theorem halfspaceFlow_symm {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) :
    (halfspaceFlow hV hs hb s t).symm = halfspaceFlow hV hs hb t s := by
  apply Diffeomorph.ext
  intro x
  rfl

theorem halfspaceFlow_preimage_boundary {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) :
    (halfspaceFlow hV hs hb s t) ⁻¹' (𝓡∂ 3).boundary (EuclideanHalfSpace 3) =
      (𝓡∂ 3).boundary (EuclideanHalfSpace 3) := by
  exact Diffeomorph.preimage_boundary (by simp) (halfspaceFlow hV hs hb s t)

theorem halfspaceFlow_image_boundary {V : ℝ × Euc 3 → Euc 3}
    (hV : ContDiff ℝ ∞ V) (hs : HasCompactSupport V)
    (hb : ∀ t x, x 0 = 0 → V (t, x) 0 = 0) (s t : ℝ) :
    (halfspaceFlow hV hs hb s t) '' (𝓡∂ 3).boundary (EuclideanHalfSpace 3) =
      (𝓡∂ 3).boundary (EuclideanHalfSpace 3) := by
  exact Diffeomorph.image_boundary (by simp) (halfspaceFlow hV hs hb s t)

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
