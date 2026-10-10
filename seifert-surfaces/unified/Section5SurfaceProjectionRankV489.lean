import Section5ActualSurfaceBoundaryV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
open SeifertSurfaces.Foundations SeifertSurfaces.AppendixACoordinates
noncomputable section

theorem two_coordinate_rank (L : E2 →L[ℝ] E2)
    (hnormal : ∃ u, L u 0 ≠ 0)
    (htangent : ∃ v, L v 0 = 0 ∧ L v 1 ≠ 0) : Injective L := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=L.toLinearMap) rfl).mpr
  obtain ⟨u,hu⟩ := hnormal
  obtain ⟨v,hv0,hv1⟩ := htangent
  intro w
  refine ⟨(w 0 / L u 0) • u + ((w 1 - (w 0 / L u 0) * L u 1) / L v 1) • v,?_⟩
  ext i
  fin_cases i
  · simp only [ContinuousLinearMap.coe_coe,map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,
      smul_eq_mul]
    change w 0 / L u 0 * L u 0 + (w 1 - w 0 / L u 0 * L u 1) / L v 1 * L v 0 = w 0
    rw [hv0,mul_zero,add_zero,div_mul_cancel₀ _ hu]
  · simp only [ContinuousLinearMap.coe_coe,map_add,map_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    change w 0 / L u 0 * L u 1 + (w 1 - w 0 / L u 0 * L u 1) / L v 1 * L v 1 = w 1
    rw [div_mul_cancel₀ _ hv1]
    ring

/-- A noncritical boundary defining function and a nonzero tangential
coordinate give full rank; both hypotheses are derivative facts at the same point. -/
theorem scalar_pair_rank {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S]
    {f : S → EuclideanHalfSpace 2} {r s : S → ℝ} {x : S}
    (hf : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) f x)
    (hr : ∀ y, (f y).val 0 = r y) (hs : ∀ y, (f y).val 1 = s y)
    (hnormal : mfderiv (𝓡∂ 2) 𝓘(ℝ) r x ≠ 0)
    (htangent : ∃ v : TangentSpace (𝓡∂ 2) x,
      mfderiv (𝓡∂ 2) 𝓘(ℝ) r x v = 0 ∧ mfderiv (𝓡∂ 2) 𝓘(ℝ) s x v ≠ 0) :
    Injective (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x) := by
  let ev (i : Fin 2) : E2 →L[ℝ] ℝ := (EuclideanSpace.proj i)
  have hd (i : Fin 2) : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ) (fun z : EuclideanHalfSpace 2 => z.val i) (f x) :=
    ((ev i).contDiff.contMDiff.comp (𝓡∂ 2).contMDiff).mdifferentiableAt (n:=∞) (by simp)
  have hcalc (i : Fin 2) (v : TangentSpace (𝓡∂ 2) x) :
      mfderiv (𝓡∂ 2) 𝓘(ℝ) (fun y => (f y).val i) x v =
      (show E2 from mfderiv (𝓡∂ 2) (𝓡∂ 2) f x v) i := by
    rw [show (fun y => (f y).val i) = (fun z : EuclideanHalfSpace 2 => z.val i) ∘ f from rfl,
      mfderiv_comp x (hd i) hf]
    change (mfderiv (𝓡∂ 2) 𝓘(ℝ) (ev i ∘ (𝓡∂ 2)) (f x))
      (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x v) = _
    rw [mfderiv_comp (f x) ((ev i).contDiff.contMDiff.mdifferentiableAt (n:=∞) (by simp))
      ((𝓡∂ 2).contMDiff.mdifferentiableAt (n:=∞) (by simp))]
    simp only [mfderiv_eq_fderiv,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
    have hm : mfderiv (𝓡∂ 2) (𝓡 2) (𝓡∂ 2) (f x) = ContinuousLinearMap.id ℝ E2 := by
      simpa only [extChartAt_self_eq] using! (mfderiv_extChartAt_self (I:=𝓡∂ 2) (x:=f x))
    rw [hm]
    rfl
  have heqr : (fun y => (f y).val 0) = r := funext hr
  have heqs : (fun y => (f y).val 1) = s := funext hs
  have hnormal' : ∃ u : TangentSpace (𝓡∂ 2) x,
      (show E2 from mfderiv (𝓡∂ 2) (𝓡∂ 2) f x u) 0 ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hnormal
    ext u
    rw [← heqr,hcalc]
    exact hn u
  obtain ⟨v,hv0,hv1⟩ := htangent
  apply two_coordinate_rank (mfderiv (𝓡∂ 2) (𝓡∂ 2) f x) hnormal'
  refine ⟨v,?_,?_⟩
  · have hh := hcalc 0 v
    rw [heqr] at hh
    simpa only [] using! hh.symm.trans hv0
  · intro he
    apply hv1
    exact (heqs ▸ hcalc 1 v).trans he

#print axioms two_coordinate_rank
#print axioms scalar_pair_rank
end
end SeifertSurfaces.OriginalEndpoints.Section5.SurfaceInverseV489
