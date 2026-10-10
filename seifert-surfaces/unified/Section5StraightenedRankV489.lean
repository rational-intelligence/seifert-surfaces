import Section5StraightenedStripV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Function Filter Manifold Topology
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section

theorem longitude_label_differential_injective (a : Circle) (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ) (𝓡 1) (fun y : ℝ => longitudeLabelFlow y a) t) := by
  let R : Circle → Circle := fun z => z * a
  have hR : ContMDiff (𝓡 1) (𝓡 1) ∞ R := contMDiff_id.mul contMDiff_const
  have hRi : ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z * a⁻¹) :=
    contMDiff_id.mul contMDiff_const
  have hleft : (fun z : Circle => R z * a⁻¹) = id := by
    funext z
    simp [R,mul_assoc]
  have hder (z : Circle) : Injective (mfderiv (𝓡 1) (𝓡 1) R z) := by
    have he := mfderiv_comp z (hRi.mdifferentiableAt (by simp))
      (hR.mdifferentiableAt (by simp))
    have hc : (fun z : Circle => z * a⁻¹) ∘ R = id := hleft
    rw [hc,mfderiv_id] at he
    apply Injective.of_comp (f := mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z*a⁻¹) (R z))
    change Injective ((mfderiv (𝓡 1) (𝓡 1) (fun z : Circle => z*a⁻¹) (R z)).comp
      (mfderiv (𝓡 1) (𝓡 1) R z))
    rw [← he]
    exact fun _ _ h => h
  change Injective (mfderiv 𝓘(ℝ) (𝓡 1) (R ∘ Circle.exp) t)
  rw [mfderiv_comp t (hR.mdifferentiableAt (by simp))
    ((contMDiff_circleExp (m:=∞)).mdifferentiableAt (by simp))]
  exact (hder _).comp (circle_clock_differential_injective t)

theorem time_value_differential_injective (t : Time) :
    Injective (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) t) := by
  have hs : Surjective (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) t) := by
    intro r
    refine ⟨(show ℝ from r) • (1 : TangentSpace (𝓡∂ 1) t),?_⟩
    rw [map_smul,mfderiv_subtypeVal_Icc_one]
    change (show ℝ from r)*1=(show ℝ from r)
    exact mul_one (show ℝ from r)
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f:=
    (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) t).toLinearMap) ?_).mpr hs
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ ℝ
  simp

theorem straightened_reference_rank (a : Circle) (p : Circle × (Time × ℝ)) :
    Injective (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
      ((𝓡 1).prod (𝓘(ℝ).prod (𝓡 1)))
      (fun q : Circle × (Time × ℝ) => (q.1,((q.2.1:ℝ),longitudeLabelFlow q.2.2 a))) p) := by
  let ell : ℝ → Circle := fun y => longitudeLabelFlow y a
  have he : ContMDiff 𝓘(ℝ) (𝓡 1) ∞ ell :=
    longitude_label_flow_smooth.comp (contMDiff_id.prodMk contMDiff_const)
  change Injective (mfderiv ((𝓡 1).prod ((𝓡∂ 1).prod 𝓘(ℝ)))
    ((𝓡 1).prod (𝓘(ℝ).prod (𝓡 1)))
    (Prod.map id (Prod.map (Subtype.val : Time → ℝ) ell)) p)
  have hprod : MDifferentiableAt ((𝓡∂ 1).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓡 1))
      (Prod.map (Subtype.val : Time → ℝ) ell) p.2 :=
    ((contMDiff_subtypeVal_Icc.comp contMDiff_fst).prodMk (he.comp contMDiff_snd)).mdifferentiableAt (n:=∞) (by simp)
  rw [mfderiv_prodMap mdifferentiableAt_id hprod,
    mfderiv_prodMap (contMDiff_subtypeVal_Icc.mdifferentiableAt (n:=∞) (by simp))
      (he.mdifferentiableAt (by simp)),mfderiv_id]
  intro u v huv
  apply Prod.ext
  · exact congrArg (fun x : TangentSpace ((𝓡 1).prod (𝓘(ℝ).prod (𝓡 1))) (p.1,((p.2.1:ℝ),ell p.2.2)) => x.1) huv
  · apply Prod.ext
    · apply time_value_differential_injective p.2.1
      exact congrArg (fun x => x.2.1) huv
    · apply longitude_label_differential_injective a p.2.2
      exact congrArg (fun x => x.2.2) huv

#print axioms longitude_label_differential_injective
#print axioms time_value_differential_injective
#print axioms straightened_reference_rank
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
