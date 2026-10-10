import Section5PolarDistanceV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
local instance : TopologicalSpace PolarDomain := inferInstanceAs (TopologicalSpace (Circle × (Circle × Time)))
local instance : ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) PolarDomain :=
  inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) (Circle × (Circle × Time)))
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

theorem timeUnit_eq_canonical_one : timeUnit = (1 : TangentSpace (𝓡∂ 1) (0 : Time)) := by
  change timeUnit = oneTangentSpaceIcc (0 : Time)
  have hd := (contMDiffOn_projIcc (x := (0:ℝ)) (y := 1) (n := ∞) 0 (by norm_num)).mdifferentiableWithinAt (by simp)
  simp [oneTangentSpaceIcc, mfderivWithin, timeUnit, tangentSpaceCastModel, hd]
  change EuclideanSpace.single 0 1 = fderivWithin ℝ
    (((𝓡∂ 1) ∘ (IccLeftChart 0 1)) ∘ projIcc 0 1 (by norm_num)) (Icc 0 1) 0 1
  have he : EqOn (((𝓡∂ 1) ∘ (IccLeftChart 0 1)) ∘ projIcc 0 1 (by norm_num))
      (fun x : ℝ => x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) (Icc 0 1) := by
    intro x hx
    ext i
    fin_cases i
    simp [Function.comp_apply,projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num) hx,
      IccLeftChart,modelWithCornersEuclideanHalfSpace,EuclideanSpace.single]
  rw [fderivWithin_congr' he (by norm_num)]
  have hder := fderivWithin_smul_const
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))
    differentiableWithinAt_id (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  rw [fderivWithin_id (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) 0 (by norm_num))] at hder
  have hder' := congrArg (fun d => d (1 : ℝ)) hder
  simpa only [id_eq, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul] using! hder'.symm

include P in
theorem polar_distance_real_extension (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ F : ℝ × (Circle × Circle) → ℝ,
      ContMDiff (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) ∞ F ∧
      (∀ p : Circle × Circle, ∀ t : Time, (t : ℝ) ≤ a →
        F ((t : ℝ),p) = r (givenExteriorPolarMap E (p.1,p.2,t))) ∧
      (∀ p, F (0,p) = 0) ∧
      (∀ p, 0 < (show ℝ from mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ)
        F (0,p) (1,0))) := by
  obtain ⟨a,ha,ha1,hinside⟩ := polar_collar_uniform_inside P hU hb
  let Q : ℝ × (Circle × Circle) → E.Carrier := fun q =>
    givenExteriorPolarMap E (q.2.1,q.2.2,projIcc 0 1 (by norm_num) q.1)
  have hQ : ContMDiffOn (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) (𝓡∂ 3) ∞ Q
      (Icc (0 : ℝ) a ×ˢ univ) := by
    apply P.smooth.comp_contMDiffOn
    exact contMDiff_snd.fst.contMDiffOn.prodMk
      (contMDiff_snd.snd.contMDiffOn.prodMk
        (contMDiffOn_projIcc.comp contMDiff_fst.contMDiffOn
          (fun q hq => ⟨hq.1.1,hq.1.2.trans ha1.le⟩)))
  have hmaps : MapsTo Q (Icc (0 : ℝ) a ×ˢ univ) U := by
    intro q hq
    apply hinside q.2
    simpa only [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num)
      ⟨hq.1.1,hq.1.2.trans ha1.le⟩] using hq.1.2
  obtain ⟨F,hF,hFe⟩ := Manifold.exists_contMDiff_extension_Icc (hr.1.comp hQ hmaps)
  have hmatch (p : Circle × Circle) (t : Time) (ht : (t : ℝ) ≤ a) :
      F ((t : ℝ),p) = r (givenExteriorPolarMap E (p.1,p.2,t)) := by
    have he := hFe (show ((t : ℝ),p) ∈ Icc (0 : ℝ) a ×ˢ univ from
      ⟨⟨t.property.1,ht⟩,mem_univ p⟩)
    have hproj : projIcc 0 1 (by norm_num) (t : ℝ) = t :=
      Subtype.ext (by simp [projIcc_of_mem (show (0 : ℝ) ≤ 1 by norm_num) t.property])
    simpa only [Function.comp_apply,Q,hproj] using he
  refine ⟨a,ha,ha1,F,hF,hmatch,?_,?_⟩
  · intro p
    have he := hmatch p (0 : Time) ha.le
    exact he.trans ((hr.2.2.1 _ (hb (P.boundary p.1 p.2))).mp (P.boundary p.1 p.2))
  · intro p
    let L : Time → ℝ × (Circle × Circle) := fun t => ((t : ℝ),p)
    have hL : ContMDiff (𝓡∂ 1) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) ∞ L :=
      contMDiff_subtypeVal_Icc.prodMk contMDiff_const
    have he : F ∘ L =ᶠ[𝓝 (0 : Time)]
        (fun t => r (givenExteriorPolarMap E (p.1,p.2,t))) := by
      have ht : ∀ᶠ t : Time in 𝓝 0, (t : ℝ) < a :=
        (isOpen_lt continuous_subtype_val continuous_const).mem_nhds ha
      filter_upwards [ht] with t ht
      exact hmatch p t ht.le
    have hder := he.mfderiv_eq (I := (𝓡∂ 1)) (I' := 𝓘(ℝ))
    have hpositive := polar_distance_transverse P g hU hr hb p
    have hLc : mfderiv (𝓡∂ 1) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) L (0 : Time) timeUnit = (1,0) := by
      rw [show L = (fun t : Time => ((t : ℝ),p)) from rfl,
        mfderiv_prodMk ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp))
          mdifferentiableAt_const,mfderiv_const]
      change (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Time → ℝ) 0 timeUnit,0) = (1,0)
      rw [timeUnit_eq_canonical_one,mfderiv_subtypeVal_Icc_one]
    rw [mfderiv_comp (0 : Time) (hF.mdifferentiableAt (by simp))
      (hL.mdifferentiableAt (by simp))] at hder
    have hd := congrArg (fun d => d timeUnit) hder
    change mfderiv (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) 𝓘(ℝ) F (0,p)
      (mfderiv (𝓡∂ 1) (𝓘(ℝ).prod ((𝓡 1).prod (𝓡 1))) L 0 timeUnit) =
      mfderiv (𝓡∂ 1) 𝓘(ℝ) (fun t => r (givenExteriorPolarMap E (p.1,p.2,t))) 0 timeUnit at hd
    rw [hLc] at hd
    exact hd.symm ▸ hpositive

#print axioms polar_distance_real_extension
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
