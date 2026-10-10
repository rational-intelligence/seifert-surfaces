import InitialLiteralAllTestRadius_v460

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 600000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_actual_cap_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArtificialCircleGeometry_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_boundary_cap_circle_geometry_v411)⟩

private theorem actual_cap_normal_flux_is_arc_v460
    (f : E2 → E2) (c : ℝ → E2)
    (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1/2) :
    let e := Real.arcsin (q/2)
    let aa := s+Real.pi/2+e
    let bb := s+3*Real.pi/2-e
    ((fun t=>(disc 1).indicator f (unitCircleParameter s+q•unitCircleParameter t))
      =ᵐ[volume.restrict (Icc aa bb)] c) →
    ∀ (psi : E2 → ℝ) (i j : Fin 2),
      (∫ t in Ioo (-Real.pi) Real.pi,
        (disc 1).indicator (fun x=>f x i*psi x)
          (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)=
      ∫ t in Icc aa bb,c t i*psi (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j := by
  classical
  dsimp only
  intro htrace psi i j
  let e := Real.arcsin (q/2)
  let aa := s+Real.pi/2+e
  let bb := s+3*Real.pi/2-e
  let center := unitCircleParameter s
  let flux : ℝ → ℝ := fun t=>(disc 1).indicator (fun x=>f x i*psi x)
    (center+q•unitCircleParameter t)*unitCircleParameter t j
  have hcircle : Periodic unitCircleParameter (2*Real.pi) := by
    intro t
    ext k
    fin_cases k <;> simp [unitCircleParameter,Real.cos_add_two_pi,Real.sin_add_two_pi]
  have hperiod : Periodic flux (2*Real.pi) := by
    intro t
    dsimp only [flux]
    rw [hcircle t]
  have hshift : (∫ t in Icc aa (aa+2*Real.pi),flux t)=
      ∫ t in Ioo (-Real.pi) Real.pi,flux t := by
    have he := hperiod.intervalIntegral_add_eq aa (-Real.pi)
    rw [show -Real.pi+2*Real.pi=Real.pi by ring,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : aa ≤ aa+2*Real.pi),
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at he
    simp only [integral_Ioc_eq_integral_Ioo] at he
    rw [integral_Icc_eq_integral_Ioo]
    exact he
  have hg := paid_actual_cap_geometry s q hq hqhalf
  dsimp only at hg
  have hsub : Icc aa bb ⊆ Icc aa (aa+2*Real.pi) :=
    fun t ht=>⟨ht.1,ht.2.trans hg.2.2.1.le⟩
  have hsupported : (∫ t in Icc aa (aa+2*Real.pi),flux t)=∫ t in Icc aa bb,flux t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub
    intro t ht
    have htbb : bb < t := by
      by_contra h
      exact ht.2 ⟨ht.1.1,le_of_not_gt h⟩
    have hout := hg.2.2.2.2.2.2 t ⟨htbb.le,ht.1.2⟩
    simp only [flux,center,indicator_of_notMem hout,zero_mul]
  change (∫ t in Ioo (-Real.pi) Real.pi,flux t)=_
  rw [←hshift,hsupported]
  apply integral_congr_ae
  filter_upwards [htrace] with t ht
  have he : (disc 1).indicator (fun x=>f x i*psi x) (center+q•unitCircleParameter t)=
      ((disc 1).indicator f (center+q•unitCircleParameter t)) i*psi (center+q•unitCircleParameter t) := by
    by_cases hx:center+q•unitCircleParameter t∈disc 1
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx,PiLp.zero_apply,zero_mul]
  dsimp only [flux]
  rw [he,ht]

private theorem actual_cap_green_relative_seam_v460
    (f h : E2 → E2) (d dh : Fin 2 → E2 → E2) (b B c : ℝ → E2)
    (oldgreen : HasGreenBoundaryTrace f d b)
    (s q : ℝ) (hq : 0 < q) (hqhalf : q ≤ 1/2) :
    let e := Real.arcsin (q/2)
    let aa := s+Real.pi/2+e
    let bb := s+3*Real.pi/2-e
    ((fun t=>(disc 1).indicator f (unitCircleParameter s+q•unitCircleParameter t))
      =ᵐ[volume.restrict (Icc aa bb)] c) →
    (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
      (∫ x in planarCap (unitCircleParameter s) q,
        f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
        (q*∫ t in Ioo (-Real.pi) Real.pi,
          (disc 1).indicator (fun x=>f x i*psi x)
            (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)+
        ∫ t in circlePatch (unitCircleParameter s) q,b t i*psi (unitCircleParameter t)*unitCircleParameter t j) →
    (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
      IntegrableOn (fun x=>h x i*fderiv ℝ psi x (coordinateVector 2 j)+dh i x j*psi x)
        (planarCap (unitCircleParameter s) q) ∧
      IntegrableOn (fun t=>c t i*psi (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)
        (Icc aa bb) ∧
      IntegrableOn (fun t=>B t i*psi (unitCircleParameter t)*unitCircleParameter t j)
        (circlePatch (unitCircleParameter s) q) ∧
      (∫ x in planarCap (unitCircleParameter s) q,
        h x i*fderiv ℝ psi x (coordinateVector 2 j)+dh i x j*psi x)=
        q*(∫ t in Icc aa bb,c t i*psi (unitCircleParameter s+q•unitCircleParameter t)*unitCircleParameter t j)+
        ∫ t in circlePatch (unitCircleParameter s) q,B t i*psi (unitCircleParameter t)*unitCircleParameter t j) →
    RelativeCapGreen (unitCircleParameter s) q f h d dh b B := by
  classical
  dsimp only
  intro htrace localgreen extensiongreen psi hpsi i j
  obtain ⟨holdI,holdT,holdEq⟩ := oldgreen psi hpsi i j
  have hbulk := holdI.mono_set (inter_subset_left : planarCap (unitCircleParameter s) q⊆disc 1)
  have hbound := holdT.mono_set (inter_subset_left : circlePatch (unitCircleParameter s) q⊆Icc 0 (2*Real.pi))
  obtain ⟨hnewI,hnewA,hnewT,hnewEq⟩ := extensiongreen psi hpsi i j
  have hdelta : (fun x=>(h x i-f x i)*fderiv ℝ psi x (coordinateVector 2 j)+
      (dh i x j-d i x j)*psi x)=
      (fun x=>(h x i*fderiv ℝ psi x (coordinateVector 2 j)+dh i x j*psi x)-
        (f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)) := by funext x;ring
  have hdeltaB : (fun t=>(B t i-b t i)*psi (unitCircleParameter t)*unitCircleParameter t j)=
      (fun t=>(B t i*psi (unitCircleParameter t)*unitCircleParameter t j)-
        (b t i*psi (unitCircleParameter t)*unitCircleParameter t j)) := by funext t;ring
  rw [hdelta,hdeltaB]
  refine ⟨hnewI.sub hbulk,hnewT.sub hbound,?_⟩
  rw [integral_sub hnewI hbulk,integral_sub hnewT hbound]
  have hold := localgreen psi hpsi i j
  rw [actual_cap_normal_flux_is_arc_v460 f c s q hq hqhalf htrace psi i j] at hold
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
