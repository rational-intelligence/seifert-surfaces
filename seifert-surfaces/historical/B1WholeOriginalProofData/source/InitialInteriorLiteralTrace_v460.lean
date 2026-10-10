import InitialInteriorHarmonicRadius_v460
import InitialPeriodicL2Primitive_v460
import InitialAngularWeightedFlux_v445
import InitialPositiveTraceUniqueness_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_radius" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorHarmonicRadius_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_interior_harmonic_shell_radius_v460)⟩

local macro "paid_tangent_L2" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialTangentialPrimitive_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_circle_tangential_L2_v411)⟩

local macro "paid_tangent_period" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTangential_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_circle_tangential_period_v411)⟩

local macro "paid_primitive" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicL2Primitive_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.periodic_zero_mean_L2_primitive_v460)⟩

local macro "paid_harmonic" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialHarmonicTests_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.centered_complex_circle_power_tests_v445)⟩

local macro "paid_angular" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialAngularWeightedFlux_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_weighted_angular_integrand_v445)⟩

local macro "paid_normalize" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPositiveTraceUniqueness_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.scaled_angular_green_v457)⟩

local macro "paid_constancy" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTraceConstancy_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.real_periodic_trace_constant_positive_v460)⟩

local macro "paid_interval_weight" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArcResidualGreen_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.interval_continuous_mul_integrable_v445)⟩

private theorem original_interior_literal_circle_trace_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (x:E2) (r:ℝ) (hr : 0 < r) (hrhalf : r ≤ 1/2)
    (inside : Metric.closedBall x r ⊆ disc 1) :
    ∃ q∈Ioo (r/2) r,∃ c:ℝ→E2,
      (∀ psi : E2 → ℝ,ContDiff ℝ ∞ psi → ∀ i j : Fin 2,
        (∫ y in planarCap x q,f y i*fderiv ℝ psi y (coordinateVector 2 j)+d i y j*psi y)=
          (q*∫ t in Ioo (-Real.pi) Real.pi,(disc 1).indicator (fun y=>f y i*psi y)
            (x+q•unitCircleParameter t)*unitCircleParameter t j)+
          ∫ t in circlePatch x q,liftedBoundaryValue Ω theta t i*psi (unitCircleParameter t)*unitCircleParameter t j) ∧
      Continuous c ∧ Periodic c (2*Real.pi) ∧
      (∀ i:Fin 2,AbsolutelyContinuousOnInterval (fun t=>c t i) (-Real.pi) Real.pi) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc (-Real.pi) Real.pi)) ∧
      (∫ t in Icc (-Real.pi) Real.pi,‖deriv c t‖^2) ≤
        2*((∫ y in planarCap x r,euclideanJetDensity d y)-
          (∫ y in planarCap x (r/2),euclideanJetDensity d y)) ∧
      (fun t=>(disc 1).indicator f (x+q•unitCircleParameter t))
        =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] c := by
  classical
  obtain ⟨q,hq,hlocal,hqf,hqd,hqpol,hqe⟩ :=
    paid_radius minimum theta sigma lift trace x r hr hrhalf inside
  let d0 : Fin 2 → E2 → E2 := fun i=>(disc 1).indicator (d i)
  let angles := Ioo (-Real.pi) Real.pi
  let W := Icc (-Real.pi) Real.pi
  let J : E2 → E2 := fun v=>(EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1,v 0]
  let a : ℝ → E2 := fun t=>(EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i=>q*inner ℝ (d0 i (x+q•unitCircleParameter t)) (J (unitCircleParameter t)))
  let F : ℝ → E2 := fun t=>(disc 1).indicator f (x+q•unitCircleParameter t)
  let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z=>
    ![((((z 0-x 0:ℝ):ℂ)+((z 1-x 1:ℝ):ℂ)*Complex.I)^n).re,
      ((((z 0-x 0:ℝ):ℂ)+((z 1-x 1:ℝ):ℂ)*Complex.I)^n).im] k
  have htangent := paid_tangent_L2 d0 x q hqd
  change MemLp a 2 (volume.restrict angles) ∧
    (∀ t,‖a t‖^2 ≤ q^2*euclideanJetDensity d0 (x+q•unitCircleParameter t)) ∧
    (∫ t in angles,‖a t‖^2) ≤ q^2*∫ t in angles,euclideanJetDensity d0 (x+q•unitCircleParameter t) at htangent
  have harm (n:ℕ) (k i:Fin 2) :
      (∫ t in angles,a t i*phi n k (x+q•unitCircleParameter t)+
        F t i*deriv (fun u=>phi n k (x+q•unitCircleParameter u)) t)=0 := by
    have hphi : ContDiff ℝ ∞ (phi n k) := (paid_harmonic x n).1 k
    have hpoint := paid_angular f d (phi n k) hphi x q i
    have hflux := hqpol n k i
    rw [←integral_const_mul] at hflux
    calc
      _ = ∫ t in angles,q*inner ℝ ((disc 1).indicator
          (fun z=>phi n k z•d i z+f z i•(EuclideanSpace.equiv (Fin 2) ℝ).symm
            (fun j=>fderiv ℝ (phi n k) z (coordinateVector 2 j)))
          (x+q•unitCircleParameter t)) (J (unitCircleParameter t)) := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [hpoint t]
        change a t i*_+F t i*_= _*a t i+F t i*_
        ring
      _ = 0 := hflux.symm
  let : IsFiniteMeasure (volume.restrict angles) := isFiniteMeasure_restrict.mpr
    ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  let : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have haI : IntegrableOn a angles := htangent.1.integrable (by norm_num)
  have hmean : (∫ t in angles,a t)=0 := by
    ext i
    have hp := (EuclideanSpace.proj (𝕜:=ℝ) i).integral_comp_comm haI
    change (∫ t in angles,a t i)=(∫ t in angles,a t) i at hp
    rw [←hp]
    simpa [phi] using harm 0 0 i
  have hperiod : Periodic a (2*Real.pi) := paid_tangent_period d0 x q
  have hprim := paid_primitive a hperiod htangent.1 hmean
  dsimp only at hprim
  let c0 : ℝ → E2 := fun t=>∫ u in (-Real.pi)..t,a u
  change Continuous c0 ∧ Periodic c0 (2*Real.pi) ∧ c0 (-Real.pi)=0 ∧ c0 Real.pi=0 ∧
    (∀ i,AbsolutelyContinuousOnInterval (fun t=>c0 t i) (-Real.pi) Real.pi) ∧
    (∀ᵐ t ∂volume.restrict W,HasDerivAt c0 (a t) t) ∧
    MemLp (deriv c0) 2 (volume.restrict W) ∧
    (∫ t in W,‖deriv c0 t‖^2)=∫ t in angles,‖a t‖^2 ∧
    (∀ psi,ContDiff ℝ ∞ psi → ∀ i,(∫ t in W,a t i*psi t+c0 t i*deriv psi t)=0) at hprim
  rcases hprim with ⟨hcc,hcp,hcleft,hcright,hca,hcder,hcd,hcenergy,hcgreen⟩
  have hFcc : MemLp F 2 (volume.restrict W) := by rwa [←restrict_Ioo_eq_restrict_Icc]
  have hac : MemLp a 2 (volume.restrict W) := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    exact htangent.1
  have hresidual (psi:ℝ→ℝ) (hpsi:ContDiff ℝ ∞ psi) (i:Fin 2)
      (horig : (∫ t in angles,a t i*psi t+F t i*deriv psi t)=0) :
      (∫ t in W,(F t i-c0 t i)*deriv psi t)=0 := by
    have hA := paid_interval_weight (-Real.pi) Real.pi (fun t=>a t i) psi
      ((hac.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) i)).integrable (by norm_num)) hpsi.continuous
    have hFd := paid_interval_weight (-Real.pi) Real.pi (fun t=>F t i) (deriv psi)
      ((hFcc.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) i)).integrable (by norm_num))
      (hpsi.continuous_deriv (by simp))
    have hCd : IntegrableOn (fun t=>c0 t i*deriv psi t) W :=
      (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hcc).mul
        (hpsi.continuous_deriv (by simp))).integrableOn_Icc
    have hp := hcgreen psi hpsi i
    rw [←integral_Icc_eq_integral_Ioo] at horig
    rw [integral_add hA hFd] at horig
    rw [integral_add hA hCd] at hp
    have he : (fun t=>(F t i-c0 t i)*deriv psi t)=(fun t=>F t i*deriv psi t-c0 t i*deriv psi t) := by funext t;ring
    rw [he,integral_sub hFd hCd]
    linarith
  have hpair (n:ℕ) (k i:Fin 2) :
      let psi : ℝ → ℝ := fun t=>![Real.cos ((n:ℝ)*t),Real.sin ((n:ℝ)*t)] k
      (∫ t in W,(F t i-c0 t i)*deriv psi t)=0 := by
    dsimp only
    let psi : ℝ → ℝ := fun t=>![Real.cos ((n:ℝ)*t),Real.sin ((n:ℝ)*t)] k
    have hpsi : ContDiff ℝ ∞ psi := by
      fin_cases k
      · change ContDiff ℝ ∞ (fun t:ℝ=>Real.cos ((n:ℝ)*t))
        fun_prop
      · change ContDiff ℝ ∞ (fun t:ℝ=>Real.sin ((n:ℝ)*t))
        fun_prop
    have htest : (fun t=>phi n k (x+q•unitCircleParameter t))=(fun t=>q^n*psi t) := by
      funext t
      fin_cases k
      · exact (paid_harmonic x n).2 q t |>.1
      · exact (paid_harmonic x n).2 q t |>.2
    have hs := harm n k i
    have hp := congrFun htest
    simp only [hp] at hs
    have horig := paid_normalize q (lt_trans (by positivity) hq.1).ne' n angles
      (fun t=>a t i) (fun t=>F t i) psi hpsi (-Real.pi) Real.pi 0 0 (by simpa only [zero_mul,sub_zero] using hs)
    apply hresidual psi hpsi i
    simpa only [zero_mul,sub_zero] using horig
  have hconst (i:Fin 2) : ∃ k:ℝ,(fun t=>F t i)=ᵐ[volume.restrict W] (fun t=>c0 t i+k) := by
    have hend : -Real.pi+2*Real.pi=Real.pi := by ring
    have ht := paid_constancy (-Real.pi) (fun t=>F t i) (fun t=>c0 t i)
      (by rw [hend];exact hFcc.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) i))
      (by rw [hend];exact ((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hcc).continuousOn)
      (fun n hn=>by simpa only [hend,W,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using hpair n 0 i)
      (fun n hn=>by simpa only [hend,W,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons] using hpair n 1 i)
    simpa only [hend] using ht
  obtain ⟨k0,hk0⟩ := hconst 0
  obtain ⟨k1,hk1⟩ := hconst 1
  let k : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![k0,k1]
  let c : ℝ → E2 := fun t=>c0 t+k
  have htraceF : F=ᵐ[volume.restrict W] c := by
    filter_upwards [hk0,hk1] with t ht0 ht1
    ext i
    fin_cases i
    · simpa [c,k,PiLp.add_apply] using ht0
    · simpa [c,k,PiLp.add_apply] using ht1
  have hcdEq : deriv c=deriv c0 := deriv_add_const' k
  refine ⟨q,hq,c,hlocal,hcc.add continuous_const,?_,?_,?_,?_,htraceF⟩
  · intro t
    dsimp only [c]
    rw [hcp t]
  · intro i
    have hcK : AbsolutelyContinuousOnInterval (fun _ : ℝ=>k i) (-Real.pi) Real.pi :=
      (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ=>k i)).contDiffOn.absolutelyContinuousOnInterval
    exact (hca i).add hcK
  · rw [hcdEq]
    exact hcd
  · rw [hcdEq,hcenergy]
    exact htangent.2.2.trans hqe

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
