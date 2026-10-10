import InitialHarmonicActualArcAE_v460
import InitialPositiveTraceUniqueness_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_harmonic_actual_arc" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialHarmonicActualArcAE_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_harmonic_actual_cap_arc_path_with_ae_v460)⟩

local macro "paid_circle_tangent_L2" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialTangentialPrimitive_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_circle_tangential_L2_v411)⟩

local macro "paid_circle_tangent_period" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTangential_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_circle_tangential_period_v411)⟩

local macro "paid_periodic_vector" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTangential_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.periodic_tangent_all_intervals_v411)⟩

local macro "paid_actual_cap_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArtificialCircleGeometry_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_boundary_cap_circle_geometry_v411)⟩

local macro "paid_harmonic_test" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialHarmonicTests_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.centered_complex_circle_power_tests_v445)⟩

local macro "paid_normalize_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPositiveTraceUniqueness_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.scaled_angular_green_v457)⟩

local macro "paid_trig_period" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPositiveTraceUniqueness_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.nat_frequency_periodic_v457)⟩

local macro "paid_shift_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPositiveTraceUniqueness_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.periodic_angular_green_shift_v457)⟩

local macro "paid_residual_pairing" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArcResidualGreen_v445 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_arc_residual_pairing_v445)⟩

local macro "paid_positive_unique" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPositiveTraceUniqueness_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.real_arc_trace_uniqueness_positive_v457)⟩

private theorem original_literal_cap_arc_trace_with_ae_v460
    {R : ℝ} {Ω : SmoothFlatJordanDomain R} {M : E2 → Mat2}
    {f : E2 → E2} {d : Fin 2 → E2 → E2}
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (trace : HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta))
    (s r : ℝ) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (Extra : ℝ → Prop)
    (hExtra : ∀ᵐ q ∂volume.restrict (Ioo (r / 2) r),Extra q) :
    let f0 : E2 → E2 := (disc 1).indicator f
    let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
    let angles : Set ℝ := Ioo (-Real.pi) Real.pi
    let J : E2 → E2 := fun v =>
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
    let shell : ℝ :=
      (∫ z in planarCap (unitCircleParameter s) r, euclideanJetDensity d z) -
        (∫ z in planarCap (unitCircleParameter s) (r / 2), euclideanJetDensity d z)
    ∃ q ∈ Ioo (r / 2) r,Extra q ∧
      MemLp (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles) ∧
      (∀ i, MemLp (fun t => d0 i (unitCircleParameter s + q • unitCircleParameter t)) 2
        (volume.restrict angles)) ∧
      let e : ℝ := Real.arcsin (q / 2)
      let aa : ℝ := s + Real.pi / 2 + e
      let bb : ℝ := s + 3 * Real.pi / 2 - e
      let a : ℝ → E2 := fun t =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun i => q * inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t)))
      let c : ℝ → E2 := fun t =>
        liftedBoundaryValue Ω theta (s + 2 * e) + ∫ x in aa..t, a x
      aa < bb ∧ bb - aa ≤ Real.pi ∧
      ContinuousOn c (Icc aa bb) ∧
      c aa = liftedBoundaryValue Ω theta (s + 2 * e) ∧
      c bb = liftedBoundaryValue Ω theta (s - 2 * e) ∧
      (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) ∧
      (∀ᵐ t ∂volume.restrict (Icc aa bb), HasDerivAt c (a t) t) ∧
      MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) ∧
      (∫ t in Icc aa bb, ‖deriv c t‖ ^ 2) ≤ 2 * shell ∧
      (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
        (∫ t in Icc aa bb, a t i * psi t + c t i * deriv psi t) =
          liftedBoundaryValue Ω theta (s - 2 * e) i * psi bb -
            liftedBoundaryValue Ω theta (s + 2 * e) i * psi aa) ∧
      let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
        ![((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
            ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).re,
          ((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
            ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).im] k
      (∀ (n : ℕ) (k i : Fin 2),
        (∫ t in angles,
          a t i * phi n k (unitCircleParameter s + q • unitCircleParameter t) +
          f0 (unitCircleParameter s + q • unitCircleParameter t) i *
            deriv (fun u => phi n k (unitCircleParameter s + q • unitCircleParameter u)) t) =
          liftedBoundaryValue Ω theta (s - 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter bb) -
          liftedBoundaryValue Ω theta (s + 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter aa)) ∧
      (fun t => f0 (unitCircleParameter s + q • unitCircleParameter t))
        =ᵐ[volume.restrict (Icc aa bb)] c := by
  classical
  dsimp only
  let f0 : E2 → E2 := (disc 1).indicator f
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let center := unitCircleParameter s
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  obtain ⟨q,hq,hqx,hqf,hqd,hpath⟩ :=
    paid_harmonic_actual_arc minimum theta sigma lift trace s r hr hrhalf Extra hExtra
  let e := Real.arcsin (q / 2)
  let aa := s + Real.pi / 2 + e
  let bb := s + 3 * Real.pi / 2 - e
  let a : ℝ → E2 := fun t =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => q * inner ℝ (d0 i (center + q • unitCircleParameter t))
        (J (unitCircleParameter t)))
  let F : ℝ → E2 := fun t => f0 (center + q • unitCircleParameter t)
  let c : ℝ → E2 := fun t => liftedBoundaryValue Ω theta (s + 2 * e) + ∫ x in aa..t,a x
  let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
      ![((((z 0 - center 0 : ℝ) : ℂ) + ((z 1 - center 1 : ℝ) : ℂ) * Complex.I)^n).re,
        ((((z 0 - center 0 : ℝ) : ℂ) + ((z 1 - center 1 : ℝ) : ℂ) * Complex.I)^n).im] k
  dsimp only at hpath
  rcases hpath with ⟨haa,hwidth,hcont,hca,hcb,hac,hder,hL2,hen,hgreen,harm⟩
  change c aa = liftedBoundaryValue Ω theta (s + 2 * e) at hca
  change c bb = liftedBoundaryValue Ω theta (s - 2 * e) at hcb
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqhalf : q ≤ 1/2 := hq.2.le.trans hrhalf
  have hg := paid_actual_cap_geometry s q hqpos hqhalf
  dsimp only at hg
  have hvp : bb < aa + 2 * Real.pi := hg.2.2.1
  have houta : ∀ t ∈ Icc bb (aa + 2 * Real.pi), a t = 0 := by
    intro t ht
    have hz := hg.2.2.2.2.2.2 t ht
    ext i
    simp [a,d0,center,indicator_of_notMem hz]
  have houtF : ∀ t ∈ Ioo bb (aa + 2 * Real.pi), F t = 0 := by
    intro t ht
    exact indicator_of_notMem (hg.2.2.2.2.2.2 t ⟨ht.1.le,ht.2.le⟩) f
  have hcircle : Periodic unitCircleParameter (2 * Real.pi) := by
    intro t
    ext i
    fin_cases i <;> simp [unitCircleParameter,Real.cos_add_two_pi,Real.sin_add_two_pi]
  have hFperiod : Periodic F (2 * Real.pi) := fun t => by dsimp only [F]; rw [hcircle t]
  have haperiod : Periodic a (2 * Real.pi) := paid_circle_tangent_period d0 center q
  have ha0 := (paid_circle_tangent_L2 d0 center q hqd).1
  have hFS := (paid_periodic_vector F hFperiod hqf).1 aa (aa+2*Real.pi)
  have haS := (paid_periodic_vector a haperiod ha0).1 aa (aa+2*Real.pi)
  let W := Icc aa (aa+2*Real.pi)
  let : IsFiniteMeasure (volume.restrict W) :=
    isFiniteMeasure_restrict.mpr measure_Icc_lt_top.ne
  have hFc (i : Fin 2) : MemLp (fun t => F t i) 2 (volume.restrict W) :=
    hFS.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)
  have hacI (i : Fin 2) : IntegrableOn (fun t => a t i) W :=
    (haS.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)).integrable (by norm_num)
  have hFcI (i : Fin 2) : IntegrableOn (fun t => F t i) W := (hFc i).integrable (by norm_num)
  have hccont (i : Fin 2) : ContinuousOn (fun t => c t i) (Icc aa bb) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp_continuousOn hcont
  have hcos (n : ℕ) (i : Fin 2) :
      (∫ t in W,(F t i-(Icc aa bb).indicator (fun z => c z i) t)*
        deriv (fun z => Real.cos ((n:ℝ)*z)) t)=0 := by
    let psi : ℝ → ℝ := fun z => Real.cos ((n:ℝ)*z)
    have hpsi : ContDiff ℝ ∞ psi := by fun_prop
    have hdc : ∀ t : ℝ, deriv psi t = -(n:ℝ)*Real.sin ((n:ℝ)*t) := by
      intro t
      simp [psi,mul_comm,mul_left_comm,mul_assoc]
    have hp := paid_trig_period n
    have hdperiod : Periodic (deriv psi) (2*Real.pi) := by
      intro t
      simp only [hdc]
      exact congrArg (fun y : ℝ => -(n:ℝ)*y) (hp.2 t)
    have htest : (fun t => phi n 0 (center+q•unitCircleParameter t)) =
        (fun t => q^n*psi t) := by
      funext t
      exact (paid_harmonic_test center n).2 q t |>.1
    have hscaled := harm n 0 i
    rw [←hcb,←hca] at hscaled
    change (∫ t in angles,a t i*phi n 0 (center+q•unitCircleParameter t)+
      F t i*deriv (fun u=>phi n 0 (center+q•unitCircleParameter u)) t)=
      c bb i*phi n 0 (center+q•unitCircleParameter bb)-
      c aa i*phi n 0 (center+q•unitCircleParameter aa) at hscaled
    have hpoint := congrFun htest
    simp only [hpoint] at hscaled
    have horig := paid_normalize_green q hqpos.ne' n angles (fun t=>a t i)
      (fun t=>F t i) psi hpsi aa bb (c aa i) (c bb i) hscaled
    have hshift := paid_shift_green (fun t=>a t i) (fun t=>F t i) psi
      (fun t=>congrArg (fun v:E2=>v i) (haperiod t))
      (fun t=>congrArg (fun v:E2=>v i) (hFperiod t)) hp.1 hdperiod aa
    have hprim := hgreen psi hpsi i
    change (∫ t in Icc aa bb,a t i*psi t+c t i*deriv psi t)=
      liftedBoundaryValue Ω theta (s-2*e) i*psi bb-
      liftedBoundaryValue Ω theta (s+2*e) i*psi aa at hprim
    rw [← hcb,← hca] at hprim
    exact paid_residual_pairing aa bb haa.le hvp.le (fun t=>F t i) (fun t=>a t i)
      (fun t=>c t i) (hFcI i) (hacI i) (hccont i)
      (fun t ht=>congrArg (fun v:E2=>v i) (houta t ht)) psi hpsi
      (hshift.trans horig) hprim
  have hsin (n : ℕ) (i : Fin 2) :
      (∫ t in W,(F t i-(Icc aa bb).indicator (fun z => c z i) t)*
        deriv (fun z => Real.sin ((n:ℝ)*z)) t)=0 := by
    let psi : ℝ → ℝ := fun z => Real.sin ((n:ℝ)*z)
    have hpsi : ContDiff ℝ ∞ psi := by fun_prop
    have hds : ∀ t : ℝ, deriv psi t = (n:ℝ)*Real.cos ((n:ℝ)*t) := by
      intro t
      simp [psi,mul_comm,mul_left_comm,mul_assoc]
    have hp := paid_trig_period n
    have hdperiod : Periodic (deriv psi) (2*Real.pi) := by
      intro t
      simp only [hds]
      exact congrArg (fun y : ℝ => (n:ℝ)*y) (hp.1 t)
    have htest : (fun t => phi n 1 (center+q•unitCircleParameter t)) =
        (fun t => q^n*psi t) := by
      funext t
      exact (paid_harmonic_test center n).2 q t |>.2
    have hscaled := harm n 1 i
    rw [←hcb,←hca] at hscaled
    change (∫ t in angles,a t i*phi n 1 (center+q•unitCircleParameter t)+
      F t i*deriv (fun u=>phi n 1 (center+q•unitCircleParameter u)) t)=
      c bb i*phi n 1 (center+q•unitCircleParameter bb)-
      c aa i*phi n 1 (center+q•unitCircleParameter aa) at hscaled
    have hpoint := congrFun htest
    simp only [hpoint] at hscaled
    have horig := paid_normalize_green q hqpos.ne' n angles (fun t=>a t i)
      (fun t=>F t i) psi hpsi aa bb (c aa i) (c bb i) hscaled
    have hshift := paid_shift_green (fun t=>a t i) (fun t=>F t i) psi
      (fun t=>congrArg (fun v:E2=>v i) (haperiod t))
      (fun t=>congrArg (fun v:E2=>v i) (hFperiod t)) hp.2 hdperiod aa
    have hprim := hgreen psi hpsi i
    change (∫ t in Icc aa bb,a t i*psi t+c t i*deriv psi t)=
      liftedBoundaryValue Ω theta (s-2*e) i*psi bb-
      liftedBoundaryValue Ω theta (s+2*e) i*psi aa at hprim
    rw [← hcb,← hca] at hprim
    exact paid_residual_pairing aa bb haa.le hvp.le (fun t=>F t i) (fun t=>a t i)
      (fun t=>c t i) (hFcI i) (hacI i) (hccont i)
      (fun t ht=>congrArg (fun v:E2=>v i) (houta t ht)) psi hpsi
      (hshift.trans horig) hprim
  have heq (i : Fin 2) : (fun t=>F t i)=ᵐ[volume.restrict (Icc aa bb)] (fun t=>c t i) :=
    paid_positive_unique aa bb haa.le hvp (fun t=>F t i) (fun t=>c t i)
      (hFc i) (hccont i) (fun t ht=>congrArg (fun v:E2=>v i) (houtF t ht))
      (fun n _=>hcos n i) (fun n _=>hsin n i)
  have hvec : F=ᵐ[volume.restrict (Icc aa bb)] c := by
    filter_upwards [heq 0,heq 1] with t h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  exact ⟨q,hq,hqx,hqf,hqd,haa,hwidth,hcont,hca,hcb,hac,hder,hL2,hen,hgreen,harm,hvec⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
