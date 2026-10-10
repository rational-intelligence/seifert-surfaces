import InitialHarmonicTraceRadiusAE_v460
import InitialAngularWeightedFlux_v445
import InitialArcPrimitive_v411

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 400000

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_polynomial_trace_radius" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialHarmonicTraceRadiusAE_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_cap_harmonic_trace_radius_with_ae_v460)⟩
local macro "paid_actual_cap_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArtificialCircleGeometry_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_boundary_cap_circle_geometry_v411)⟩
local macro "paid_circle_tangent_L2" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialTangentialPrimitive_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_circle_tangential_L2_v411)⟩
local macro "paid_circle_tangent_period" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialPeriodicTangential_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.actual_circle_tangential_period_v411)⟩
local macro "paid_supported_arc_primitive" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialArcPrimitive_v411 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.circle_supported_arc_primitive_v411)⟩

/- An unconditional actual-arc producer for the original minimizer. The
literal original circle slice is retained; the path is anchored at the true
first endpoint, supported on the correct arc, and ends at the true second
endpoint. Its full one-dimensional Green identity and energy are proved. -/
private theorem original_harmonic_actual_cap_arc_path_with_ae_v460
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
      ∀ (n : ℕ) (k i : Fin 2),
        (∫ t in angles,
          a t i * phi n k (unitCircleParameter s + q • unitCircleParameter t) +
          f0 (unitCircleParameter s + q • unitCircleParameter t) i *
            deriv (fun u => phi n k (unitCircleParameter s + q • unitCircleParameter u)) t) =
          liftedBoundaryValue Ω theta (s - 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter bb) -
          liftedBoundaryValue Ω theta (s + 2 * e) i *
            phi n k (unitCircleParameter s + q • unitCircleParameter aa) := by
  classical
  dsimp only
  let f0 : E2 → E2 := (disc 1).indicator f
  let d0 : Fin 2 → E2 → E2 := fun i => (disc 1).indicator (d i)
  let angles : Set ℝ := Ioo (-Real.pi) Real.pi
  let center := unitCircleParameter s
  let J : E2 → E2 := fun v =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-v 1, v 0]
  obtain ⟨q, hq,hqx, hqf, hqd, hqpol, hqe⟩ :=
    paid_polynomial_trace_radius minimum theta sigma lift trace s r hr hrhalf Extra hExtra
  let e := Real.arcsin (q / 2)
  let aa := s + Real.pi / 2 + e
  let bb := s + 3 * Real.pi / 2 - e
  let a : ℝ → E2 := fun t =>
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i => q * inner ℝ (d0 i (unitCircleParameter s + q • unitCircleParameter t))
        (J (unitCircleParameter t)))
  let phi : ℕ → Fin 2 → E2 → ℝ := fun n k z =>
      ![((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
          ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).re,
        ((((z 0 - unitCircleParameter s 0 : ℝ) : ℂ) +
          ((z 1 - unitCircleParameter s 1 : ℝ) : ℂ) * Complex.I) ^ n).im] k
  let b0 := liftedBoundaryValue Ω theta (s + 2 * e)
  let b1 := liftedBoundaryValue Ω theta (s - 2 * e)
  let c : ℝ → E2 := fun t => b0 + ∫ x in aa..t, a x
  have hqpos : 0 < q := lt_trans (by positivity) hq.1
  have hqhalf : q ≤ 1 / 2 := hq.2.le.trans hrhalf
  have hg := paid_actual_cap_geometry s q hqpos hqhalf
  dsimp only at hg
  change aa < bb ∧ bb - aa ≤ Real.pi ∧ bb < aa + 2 * Real.pi ∧
    unitCircleParameter s + q • unitCircleParameter aa = unitCircleParameter (s + 2 * e) ∧
    unitCircleParameter s + q • unitCircleParameter bb = unitCircleParameter (s - 2 * e) ∧
    (∀ t ∈ Ioo aa bb, unitCircleParameter s + q • unitCircleParameter t ∈ disc 1) ∧
    (∀ t ∈ Icc bb (aa + 2 * Real.pi),
      unitCircleParameter s + q • unitCircleParameter t ∉ disc 1) at hg
  have houtside : ∀ t ∈ Icc bb (aa + 2 * Real.pi), a t = 0 := by
    intro t ht
    have hz := hg.2.2.2.2.2.2 t ht
    ext i
    simp [a, d0, indicator_of_notMem hz]
  have htangent := paid_circle_tangent_L2 d0 (unitCircleParameter s) q hqd
  dsimp only at htangent
  change MemLp a 2 (volume.restrict angles) ∧
    (∀ t, ‖a t‖ ^ 2 ≤ q ^ 2 * euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t)) ∧
    (∫ t in angles, ‖a t‖ ^ 2) ≤
      q ^ 2 * ∫ t in angles, euclideanJetDensity d0 (unitCircleParameter s + q • unitCircleParameter t) at htangent
  have hperiod : Periodic a (2 * Real.pi) :=
    paid_circle_tangent_period d0 (unitCircleParameter s) q
  let : IsFiniteMeasure (volume.restrict angles) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have haI : IntegrableOn a angles := htangent.1.integrable (by norm_num)
  have hends : (∫ t in angles, a t) = b1 - b0 := by
    ext i
    have hp := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm haI
    change (∫ t in angles, a t i) = (∫ t in angles, a t) i at hp
    rw [← hp]
    change (∫ t in angles, q * inner ℝ
      (d0 i (unitCircleParameter s + q • unitCircleParameter t)) (J (unitCircleParameter t))) = _
    rw [integral_const_mul]
    have hflux := hqpol 0 0 i
    have hzero : (WithLp.toLp 2 (fun _ : Fin 2 => (0 : ℝ)) : E2) = 0 := rfl
    simpa [b1, b0, e, phi, d0, J, angles, hzero] using hflux.symm
  have hc := paid_supported_arc_primitive a hperiod htangent.1 aa bb hg.1.le hg.2.2.1.le
    houtside b0 b1 hends
  dsimp only at hc
  change ContinuousOn c (Icc aa bb) ∧ c aa = b0 ∧ c bb = b1 ∧
    (∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => c t i) aa bb) ∧
    (∀ᵐ t ∂volume.restrict (Icc aa bb), HasDerivAt c (a t) t) ∧
    MemLp (deriv c) 2 (volume.restrict (Icc aa bb)) ∧
    (∫ t in Icc aa bb, ‖deriv c t‖ ^ 2) ≤ ∫ t in angles, ‖a t‖ ^ 2 ∧
    (∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → ∀ i : Fin 2,
      (∫ t in Icc aa bb, a t i * psi t + c t i * deriv psi t) =
        b1 i * psi bb - b0 i * psi aa) at hc
  refine ⟨q, hq,hqx, hqf, hqd, hg.1, hg.2.1, hc.1, hc.2.1, hc.2.2.1,
    hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_, hc.2.2.2.2.2.2.2, ?_⟩
  · exact hc.2.2.2.2.2.2.1.trans (htangent.2.2.trans hqe)
  · intro n k i
    have hphi : ContDiff ℝ ∞ (phi n k) := by
      run_tac Lean.Elab.Tactic.withMainContext do
        let name := (Lean.Name.num `_private.InitialHarmonicTests_v445 0) ++
          `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.centered_complex_circle_power_tests_v445
        let xx ← Lean.Elab.Term.elabTerm (Lean.mkIdent `center) none
        let nn ← Lean.Elab.Term.elabTerm (Lean.mkIdent `n) none
        let kk ← Lean.Elab.Term.elabTerm (Lean.mkIdent `k) none
        let hp := Lean.mkAppN (Lean.mkConst name) #[xx, nn]
        let left ← Lean.Meta.mkAppM ``And.left #[hp]
        Lean.Elab.Tactic.closeMainGoal `harmonic_smooth (Lean.mkApp left kk)
    let weight := phi n k
    have hpoint : ∀ t : ℝ,
        q * inner ℝ ((disc 1).indicator
            (fun z => weight z • d i z + f z i •
              (EuclideanSpace.equiv (Fin 2) ℝ).symm
                (fun j => fderiv ℝ weight z (coordinateVector 2 j)))
            (unitCircleParameter s + q • unitCircleParameter t))
          (J (unitCircleParameter t)) =
        weight (unitCircleParameter s + q • unitCircleParameter t) * a t i +
          f0 (unitCircleParameter s + q • unitCircleParameter t) i *
            deriv (fun u => weight (unitCircleParameter s + q • unitCircleParameter u)) t := by
      run_tac Lean.Elab.Tactic.withMainContext do
        let name := (Lean.Name.num `_private.InitialAngularWeightedFlux_v445 0) ++
          `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_weighted_angular_integrand_v445
        let args ← ([`f, `d, `weight, `hphi, `center, `q].toArray.mapM
          fun n => Lean.Elab.Term.elabTerm (Lean.mkIdent n) none)
        let ii ← Lean.Elab.Term.elabTerm (Lean.mkIdent `i) none
        let all := Lean.mkAppN (Lean.mkConst name) args
        Lean.Elab.Tactic.closeMainGoal `native_angular_integrand (Lean.mkApp all ii)
    have hflux := hqpol n k i
    rw [← integral_const_mul] at hflux
    have hrewrite :
        (∫ t in angles,
          a t i * weight (unitCircleParameter s + q • unitCircleParameter t) +
            f0 (unitCircleParameter s + q • unitCircleParameter t) i *
              deriv (fun u => weight (unitCircleParameter s + q • unitCircleParameter u)) t) =
        ∫ t in angles,
          q * inner ℝ ((disc 1).indicator
            (fun z => weight z • d i z + f z i •
              (EuclideanSpace.equiv (Fin 2) ℝ).symm
                (fun j => fderiv ℝ weight z (coordinateVector 2 j)))
            (unitCircleParameter s + q • unitCircleParameter t))
            (J (unitCircleParameter t)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hpoint]
      ring
    change _ = b1 i * weight (unitCircleParameter s + q • unitCircleParameter bb) -
      b0 i * weight (unitCircleParameter s + q • unitCircleParameter aa)
    rw [hrewrite, hg.2.2.2.1, hg.2.2.2.2.1]
    change weight (unitCircleParameter (s - 2 * e)) * b1 i -
      weight (unitCircleParameter (s + 2 * e)) * b0 i = _ at hflux
    rw [mul_comm (b1 i), mul_comm (b0 i)]
    exact hflux.symm

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
