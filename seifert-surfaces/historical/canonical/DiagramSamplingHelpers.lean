import DiagramApproximation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option maxSynthPendingDepth 3
set_option autoImplicit false
open scoped Manifold ContDiff Interval
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

def chartKnotLift (K : OrientedKnot) (L : StereographicPlacement K) (t : ℝ) : Euc 3 :=
  L.chart (K.component 0 (Circle.exp t))

def anglePolygonParameter (n : ℕ) (phase : ℝ) (i : Fin n) (s : Time) : Circle :=
  Circle.exp (phase + 2 * Real.pi * (i.val + (s : ℝ)) / n)

def moduloNext {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- Literal upstream formulas; no public rounding theorem is adopted here. -/
def roundingSmoothAbs (epsilon x : ℝ) : ℝ :=
  x + 2 * ∫ t in x..epsilon, Real.smoothTransition ((epsilon - t) / (2 * epsilon))
def roundingSmoothMax (epsilon x y : ℝ) : ℝ :=
  (x + y + roundingSmoothAbs epsilon (x - y)) / 2
def roundingSmoothCorner (epsilon : ℝ) (p v w : Euc 3) (t : ℝ) : Euc 3 :=
  p + t • v + roundingSmoothMax epsilon t 0 • (w - v)
def sampledRoundedLift (h epsilon : ℝ) (p : ℤ → Euc 3) (t : ℝ) : Euc 3 :=
  let k : ℤ := ⌊t / h + 1 / 2⌋
  roundingSmoothCorner epsilon (p k) (h⁻¹ • (p k - p (k - 1)))
    (h⁻¹ • (p (k + 1) - p k)) (t - k * h)

theorem periodic_knot_chart_regular (K : OrientedKnot) (L : StereographicPlacement K) :
    Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 3) ∞
      (fun z => L.chart (K.component 0 z)) ∧
    ContDiff ℝ ∞ (chartKnotLift K L) ∧
    Function.Periodic (chartKnotLift K L) (2 * Real.pi) ∧
    (∀ t, HasDerivAt (chartKnotLift K L) (deriv (chartKnotLift K L) t) t) ∧
    Function.Periodic (deriv (chartKnotLift K L)) (2 * Real.pi) ∧
    UniformContinuous (deriv (chartKnotLift K L)) ∧
    ∃ a : ℝ, 0 < a ∧ ∀ t, a ≤ ‖deriv (chartKnotLift K L) t‖ := by
  have hsource (z : Circle) : K.component 0 z ∈ L.chart.source := by
    rw [L.source_eq]
    intro hz
    apply L.avoids_knot
    exact ⟨z, hz⟩
  have hchart := contMDiffOn_of_mem_maximalAtlas L.chart_smooth
  have hinverse := contMDiffOn_symm_of_mem_maximalAtlas L.chart_smooth
  let c : PartialDiffeomorph (𝓡 3) 𝓘(ℝ, Euc 3) ThreeSphere (Euc 3) ∞ :=
    {toPartialEquiv := L.chart.toPartialEquiv
     open_source := L.chart.open_source
     open_target := L.chart.open_target
     contMDiffOn_toFun := hchart
     contMDiffOn_invFun := hinverse}
  let F : Circle → Euc 3 := fun z => L.chart (K.component 0 z)
  have hF : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 3) ∞ F := by
    intro z
    exact (hchart.contMDiffAt (L.chart.open_source.mem_nhds (hsource z))).comp z
      ((K.smoothEmbedding 0).contMDiff z)
  have hFi : Manifold.IsImmersion (𝓡 1) 𝓘(ℝ, Euc 3) ∞ F := by
    exact (K.smoothEmbedding 0).isImmersion.isLocalDiffeomorphOn_comp
      (fun y => c.isLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, Euc 3) ∞ (by
        obtain ⟨z, hz⟩ := y.property
        rw [← hz]
        exact hsource z))
  have hFe : IsEmbedding F := by
    exact (hF.continuous.isClosedEmbedding (fun z z' hz =>
      (K.smoothEmbedding 0).isEmbedding.injective
        (L.chart.injOn (hsource z) (hsource z') hz))).isEmbedding
  have hFemb : Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 3) ∞ F := ⟨hFi, hFe⟩
  have hExp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ Circle.exp := contMDiff_circleExp
  have hLift : ContDiff ℝ ∞ (chartKnotLift K L) := (hF.comp hExp).contDiff
  have hHas (t : ℝ) : HasDerivAt (chartKnotLift K L) (deriv (chartKnotLift K L) t) t :=
    (hLift.differentiable (by simp) t).hasDerivAt
  have hPeriod : Function.Periodic (chartKnotLift K L) (2 * Real.pi) := by
    intro t
    simp only [chartKnotLift, Circle.periodic_exp t]
  have hDPeriod : Function.Periodic (deriv (chartKnotLift K L)) (2 * Real.pi) := by
    intro t
    rw [← deriv_comp_add_const (chartKnotLift K L) (2 * Real.pi) t, hPeriod.funext]
  have hDContinuous : Continuous (deriv (chartKnotLift K L)) := hLift.continuous_deriv (by simp)
  have hDNonzero (t : ℝ) : deriv (chartKnotLift K L) t ≠ 0 := by
    let V : ℂ := Complex.exp (t * Complex.I) * Complex.I
    have hV : V ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
    have hcoeHas : HasDerivAt (fun r : ℝ => (Circle.exp r : ℂ)) V t := by
      simpa only [Circle.coe_exp, Complex.ofReal_one, one_mul, V, id_eq] using
        (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
    have hdf : Function.Injective (fderiv ℝ (fun r : ℝ => (Circle.exp r : ℂ)) t) := by
      intro a b hab
      rw [hcoeHas.hasFDerivAt.fderiv] at hab
      simp only [ContinuousLinearMap.toSpanSingleton_apply] at hab
      have hh : (a - b) • V = 0 := by rw [sub_smul, hab, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hV)
    have hmf : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
        (fun r : ℝ => (Circle.exp r : ℂ)) t) := by
      rw [mfderiv_eq_fderiv]
      exact (NormedSpace.fromTangentSpace (Circle.exp t : ℂ)).symm.injective.comp
        (hdf.comp (NormedSpace.fromTangentSpace t).injective)
    haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
    have hCoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
      contMDiff_coe_sphere
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      ((fun z : Circle => (z : ℂ)) ∘ Circle.exp) t) at hmf
    rw [mfderiv_comp t (hCoe.mdifferentiableAt (by simp))
      (hExp.mdifferentiableAt (by simp))] at hmf
    have hExpInj : Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) :=
      Function.Injective.of_comp hmf
    have hCompInj : Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Euc 3)
        (F ∘ Circle.exp) t) := by
      rw [mfderiv_comp t (hF.mdifferentiableAt (by simp))
        (hExp.mdifferentiableAt (by simp))]
      exact (hFi.mfderiv_injective (by simp) _).comp hExpInj
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Euc 3) (chartKnotLift K L) t) at hCompInj
    intro hz
    let u := (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (1 : ℝ)
    let v := (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm (0 : ℝ)
    have heq : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Euc 3) (chartKnotLift K L) t u =
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Euc 3) (chartKnotLift K L) t v := by
      rw [mfderiv_eq_fderiv]
      simp [u, v, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, hz]
    have hab := congrArg (NormedSpace.fromTangentSpace (𝕜 := ℝ) t) (hCompInj heq)
    simpa only [u, v, ContinuousLinearEquiv.apply_symm_apply, one_ne_zero] using hab
  have hUniform : UniformContinuous (deriv (chartKnotLift K L)) := by
    have hcompact : IsCompact (Icc (-1 : ℝ) (2 * Real.pi + 1)) := isCompact_Icc
    have hu := hcompact.uniformContinuousOn_of_continuous hDContinuous.continuousOn
    apply Metric.uniformContinuous_iff.mpr
    intro epsilon hepsilon
    obtain ⟨delta, hdelta, hd⟩ := Metric.uniformContinuousOn_iff.mp hu epsilon hepsilon
    refine ⟨min delta 1, lt_min hdelta zero_lt_one, ?_⟩
    intro x y hxy
    obtain ⟨m, hm, _⟩ := existsUnique_add_zsmul_mem_Ico
      (mul_pos zero_lt_two Real.pi_pos) x (0 : ℝ)
    have hx : x + m • (2 * Real.pi) ∈ Icc (-1 : ℝ) (2 * Real.pi + 1) := by
      constructor <;> linarith [hm.1, hm.2]
    have hdist : dist (x + m • (2 * Real.pi)) (y + m • (2 * Real.pi)) = dist x y :=
      dist_add_right _ _ _
    have hsmall : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
    have hsmall' := abs_lt.mp (show |x - y| < 1 by simpa only [Real.dist_eq] using hsmall)
    have hy : y + m • (2 * Real.pi) ∈ Icc (-1 : ℝ) (2 * Real.pi + 1) := by
      constructor <;> linarith [hm.1, hm.2, hsmall'.1, hsmall'.2]
    have hh := hd (x + m • (2 * Real.pi)) hx (y + m • (2 * Real.pi)) hy
      (hdist ▸ lt_of_lt_of_le hxy (min_le_left _ _))
    simpa only [hDPeriod.zsmul m x, hDPeriod.zsmul m y] using hh
  have hcompact := hDPeriod.compact_of_continuous
    (mul_ne_zero (by norm_num) Real.pi_ne_zero) hDContinuous
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn (Set.range_nonempty _) continuous_norm.continuousOn
  refine ⟨hFemb, hLift, hPeriod, hHas, hDPeriod, hUniform, ‖v‖, ?_, ?_⟩
  · rw [norm_pos_iff]
    obtain ⟨t, rfl⟩ := hv
    exact hDNonzero t
  · intro t
    exact hmin (Set.mem_range_self t)

structure SampledCyclicPolygon (K : OrientedKnot) (L : StereographicPlacement K)
    (eta : ℝ) where
  n : ℕ
  n_ge_three : 3 ≤ n
  h : ℝ
  h_eq : h = 2 * Real.pi / n
  h_pos : 0 < h
  polygon : PolygonalKnot
  indexing : Fin n ≃ Fin polygon.polygon.count
  next_eq : ∀ i, indexing (moduloNext i) = polygon.polygon.next (indexing i)
  vertex_eq : ∀ i, polygon.polygon.vertex (indexing i) = chartKnotLift K L (i.val * h)
  phase_eq : ∀ i s, polygon.parametrization (anglePolygonParameter n 0 i s) =
    Quotient.mk (polygonSetoid polygon.polygon) (indexing i, s)
  value_close : ∀ i s,
    ‖polygonEdge polygon.polygon (indexing i) s -
      chartKnotLift K L ((i.val + (s : ℝ)) * h)‖ < eta
  secant_close : ∀ i, ∀ s : Time,
    ‖h⁻¹ • (polygon.polygon.vertex (indexing (moduloNext i)) -
      polygon.polygon.vertex (indexing i)) -
      deriv (chartKnotLift K L) ((i.val + (s : ℝ)) * h)‖ < eta
  separation : ℝ
  separation_pos : 0 < separation
  separated : ∀ i j, i ≠ j → polygon.polygon.next i ≠ j →
    polygon.polygon.next j ≠ i →
    Disjoint (Metric.thickening separation (Set.range (polygonEdge polygon.polygon i)))
      (Metric.thickening separation (Set.range (polygonEdge polygon.polygon j)))


structure RoundedSampledPolygon {K : OrientedKnot} {L : StereographicPlacement K}
    {sampleTolerance : ℝ} (S : SampledCyclicPolygon K L sampleTolerance) (eta : ℝ) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_half_h : epsilon < S.h / 2
  smoothing : PolygonSmoothing S.polygon
  rounded_eq : ∀ t, smoothing.curve (Circle.exp t) =
    sampledRoundedLift S.h epsilon (fun k : ℤ => chartKnotLift K L (k * S.h)) t
  value_close : ∀ t, ‖smoothing.curve (Circle.exp t) - chartKnotLift K L t‖ < eta
  deriv_close : ∀ t,
    ‖deriv (fun r : ℝ => smoothing.curve (Circle.exp r)) t -
      deriv (chartKnotLift K L) t‖ < eta



end
end SeifertSurfaces.LongitudeProducers
