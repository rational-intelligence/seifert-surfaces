import Mathlib

/-!
Coordinate geometry and analytic obligations for Appendix A, pp. 24--28.
Unlike an abstract `regularity : Prop` field, the definitions here fix the metric,
Christoffel symbols, Hessian, induced metric, and traced normal acceleration.
The coordinate A.4 theorem still requires a chart-to-manifold bridge, and its
analytic proof is a substantial open obligation. This file does not assert A.5/A.6.
-/

noncomputable section

open Set MeasureTheory Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates

set_option maxHeartbeats 1000000

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev MetricTensor := E3 → Matrix (Fin 3) (Fin 3) ℝ

def coordinateVector (n : ℕ) (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single i 1

/-- Metric scalar product in a local three-dimensional chart. -/
def coordinateInner (g : MetricTensor) (y : E3) (v w : E3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, g y a b * v a * w b

/-- Actual smooth positive-definite metric coefficients on an open coordinate domain. -/
structure CoordinateMetric (V : Set E3) where
  tensor : MetricTensor
  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun y => tensor y a b) V
  symmetric : ∀ y ∈ V, ∀ a b, tensor y a b = tensor y b a
  positive : ∀ y ∈ V, ∀ v : E3, v ≠ 0 → 0 < coordinateInner tensor y v v

/-- A coordinate partial derivative; every use below is at a point where the function is smooth. -/
def partial3 (f : E3 → ℝ) (y : E3) (a : Fin 3) : ℝ :=
  fderiv ℝ f y (coordinateVector 3 a)

/-- The Levi-Civita Christoffel coefficient in coordinates. -/
def christoffel (g : MetricTensor) (y : E3) (a b k : Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin 3, (g y)⁻¹ k l *
    (partial3 (fun z => g z l b) y a + partial3 (fun z => g z l a) y b -
      partial3 (fun z => g z a b) y l)

/-- The covariant Hessian of the collar defining function. -/
def hessianCoefficient (g : MetricTensor) (r : E3 → ℝ) (y : E3)
    (a b : Fin 3) : ℝ :=
  partial3 (fun z => partial3 r z b) y a -
    ∑ k : Fin 3, christoffel g y a b k * partial3 r y k

def hessianQuadratic (g : MetricTensor) (r : E3 → ℝ) (y v : E3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, hessianCoefficient g r y a b * v a * v b

/-- A.4's graph map. A scalar height is sufficient because the orthogonal complement
of a plane in three-space is one-dimensional. -/
def graphMap (p : E3) (L : E2 →L[ℝ] E3) (normal : E3) (w : E2 → ℝ) : E2 → E3 :=
  fun x => p + L x + w x • normal

def graphTangent (Φ : E2 → E3) (x : E2) (i : Fin 2) : E3 :=
  fderiv ℝ Φ x (coordinateVector 2 i)

def inducedMetric (g : MetricTensor) (Φ : E2 → E3) (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordinateInner g (Φ x) (graphTangent Φ x i) (graphTangent Φ x j)

def covariantAcceleration (g : MetricTensor) (Φ : E2 → E3) (x : E2)
    (i j : Fin 2) : E3 :=
  fderiv ℝ (fun z => graphTangent Φ z j) x (coordinateVector 2 i) +
    ∑ k : Fin 3, (∑ a : Fin 3, ∑ b : Fin 3,
      christoffel g (Φ x) a b k * graphTangent Φ x i a * graphTangent Φ x j b) •
        coordinateVector 3 k

/-- Trace of ambient covariant acceleration before taking its normal component. -/
def tracedAcceleration (g : MetricTensor) (Φ : E2 → E3) (x : E2) : E3 :=
  ∑ i : Fin 2, ∑ j : Fin 2, (inducedMetric g Φ x)⁻¹ i j •
    covariantAcceleration g Φ x i j

/-- For an immersion, this says precisely that the normal trace of the second fundamental
form vanishes. The tangential component is allowed, as arbitrary graph coordinates need
not be intrinsic geodesic coordinates. -/
def IsMinimalParametrizationOn (g : MetricTensor) (Φ : E2 → E3) (Ω : Set E2) : Prop :=
  ContDiffOn ℝ ∞ Φ Ω ∧
    ∀ x ∈ Ω, tracedAcceleration g Φ x ∈ LinearMap.range (fderiv ℝ Φ x).toLinearMap

/-- The interior sphere condition at a point of a closed planar region, exactly as in A.4. -/
def InteriorSphereAt (U : Set E2) (x : E2) : Prop :=
  ∃ c : E2, ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball c ρ ⊆ interior U ∧ dist x c = ρ

/-- The circular half-disc used in A.7. -/
def closedHalfDisc (ρ : ℝ) : Set E2 :=
  Metric.closedBall 0 ρ ∩ {x : E2 | 0 ≤ x 0}

theorem halfDisc_has_interiorSphere (ρ : ℝ) (hρ : 0 < ρ) :
    InteriorSphereAt (closedHalfDisc ρ) 0 := by
  let c : E2 := EuclideanSpace.single 0 (ρ / 2)
  have hc : ‖c‖ = ρ / 2 := by
    simp [c, EuclideanSpace.single, PiLp.norm_single, hρ.le]
  refine ⟨c, ρ / 2, half_pos hρ, ?_, ?_⟩
  · apply interior_maximal _ Metric.isOpen_ball
    intro x hx
    have hxc : ‖x - c‖ < ρ / 2 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hcoord : |x 0 - ρ / 2| < ρ / 2 := by
      have h := (PiLp.norm_apply_le (x - c) 0).trans_lt hxc
      simpa [c, EuclideanSpace.single, PiLp.single_apply, Real.norm_eq_abs] using h
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hn := norm_add_le (x - c) c
      rw [sub_add_cancel, hc] at hn
      linarith
    · change 0 ≤ x 0
      linarith [(abs_lt.mp hcoord).1]
  · simpa only [dist_zero_left] using hc

/-- The collar calculation needed by A.4: a nonpositive Hessian has nonpositive
trace on any finite orthonormal frame. The frame orthonormality is irrelevant for this
pure sign step and is consequently not imposed here. -/
theorem hessian_trace_nonpositive {ι : Type*} (s : Finset ι)
    (g : MetricTensor) (r : E3 → ℝ) (y : E3) (frame : ι → E3)
    (hHess : ∀ v : E3, hessianQuadratic g r y v ≤ 0) :
    ∑ i ∈ s, hessianQuadratic g r y (frame i) ≤ 0 := by
  exact Finset.sum_nonpos fun i _ => hHess (frame i)

lemma coordinateInner_add_left (g : MetricTensor) (y u v w : E3) :
    coordinateInner g y (u + v) w = coordinateInner g y u w + coordinateInner g y v w := by
  simp only [coordinateInner, PiLp.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma coordinateInner_smul_left (g : MetricTensor) (y v w : E3) (c : ℝ) :
    coordinateInner g y (c • v) w = c * coordinateInner g y v w := by
  simp only [coordinateInner, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

lemma coordinateInner_zero_left (g : MetricTensor) (y w : E3) :
    coordinateInner g y 0 w = 0 := by simp [coordinateInner]

lemma graph_linearization_injective
    (V : Set E3) (g : CoordinateMetric V) (p normal : E3) (hp : p ∈ V)
    (hnormal : normal ≠ 0) (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (hnormalOrthogonal : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (dw : E2 →L[ℝ] ℝ) :
    Function.Injective (L + dw.smulRight normal) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change L v + dw v • normal = 0 at hv
  have hpv : coordinateInner g.tensor p (L v + dw v • normal) normal = 0 := by
    rw [hv]
    exact coordinateInner_zero_left g.tensor p normal
  rw [coordinateInner_add_left, hnormalOrthogonal, zero_add, coordinateInner_smul_left] at hpv
  have hdw : dw v = 0 := (mul_eq_zero.mp hpv).resolve_right (ne_of_gt (g.positive p hp normal hnormal))
  apply hL
  simpa only [hdw, zero_smul, add_zero, map_zero] using hv

lemma graph_fderiv_injective
    (V : Set E3) (g : CoordinateMetric V) (p normal : E3) (hp : p ∈ V)
    (hnormal : normal ≠ 0) (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (hnormalOrthogonal : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (w : E2 → ℝ) (x : E2) (hw : DifferentiableAt ℝ w x) :
    Function.Injective (fderiv ℝ (graphMap p L normal w) x) := by
  have hderiv : HasFDerivAt (graphMap p L normal w)
      (L + (fderiv ℝ w x).smulRight normal) x := by
    convert ((hasFDerivAt_const p x).add (L.hasFDerivAt)).add
      (hw.hasFDerivAt.smul_const normal) using 1 <;> first | rfl | simp only [zero_add]
  rw [hderiv.fderiv]
  exact graph_linearization_injective V g p normal hp hnormal L hL hnormalOrthogonal _

lemma graph_fderiv_injective_on_interior
    (V : Set E3) (g : CoordinateMetric V) (U : Set E2)
    (p normal : E3) (hp : p ∈ V) (hnormal : normal ≠ 0)
    (L : E2 →L[ℝ] E3) (hL : Function.Injective L)
    (hnormalOrthogonal : ∀ v : E2, coordinateInner g.tensor p (L v) normal = 0)
    (w : E2 → ℝ) (hwC1 : ContDiffOn ℝ 1 w U) :
    ∀ x ∈ interior U, Function.Injective (fderiv ℝ (graphMap p L normal w) x) := by
  intro x hx
  apply graph_fderiv_injective V g p normal hp hnormal L hL hnormalOrthogonal w x
  exact ((hwC1.mono interior_subset).differentiableOn (by norm_num) x hx).differentiableAt
    (isOpen_interior.mem_nhds hx)


/-! Analytic obligations in the proofs of A.3 and A.5. -/

def planarGradient (u : E2 → ℝ) (x : E2) : E2 :=
  ∑ i : Fin 2, fderiv ℝ u x (coordinateVector 2 i) • coordinateVector 2 i

abbrev Jet := E2 × ℝ × E2

/-- A genuine divergence-form operator `div A(x,u,Du) + B(x,u,Du)`. -/
structure SmoothQuasilinearOperator (J : Set Jet) where
  flux : Jet → E2
  lowerOrder : Jet → ℝ
  flux_smooth : ContDiffOn ℝ ∞ flux J
  lowerOrder_smooth : ContDiffOn ℝ ∞ lowerOrder J

def UniformlyEllipticOn (J : Set Jet) (A : Jet → E2) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∀ (x : E2) (z : ℝ) (p ξ : E2), (x, z, p) ∈ J →
    κ * ‖ξ‖ ^ 2 ≤ inner ℝ (fderiv ℝ (fun q : E2 => A (x, z, q)) p ξ) ξ

def weakFluxIdentity (Ω : Set E2) (A : E2 → E2) (B φ : E2 → ℝ) : Prop :=
  (∫ x in Ω, inner ℝ (A x) (planarGradient φ x) - B x * φ x) = 0

def IsWeakDivergenceSolutionOn (Ω : Set E2) (A : Jet → E2) (B : Jet → ℝ)
    (u : E2 → ℝ) : Prop :=
  ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    weakFluxIdentity Ω (fun x => A (x, u x, planarGradient u x))
      (fun x => B (x, u x, planarGradient u x)) φ

lemma norm_planarGradient_le (u : E2 → ℝ) (x : E2) :
    ‖planarGradient u x‖ ≤ 2 * ‖fderiv ℝ u x‖ := by
  calc
    _ ≤ ∑ i : Fin 2, ‖fderiv ℝ u x (coordinateVector 2 i) • coordinateVector 2 i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, ‖fderiv ℝ u x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [norm_smul]
      have hi1 : ‖coordinateVector 2 i‖ = 1 := by
        simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
      rw [hi1, mul_one]
      simpa only [hi1, mul_one] using (fderiv ℝ u x).le_opNorm (coordinateVector 2 i)
    _ = _ := by simp

lemma planarGradient_sub {u v : E2 → ℝ} {x : E2}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    planarGradient (fun x => u x - v x) x = planarGradient u x - planarGradient v x := by
  simp [planarGradient, fderiv_fun_sub hu hv, sub_smul, Finset.sum_sub_distrib]

lemma planarGradient_eq_zero_off_support (u : E2 → ℝ) {x : E2}
    (hx : x ∉ tsupport u) : planarGradient u x = 0 := by
  simp [planarGradient, fderiv_of_notMem_tsupport ℝ hx]

lemma continuous_planarGradient {u : E2 → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (planarGradient u) := by
  unfold planarGradient
  exact continuous_finsetSum _ fun i _ =>
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

lemma flux_integrand_support_subset (A : E2 → E2) (B u : E2 → ℝ) :
    support (fun x => inner ℝ (A x) (planarGradient u x) - B x * u x) ⊆ tsupport u := by
  intro x hx
  contrapose! hx
  simp [mem_support, planarGradient_eq_zero_off_support u hx, image_eq_zero_of_notMem_tsupport hx]

lemma flux_integrand_integrable (Ω : Set E2) (A : E2 → E2) (B u : E2 → ℝ)
    (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hu : ContDiff ℝ ∞ u) (huK : HasCompactSupport u) (huΩ : tsupport u ⊆ Ω) :
    Integrable (fun x => inner ℝ (A x) (planarGradient u x) - B x * u x) := by
  apply (integrableOn_iff_integrable_of_support_subset (flux_integrand_support_subset A B u)).mp
  exact (((hA.mono huΩ).inner (continuous_planarGradient hu).continuousOn).sub
    ((hB.mono huΩ).mul hu.continuous.continuousOn)).integrableOn_compact huK

lemma flux_integral_sub (Ω : Set E2) (A : E2 → E2) (B u v : E2 → ℝ)
    (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hu : ContDiff ℝ ∞ u) (huK : HasCompactSupport u) (huΩ : tsupport u ⊆ Ω)
    (hv : ContDiff ℝ ∞ v) (hvK : HasCompactSupport v) (hvΩ : tsupport v ⊆ Ω) :
    (∫ x in Ω, inner ℝ (A x) (planarGradient (fun x => u x - v x) x) - B x * (u x - v x)) =
      (∫ x in Ω, inner ℝ (A x) (planarGradient u x) - B x * u x) -
        (∫ x in Ω, inner ℝ (A x) (planarGradient v x) - B x * v x) := by
  rw [← integral_sub (flux_integrand_integrable Ω A B u hA hB hu huK huΩ).integrableOn
    (flux_integrand_integrable Ω A B v hA hB hv hvK hvΩ).integrableOn]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [planarGradient_sub (hu.differentiable (by simp) x) (hv.differentiable (by simp) x)]
  simp only [inner_sub_right]
  ring


/-- Smooth cutoffs around a point, with the derivative cost of rescaling explicit. -/
lemma exists_point_cutoffs (q : E2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε → ∃ χ : E2 → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      χ =ᶠ[𝓝 q] (fun _ => 1) ∧ tsupport χ ⊆ Metric.closedBall q ε ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ D / ε := by
  let β : ContDiffBump (0 : E2) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  have hβ : ContDiff ℝ ∞ (β : E2 → ℝ) := β.contDiff
  obtain ⟨D, hD⟩ := (hβ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport (β.hasCompactSupport.fderiv ℝ).norm
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD (mem_range_self (0 : E2)))
  refine ⟨D, hD0, ?_⟩
  intro ε hε
  let t : E2 → E2 := fun x => ε⁻¹ • (x - q)
  have ht : ContDiff ℝ ∞ t := (contDiff_id.sub contDiff_const).const_smul _
  let χ : E2 → ℝ := fun x => β (t x)
  refine ⟨χ, hβ.comp ht, (fun x => ⟨β.nonneg, β.le_one⟩), ?_, ?_, ?_⟩
  · have htq : t q = 0 := by simp [t]
    simpa only [Function.comp_def, χ, Pi.one_apply] using
      β.eventuallyEq_one.comp_tendsto (htq ▸ ht.continuous.continuousAt (x := q))
  · apply closure_minimal _ Metric.isClosed_closedBall
    intro x hx
    have hxβ : t x ∈ support (β : E2 → ℝ) := hx
    rw [β.support_eq] at hxβ
    have hnorm : ‖t x‖ < 1 := by simpa [β] using hxβ
    have hxε : ‖x - q‖ < ε := by
      dsimp only [t] at hnorm
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)] at hnorm
      exact (div_lt_one hε).mp (by simpa only [div_eq_mul_inv, mul_comm] using hnorm)
    exact (Metric.mem_closedBall.mpr hxε.le)
  · intro x
    have hdt : HasFDerivAt t (ε⁻¹ • ContinuousLinearMap.id ℝ E2) x :=
      ((hasFDerivAt_id x).sub_const q).const_smul ε⁻¹
    have hdχ := (hβ.differentiable (by simp) (t x)).hasFDerivAt.comp x hdt
    rw [show χ = (β : E2 → ℝ) ∘ t from rfl, hdχ.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hD0 hε.le)
    intro v
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    calc
      _ ≤ ε⁻¹ * (‖fderiv ℝ (β : E2 → ℝ) (t x)‖ * ‖v‖) := by
        gcongr
        exact (fderiv ℝ (β : E2 → ℝ) (t x)).le_opNorm v
      _ ≤ ε⁻¹ * (D * ‖v‖) := by gcongr; exact hD (mem_range_self (t x))
      _ = D / ε * ‖v‖ := by ring


lemma cutoff_flux_estimate
    (Ω : Set E2) (q : E2) (A : E2 → E2) (B φ χ : E2 → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hχ : ContDiff ℝ ∞ χ)
    (hφΩ : tsupport φ ⊆ Ω) (ε : ℝ) (hε : 0 < ε)
    (hχsupport : tsupport χ ⊆ Metric.closedBall q ε)
    (hχbound : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (a b c d D : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hD : 0 ≤ D)
    (hAbound : ∀ x ∈ tsupport φ, ‖A x‖ ≤ a)
    (hBbound : ∀ x ∈ tsupport φ, ‖B x‖ ≤ b)
    (hφbound : ∀ x, ‖φ x‖ ≤ c) (hdφbound : ∀ x, ‖fderiv ℝ φ x‖ ≤ d)
    (hdχbound : ∀ x, ‖fderiv ℝ χ x‖ ≤ D / ε) :
    ‖∫ x in Ω, inner ℝ (A x) (planarGradient (fun x => φ x * χ x) x) -
      B x * (φ x * χ x)‖ ≤ (a * (2 * (c * (D / ε) + d)) + b * c) *
        (Real.pi * ε ^ 2) := by
  let ψ : E2 → ℝ := fun x => φ x * χ x
  let F : E2 → ℝ := fun x => inner ℝ (A x) (planarGradient ψ x) - B x * ψ x
  have hψφ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_left
  have hψball : tsupport ψ ⊆ Metric.closedBall q ε :=
    tsupport_mul_subset_right.trans hχsupport
  have hFφ : support F ⊆ tsupport φ := (flux_integrand_support_subset A B ψ).trans hψφ
  have hFball : support F ⊆ Metric.closedBall q ε :=
    (flux_integrand_support_subset A B ψ).trans hψball
  change ‖∫ x in Ω, F x‖ ≤ _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    notMem_support.mp (fun h => hx (hφΩ (hFφ h)))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall q ε)
      (fun x hx => notMem_support.mp (fun h => hx (hFball h)))]
  have hbound : ∀ x ∈ Metric.closedBall q ε,
      ‖F x‖ ≤ a * (2 * (c * (D / ε) + d)) + b * c := by
    intro x hx
    by_cases hxφ : x ∈ tsupport φ
    · have hχnorm : ‖χ x‖ ≤ 1 := by simpa [Real.norm_of_nonneg (hχbound x).1] using (hχbound x).2
      have hψnorm : ‖ψ x‖ ≤ c := by
        calc
          _ = ‖φ x‖ * ‖χ x‖ := norm_mul _ _
          _ ≤ c * 1 := mul_le_mul (hφbound x) hχnorm (norm_nonneg _) hc
          _ = c := mul_one c
      have hdψ : ‖fderiv ℝ ψ x‖ ≤ c * (D / ε) + d := by
        rw [show ψ = (fun x => φ x * χ x) from rfl,
          fderiv_fun_mul (hφ.differentiable (by simp) x) (hχ.differentiable (by simp) x)]
        calc
          _ ≤ ‖φ x • fderiv ℝ χ x‖ + ‖χ x • fderiv ℝ φ x‖ := norm_add_le _ _
          _ = ‖φ x‖ * ‖fderiv ℝ χ x‖ + ‖χ x‖ * ‖fderiv ℝ φ x‖ := by rw [norm_smul, norm_smul]
          _ ≤ c * (D / ε) + 1 * d := by
            exact add_le_add (mul_le_mul (hφbound x) (hdχbound x) (norm_nonneg _) hc)
              (mul_le_mul hχnorm (hdφbound x) (norm_nonneg _) (by norm_num))
          _ = _ := by ring
      calc
        _ ≤ ‖inner ℝ (A x) (planarGradient ψ x)‖ + ‖B x * ψ x‖ := norm_sub_le _ _
        _ ≤ ‖A x‖ * ‖planarGradient ψ x‖ + ‖B x‖ * ‖ψ x‖ :=
          add_le_add (norm_inner_le_norm _ _) (norm_mul_le _ _)
        _ ≤ a * (2 * (c * (D / ε) + d)) + b * c := by
          exact add_le_add (mul_le_mul (hAbound x hxφ)
            ((norm_planarGradient_le ψ x).trans (mul_le_mul_of_nonneg_left hdψ (by norm_num)))
            (norm_nonneg _) ha) (mul_le_mul (hBbound x hxφ) hψnorm (norm_nonneg _) hb)
    · have hFx : F x = 0 := notMem_support.mp (fun h => hxφ (hFφ h))
      rw [hFx, norm_zero]
      positivity
  have hvol : volume.real (Metric.closedBall q ε) = Real.pi * ε ^ 2 := by
    rw [Measure.real, EuclideanSpace.volume_closedBall_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal Real.pi_pos.le]
    ring
  simpa only [hvol] using norm_setIntegral_le_of_norm_le_const (μ := volume) measure_closedBall_lt_top hbound



/-- A.5, p. 25--26: bounded continuous flux cannot carry an isolated point defect
in a two-dimensional weak divergence equation. This separates the cutoff argument from
the geometry and from elliptic regularity. -/
theorem weak_divergence_extends_over_point
    (Ω : Set E2) (hΩ : IsOpen Ω) (q : E2) (hq : q ∈ Ω)
    (A : E2 → E2) (B : E2 → ℝ)
    (hA : ContinuousOn A Ω) (hB : ContinuousOn B Ω)
    (hpunctured : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω \ {q} → weakFluxIdentity Ω A B φ) :
    ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → weakFluxIdentity Ω A B φ := by
  intro φ hφ hφK hφΩ
  obtain ⟨a₀, ha₀⟩ := hφK.exists_bound_of_continuousOn (hA.mono hφΩ)
  obtain ⟨b₀, hb₀⟩ := hφK.exists_bound_of_continuousOn (hB.mono hφΩ)
  obtain ⟨c₀, hc₀⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport hφK.norm
  obtain ⟨d₀, hd₀⟩ := (hφ.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    (hφK.fderiv ℝ).norm
  let a := max a₀ 0
  let b := max b₀ 0
  let c := max c₀ 0
  let d := max d₀ 0
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hc : 0 ≤ c := le_max_right _ _
  have hd : 0 ≤ d := le_max_right _ _
  have hAbound : ∀ x ∈ tsupport φ, ‖A x‖ ≤ a := fun x hx => (ha₀ x hx).trans (le_max_left _ _)
  have hBbound : ∀ x ∈ tsupport φ, ‖B x‖ ≤ b := fun x hx => (hb₀ x hx).trans (le_max_left _ _)
  have hφbound : ∀ x, ‖φ x‖ ≤ c := fun x => (hc₀ (mem_range_self x)).trans (le_max_left _ _)
  have hdφbound : ∀ x, ‖fderiv ℝ φ x‖ ≤ d := fun x => (hd₀ (mem_range_self x)).trans (le_max_left _ _)
  obtain ⟨D, hD, hcut⟩ := exists_point_cutoffs q
  let I : ℝ := ∫ x in Ω, inner ℝ (A x) (planarGradient φ x) - B x * φ x
  have hI : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖I‖ ≤ (a * (2 * (c * D + d)) + b * c) * Real.pi * ε := by
    intro ε hε hε1
    obtain ⟨χ, hχ, hχbound, hχq, hχsupport, hdχbound⟩ := hcut ε hε
    let ψ : E2 → ℝ := fun x => φ x * χ x
    have hψ : ContDiff ℝ ∞ ψ := hφ.mul hχ
    have hψK : HasCompactSupport ψ := hφK.mul_right
    have hψΩ : tsupport ψ ⊆ Ω := tsupport_mul_subset_left.trans hφΩ
    have htestΩ : tsupport (fun x => φ x - ψ x) ⊆ Ω \ {q} := by
      intro x hx
      refine ⟨(union_subset hφΩ hψΩ) (tsupport_sub φ ψ hx), ?_⟩
      intro hxq
      have hxq' : x = q := hxq
      subst x
      have heq : (fun x => φ x - ψ x) =ᶠ[𝓝 q] (0 : E2 → ℝ) := by
        filter_upwards [hχq] with x hx
        simp [ψ, hx]
      exact (notMem_tsupport_iff_eventuallyEq.mpr heq) hx
    have hzero := hpunctured (fun x => φ x - ψ x) (hφ.sub hψ) (hφK.sub hψK) htestΩ
    unfold weakFluxIdentity at hzero
    rw [flux_integral_sub Ω A B φ ψ hA hB hφ hφK hφΩ hψ hψK hψΩ] at hzero
    have hIeq : I = ∫ x in Ω, inner ℝ (A x) (planarGradient ψ x) - B x * ψ x :=
      sub_eq_zero.mp hzero
    rw [hIeq]
    have hest := cutoff_flux_estimate Ω q A B φ χ hφ hχ hφΩ ε hε hχsupport hχbound
      a b c d D ha hb hc hd hD hAbound hBbound hφbound hdφbound hdχbound
    apply hest.trans
    have heq : (a * (2 * (c * (D / ε) + d)) + b * c) * (Real.pi * ε ^ 2) =
        (2 * a * c * D * Real.pi) * ε + ((2 * a * d + b * c) * Real.pi) * ε ^ 2 := by
      field_simp
      ring
    rw [heq]
    have hsquare : ε ^ 2 ≤ ε := by nlinarith
    have hcoef : 0 ≤ (2 * a * d + b * c) * Real.pi := by positivity
    have hprod := mul_le_mul_of_nonneg_left hsquare hcoef
    nlinarith
  unfold weakFluxIdentity
  change I = 0
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let K := (a * (2 * (c * D + d)) + b * c) * Real.pi
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ε := min 1 (δ / (K + 1))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hδ (by linarith))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ / (K + 1) := min_le_right _ _
  have hmul : K * ε ≤ δ := by
    have hmul' := (le_div_iff₀ (show 0 < K + 1 by linarith)).mp hεδ
    nlinarith
  simpa only [zero_add] using (hI ε hε hε1).trans hmul


end SeifertSurfaces.AppendixACoordinates
