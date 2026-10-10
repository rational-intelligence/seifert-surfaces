import AppendixACoordinates
import LocalizationBasic
import JetBoundsHelpers

/-!
Source-aligned R1--R3 obligations for Appendix A.3 (paper p. 24, lines 1164--1173).
The imported target and operative definitions are a literal reviewed snapshot.
The helpers expose the lower terms suppressed by the source's difference-quotient sentence.
No Sobolev provider or regularity theorem is assumed in this provider-independent file.
-/

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearLocalization

open SeifertSurfaces.AppendixACoordinates

def firstJet (u : E2 → ℝ) (x : E2) : Jet := (x, u x, planarGradient u x)

def fluxDx {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 →L[ℝ] E2 :=
  fderiv ℝ (fun x : E2 => Q.flux (x, j.2.1, j.2.2)) j.1

def fluxDz {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 :=
  fderiv ℝ (fun z : ℝ => Q.flux (j.1, z, j.2.2)) j.2.1 1

def fluxDp {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 →L[ℝ] E2 :=
  fderiv ℝ (fun p : E2 => Q.flux (j.1, j.2.1, p)) j.2.2

def lowerDx {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 →L[ℝ] ℝ :=
  fderiv ℝ (fun x : E2 => Q.lowerOrder (x, j.2.1, j.2.2)) j.1

def lowerDz {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : ℝ :=
  fderiv ℝ (fun z : ℝ => Q.lowerOrder (j.1, z, j.2.2)) j.2.1 1

def lowerDp {J : Set Jet} (Q : SmoothQuasilinearOperator J) (j : Jet) : E2 →L[ℝ] ℝ :=
  fderiv ℝ (fun p : E2 => Q.lowerOrder (j.1, j.2.1, p)) j.2.2

/- Full local bounds, including actual first and second jet derivatives. No derivative
of `u` beyond its already given C¹ gradient occurs in this definition. -/
def JetTubeBounds {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x₀ : E2) (r κ M : ℝ) (T : Set Jet) : Prop :=
  0 < κ ∧ 1 ≤ M ∧
    (∀ x ∈ Metric.closedBall x₀ (4 * r), |u x| ≤ M ∧ ‖planarGradient u x‖ ≤ M) ∧
    (∀ j ∈ closure T, ‖Q.flux j‖ ≤ M ∧ |Q.lowerOrder j| ≤ M ∧
      ‖fluxDx Q j‖ ≤ M ∧ ‖fluxDz Q j‖ ≤ M ∧ ‖fluxDp Q j‖ ≤ M ∧
      ‖lowerDx Q j‖ ≤ M ∧ |lowerDz Q j| ≤ M ∧ ‖lowerDp Q j‖ ≤ M) ∧
    (∀ j ∈ closure T, ∀ m : ℕ, m ≤ 2 →
      ‖iteratedFDeriv ℝ m Q.flux j‖ ≤ M ∧
        ‖iteratedFDeriv ℝ m Q.lowerOrder j‖ ≤ M) ∧
    (∀ j ∈ closure T, ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (fluxDp Q j ξ) ξ)

/- R1: a local convex jet tube is produced inside the supplied open `J`; no global
convexity of `J` or boundedness of `Ω` is added. -/
theorem R1_local_jet_tube
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J) (x₀ : E2) (hx₀ : x₀ ∈ Ω) :
    ∃ r κ M : ℝ, ∃ T : Set Jet,
      0 < r ∧ Metric.closedBall x₀ (4 * r) ⊆ Ω ∧
      IsOpen T ∧ Convex ℝ T ∧ IsCompact (closure T) ∧ closure T ⊆ J ∧
      (∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T) ∧
      JetTubeBounds Q u x₀ r κ M T := by
  have hgrad := Helpers.gradient_continuousOn Ω hΩ u hC1
  have hjet : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk hgrad)
  obtain ⟨ε, hε, hεJ⟩ := Metric.isOpen_iff.mp hJ (firstJet u x₀) (hjets x₀ hx₀)
  let T := Metric.ball (firstJet u x₀) (ε / 2)
  have hε2 : 0 < ε / 2 := half_pos hε
  have hclosure : closure T = Metric.closedBall (firstJet u x₀) (ε / 2) :=
    closure_ball _ hε2.ne'
  have hTcompact : IsCompact (closure T) := by
    rw [hclosure]
    exact isCompact_closedBall _ _
  have hTJ : closure T ⊆ J := by
    rw [hclosure]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hεJ
  have hpre : Ω ∩ firstJet u ⁻¹' T ∈ 𝓝 x₀ :=
    inter_mem (hΩ.mem_nhds hx₀)
      ((hjet.continuousAt (hΩ.mem_nhds hx₀)).preimage_mem_nhds
        (Metric.ball_mem_nhds _ hε2))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  let r := δ / 4
  have hr : 0 < r := div_pos hδ (by norm_num)
  have h4r : 4 * r = δ := by dsimp [r]; ring
  have hball : Metric.closedBall x₀ (4 * r) ⊆ Ω := by
    rw [h4r]
    exact fun x hx => (hδsub hx).1
  have hjetT : ∀ x ∈ Metric.closedBall x₀ (4 * r), firstJet u x ∈ T := by
    rw [h4r]
    exact fun x hx => (hδsub hx).2
  obtain ⟨κ, hκ, hcoercive⟩ := helliptic
  obtain ⟨U, hU⟩ := (isCompact_closedBall x₀ (4 * r)).exists_bound_of_continuousOn
    (hC1.continuousOn.mono hball)
  obtain ⟨G, hG⟩ := (isCompact_closedBall x₀ (4 * r)).exists_bound_of_continuousOn
    (hgrad.mono hball)
  obtain ⟨A, hA⟩ := Helpers.compact_C2_bounds J (closure T) hJ hTcompact hTJ
    Q.flux Q.flux_smooth
  obtain ⟨B, hB⟩ := Helpers.compact_C2_bounds J (closure T) hJ hTcompact hTJ
    Q.lowerOrder Q.lowerOrder_smooth
  let M := max 1 (max U (max G (max A B)))
  have h1M : 1 ≤ M := le_max_left _ _
  have hUM : U ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hGM : G ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAM : A ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  have hBM : B ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨r, κ, M, T, hr, hball, Metric.isOpen_ball, convex_ball _ _, hTcompact,
    hTJ, hjetT, hκ, h1M, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨by simpa [Real.norm_eq_abs] using (hU x hx).trans hUM, (hG x hx).trans hGM⟩
  · intro j hj
    have hAf := (Q.flux_smooth.contDiffAt (hJ.mem_nhds (hTJ hj))).differentiableAt (by simp)
    have hBf := (Q.lowerOrder_smooth.contDiffAt (hJ.mem_nhds (hTJ hj))).differentiableAt (by simp)
    have ha := (hA j hj).2.1.trans hAM
    have hb := (hB j hj).2.1.trans hBM
    refine ⟨(hA j hj).1.trans hAM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [Real.norm_eq_abs] using (hB j hj).1.trans hBM
    · exact (Helpers.norm_fderiv_x_slice_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_z_slice_one_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_p_slice_le Q.flux j hAf).trans ha
    · exact (Helpers.norm_fderiv_x_slice_le Q.lowerOrder j hBf).trans hb
    · simpa only [Real.norm_eq_abs, lowerDz] using
        (Helpers.norm_fderiv_z_slice_one_le Q.lowerOrder j hBf).trans hb
    · exact (Helpers.norm_fderiv_p_slice_le Q.lowerOrder j hBf).trans hb
  · intro j hj m hm
    exact ⟨((hA j hj).2.2 m hm).trans hAM, ((hB j hj).2.2 m hm).trans hBM⟩
  · intro j hj ξ
    exact hcoercive j.1 j.2.1 j.2.2 ξ (hTJ hj)

/- The literal coordinate gradient evaluates the derivative by the Euclidean pairing. -/
theorem R1_planarGradient_pairing
    (u : E2 → ℝ) (x ξ : E2) :
    inner ℝ (planarGradient u x) ξ = fderiv ℝ u x ξ := by
  rw [← InnerProductSpace.toDual_apply_apply, Helpers.gradient_dual]

/- R1: ordinary C¹ and continuity on the test support make the two terms integrable.
The weak identity cannot exploit the totalized integral of a nonintegrable function. -/
theorem R1_test_integrability
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ Ω) :
    IntegrableOn (fun x => inner ℝ (Q.flux (firstJet u x)) (planarGradient φ x)) Ω ∧
      IntegrableOn (fun x => Q.lowerOrder (firstJet u x) * φ x) Ω := by
  have hgrad := Helpers.gradient_continuousOn Ω hΩ u hC1
  have hjet : ContinuousOn (firstJet u) Ω :=
    continuousOn_id.prodMk (hC1.continuousOn.prodMk hgrad)
  have hA : ContinuousOn (fun x => Q.flux (firstJet u x)) Ω :=
    Q.flux_smooth.continuousOn.comp hjet hjets
  have hB : ContinuousOn (fun x => Q.lowerOrder (firstJet u x)) Ω :=
    Q.lowerOrder_smooth.continuousOn.comp hjet hjets
  constructor
  · apply Integrable.integrableOn
    exact Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
      (hA.inner (Helpers.gradient_continuous φ hφ).continuousOn)
      (Helpers.inner_gradient_support_subset _ φ)
  · apply Integrable.integrableOn
    exact Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
      (hB.mul hφ.continuous.continuousOn) (Helpers.mul_test_support_subset _ φ)

theorem R1_weak_equation_restrict
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u)
    (B : Set E2) (hB : IsOpen B) (hBΩ : B ⊆ Ω) :
    IsWeakDivergenceSolutionOn B Q.flux Q.lowerOrder u := by
  intro φ hφ hsupp hsub
  have h := hweak φ hφ hsupp (hsub.trans hBΩ)
  unfold weakFluxIdentity at h ⊢
  have hzero : ∀ x, x ∉ B →
      inner ℝ (Q.flux (x, u x, planarGradient u x)) (planarGradient φ x) -
        Q.lowerOrder (x, u x, planarGradient u x) * φ x = 0 := by
    intro x hx
    have hs : x ∉ tsupport φ := fun h => hx (hsub h)
    simp [Helpers.gradient_zero_off_tsupport φ hs, image_eq_zero_of_notMem_tsupport hs]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
    hzero x (fun hb => hx (hBΩ hb)))] at h
  exact h

def shift (k : Fin 2) (h : ℝ) (x : E2) : E2 := x + h • coordinateVector 2 k

def differenceQuotient (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (x : E2) : ℝ :=
  (u (shift k h x) - u x) / h

def jetSegment (u : E2 → ℝ) (k : Fin 2) (h : ℝ) (x : E2) (t : ℝ) : Jet :=
  (1 - t) • firstJet u x + t • firstJet u (shift k h x)

/- Six actual coefficient fields of the differentiated weak equation. `b` is the scalar
linear functional `D_p B`, so `b(Dv)` retains exactly the source's first-order scalar term. -/
structure LinearizedCoefficients where
  a : E2 → E2 →L[ℝ] E2
  c : E2 → E2
  d : E2 → E2
  b : E2 → E2 →L[ℝ] ℝ
  q : E2 → ℝ
  f : E2 → ℝ

def averagedCoefficients {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (k : Fin 2) (h : ℝ) : LinearizedCoefficients where
  a x := ∫ t in Icc (0 : ℝ) 1, fluxDp Q (jetSegment u k h x t)
  c x := ∫ t in Icc (0 : ℝ) 1, fluxDz Q (jetSegment u k h x t)
  d x := ∫ t in Icc (0 : ℝ) 1, fluxDx Q (jetSegment u k h x t) (coordinateVector 2 k)
  b x := ∫ t in Icc (0 : ℝ) 1, lowerDp Q (jetSegment u k h x t)
  q x := ∫ t in Icc (0 : ℝ) 1, lowerDz Q (jetSegment u k h x t)
  f x := ∫ t in Icc (0 : ℝ) 1, lowerDx Q (jetSegment u k h x t) (coordinateVector 2 k)

/- Actual limiting coefficients, evaluated at the original first jet. -/
def differentiatedCoefficients {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (k : Fin 2) : LinearizedCoefficients where
  a x := fluxDp Q (firstJet u x)
  c x := fluxDz Q (firstJet u x)
  d x := fluxDx Q (firstJet u x) (coordinateVector 2 k)
  b x := lowerDp Q (firstJet u x)
  q x := lowerDz Q (firstJet u x)
  f x := lowerDx Q (firstJet u x) (coordinateVector 2 k)

def linearizedFlux (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2) (x : E2) : E2 :=
  C.a x (G x) + v x • C.c x + C.d x

def linearizedSource (C : LinearizedCoefficients) (v : E2 → ℝ) (G : E2 → E2) (x : E2) : ℝ :=
  C.b x (G x) + C.q x * v x + C.f x

/- Smooth-test weak equation with its two separate integrability conditions. -/
def LinearWeakEquation (B : Set E2) (C : LinearizedCoefficients)
    (v : E2 → ℝ) (G : E2 → E2) : Prop :=
  ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ B →
    IntegrableOn (fun x => inner ℝ (linearizedFlux C v G x) (planarGradient φ x)) B ∧
    IntegrableOn (fun x => linearizedSource C v G x * φ x) B ∧
    (∫ x in B, inner ℝ (linearizedFlux C v G x) (planarGradient φ x) -
      linearizedSource C v G x * φ x) = 0

def CoefficientBounds (B : Set E2) (C : LinearizedCoefficients) (κ M : ℝ) : Prop :=
  0 < κ ∧ 1 ≤ M ∧
    (∀ x ∈ B, ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ inner ℝ (C.a x ξ) ξ) ∧
    (∀ x ∈ B, ‖C.a x‖ ≤ M ∧ ‖C.c x‖ ≤ M ∧ ‖C.d x‖ ≤ M ∧
      ‖C.b x‖ ≤ M ∧ |C.q x| ≤ M ∧ |C.f x| ≤ M)

def CoefficientMeasurableOn (B : Set E2) (C : LinearizedCoefficients) : Prop :=
  AEStronglyMeasurable C.a (volume.restrict B) ∧
    AEStronglyMeasurable C.c (volume.restrict B) ∧ AEStronglyMeasurable C.d (volume.restrict B) ∧
    AEStronglyMeasurable C.b (volume.restrict B) ∧ AEStronglyMeasurable C.q (volume.restrict B) ∧
    AEStronglyMeasurable C.f (volume.restrict B)

def coefficientsContinuousOn (B : Set E2) (C : LinearizedCoefficients) : Prop :=
  ContinuousOn C.a B ∧ ContinuousOn C.c B ∧ ContinuousOn C.d B ∧
    ContinuousOn C.b B ∧ ContinuousOn C.q B ∧ ContinuousOn C.f B

/- Each coefficient average is an actual Bochner integral along the compact jet segment. -/


/- R2: pointwise jet-segment FTC, retaining all x/z/p flux and scalar derivatives. -/




/- R2: the actual difference quotient satisfies the full weak equation on `2r`. -/


/- R2: all constants are supplied by R1, and none depends on the nonzero step `h`. -/




/- Classical C¹ weak functions with finite local energy suffice for this provider-independent
estimate. The provider module separately supplies the H₀¹ density/energy-test bridge. -/


/- Uniform interior energy is concluded from C¹ and the weak equation; it is not assumed
uniformly in `h`, and no derivative of `a_h` or H² input is used. -/


/-! R3: concrete nonsymmetric homogeneous lift on ordinary `Fin 3` coordinates. -/

def planarPart (y : E3) : E2 := WithLp.toLp 2 ![y 0, y 1]
def liftedPoint (x : E2) (t : ℝ) : E3 := WithLp.toLp 2 ![x 0, x 1, t]
def cylinder (B : Set E2) : Set E3 := {y | planarPart y ∈ B ∧ |y 2| < 1}

def gradient3 (φ : E3 → ℝ) (y : E3) : E3 :=
  ∑ i : Fin 3, fderiv ℝ φ y (coordinateVector 3 i) • coordinateVector 3 i

def liftFunction (v : E2 → ℝ) (y : E3) : ℝ := v (planarPart y) + y 2
def liftGradient (G : E2 → E2) (y : E3) : E3 := liftedPoint (G (planarPart y)) 1

def liftMatrix (C : LinearizedCoefficients) (v : E2 → ℝ) (D : ℝ) (y : E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let x := planarPart y
  let F := v x • C.c x + C.d x
  let g := C.q x * v x + C.f x
  !![C.a x (coordinateVector 2 0) 0, C.a x (coordinateVector 2 1) 0, F 0;
     C.a x (coordinateVector 2 0) 1, C.a x (coordinateVector 2 1) 1, F 1;
     y 2 * C.b x (coordinateVector 2 0), y 2 * C.b x (coordinateVector 2 1), D + y 2 * g]

def matrixAction (A : Matrix (Fin 3) (Fin 3) ℝ) (ξ : E3) : E3 :=
  WithLp.toLp 2 (Matrix.mulVec A ξ.ofLp)

def liftD (κ M L : ℝ) : ℝ :=
  (M * L + M) + (M * L + 2 * M) ^ 2 / (2 * κ) + 1

def liftEntryBound (κ M L : ℝ) : ℝ := liftD κ M L + M * L + 2 * M + 1

/- A fixed normalized inverse-coercivity scale, depending only on common input bounds. -/
def liftLambda (κ M L : ℝ) : ℝ :=
  max 1 (3 * liftEntryBound κ M L / min (κ / 2) 1) ^ 2

open Classical in
/- The local matrix is normalized and extended by the identity off the intended ball.
A measurable representative inside the ball is still needed when coefficients are only a.e.
measurable; the provider bridge records agreement a.e. rather than asserting pointwise identity. -/
def extendedNormalizedLiftMatrix (C : LinearizedCoefficients) (v : E2 → ℝ)
    (κ M L : ℝ) (center : E3) (R : ℝ) (y : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if y ∈ Metric.ball center R then (min (κ / 2) 1)⁻¹ • liftMatrix C v (liftD κ M L) y
  else 1

def LiftWeakEquation (B : Set E3) (A : E3 → Matrix (Fin 3) (Fin 3) ℝ)
    (G : E3 → E3) : Prop :=
  ∀ ψ : E3 → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
    IntegrableOn (fun y => inner ℝ (matrixAction (A y) (G y)) (gradient3 ψ y)) B ∧
      (∫ y in B, inner ℝ (matrixAction (A y) (G y)) (gradient3 ψ y)) = 0





/- The plus signs in the bottom row cancel the distributional `div_x` source.
This is proved by slicing and Fubini, not a pointwise second-derivative assumption. -/


/- Coercivity of the concrete lift, with fixed `D` independent of `h`. -/




/- Rank-free nonsymmetric inverse coercivity, required by the selected provider. -/


/- Slicing/Fubini must use this actual product-to-ordinary-three-space volume identity. -/


/- Continuity and the full support of Lebesgue measure identify the actual function
with a positive-exponent Hölder representative on an open set. -/


/- Restricting a continuous Hölder lift to `t=0` gives the same planar function. -/


/- Uniform quotient Hölder bounds pass to the actual first derivative, without
assuming a second derivative or regularity of a chosen representative. -/


end SeifertSurfaces.QuasilinearLocalization
