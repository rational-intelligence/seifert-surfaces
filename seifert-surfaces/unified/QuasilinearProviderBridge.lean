import QuasilinearLocalization
import ProviderLocalHelpers
import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.External.DeGiorgi.EllipticCoefficients

/-!
Pending separate provider review. Only the selected DifferentialGeometry ExternalDeGiorgi
snapshot (commit 777299070a5529e96345e0033979706fd00c7e62) supplies Sobolev/coefficient types.
No original `DeGiorgi.*` import is used. The all-H₀¹-test identity is explicit here;
the provider endpoint adapter awaits its reviewed, compatible SolutionInterfaces closure.
-/

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.QuasilinearProviderBridge

open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

/- R1: C¹ on a neighborhood of a closed ball gives the selected provider's actual H¹
membership and classical weak gradient, without a global C¹ extension assumption. -/
theorem R1_C1_memW1p_on_ball
    (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (x₀ : E2) (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall x₀ r ⊆ Ω) :
    DeGiorgi.MemW1p 2 u (Metric.ball x₀ r) ∧
      DeGiorgi.HasWeakGrad (planarGradient u) u (Metric.ball x₀ r) := by
  have hweak := Helpers.C1_hasWeakGrad Ω hΩ u hC1
  have hballΩ : Metric.ball x₀ r ⊆ Ω := Metric.ball_subset_closedBall.trans hball
  have hweakball : DeGiorgi.HasWeakGrad (planarGradient u) u (Metric.ball x₀ r) :=
    Helpers.C1_hasWeakGrad _ Metric.isOpen_ball u (hC1.mono hballΩ)
  refine ⟨⟨Helpers.continuousOn_closedBall_memLp u x₀ r (hC1.continuousOn.mono hball), ?_⟩,
    hweakball⟩
  intro i
  refine ⟨fun x => planarGradient u x i, ?_, hweakball i⟩
  apply Helpers.continuousOn_closedBall_memLp
  have hc := SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1
  exact ((EuclideanSpace.proj i).continuous.continuousOn.comp hc (mapsTo_univ _ _)).mono hball

/- Every provider weak-gradient witness agrees a.e. with the literal classical gradient. -/
theorem R1_classical_weak_gradient_agrees
    (Ω : Set E2) (hΩ : IsOpen Ω) (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hw : DeGiorgi.MemW1pWitness 2 u Ω) :
    hw.weakGrad =ᵐ[volume.restrict Ω] planarGradient u := by
  have hweak := Helpers.C1_hasWeakGrad Ω hΩ u hC1
  have hcont := SeifertSurfaces.QuasilinearLocalization.Helpers.gradient_continuousOn Ω hΩ u hC1
  have hcomp : ∀ i : Fin 2, (fun x => hw.weakGrad x i) =ᵐ[volume.restrict Ω]
      (fun x => planarGradient u x i) := by
    intro i
    have hci : ContinuousOn (fun x => planarGradient u x i) Ω :=
      (EuclideanSpace.proj i).continuous.continuousOn.comp hcont (mapsTo_univ _ _)
    have hloc := (hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num)
    suffices hz : ∀ᵐ x ∂(volume.restrict Ω), hw.weakGrad x i - planarGradient u x i = 0 by
      filter_upwards [hz] with x hx using sub_eq_zero.mp hx
    rw [ae_restrict_iff' hΩ.measurableSet]
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((locallyIntegrableOn_of_locallyIntegrable_restrict hloc).sub
        (hci.locallyIntegrableOn hΩ.measurableSet))
    intro φ hφ hsupp hsub
    have h1 := hw.isWeakGrad i φ hφ hsupp hsub
    have h2 := hweak i φ hφ hsupp hsub
    have hg1 : Integrable (fun x => φ x * hw.weakGrad x i) (volume.restrict Ω) := by
      simpa [smul_eq_mul] using hloc.integrable_smul_left_of_hasCompactSupport hφ.continuous hsupp
    have hg2 : Integrable (fun x => φ x * planarGradient u x i) (volume.restrict Ω) := by
      apply Integrable.integrableOn
      apply SeifertSurfaces.QuasilinearLocalization.Helpers.continuousOn_supported_integrable
        Ω (tsupport φ) _ hsupp hsub (hφ.continuous.continuousOn.mul hci)
      exact (support_mul_subset_left _ _).trans (subset_tsupport φ)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
      have hzero : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))
      simp [hzero])]
    simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
    rw [integral_sub hg1 hg2]
    simp_rw [mul_comm (φ _)]
    linarith
  filter_upwards [ae_all_iff.mpr hcomp] with x hx
  ext i
  exact hx i

def ProviderLinearWeakEquation (B : Set E2) (C : LinearizedCoefficients)
    (v : E2 → ℝ) : Prop :=
  DeGiorgi.MemW1p 2 v B ∧
    ∀ (hv : DeGiorgi.MemW1pWitness 2 v B) (φ : E2 → ℝ), DeGiorgi.MemH01 φ B →
    ∀ hφ : DeGiorgi.MemW1pWitness 2 φ B,
      IntegrableOn (fun x => inner ℝ (linearizedFlux C v hv.weakGrad x) (hφ.weakGrad x)) B ∧
      IntegrableOn (fun x => linearizedSource C v hv.weakGrad x * φ x) B ∧
      (∫ x in B, inner ℝ (linearizedFlux C v hv.weakGrad x) (hφ.weakGrad x) -
        linearizedSource C v hv.weakGrad x * φ x) = 0

/- R2: smooth tests extend to every H₀¹ test and every valid weak-gradient witness. -/


/- R2 energy testing produces a genuine weak derivative of each first derivative.
This is the W²,²_loc step; the second weak gradients are conclusions. -/


/- Weak compactness and passage to the quotient limit produce the exact differentiated
equation with every lower term, rather than postulating it as a regularity assumption. -/


/- R3: an H¹ planar function yields an H¹ lift, with the explicit weak gradient. -/


/- Full lift equation for rough bounded measurable coefficients and the actual Sobolev
gradient. No C¹ premise on `v` or symmetry of the principal field is imposed. -/


/- Sufficient common constants to instantiate the nonsymmetric selected provider:
normalize by λ=min(κ/2,1), extend by identity off the local 3-ball, and conclude inverse
coercivity in the genuine provider bundle. Measurability of all entries is explicit. -/


/- Equality form used by the provider endpoint, with integrability recorded independently
of the totalized bilinear integral. This is not a replacement opaque solution predicate. -/
def ProviderHomogeneousEquation (B : Set E3)
    (A : DeGiorgi.EllipticCoeff 3 B) (V : E3 → ℝ) : Prop :=
  DeGiorgi.MemW1p 2 V B ∧
    ∀ (hV : DeGiorgi.MemW1pWitness 2 V B) (ψ : E3 → ℝ), DeGiorgi.MemH01 ψ B →
    ∀ hψ : DeGiorgi.MemW1pWitness 2 ψ B,
      IntegrableOn (fun y => inner ℝ (DeGiorgi.matMulE (A.a y) (hV.weakGrad y))
        (hψ.weakGrad y)) B ∧
      (∫ y in B, inner ℝ (DeGiorgi.matMulE (A.a y) (hV.weakGrad y)) (hψ.weakGrad y)) = 0



/- Quantitative coefficient normalization alone gives no Hölder conclusion. This combined
bridge supplies the actual homogeneous H₀¹ equation and p₀=2 integrability on a contained ball. -/


def rescaledFunction (center : E3) (R : ℝ) (V : E3 → ℝ) (z : E3) : ℝ :=
  V (center + R • z)

def rescaledMatrix (center : E3) (R : ℝ)
    (A : E3 → Matrix (Fin 3) (Fin 3) ℝ) (z : E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  A (center + R • z)

/- Provider input rescaling: the ordinary 3-ball weak equation, weak gradients and
Lebesgue L² integrability are transported to the unit ball by the actual affine dilation. -/


/- The uniform Hölder constants are selected before `h` and before the direction `k`,
which is the quantitative input required for passage to the derivative limit. -/


/- Quantitative endpoint wrapper: common constants precede the coefficient field and
solution. This is needed to obtain bounds uniform in the difference-quotient step. -/


/- R3 endpoint wrapper to be proved only after the selected provider endpoint is reviewed
and ported. Continuity identifies its a.e. Hölder representative with the actual function. -/


/- R3 assembled local first-gradient Hölder estimate. This remains a proof obligation,
not an input field asserting the regularity used by the protected root theorem. -/


end SeifertSurfaces.QuasilinearProviderBridge
