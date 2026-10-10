import B1ActualNativePositive_v468
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakFormulation
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 0

/-- The native supplied derivative gives the exact regularity-library witness on any set. -/
def native_regular_witness_v468 (U : Set E2) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) : DeGiorgi.MemW1pWitness 2 u U where
  memLp := hu.2.1
  weakGrad := du
  weakGrad_component_memLp := fun i => hu.2.2.eval_piLp i
  isWeakGrad := by
    intro i φ hφ hc ht
    exact hu.1.2.2 φ (hφ.of_le (by simp)) hc ht i

/-- The literal bounded lower-order source is square integrable on the native domain. -/
theorem native_lower_source_L2_v468
    (U : Set E2) (u : E2 → ℝ) (du b : E2 → E2) (c : E2 → ℝ)
    (hu : H1On U u du)
    (hb : AEStronglyMeasurable b (volume.restrict U))
    (hc : AEStronglyMeasurable c (volume.restrict U))
    (B C : ℝ)
    (hB : ∀ᵐ x ∂(volume.restrict U), ‖b x‖ ≤ B)
    (hC : ∀ᵐ x ∂(volume.restrict U), |c x| ≤ C) :
    MemLp (fun x => inner ℝ (b x) (du x) + c x * u x) 2 (volume.restrict U) := by
  have hbd : MemLp (fun x => inner ℝ (b x) (du x)) 2 (volume.restrict U) := by
    apply hu.2.2.of_le_mul (hb.inner hu.2.2.aestronglyMeasurable)
    filter_upwards [hB] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hcu : MemLp (fun x => c x * u x) 2 (volume.restrict U) := by
    apply hu.2.1.of_le_mul (hc.mul hu.2.1.aestronglyMeasurable)
    filter_upwards [hC] with x hx
    simpa [Real.norm_eq_abs,abs_mul] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (u x))
  exact hbd.add hcu

/-- The original native equation is the exact principal-divergence equation with its
actual lower-order L2 source; no regularity premise is introduced. -/
theorem native_linear_principal_weak_v468
    (U : Set E2) (hU : IsOpen U) (a : E2 → Mat2)
    (b : E2 → E2) (c u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du) (heq : WeakLinearEquationOn U a b c u du)
    (A : DeGiorgi.EllipticCoeff 2 U)
    (hAa : ∀ x ∈ U, A.a x = a x)
    (hf : MemLp (fun x => inner ℝ (b x) (du x) + c x * u x) 2 (volume.restrict U)) :
    ∀ v, DeGiorgi.MemH01 v U → ∀ hv : DeGiorgi.MemW1pWitness 2 v U,
      DeGiorgi.bilinFormOfCoeff A (native_regular_witness_v468 U u du hu) hv =
        ∫ x in U, (inner ℝ (b x) (du x) + c x * u x) * v x := by
  apply (DeGiorgi.bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hU _ hf).mpr
  intro φ hs hc ht
  have hφ : MemLp φ 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
  have hlo : IntegrableOn (fun x => (inner ℝ (b x) (du x) + c x * u x) * φ x) U := by
    change Integrable ((fun x => inner ℝ (b x) (du x) + c x * u x) * φ)
      (volume.restrict U)
    exact hf.integrable_mul hφ
  let htest := DeGiorgi.smoothTestWitness hU (show DeGiorgi.IsSmoothTestOn U φ from ⟨hs,hc,ht⟩)
  have hpr := DeGiorgi.integrable_bilinFormIntegrandOfCoeff A
    (native_regular_witness_v468 U u du hu) htest
  have hgrad : DeGiorgi.smoothGradField φ = planarGradient φ := by
    ext x i
    fin_cases i <;> simp [DeGiorgi.smoothGradField,planarGradient,coordinateVector,Fin.sum_univ_two]
  have hact (M : Mat2) (p : E2) : DeGiorgi.matMulE M p = matrixAction M p := by
    ext i
    rfl
  have hpr' : IntegrableOn (fun x => inner ℝ (matrixAction (a x) (du x))
      (planarGradient φ x)) U := by
    have htestgrad : htest.weakGrad = planarGradient φ := by
      change DeGiorgi.smoothGradField φ = planarGradient φ
      exact hgrad
    apply hpr.congr
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [DeGiorgi.bilinFormIntegrandOfCoeff,native_regular_witness_v468,
      hAa x hx,hact]
    rw [htestgrad]
  have hh := (heq.2 φ (hs.of_le (by simp)) hc ht).2
  rw [integral_sub hpr' hlo] at hh
  have hscalar : (∫ x in U, inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x)) =
      ∫ x in U, (inner ℝ (b x) (du x) + c x * u x) * φ x := sub_eq_zero.mp hh
  change (∫ x in U, ∑ i : Fin 2, DeGiorgi.matMulE (A.a x) (du x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
    -(∫ x in U, -(inner ℝ (b x) (du x) + c x * u x) * φ x)
  have hleft' : (∫ x in U, ∑ i : Fin 2, DeGiorgi.matMulE (A.a x) (du x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in U, inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hAa x hx, hact]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [planarGradient, coordinateVector, Fin.sum_univ_two]
    ring
  rw [hleft', hscalar]
  simp_rw [neg_mul]
  rw [integral_neg, neg_neg]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
