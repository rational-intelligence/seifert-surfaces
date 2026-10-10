import B1BoundaryH3Step_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
set_option maxHeartbeats 60000
set_option maxRecDepth 1000
set_option backward.isDefEq.respectTransparency false

/-- The original native equation is the exact principal-divergence equation with its
actual lower-order L2 source; no regularity premise is introduced. -/
theorem native_principal_completed_weak_v474
    (U : Set E2) (hU : IsOpen U) (a : E2 → Mat2)
    (S u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On U u du)
    (hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x)-S x*φ x)=0)
    (A : DeGiorgi.EllipticCoeff 2 U)
    (hAa : ∀ x ∈ U, A.a x = a x)
    (hf : MemLp S 2 (volume.restrict U)) :
    ∀ v, DeGiorgi.MemH01 v U → ∀ hv : DeGiorgi.MemW1pWitness 2 v U,
      DeGiorgi.bilinFormOfCoeff A (native_regular_witness_v468 U u du hu) hv =
        ∫ x in U, (S x) * v x := by
  apply (DeGiorgi.bilinFormOfCoeff_eq_integral_iff_hasWeakDiv hU _ hf).mpr
  intro φ hs hc ht
  have hφ : MemLp φ 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict U
  have hlo : IntegrableOn (fun x => (S x) * φ x) U := by
    change Integrable (S * φ)
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
  have hh := hweak φ hs hc ht
  rw [integral_sub hpr' hlo] at hh
  have hscalar : (∫ x in U, inner ℝ (matrixAction (a x) (du x)) (planarGradient φ x)) =
      ∫ x in U, (S x) * φ x := sub_eq_zero.mp hh
  change (∫ x in U, ∑ i : Fin 2, DeGiorgi.matMulE (A.a x) (du x) i *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) =
    -(∫ x in U, -(S x) * φ x)
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
