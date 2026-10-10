import B1BoundaryLowerSourceTower_v468
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Differentiation
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 800000

theorem regular_witness_native_H1_v468 (U : Set E2) (u : E2 → ℝ)
    (hu : DeGiorgi.MemW1pWitness 2 u U) : H1On U u hu.weakGrad := by
  refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hu.memLp.locallyIntegrable (by norm_num)),
    locallyIntegrableOn_of_locallyIntegrable_restrict (hu.weakGrad_memLp.locallyIntegrable (by norm_num)),
    ?_⟩,hu.memLp,hu.weakGrad_memLp⟩
  intro phi hs hc ht i
  simpa only [coordinateVector] using hu.isWeakGrad i phi hs hc ht

/-- The paid distributional differentiation theorem applies on a patch meeting
the flat edge. Its actual derivative and actual L2 source are constructed from
native H2; no classical boundary derivative is assumed. -/
theorem native_boundary_differentiated_equation_v468
    (U : Set E2) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du)
    (hs : ContDiffOn ℝ ∞ u U) (hdu : ∀ x ∈ U, du x=planarGradient u x)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (heq : WeakLinearEquationOn U a b c u du)
    (A : DeGiorgi.EllipticCoeff 2 U) (hAa : ∀ x ∈ U, A.a x=a x)
    (B : DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm 2 univ)
    (hAB : ∀ x ∈ U, A.a x=B.a x)
    (hu2 : MemWkp 2 2 u U)
    (hf : DeGiorgi.MemW1p 2 (fun x => inner ℝ (b x) (du x)+c x*u x) U)
    (l : Fin 2) :
    ∃ f : E2 → ℝ, MemLp f 2 (volume.restrict U) ∧
      H1On U (fun x => planarGradient u x l) (planarGradient (fun x => planarGradient u x l)) ∧
      ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ U →
        IntegrableOn (fun x => inner ℝ (matrixAction (a x)
          (planarGradient (fun y => planarGradient u y l) x)) (planarGradient phi x)-f x*phi x) U ∧
        (∫ x in U, inner ℝ (matrixAction (a x)
          (planarGradient (fun y => planarGradient u y l) x)) (planarGradient phi x)-f x*phi x)=0 := by
  classical
  let S : E2 → ℝ := fun x => inner ℝ (b x) (du x)+c x*u x
  let hw : DeGiorgi.MemW1pWitness 2 u U := native_regular_witness_v468 U u du hu
  have hweak := native_linear_principal_weak_v468 U hU a b c u du hu heq A hAa hf.1
  let z : E2 → ℝ := chosenWeakPartialOrZero 2 l u U
  let hz : DeGiorgi.MemW1pWitness 2 z U := (hu2.chosenWeakPartial_mem l).memW1p.someWitness
  have hchosen : z =ᵐ[volume.restrict U] (fun x => planarGradient u x l) := by
    have he := (chosenWeakPartialOrZero_isWeakPartial_of_mem hu2.memW1p l).ae_eq hU
      (hw.isWeakGrad l) ((chosenWeakPartialOrZero_memLp_of_mem hu2.memW1p l).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp l).locallyIntegrable (by norm_num))
    filter_upwards [he,ae_restrict_mem hU.measurableSet] with x hx hxU
    exact hx.trans (congrArg (fun v : E2 => v l) (hdu x hxU))
  have hzs : ContDiffOn ℝ ∞ (fun x => planarGradient u x l) U := by
    have he : (fun x => planarGradient u x l)=fun x => fderiv ℝ u x (coordinateVector 2 l) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply u x l
    rw [he]
    exact (hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
  have hzn := regular_witness_native_H1_v468 U z hz
  have hgrad := native_smooth_gradient_ae_v468 U hU z _ hz.weakGrad hzn hzs hchosen
  have hactual := native_h1_congr_ae_v468 U z _ hz.weakGrad _ hzn hchosen hgrad
  let f : E2 → ℝ := fun x => chosenWeakPartialOrZero 2 l S U x+
    DeGiorgi.coefficientDerivativeSource 2 B.a u U l x
  have hflp : MemLp f 2 (volume.restrict U) :=
    (chosenWeakPartialOrZero_memLp_of_mem hf l).add
      (DeGiorgi.memLp_coefficientDerivativeSource hU.measurableSet hUc B.smooth_a hu2 l)
  have hcoeff : ∀ x ∈ U, ∀ i j : Fin 2, A.a x i j=1*B.a x i j := by
    intro x hx i j
    rw [hAB x hx,one_mul]
  have hdiv := DeGiorgi.hasWeakDiv_matMulE_chosenWeakPartialOrZero hU hw hweak hf
    B.smooth_a hcoeff hu2 l hz
  have hdivact : DeGiorgi.HasWeakDiv (fun x => -f x)
      (fun x => matrixAction (a x) (planarGradient (fun y => planarGradient u y l) x)) U := by
    apply hdiv.congr_ae
    · filter_upwards with x
      simp only [f,S,one_mul]
    · filter_upwards [hgrad,ae_restrict_mem hU.measurableSet] with x hx hxU
      rw [hAa x hxU,hx]
      rfl
  refine ⟨f,hflp,hactual,?_⟩
  intro phi hp hc ht
  have hpLp : MemLp phi 2 (volume.restrict U) :=
    (hp.continuous.memLp_of_hasCompactSupport (μ:=volume) hc).restrict U
  let htest := DeGiorgi.smoothTestWitness hU (show DeGiorgi.IsSmoothTestOn U phi from ⟨hp,hc,ht⟩)
  have haLp : MemLp (fun x => matrixAction (a x)
      (planarGradient (fun y => planarGradient u y l) x)) 2 (volume.restrict U) := by
    apply (A.memLp_matMulE hz.weakGrad_memLp).ae_eq
    filter_upwards [hgrad,ae_restrict_mem hU.measurableSet] with x hx hxU
    rw [hAa x hxU,hx]
    rfl
  have htgrad : htest.weakGrad=planarGradient phi := by
    change DeGiorgi.smoothGradField phi=planarGradient phi
    ext x i
    simp [DeGiorgi.smoothTestWitness,DeGiorgi.smoothGradField,planarGradient,coordinateVector,Fin.sum_univ_two]
    fin_cases i <;> simp
  have hi1 : IntegrableOn (fun x => inner ℝ (matrixAction (a x)
      (planarGradient (fun y => planarGradient u y l) x)) (planarGradient phi x)) U := by
    apply (DeGiorgi.integrable_bilinFormIntegrandOfCoeff A hz htest).congr
    filter_upwards [hgrad,ae_restrict_mem hU.measurableSet] with x hx hxU
    simp only [DeGiorgi.bilinFormIntegrandOfCoeff,hAa x hxU,hx,htgrad]
    rfl
  have hi2 : IntegrableOn (fun x => f x*phi x) U := hflp.integrable_mul hpLp
  refine ⟨hi1.sub hi2,?_⟩
  have hh := hdivact phi hp hc ht
  have hleft : (∫ x in U, ∑ i : Fin 2,
      matrixAction (a x) (planarGradient (fun y => planarGradient u y l) x) i*
        fderiv ℝ phi x (EuclideanSpace.single i 1)) =
    ∫ x in U, inner ℝ (matrixAction (a x)
      (planarGradient (fun y => planarGradient u y l) x)) (planarGradient phi x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,Pi.star_apply,star_trivial]
    simp_rw [QuasilinearLocalization.Helpers.gradient_apply,coordinateVector]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hleft] at hh
  simp only [neg_mul,integral_neg,neg_neg] at hh
  rw [integral_sub hi1 hi2,hh,sub_self]
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.regular_witness_native_H1_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_differentiated_equation_v468
