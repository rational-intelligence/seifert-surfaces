import DifferentialGeometry.Analysis.Schauder.Elliptic.VariableCoefficient.BallInterior
import FirstPlanarGain
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

attribute [-instance] DifferentialGeometry.Tensor0SBundle.instNormedAddCommGroupTensor0SModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff Interval NNReal RealInnerProductSpace
open DifferentialGeometry.Analysis.Parabolic.Euclidean DifferentialGeometry.Analysis.Schauder
namespace SeifertSurfaces.QuasilinearBootstrap
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.QuasilinearLocalization

abbrev PlanarMatrix := Matrix (Fin 2) (Fin 2) ℝ

def scalarPartial (f : E2 → ℝ) (i : Fin 2) (x : E2) : ℝ :=
  fderiv ℝ f x (coordinateVector 2 i)

def partialWord (u : E2 → ℝ) : List (Fin 2) → E2 → ℝ
  | [] => u
  | i :: w => scalarPartial (partialWord u w) i

def planarHessian (u : E2 → ℝ) (x : E2) (i j : Fin 2) : ℝ :=
  (fderiv ℝ (fderiv ℝ u) x (coordinateVector 2 i)) (coordinateVector 2 j)

def matrixHessian (a : E2 → PlanarMatrix) (u : E2 → ℝ) (x : E2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, a x i j * planarHessian u x i j

def LinearClassicalEquation (B : Set E2) (a : E2 → PlanarMatrix)
    (f u : E2 → ℝ) : Prop := ∀ x ∈ B, matrixHessian a u x = f x

def rawPrincipalMatrix {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : PlanarMatrix :=
  fun i j => fluxDp Q (firstJet u x) (coordinateVector 2 j) i

def principalMatrix {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : PlanarMatrix :=
  (1 / 2 : ℝ) • (rawPrincipalMatrix Q u x + (rawPrincipalMatrix Q u x).transpose)

def classicalSource {J : Set Jet} (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) : ℝ :=
  -Q.lowerOrder (firstJet u x) -
    ∑ i : Fin 2, (fluxDx Q (firstJet u x) (coordinateVector 2 i) i +
      fluxDz Q (firstJet u x) i * planarGradient u x i)

structure PlanarCoefficientControl (a : E2 → PlanarMatrix) (B : Set E2)
    (κ Λ : ℝ) (H α : NNReal) : Prop where
  symmetric : ∀ x ∈ B, ∀ i j, a x i j = a x j i
  coercive : ∀ x ∈ B, ∀ ξ : E2,
    κ * ‖ξ‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, a x i j * ξ i * ξ j
  bounded : ∀ x ∈ B, ∀ i j, |a x i j| ≤ Λ
  holder : ∀ i j, HolderOnWith H α (fun x => a x i j) B

def ScalarHolderBound (f : E2 → ℝ) (B : Set E2) (α K : NNReal) : Prop :=
  (∀ x ∈ B, |f x| ≤ (K : ℝ)) ∧ HolderOnWith K α f B

/-- The actual convex cutoff interpolation with the frozen matrix. -/
def cutoffMatrix (χ : E2 → ℝ) (a : E2 → PlanarMatrix)
    (A : PlanarMatrix) (x : E2) : PlanarMatrix :=
  χ x • a x + (1 - χ x) • A

/-- After the first gain, integration by parts gives the pointwise PDE with
the sign prescribed by the original weak identity. Only the symmetric part
is used for the classical Hessian contraction. -/
theorem R5_weak_to_pointwise
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ)
    (hC2 : ContDiffOn ℝ 2 u Ω) (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u) :
    LinearClassicalEquation Ω (rawPrincipalMatrix Q u) (classicalSource Q u) u ∧
      LinearClassicalEquation Ω (principalMatrix Q u) (classicalSource Q u) u := by
  classical
  let A : E2 → E2 := fun x => Q.flux (firstJet u x)
  let b : E2 → ℝ := fun x => Q.lowerOrder (firstJet u x)
  have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) Ω := hC2.fderiv_of_isOpen hΩ (by norm_num)
  have hgrad : ContDiffOn ℝ 1 (planarGradient u) Ω := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ => (hdu.clm_apply contDiffOn_const).smul_const _)
  have hjet : ContDiffOn ℝ 1 (firstJet u) Ω :=
    contDiffOn_id.prodMk ((hC2.of_le (by norm_num)).prodMk hgrad)
  have hA : ContDiffOn ℝ 1 A Ω :=
    (Q.flux_smooth.of_le (by simp)).comp hjet hjets
  have hb : ContinuousOn b Ω := Q.lowerOrder_smooth.continuousOn.comp hjet.continuousOn hjets
  have hAi (i : Fin 2) : ContDiffOn ℝ 1 (fun x => A x i) Ω := by
    simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
      (EuclideanSpace.proj i).contDiff.contDiffOn.comp hA (mapsTo_univ _ _)
  let d (i : Fin 2) (x : E2) : ℝ := fderiv ℝ (fun y => A y i) x (coordinateVector 2 i)
  let div (x : E2) : ℝ := ∑ i : Fin 2, d i x
  have hd (i : Fin 2) : ContinuousOn (d i) Ω :=
    ((hAi i).continuousOn_fderiv_of_isOpen hΩ (by norm_num)).clm_apply continuousOn_const
  have hdiv : ContinuousOn div Ω := continuousOn_finsetSum _ (fun i _ => hd i)
  have heq : ∀ x ∈ Ω, div x + b x = 0 := by
    have hae : (fun x => div x + b x) =ᵐ[volume.restrict Ω] 0 := by
      change ∀ᵐ x ∂(volume.restrict Ω), div x + b x = 0
      rw [ae_restrict_iff' hΩ.measurableSet]
      apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((hdiv.add hb).locallyIntegrableOn hΩ.measurableSet)
      intro φ hφ hsupp hsub
      have hdint (i : Fin 2) : IntegrableOn (fun x => d i x * φ x) Ω :=
        (Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          ((hd i).mul hφ.continuous.continuousOn) (Helpers.mul_test_support_subset _ φ)).integrableOn
      have hφgrad (i : Fin 2) : Continuous (fun x => planarGradient φ x i) := by
        simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply] using
          (EuclideanSpace.proj i).continuous.comp (Helpers.gradient_continuous φ hφ)
      have hfluxint (i : Fin 2) : IntegrableOn
          (fun x => A x i * planarGradient φ x i) Ω := by
        apply Integrable.integrableOn
        apply Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          ((hAi i).continuousOn.mul
            (hφgrad i).continuousOn)
        intro x hx
        apply (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i))
        apply subset_tsupport
        simpa only [Function.mem_support, Helpers.gradient_apply] using (mul_ne_zero_iff.mp hx).2
      have hbint : IntegrableOn (fun x => b x * φ x) Ω :=
        (Helpers.continuousOn_supported_integrable Ω (tsupport φ) _ hsupp hsub
          (hb.mul hφ.continuous.continuousOn) (Helpers.mul_test_support_subset _ φ)).integrableOn
      have hip (i : Fin 2) : (∫ x in Ω, A x i * planarGradient φ x i) =
          -(∫ x in Ω, d i x * φ x) := by
        simpa only [Helpers.gradient_apply, coordinateVector, d] using
          (SeifertSurfaces.QuasilinearProviderBridge.Helpers.C1_hasWeakGrad Ω hΩ
            (fun x => A x i) (hAi i) i φ hφ hsupp hsub)
      have hweakφ := hweak φ hφ hsupp hsub
      change (∫ x in Ω, inner ℝ (A x) (planarGradient φ x) - b x * φ x) = 0 at hweakφ
      have hinner : (fun x => inner ℝ (A x) (planarGradient φ x)) =
          (fun x => ∑ i : Fin 2, A x i * planarGradient φ x i) := by
        funext x
        simp [PiLp.inner_apply, mul_comm]
      have hinnerPt (x : E2) := congrFun hinner x
      simp_rw [hinnerPt] at hweakφ
      rw [integral_sub (integrable_finsetSum _ (fun i _ => hfluxint i)) hbint,
        integral_finsetSum _ (fun i _ => hfluxint i)] at hweakφ
      simp_rw [hip] at hweakφ
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω) (fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsub h))])]
      simp only [smul_eq_mul]
      have hfun : (fun x => φ x * (div x + b x)) =
          (fun x => (∑ i : Fin 2, d i x * φ x) + b x * φ x) := by
        funext x
        simp only [div, Fin.sum_univ_two]
        ring
      change (∫ x in Ω, φ x * (div x + b x)) = 0
      rw [hfun, integral_add (integrable_finsetSum _ (fun i _ => hdint i)) hbint,
        integral_finsetSum _ (fun i _ => hdint i)]
      simp only [Fin.sum_univ_two] at hweakφ ⊢
      linarith
    exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae hΩ (hdiv.add hb) continuousOn_const
  have hgradder (x : E2) (hx : x ∈ Ω) (ξ : E2) :
      fderiv ℝ (planarGradient u) x ξ =
        ∑ j : Fin 2, (fderiv ℝ (fderiv ℝ u) x ξ (coordinateVector 2 j)) • coordinateVector 2 j := by
    have hdx := (hdu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
    unfold planarGradient
    rw [fderiv_fun_sum (fun j _ => (hdx.clm_apply (differentiableAt_const _)).smul_const _)]
    simp only [ContinuousLinearMap.sum_apply, fderiv_smul_const
      (hdx.clm_apply (differentiableAt_const _)), ContinuousLinearMap.smulRight_apply,
      fderiv_clm_apply hdx (differentiableAt_const _), fderiv_fun_const,
      Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  have hchain (x : E2) (hx : x ∈ Ω) (i : Fin 2) :
      d i x = fluxDx Q (firstJet u x) (coordinateVector 2 i) i +
        fluxDz Q (firstJet u x) i * planarGradient u x i +
        ∑ j : Fin 2, rawPrincipalMatrix Q u x i j * planarHessian u x i j := by
    have huat := (hC2.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
    have hgat := (hgrad.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by norm_num)
    have hQ := (Q.flux_smooth.contDiffAt (hJ.mem_nhds (hjets x hx))).differentiableAt (by simp)
    have hjetD : HasFDerivAt (firstJet u)
        ((ContinuousLinearMap.id ℝ E2).prod
          ((fderiv ℝ u x).prod (fderiv ℝ (planarGradient u) x))) x :=
      (hasFDerivAt_id x).prodMk (huat.hasFDerivAt.prodMk hgat.hasFDerivAt)
    have hAD := hQ.hasFDerivAt.comp x hjetD
    have hAiD := (EuclideanSpace.proj i).hasFDerivAt.comp x hAD
    have hAiDeq : fderiv ℝ (fun y => A y i) x =
        (EuclideanSpace.proj i).comp ((fderiv ℝ Q.flux (firstJet u x)).comp
          ((ContinuousLinearMap.id ℝ E2).prod
            ((fderiv ℝ u x).prod (fderiv ℝ (planarGradient u) x)))) := by
      simpa only [Function.comp_def, EuclideanSpace.proj, PiLp.proj_apply, A] using hAiD.fderiv
    change (fderiv ℝ (fun y => A y i) x) (coordinateVector 2 i) = _
    rw [hAiDeq]
    change (fderiv ℝ Q.flux (firstJet u x)
      (coordinateVector 2 i, (fderiv ℝ u x (coordinateVector 2 i),
        fderiv ℝ (planarGradient u) x (coordinateVector 2 i)))) i = _
    rw [hgradder x hx, ← Helpers.gradient_apply]
    have hv : (coordinateVector 2 i, (planarGradient u x i,
        ∑ j : Fin 2, planarHessian u x i j • coordinateVector 2 j)) =
        (coordinateVector 2 i, (0, 0)) +
        (planarGradient u x i) • (0, (1, 0)) +
        ∑ j : Fin 2, planarHessian u x i j • (0, (0, coordinateVector 2 j)) := by
      simp only [planarHessian, Fin.sum_univ_two, Prod.fst_add, Prod.snd_add,
        Prod.fst_smul, Prod.snd_smul, smul_zero, zero_add, add_zero, smul_eq_mul, mul_one]
      ext <;> simp [Fin.sum_univ_two]
    change ((fderiv ℝ Q.flux (firstJet u x))
      (coordinateVector 2 i, (planarGradient u x i,
        ∑ j : Fin 2, planarHessian u x i j • coordinateVector 2 j))) i = _
    rw [hv]
    simp only [map_add, map_smul, map_sum, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    unfold rawPrincipalMatrix fluxDp fluxDx fluxDz
    rw [Helpers.fderiv_x_slice Q.flux (firstJet u x) hQ,
      Helpers.fderiv_z_slice Q.flux (firstJet u x) hQ,
      Helpers.fderiv_p_slice Q.flux (firstJet u x) hQ]
    simp only [fluxDx, fluxDz, fluxDp, rawPrincipalMatrix,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    simp only [Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show (0 : ℝ × E2) = (0, 0) from rfl]
    ring
  have hraw : LinearClassicalEquation Ω (rawPrincipalMatrix Q u) (classicalSource Q u) u := by
    intro x hx
    have hp := heq x hx
    dsimp [div, b] at hp
    simp_rw [hchain x hx] at hp
    dsimp [matrixHessian, classicalSource]
    simp only [Fin.sum_univ_two] at hp ⊢
    linarith
  refine ⟨hraw, ?_⟩
  intro x hx
  have hs := (hC2.contDiffAt (hΩ.mem_nhds hx)).isSymmSndFDerivAt (by simp)
  have hij : planarHessian u x 0 1 = planarHessian u x 1 0 := hs.eq _ _
  have hp := hraw x hx
  dsimp [matrixHessian, principalMatrix] at hp ⊢
  simp only [Fin.sum_univ_two, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
    smul_eq_mul] at hp ⊢
  rw [hij] at hp ⊢
  linarith

/-- Actual supported cutoff times u, with global C2,alpha derivative data.
All cost constants precede u and its input norm. No extension is postulated. -/
theorem R5_supported_holder_extension
    (R : ℝ) (hR : 0 < R) (α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : E2) (u : E2 → ℝ) (K : NNReal),
      PlanarHolderJetBound 2 u (Metric.ball x₀ (2 * R)) α K →
      ∃ (χ : E2 → ℝ) (K' : NNReal),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ Metric.ball x₀ R, χ x = 1) ∧
        (∀ q : ℕ, q ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ q χ x‖ ≤ C / R ^ q) ∧
        (K' : ℝ) ≤ C * (K : ℝ) ∧
        PlanarHolderJetBound 2 (fun x => χ x * u x) Set.univ α K' := by
  classical
  let χ₀ : ContDiffBump (0 : E2) := ⟨R, 3 * R / 2, hR, by linarith⟩
  have hχ₀ : ContDiff ℝ ∞ (χ₀ : E2 → ℝ) := χ₀.contDiff
  obtain ⟨D, hD0, hD⟩ := χ₀.hasCompactSupport.exists_bound_iteratedFDeriv hχ₀ 3
  let A : NNReal := Real.toNNReal (D + 1)
  have hA : (A : ℝ) = D + 1 := Real.coe_toNNReal _ (by positivity)
  have hAb (j : ℕ) (hj : j ≤ 3) (x : E2) :
      ‖iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x‖ ≤ (A : ℝ) := by
    rw [hA]
    linarith [hD j hj x]
  have hχ₀jetH (j : ℕ) (hj : j ≤ 2) :
      HolderWith (3 * A) α (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) := by
    have hLip : LipschitzWith A (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) := by
      apply lipschitzWith_of_nnnorm_fderiv_le
        (hχ₀.differentiable_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j))
      intro x
      apply NNReal.coe_le_coe.mp
      change ‖fderiv ℝ (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) x‖ ≤ (A : ℝ)
      simpa only [norm_fderiv_iteratedFDeriv] using hAb (j+1) (by omega) x
    intro x y
    have hr : dist (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x)
        (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) y) ≤ (3 * A : NNReal) * dist x y ^ (α : ℝ) := by
      by_cases hsmall : dist x y ≤ 1
      · calc
          _ ≤ (A : ℝ) * dist x y := hLip.dist_le_mul x y
          _ ≤ (3 * A : NNReal) * dist x y ^ (α : ℝ) := by
            simp only [NNReal.coe_mul, NNReal.coe_ofNat]
            have hd := Real.self_le_rpow_of_le_one dist_nonneg hsmall
              (by exact_mod_cast hαone.le)
            exact (mul_le_mul_of_nonneg_left hd A.coe_nonneg).trans (mul_le_mul_of_nonneg_right (by linarith [A.coe_nonneg]) (Real.rpow_nonneg dist_nonneg (α : ℝ)))
      · have hn : dist (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x)
            (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) y) ≤ 2 * (A : ℝ) :=
          (dist_le_norm_add_norm _ _).trans (by linarith [hAb j (by omega) x, hAb j (by omega) y])
        have hp : 1 ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow (by linarith) α.coe_nonneg
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        nlinarith [A.coe_nonneg]
    simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  let C : ℝ := (A : ℝ) * (1 + R + R^2 + R^3) + 16 * (A : ℝ) + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  have h16 : 16 * (A : ℝ) ≤ C := by dsimp [C]; nlinarith [mul_nonneg A.coe_nonneg (show 0 ≤ 1+R+R^2+R^3 by positivity)]
  refine ⟨C, hCpos, ?_⟩
  intro x₀ u K hu
  let χ : E2 → ℝ := fun x => χ₀ (x - x₀)
  have hχsmooth : ContDiff ℝ ∞ χ := hχ₀.comp (contDiff_id.sub contDiff_const)
  have hχid : χ = (show ContDiffBump x₀ from ⟨R, 3 * R / 2, hR, by linarith⟩) := by
    funext x
    simp only [χ, ContDiffBump.apply, χ₀, sub_zero]
  have hχsupp : tsupport χ = Metric.closedBall x₀ (3 * R / 2) := by
    rw [hχid, ContDiffBump.tsupport_eq]
  have hχtr (j : ℕ) (x : E2) : iteratedFDeriv ℝ j χ x =
      iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) (x - x₀) := by
    exact iteratedFDeriv_comp_sub j x₀ x
  have hχb (j : ℕ) (hj : j ≤ 3) (x : E2) : ‖iteratedFDeriv ℝ j χ x‖ ≤ (A : ℝ) := by
    rw [hχtr]
    exact hAb j hj _
  have hχjetH (j : ℕ) (hj : j ≤ 2) : HolderWith (3 * A) α (iteratedFDeriv ℝ j χ) := by
    intro x y
    simpa only [hχtr, edist_sub_right] using hχ₀jetH j hj (x-x₀) (y-x₀)
  let B : Set E2 := Metric.ball x₀ (2 * R)
  have hB : IsOpen B := Metric.isOpen_ball
  have hχoutside (x : E2) (hx : x ∉ B) : χ =ᶠ[𝓝 x] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    rw [hχsupp]
    exact fun hy => hx (Metric.closedBall_subset_ball (by linarith) hy)
  have hvoutside (x : E2) (hx : x ∉ B) :
      (fun z => χ z * u z) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hχoutside x hx] with z hz
    simp [hz]
  have hvzero (j : ℕ) (x : E2) (hx : x ∉ B) :
      iteratedFDeriv ℝ j (fun z => χ z * u z) x = 0 := by
    simpa only [iteratedFDeriv_zero, Pi.zero_apply] using ((hvoutside x hx).iteratedFDeriv ℝ j).eq_of_nhds
  have hvC2 : ContDiffOn ℝ 2 (fun z => χ z * u z) Set.univ := by
    intro x _
    apply ContDiffAt.contDiffWithinAt
    by_cases hx : x ∈ B
    · exact ((hχsmooth.of_le (by simp)).contDiffAt).mul (hu.1.contDiffAt (hB.mem_nhds hx))
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hvoutside x hx)
  have hmul {t : Set E2} (ht : IsOpen t) {x : E2} (hx : x ∈ t)
      {f g : E2 → ℝ} (hf : ContDiffOn ℝ 2 f t) (hg : ContDiffOn ℝ 2 g t)
      {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
      (hfb : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
      (hgb : ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j g x‖ ≤ B)
      (q : ℕ) (hq : q ≤ 2) :
      ‖iteratedFDeriv ℝ q (fun z => f z * g z) x‖ ≤ 4 * A * B := by
      have hs := norm_iteratedFDerivWithin_mul_le hf hg ht.uniqueDiffOn hx (n := q)
        (by exact_mod_cast hq)
      simp_rw [iteratedFDerivWithin_of_isOpen _ ht hx] at hs
      apply hs.trans
      have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (q-i) g x‖) ≤
          ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hiq : i ≤ q := by have := Finset.mem_range.mp hi; omega
        gcongr
        · exact hfb i (hiq.trans hq)
        · exact hgb (q-i) ((Nat.sub_le _ _).trans hq)
      apply hsum.trans
      interval_cases q <;> norm_num [Finset.sum_range_succ] <;> nlinarith

  let K' : NNReal := Real.toNNReal C * K
  have hK' : (K' : ℝ) = C * (K : ℝ) := by
    simp only [K', NNReal.coe_mul, Real.coe_toNNReal _ hCpos.le]
  refine ⟨χ, K', hχsmooth, ?_, hχsupp.subset, ?_, ?_, ?_, hK'.le, hvC2, ?_⟩
  · rw [hχid]
    exact ContDiffBump.hasCompactSupport _
  · intro x
    exact ⟨χ₀.nonneg, χ₀.le_one⟩
  · intro x hx
    rw [hχid]
    exact ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hx)
  · intro q hq x
    have hb := hχb q hq x
    have hp : R ^ q ≤ 1 + R + R^2 + R^3 := by
      interval_cases q <;> norm_num <;> nlinarith [pow_nonneg hR.le 3, sq_nonneg R]
    apply (le_div_iff₀ (pow_pos hR q)).mpr
    calc
      _ ≤ (A : ℝ) * R ^ q := mul_le_mul_of_nonneg_right hb (pow_pos hR q).le
      _ ≤ (A : ℝ) * (1 + R + R^2 + R^3) := mul_le_mul_of_nonneg_left hp A.coe_nonneg
      _ ≤ C := by dsimp [C]; nlinarith [A.coe_nonneg]
  intro q hq
  constructor
  · intro x _
    rw [hK']
    by_cases hx : x ∈ B
    · exact (hmul hB hx ((hχsmooth.of_le (by simp)).contDiffOn) hu.1
        A.coe_nonneg K.coe_nonneg (fun j hj => hχb j (by omega) x)
        (fun j hj => (hu.2 j hj).1 x hx) q hq).trans
        (mul_le_mul_of_nonneg_right (by linarith : 4 * (A : ℝ) ≤ C) K.coe_nonneg)
    · rw [hvzero q x hx, norm_zero]
      positivity
  · intro x _ y _
    have hχzero (j : ℕ) (z : E2) (hz : z ∉ B) : iteratedFDeriv ℝ j χ z = 0 := by
      simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
        ((hχoutside z hz).iteratedFDeriv ℝ j).eq_of_nhds
    have hgeneral (x y : E2) (hx : x ∈ B) :
        ‖iteratedFDeriv ℝ q (fun z => χ z * u z) x -
          iteratedFDeriv ℝ q (fun z => χ z * u z) y‖ ≤
          16 * (A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ) := by
      let T : Set E2 := (fun z => z+x) ⁻¹' B ∩ (fun z => z+y) ⁻¹' B
      have hT : IsOpen T := (hB.preimage (continuous_id.add continuous_const)).inter
        (hB.preimage (continuous_id.add continuous_const))
      have hχx : ContDiffOn ℝ 2 (fun z => χ (z+x)) T :=
        ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
      have hχy : ContDiffOn ℝ 2 (fun z => χ (z+y)) T :=
        ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
      have hχxq : ContDiffAt ℝ q (fun z => χ (z+x)) 0 :=
        (((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
          (by simp)).contDiffAt : ContDiffAt ℝ q (fun z => χ (z+x)) 0)
      have hχyq : ContDiffAt ℝ q (fun z => χ (z+y)) 0 :=
        (((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
          (by simp)).contDiffAt : ContDiffAt ℝ q (fun z => χ (z+y)) 0)
      have hχdiff (j : ℕ) (hj : j ≤ 2) :
          ‖iteratedFDeriv ℝ j (fun z => χ (z+x) - χ (z+y)) 0‖ ≤
            3 * (A : ℝ) * dist x y ^ (α : ℝ) := by
        have hc := (hχjetH j hj).dist_le x y
        rw [dist_eq_norm] at hc
        rw [fun_iteratedFDeriv_sub_apply (f := fun z => χ (z+x)) (g := fun z => χ (z+y))
          ((((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt) :
            ContDiffAt ℝ j (fun z => χ (z+x)) 0)
          ((((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
            (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt) :
            ContDiffAt ℝ j (fun z => χ (z+y)) 0),
          iteratedFDeriv_comp_add_right, iteratedFDeriv_comp_add_right, zero_add, zero_add]
        simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hc
      have htransprod (z : E2) :
          iteratedFDeriv ℝ q (fun w => χ (w+z) * u (w+z)) 0 =
            iteratedFDeriv ℝ q (fun w => χ w * u w) z := by
        simpa only [zero_add] using
          (iteratedFDeriv_comp_add_right (f := fun w => χ w * u w) q z (0 : E2))
      by_cases hy : y ∈ B
      · have hT0 : (0 : E2) ∈ T := by simpa only [T, Set.mem_inter_iff, Set.mem_preimage, zero_add] using And.intro hx hy
        have hux : ContDiffOn ℝ 2 (fun z => u (z+x)) T := hu.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.1)
        have huy : ContDiffOn ℝ 2 (fun z => u (z+y)) T := hu.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.2)
        have huxb (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (fun z => u (z+x)) 0‖ ≤ (K : ℝ) := by
          simpa only [iteratedFDeriv_comp_add_right, zero_add] using (hu.2 j hj).1 x hx
        have huyχb (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (fun z => χ (z+y)) 0‖ ≤ (A : ℝ) := by
          simpa only [iteratedFDeriv_comp_add_right, zero_add] using hχb j (by omega) y
        have hudiff (j : ℕ) (hj : j ≤ 2) :
            ‖iteratedFDeriv ℝ j (fun z => u (z+x) - u (z+y)) 0‖ ≤
              (K : ℝ) * dist x y ^ (α : ℝ) := by
          have hc := ((hu.2 j hj).2).dist_le hx hy
          rw [dist_eq_norm] at hc
          simpa only [fun_iteratedFDeriv_sub_apply
            ((hux.of_le (by exact_mod_cast hj)).contDiffAt (hT.mem_nhds hT0))
            ((huy.of_le (by exact_mod_cast hj)).contDiffAt (hT.mem_nhds hT0)),
            iteratedFDeriv_comp_add_right, zero_add] using hc
        have hb1 := hmul hT hT0 (hχx.sub hχy) hux
          (by positivity : 0 ≤ 3 * (A : ℝ) * dist x y ^ (α : ℝ)) K.coe_nonneg
          hχdiff huxb q hq
        have hb2 := hmul hT hT0 hχy (hux.sub huy) A.coe_nonneg
          (by positivity : 0 ≤ (K : ℝ) * dist x y ^ (α : ℝ))
          huyχb hudiff q hq
        have hvxq : ContDiffAt ℝ q (fun z => χ (z+x) * u (z+x)) 0 :=
          ((hχx.mul hux).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0)
        have hvyq : ContDiffAt ℝ q (fun z => χ (z+y) * u (z+y)) 0 :=
          ((hχy.mul huy).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0)
        have he : (fun z => χ (z+x) * u (z+x) - χ (z+y) * u (z+y)) =
            (fun z => (χ (z+x) - χ (z+y)) * u (z+x) + χ (z+y) * (u (z+x) - u (z+y))) := by
          funext z
          ring
        have hd := congrArg (fun f : E2 → ℝ => iteratedFDeriv ℝ q f 0) he
        rw [fun_iteratedFDeriv_sub_apply hvxq hvyq,
          fun_iteratedFDeriv_add_apply
            ((((hχx.sub hχy).mul hux).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0))
            (((hχy.mul (hux.sub huy)).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0))] at hd
        rw [htransprod x, htransprod y] at hd
        rw [hd]
        exact (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans_eq (by ring))
      · let S : Set E2 := (fun z => z+x) ⁻¹' B
        have hS : IsOpen S := hB.preimage (continuous_id.add continuous_const)
        have hS0 : (0 : E2) ∈ S := by simpa only [S, Set.mem_preimage, zero_add] using hx
        have hsχ : ContDiffOn ℝ 2 (fun z => χ (z+x)) S :=
          ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
        have hsu : ContDiffOn ℝ 2 (fun z => u (z+x)) S := hu.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz)
        have hsb (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (fun z => χ (z+x)) 0‖ ≤
            3 * (A : ℝ) * dist x y ^ (α : ℝ) := by
          have hc := (hχjetH j hj).dist_le x y
          rw [dist_eq_norm, hχzero j y hy, sub_zero] at hc
          simpa only [iteratedFDeriv_comp_add_right, zero_add, NNReal.coe_mul, NNReal.coe_ofNat] using hc
        have hb := hmul hS hS0 hsχ hsu
          (by positivity : 0 ≤ 3 * (A : ℝ) * dist x y ^ (α : ℝ)) K.coe_nonneg hsb
          (fun j hj => by simpa only [iteratedFDeriv_comp_add_right, zero_add] using (hu.2 j hj).1 x hx) q hq
        rw [hvzero q y hy, sub_zero]
        rw [htransprod x] at hb
        apply hb.trans
        calc
          _ = 12 * ((A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ)) := by ring
          _ ≤ 16 * ((A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ)) :=
            mul_le_mul_of_nonneg_right (by norm_num)
              (mul_nonneg (mul_nonneg A.coe_nonneg K.coe_nonneg) (Real.rpow_nonneg dist_nonneg _))
          _ = _ := by ring
    have hr : dist (iteratedFDeriv ℝ q (fun z => χ z * u z) x)
        (iteratedFDeriv ℝ q (fun z => χ z * u z) y) ≤ (K' : ℝ) * dist x y ^ (α : ℝ) := by
      rw [dist_eq_norm, hK']
      have hcost : 16 * (A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ) ≤
          C * (K : ℝ) * dist x y ^ (α : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h16 K.coe_nonneg)
          (Real.rpow_nonneg dist_nonneg _)
      by_cases hx : x ∈ B
      · exact (hgeneral x y hx).trans hcost
      · by_cases hy : y ∈ B
        · rw [norm_sub_rev, dist_comm x y]
          exact (hgeneral y x hy).trans (by simpa only [dist_comm] using hcost)
        · rw [hvzero q x hx, hvzero q y hy, sub_self, norm_zero]
          positivity
    simpa only [edist_dist, ENNReal.ofReal_mul K'.coe_nonneg,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr

/-- Construct global bounded Hölder coefficients before using a global
provider. Ellipticity is retained by the explicit convex interpolation,
which agrees with the supplied coefficients on the inner ball. -/
theorem R5_global_coefficient_extension
    (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : E2) (a : E2 → PlanarMatrix),
      PlanarCoefficientControl a (Metric.ball x₀ (2 * R)) κ Λ H α →
      ∃ (χ : E2 → ℝ) (H' : NNReal),
        ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ Metric.ball x₀ R, χ x = 1) ∧
        (H' : ℝ) ≤ C * (Λ + (H : ℝ)) ∧
        PlanarCoefficientControl (cutoffMatrix χ a (a x₀)) Set.univ κ Λ H' α ∧
        (∀ x ∈ Metric.ball x₀ R, cutoffMatrix χ a (a x₀) x = a x) := by
  classical
  let χ₀ : ContDiffBump (0 : E2) := ⟨R, 3 * R / 2, hR, by linarith⟩
  have hχ₀ : ContDiff ℝ ∞ (χ₀ : E2 → ℝ) := χ₀.contDiff
  obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E2) (3 * R / 2)).exists_bound_of_continuousOn
    (hχ₀.continuous_fderiv (by simp)).continuousOn
  let L : NNReal := Real.toNNReal D
  have hderbound (x : E2) : ‖fderiv ℝ (χ₀ : E2 → ℝ) x‖₊ ≤ L := by
    apply NNReal.coe_le_coe.mp
    by_cases hx : x ∈ Metric.closedBall (0 : E2) (3 * R / 2)
    · exact (hD x hx).trans (Real.le_coe_toNNReal _)
    · have hz : fderiv ℝ (χ₀ : E2 → ℝ) x = 0 := by
        apply fderiv_of_notMem_tsupport
        simpa only [χ₀.tsupport_eq] using hx
      simp only [hz, nnnorm_zero, NNReal.coe_zero]
      exact L.coe_nonneg
  have hχLip : LipschitzWith L (χ₀ : E2 → ℝ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hχ₀.differentiable (by simp)) hderbound
  let Aχ := L + 2
  have hχH : HolderWith Aχ α (χ₀ : E2 → ℝ) := by
    intro x y
    have hr : dist (χ₀ x) (χ₀ y) ≤ (Aχ : ℝ) * dist x y ^ (α : ℝ) := by
      by_cases hsmall : dist x y ≤ 1
      · exact (hχLip.dist_le_mul x y).trans
          (mul_le_mul ((le_add_of_nonneg_right (show (0 : ℝ) ≤ 2 by norm_num)))
            (Real.self_le_rpow_of_le_one dist_nonneg hsmall (by exact_mod_cast hαone.le))
            dist_nonneg (by dsimp [Aχ]; positivity))
      · have hdiff : dist (χ₀ x) (χ₀ y) ≤ 2 := by
          rw [Real.dist_eq]
          exact (abs_sub _ _).trans (by rw [abs_of_nonneg χ₀.nonneg, abs_of_nonneg χ₀.nonneg]; linarith [χ₀.le_one (x := x), χ₀.le_one (x := y)])
        have hrpow : 1 ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow (by linarith) α.coe_nonneg
        exact hdiff.trans (by dsimp [Aχ]; nlinarith [L.coe_nonneg])
    simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  refine ⟨2 * (Aχ : ℝ) + 1, by positivity, ?_⟩
  intro x₀ a ha
  let χ : E2 → ℝ := fun x => χ₀ (x - x₀)
  have hχsmooth : ContDiff ℝ ∞ χ := hχ₀.comp (contDiff_id.sub contDiff_const)
  have hχid : χ = (show ContDiffBump x₀ from ⟨R, 3 * R / 2, hR, by linarith⟩) := by
    funext x
    simp only [χ, ContDiffBump.apply, χ₀, sub_zero]
  have hχsupp : tsupport χ = Metric.closedBall x₀ (3 * R / 2) := by
    rw [hχid, ContDiffBump.tsupport_eq]
  have hχrange (x : E2) : 0 ≤ χ x ∧ χ x ≤ 1 := ⟨χ₀.nonneg, χ₀.le_one⟩
  have hχone (x : E2) (hx : x ∈ Metric.ball x₀ R) : χ x = 1 := by
    rw [hχid]
    exact ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hx)
  have hχHolder : HolderWith Aχ α χ := by
    intro x y
    have h := hχH (x - x₀) (y - x₀)
    simpa only [χ, edist_sub_right] using h
  have hχzero (x : E2) (hx : x ∉ Metric.ball x₀ (2 * R)) : χ x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [hχsupp]
    exact fun hy => hx (Metric.closedBall_subset_ball (by linarith) hy)
  have hΛ0 : 0 < Λ := hκ.trans_le hΛ
  let H' : NNReal := H + 2 * Real.toNNReal Λ * Aχ
  have hH' : (H' : ℝ) ≤ (2 * (Aχ : ℝ) + 1) * (Λ + (H : ℝ)) := by
    simp only [H', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal Λ hΛ0.le]
    nlinarith [H.coe_nonneg, Aχ.coe_nonneg]
  refine ⟨χ, H', hχsmooth, ?_, hχsupp.subset, hχrange, hχone, hH', ?_, ?_⟩
  · rw [hχid]
    exact ContDiffBump.hasCompactSupport _
  · constructor
    · intro x hx i j
      by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
      · simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rw [ha.symmetric x hxB i j, ha.symmetric x₀ (Metric.mem_ball_self (by linarith)) i j]
      · simp only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul]
        exact ha.symmetric x₀ (Metric.mem_ball_self (by linarith)) i j
    · intro x hx ξ
      by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
      · have h1 := ha.coercive x hxB ξ
        have h0 := ha.coercive x₀ (Metric.mem_ball_self (by linarith)) ξ
        have hχ := hχrange x
        have he : (∑ i : Fin 2, ∑ j : Fin 2, cutoffMatrix χ a (a x₀) x i j * ξ i * ξ j) =
            χ x * (∑ i : Fin 2, ∑ j : Fin 2, a x i j * ξ i * ξ j) +
            (1 - χ x) * (∑ i : Fin 2, ∑ j : Fin 2, a x₀ i j * ξ i * ξ j) := by
          simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
          ring
        rw [he]
        nlinarith [mul_le_mul_of_nonneg_left h1 hχ.1,
          mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ 1 - χ x)]
      · simpa only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul] using
          ha.coercive x₀ (Metric.mem_ball_self (by linarith)) ξ
    · intro x hx i j
      by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
      · have hχ := hχrange x
        simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        calc
          |χ x * a x i j + (1 - χ x) * a x₀ i j| ≤
              χ x * |a x i j| + (1 - χ x) * |a x₀ i j| := by
            simpa only [abs_mul, abs_of_nonneg hχ.1, abs_of_nonneg (by linarith : 0 ≤ 1 - χ x)] using abs_add_le (χ x * a x i j) ((1 - χ x) * a x₀ i j)
          _ ≤ χ x * Λ + (1 - χ x) * Λ := add_le_add
            (mul_le_mul_of_nonneg_left (ha.bounded x hxB i j) hχ.1)
            (mul_le_mul_of_nonneg_left (ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j) (by linarith))
          _ = Λ := by ring
      · simpa only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul] using
          ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j
    · intro i j x hx y hy
      have hdist : dist (cutoffMatrix χ a (a x₀) x i j) (cutoffMatrix χ a (a x₀) y i j) ≤
          (H' : ℝ) * dist x y ^ (α : ℝ) := by
        have hzero := hχzero
        have hfreeze : |a x₀ i j| ≤ Λ := ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j
        have hbd (z : E2) (hz : z ∈ Metric.ball x₀ (2 * R)) : |a z i j - a x₀ i j| ≤ 2 * Λ :=
          (abs_sub _ _).trans (by linarith [ha.bounded z hz i j])
        have hgeneral (x y : E2) (hxB : x ∈ Metric.ball x₀ (2 * R)) :
            |cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j| ≤
              ((H : ℝ) + 2 * Λ * (Aχ : ℝ)) * dist x y ^ (α : ℝ) := by
          by_cases hyB : y ∈ Metric.ball x₀ (2 * R)
          · have hc := hχHolder.dist_le x y
            have hh := (ha.holder i j).dist_le hxB hyB
            have he : cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j =
                χ x * (a x i j - a y i j) + (χ x - χ y) * (a y i j - a x₀ i j) := by
              simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
              ring
            rw [he]
            have hχ := hχrange x
            calc
              _ ≤ |χ x| * |a x i j - a y i j| + |χ x - χ y| * |a y i j - a x₀ i j| := by simpa only [abs_mul] using abs_add_le (χ x * (a x i j - a y i j)) ((χ x - χ y) * (a y i j - a x₀ i j))
              _ ≤ (H : ℝ) * dist x y ^ (α : ℝ) + (Aχ : ℝ) * dist x y ^ (α : ℝ) * (2 * Λ) := by
                apply add_le_add
                · have hh' : |a x i j - a y i j| ≤ (H : ℝ) * dist x y ^ (α : ℝ) := by simpa only [Real.dist_eq] using hh
                  rw [abs_of_nonneg hχ.1]
                  exact (mul_le_mul hχ.2 hh' (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
                · exact mul_le_mul (by simpa only [Real.dist_eq] using hc) (hbd y hyB) (abs_nonneg _) (by positivity)
              _ = _ := by ring
          · have hc := hχHolder.dist_le x y
            rw [hzero y hyB] at hc
            simp only [Real.dist_eq, sub_zero, abs_of_nonneg (hχrange x).1] at hc
            have he : cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j =
                χ x * (a x i j - a x₀ i j) := by
              simp only [cutoffMatrix, hzero y hyB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
              ring
            rw [he, abs_mul, abs_of_nonneg (hχrange x).1]
            have hm := mul_le_mul hc (hbd x hxB) (abs_nonneg _) (mul_nonneg Aχ.coe_nonneg (Real.rpow_nonneg dist_nonneg _))
            exact hm.trans (by
              have hnn := mul_nonneg H.coe_nonneg (Real.rpow_nonneg (show 0 ≤ dist x y from dist_nonneg) (α : ℝ))
              nlinarith)
        have hcast : (H' : ℝ) = (H : ℝ) + 2 * Λ * (Aχ : ℝ) := by
          simp only [H', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal Λ hΛ0.le]
        rw [hcast, Real.dist_eq]
        by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
        · exact hgeneral x y hxB
        · by_cases hyB : y ∈ Metric.ball x₀ (2 * R)
          · simpa only [abs_sub_comm, dist_comm] using hgeneral y x hyB
          · simp only [cutoffMatrix, hzero x hxB, hzero y hyB, zero_smul, zero_add, sub_zero, one_smul, sub_self, abs_zero]
            positivity
      simpa only [edist_dist, ENNReal.ofReal_mul H'.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hdist
  · intro x hx
    simp only [cutoffMatrix, hχone x hx, one_smul, sub_self, zero_smul, add_zero]

/-- Affine rescaling makes BOTH coefficient oscillation and the scaled
Hölder seminorm small. The displayed finite sum is sufficient to make any
fixed continuous linear defect factor times that sum small. -/
theorem R5_rescaled_coefficients_small
    (x₀ : E2) (R : ℝ) (hR : 0 < R) (a : E2 → PlanarMatrix)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1)
    (hholder : ∀ i j, HolderOnWith H α (fun x => a x i j) (Metric.ball x₀ R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ 2 * s < R ∧
      (∀ i j, HolderOnWith (H * Real.toNNReal (s ^ (α : ℝ))) α
        (fun z => a (x₀ + s • z) i j) (Metric.ball (0 : E2) 2)) ∧
      (∀ i j z, z ∈ Metric.ball (0 : E2) 2 →
        |a (x₀ + s • z) i j - a x₀ i j| ≤ (H : ℝ) * (2 * s) ^ (α : ℝ)) ∧
      4 * (H : ℝ) * ((2 * s) ^ (α : ℝ) + s ^ (α : ℝ)) < ε := by
  have hc : Continuous (fun s : ℝ =>
      4 * (H : ℝ) * ((2 * s) ^ (α : ℝ) + s ^ (α : ℝ))) :=
    continuous_const.mul
      (((Real.continuous_rpow_const α.coe_nonneg).comp
        (continuous_const.mul continuous_id)).add
        (Real.continuous_rpow_const α.coe_nonneg))
  have hevent : ∀ᶠ s : ℝ in 𝓝 0,
      4 * (H : ℝ) * ((2 * s) ^ (α : ℝ) + s ^ (α : ℝ)) < ε := by
    have h0 : (4 * (H : ℝ) * ((2 * (0 : ℝ)) ^ (α : ℝ) + (0 : ℝ) ^ (α : ℝ))) = 0 := by
      simp [Real.zero_rpow (show (α : ℝ) ≠ 0 from (NNReal.coe_pos.mpr hα).ne')]
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa only [h0] using hε))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  let s : ℝ := min (R / 4) (δ / 2)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsR : 2 * s < R := by have := min_le_left (R / 4) (δ / 2); dsimp [s]; linarith
  have hsδ : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hs]
    have := min_le_right (R / 4) (δ / 2)
    dsimp [s]
    linarith
  have hmaps (z : E2) (hz : z ∈ Metric.ball (0 : E2) 2) :
      x₀ + s • z ∈ Metric.ball x₀ R := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hs.le]
    exact (mul_lt_mul_of_pos_left hz hs).trans (by simpa [mul_comm] using hsR)
  have hd (z w : E2) : dist (x₀ + s • z) (x₀ + s • w) = s * dist z w := by
    simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_of_nonneg hs.le]
  refine ⟨s, hs, hsR, ?_, ?_, hnear hsδ⟩
  · intro i j z hz w hw
    have hreal := (hholder i j).dist_le (hmaps z hz) (hmaps w hw)
    rw [hd, Real.mul_rpow hs.le dist_nonneg] at hreal
    have hcast : ((H * Real.toNNReal (s ^ (α : ℝ)) : NNReal) : ℝ) =
        (H : ℝ) * s ^ (α : ℝ) := by
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hs.le _)]
    have hb : dist (a (x₀ + s • z) i j) (a (x₀ + s • w) i j) ≤
        ((H * Real.toNNReal (s ^ (α : ℝ)) : NNReal) : ℝ) * dist z w ^ (α : ℝ) := by
      rw [hcast, mul_assoc]
      exact hreal
    simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hb
  · intro i j z hz
    have hdist : dist (x₀ + s • z) x₀ ≤ 2 * s := by
      simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
      simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
      nlinarith
    simpa only [Real.dist_eq] using (hholder i j).dist_le_of_le
      (hmaps z hz) (Metric.mem_ball_self hR) hdist

/-- Local nondivergence Schauder a priori obligation. The output C depends
only on the displayed ellipticity, radius and coefficient Hölder bound.
The supplied K2 certifies applicability and does not enter the estimate. -/
theorem R5_classical_schauder_apriori
    (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
    (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : E2) (a : E2 → PlanarMatrix),
      PlanarCoefficientControl a (Metric.ball x₀ (2 * R)) κ Λ H α →
      ∀ (f v : E2 → ℝ) (F U K2 : NNReal),
      ScalarHolderBound f (Metric.ball x₀ (2 * R)) α F →
      PlanarHolderJetBound 1 v (Metric.ball x₀ (2 * R)) α U →
      PlanarHolderJetBound 2 v (Metric.ball x₀ (2 * R)) α K2 →
      LinearClassicalEquation (Metric.ball x₀ (2 * R)) a f v →
      ∃ K' : NNReal, (K' : ℝ) ≤ C * ((U : ℝ) + (F : ℝ)) ∧
        PlanarHolderJetBound 2 v (Metric.ball x₀ R) α K' := by
  classical
  let actualSecondJet (v : E2 → ℝ) (x : E2) : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ v) x
  let affinePull (c : E2) (s : ℝ) (z : E2) : E2 := c+s • z
  let affineSolution (c : E2) (s : ℝ) (v : E2 → ℝ) : E2 → ℝ := v ∘ affinePull c s
  let affineMatrix (c : E2) (s : ℝ) (a : E2 → PlanarMatrix) : E2 → PlanarMatrix := a ∘ affinePull c s
  let affineSource (c : E2) (s : ℝ) (f : E2 → ℝ) : E2 → ℝ :=
    fun z => s^2*f (affinePull c s z)
  let scaledEntryHolder (H α : NNReal) (s : ℝ) : NNReal := H*Real.toNNReal (s^(α:ℝ))
  let normalizedEntryOscillation (K α : NNReal) : NNReal := K*(2:NNReal)^(α:ℝ)
  let normalizedWitness (a : E2 → PlanarMatrix) (f v : E2 → ℝ)
        (κ Λ : ℝ) (H α U F Cost Kapp : NNReal) : Prop :=
      ∃ (cutoff : E2 → ℝ) (coefficient_cutoff : E2 → ℝ) (solution : BoundedContinuousFunction E2 ℝ) (first : BoundedContinuousFunction E2 (E2 →L[ℝ] ℝ)) (second : BoundedContinuousFunction E2 (E2 →L[ℝ] E2 →L[ℝ] ℝ)) (source : BoundedContinuousFunction E2 ℝ) (coefficients : Fin 2 → Fin 2 → BoundedContinuousFunction E2 ℝ),
        (ContDiff ℝ ∞ cutoff) ∧
        (tsupport cutoff ⊆ Metric.closedBall (0 : E2) 3) ∧
        (∀ x, 0 ≤ cutoff x ∧ cutoff x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : E2) 2, cutoff x = 1) ∧
        (∀ q : ℕ, q ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ q cutoff x‖ ≤ (Cost : ℝ)) ∧
        (ContDiff ℝ ∞ coefficient_cutoff) ∧
        (tsupport coefficient_cutoff ⊆ Metric.closedBall (0 : E2) 3) ∧
        (∀ x, 0 ≤ coefficient_cutoff x ∧ coefficient_cutoff x ≤ 1) ∧
        (∀ x ∈ Metric.ball (0 : E2) 2, coefficient_cutoff x = 1) ∧
        (∀ x, solution x = cutoff x * v x) ∧
        (∀ x, first x = fderiv ℝ (fun y => cutoff y * v y) x) ∧
        (∀ x, second x = actualSecondJet (fun y => cutoff y * v y) x) ∧
        (∀ x, source x = cutoff x * f x) ∧
        (∀ i j x,
      coefficients i j x = cutoffMatrix coefficient_cutoff a (a 0) x i j) ∧
        (∀ x, HasFDerivAt (solution : E2 → ℝ) (first x) x) ∧
        (∀ x, HasFDerivAt (first : E2 → E2 →L[ℝ] ℝ) (second x) x) ∧
        (‖solution‖₊ ≤ Cost * U) ∧
        (‖first‖₊ ≤ Cost * U) ∧
        (‖source‖₊ ≤ Cost * F) ∧
        (‖second‖₊ ≤ Kapp) ∧
        (HolderWith (Cost * U) α (solution : E2 → ℝ)) ∧
        (HolderWith (Cost * U) α (first : E2 → E2 →L[ℝ] ℝ)) ∧
        (HolderWith (Cost * F) α (source : E2 → ℝ)) ∧
        (HolderWith Kapp α (second : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ)) ∧
        (PlanarCoefficientControl
      (fun x i j => coefficients i j x) Set.univ κ Λ
      (Cost * (Real.toNNReal Λ + H)) α)
  have hquadraticProvider
      (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
      (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
      (hcoercive : ∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤
        ∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j)
      (hentries : ∀ i j, |A i j| ≤ Λ) :
      (∀ ξ : E2, inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) A ξ) =
        ∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j) ∧
      (∀ ξ : E2, inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) A ξ) ≤
        2 * Λ * ‖ξ‖ ^ 2) ∧
      ‖(spdSqrtEquiv A hA : E2 →L[ℝ] E2)‖ ≤ Real.sqrt (2 * Λ) ∧
      ‖((spdSqrtEquiv A hA).symm : E2 →L[ℝ] E2)‖ ≤ (Real.sqrt κ)⁻¹ := by
    have hΛpos : 0 < Λ := lt_of_lt_of_le hκ hΛ
    have hquad : ∀ ξ : E2, inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) A ξ) =
        ∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j := by
      intro ξ
      simp [PiLp.inner_apply, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      ring
    have hupper : ∀ ξ : E2,
        inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 2) A ξ) ≤
          2 * Λ * ‖ξ‖ ^ 2 := by
      intro ξ
      rw [hquad]
      have hb : ∀ i j : Fin 2, A i j * ξ i * ξ j ≤ Λ * |ξ i| * |ξ j| := by
        intro i j
        calc
          A i j * ξ i * ξ j ≤ |A i j * ξ i * ξ j| := le_abs_self _
          _ = |A i j| * |ξ i| * |ξ j| := by simp only [abs_mul]
          _ ≤ Λ * |ξ i| * |ξ j| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hentries i j)
              (abs_nonneg _)) (abs_nonneg _)
      have hn : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 := by
        simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq ξ
      have habs0 : |ξ 0| ^ 2 = ξ 0 ^ 2 := sq_abs _
      have habs1 : |ξ 1| ^ 2 = ξ 1 ^ 2 := sq_abs _
      simp only [Fin.sum_univ_two]
      rw [hn]
      have hs := mul_nonneg hΛpos.le (sq_nonneg (|ξ 0| - |ξ 1|))
      nlinarith [hb 0 0, hb 0 1, hb 1 0, hb 1 1]
    exact ⟨hquad, hupper,
      spdSqrt_norm_le A hA (by positivity) hupper,
      spdSqrt_inv_le A hA hκ (by intro ξ; rw [hquad]; exact hcoercive ξ)⟩
  have hheatProvider
      (α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      (∀ K B : NNReal, heatDuhamelConstSchauderConst (V := E2) α K B 1 =
        K * heatDuhamelConstSchauderConst (V := E2) α 1 0 1 +
        B * heatDuhamelConstSchauderConst (V := E2) α 0 1 1) ∧
      ∃ S : NNReal, ∀ u : BoundedContinuousFunction E2 ℝ,
        heatSupSchauderConst (V := E2) 1 u ≤ S * ‖u‖₊ := by
    classical
    constructor
    · intro K B
      calc
        heatDuhamelConstSchauderConst (V := E2) α K B 1 =
            heatDuhamelConstSchauderConst (V := E2) α (K * 1) (K * 0) 1 +
              heatDuhamelConstSchauderConst (V := E2) α (B * 0) (B * 1) 1 := by
          simpa using heatDuhamelConstSchauderConst_add (V := E2) hαone
            (K * 1) (B * 0) (K * 0) (B * 1) (T := 1) (by norm_num)
        _ = _ := by rw [heatDuhamelConstSchauderConst_nnreal_mul,
            heatDuhamelConstSchauderConst_nnreal_mul]
    · let c₁ : NNReal := Real.toNNReal ((heatScale 1)⁻¹ * heatC1 E2)
      let c₂ : NNReal := Real.toNNReal (heatC2 E2)
      let c₃ : NNReal := Real.toNNReal ((heatScale 1)⁻¹ * heatC3 E2)
      let a : ℕ → NNReal := fun j => match j with | 0 => 1 | 1 => c₁ | _ => c₂
      refine ⟨(∑ j ∈ Finset.range 3, a j) +
        ∑ _β : Fin 2 → Fin (Module.finrank ℝ E2), max (2 * c₂) c₃, ?_⟩
      intro u
      have hscalar (c : ℝ) : Real.toNNReal (c * ‖u‖) = Real.toNNReal c * ‖u‖₊ := by
        rw [mul_comm, Real.toNNReal_mul (norm_nonneg u), norm_toNNReal, mul_comm]
      have hjet : ∀ j, heatSupSpatialJetConst (V := E2) 1 u j = a j * ‖u‖₊ := by
        intro j
        rcases j with _ | (_ | j)
        · exact (one_mul ‖u‖₊).symm
        · exact hscalar _
        · change Real.toNNReal (1⁻¹ * heatC2 E2 * ‖u‖) = c₂ * ‖u‖₊
          rw [inv_one, one_mul]
          exact hscalar _
      have hhess : heatD2SupHolderConst (V := E2) 1 u = max (2 * c₂) c₃ * ‖u‖₊ := by
        change max (2 * Real.toNNReal (1⁻¹ * heatC2 E2 * ‖u‖))
          (Real.toNNReal (‖u‖ * 1⁻¹ * (heatScale 1)⁻¹ * heatC3 E2)) = _
        rw [show ‖u‖ * 1⁻¹ * (heatScale 1)⁻¹ * heatC3 E2 =
          ((heatScale 1)⁻¹ * heatC3 E2) * ‖u‖ by ring, inv_one, one_mul,
          hscalar, hscalar]
        simpa only [mul_assoc] using
          (max_mul_of_nonneg (2 * c₂) c₃ (show 0 ≤ ‖u‖₊ from bot_le)).symm
      simp only [heatSupSchauderConst, heatSupHessianHolderConst, hjet, hhess]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← add_mul]
  have hfrozenProvider
      (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
      (α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ C : NNReal, 0 < C ∧ ∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef),
        (∀ ξ : E2, κ * ‖ξ‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j) →
        (∀ i j, |A i j| ≤ Λ) → ∀ K B : NNReal,
          spdLaplacianSchauderDefectConst A hA α K B ≤ C * (K + B) ∧
          ∀ u : BoundedContinuousFunction E2 ℝ,
            spdLaplacianSchauderConst A hA α K B u ≤ C * (K + B + ‖u‖₊) := by
    classical
    obtain ⟨hheat, S, hS⟩ := hheatProvider α hα hαone
    let R : NNReal := max 1 (Real.toNNReal (Real.sqrt κ)⁻¹)
    let Q : NNReal := (Real.toNNReal (Real.sqrt (2 * Λ))) ^ (α : ℝ)
    let D : NNReal := 1 + R + R ^ 2 + R ^ 2 * R ^ (α : ℝ)
    let H : NNReal := Q * heatDuhamelConstSchauderConst (V := E2) α 1 0 1 +
      heatDuhamelConstSchauderConst (V := E2) α 0 1 1
    refine ⟨1 + D * (H + S), by positivity, ?_⟩
    intro A hA hc he K B
    let L := spdSqrtEquiv A hA
    let r : NNReal := max 1 ‖(L.symm : E2 →L[ℝ] E2)‖₊
    let q : NNReal := ‖(L : E2 →L[ℝ] E2)‖₊ ^ (α : ℝ)
    obtain ⟨_, _, hdir, hinv⟩ := hquadraticProvider κ Λ hκ hΛ A hA hc he
    have hr : r ≤ R := by
      apply max_le_max_left
      simpa only [L, norm_toNNReal] using Real.toNNReal_le_toNNReal hinv
    have hq : q ≤ Q := by
      apply NNReal.rpow_le_rpow _ α.coe_nonneg
      simpa only [L, norm_toNNReal] using Real.toNNReal_le_toNNReal hdir
    have hD : 1 + r + r ^ 2 + r ^ 2 * r ^ (α : ℝ) ≤ D := by
      dsimp only [D]
      gcongr
    have hcost : heatDuhamelConstSchauderConst (V := E2) α (K * q) B 1 ≤ H * (K + B) := by
      rw [hheat]
      calc
        K * q * heatDuhamelConstSchauderConst (V := E2) α 1 0 1 +
            B * heatDuhamelConstSchauderConst (V := E2) α 0 1 1 ≤
          K * Q * heatDuhamelConstSchauderConst (V := E2) α 1 0 1 +
            B * heatDuhamelConstSchauderConst (V := E2) α 0 1 1 := by gcongr
        _ = (Q * heatDuhamelConstSchauderConst (V := E2) α 1 0 1) * K +
            heatDuhamelConstSchauderConst (V := E2) α 0 1 1 * B := by ring
        _ ≤ H * K + H * B := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (show 0 ≤ K from bot_le)
          · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (show 0 ≤ B from bot_le)
        _ = H * (K + B) := by ring
    have hscale (C : NNReal) : contDiffHolderLinearEquivConst L α C =
        (1 + r + r ^ 2 + r ^ 2 * r ^ (α : ℝ)) * C := by
      unfold contDiffHolderLinearEquivConst
      change C + r * C + r ^ 2 * C + r ^ 2 * (C * r ^ (α : ℝ)) = _
      ring
    have hHC : D * H ≤ 1 + D * (H + S) :=
      le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (show 0 ≤ D from bot_le))
        (le_add_of_nonneg_left (by positivity))
    have hSC : D * S ≤ 1 + D * (H + S) :=
      le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (show 0 ≤ D from bot_le))
        (le_add_of_nonneg_left (by positivity))
    constructor
    · change contDiffHolderLinearEquivConst L α
        (heatDuhamelConstSchauderConst (V := E2) α (K * q) B 1) ≤ _
      rw [hscale]
      calc
        _ ≤ D * (H * (K + B)) := mul_le_mul hD hcost (by positivity) (by positivity)
        _ = (D * H) * (K + B) := by ring
        _ ≤ (1 + D * (H + S)) * (K + B) := mul_le_mul_of_nonneg_right hHC (by positivity)
    · intro u
      have hnorm : ‖linPullBoundedContinuousFunction L u‖₊ = ‖u‖₊ := by
        exact Subtype.ext (norm_linPullBoundedContinuousFunction L u)
      change contDiffHolderLinearEquivConst L α
        (laplacianSchauderConst α (K * q) B (linPullBoundedContinuousFunction L u)) ≤ _
      rw [hscale, laplacianSchauderConst]
      have hs : heatSupSchauderConst (V := E2) 1 (linPullBoundedContinuousFunction L u) ≤
          S * ‖u‖₊ := by simpa only [hnorm] using hS (linPullBoundedContinuousFunction L u)
      calc
        _ ≤ D * (S * ‖u‖₊ + H * (K + B)) :=
          mul_le_mul hD (add_le_add hs hcost) (by positivity) (by positivity)
        _ = D * S * ‖u‖₊ + D * H * (K + B) := by ring
        _ ≤ (1 + D * (H + S)) * ‖u‖₊ + (1 + D * (H + S)) * (K + B) :=
          add_le_add (mul_le_mul_of_nonneg_right hSC (by positivity)) (mul_le_mul_of_nonneg_right hHC (by positivity))
        _ = (1 + D * (H + S)) * (K + B + ‖u‖₊) := by ring
  have haffineProvider
      (s : ℝ) (hs : 0 < s) (α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ C₁ C₂ Cf : NNReal, ∀ (c : E2) (B : Set E2),
        (∀ z ∈ Metric.ball (0 : E2) 4, affinePull c s z ∈ B) →
        ∀ (a : E2 → PlanarMatrix) (f v : E2 → ℝ) (U K₂ F : NNReal),
        PlanarHolderJetBound 1 v B α U → PlanarHolderJetBound 2 v B α K₂ →
        ScalarHolderBound f B α F → LinearClassicalEquation B a f v →
        PlanarHolderJetBound 1 (affineSolution c s v) (Metric.ball (0 : E2) 4) α (C₁ * U) ∧
        PlanarHolderJetBound 2 (affineSolution c s v) (Metric.ball (0 : E2) 4) α (C₂ * K₂) ∧
        ScalarHolderBound (affineSource c s f) (Metric.ball (0 : E2) 4) α (Cf * F) ∧
        (∀ q : ℕ, q ≤ 2 → ∀ z ∈ Metric.ball (0 : E2) 4, ∀ ξ : Fin q → E2,
          iteratedFDeriv ℝ q (affineSolution c s v) z ξ =
            s ^ q * iteratedFDeriv ℝ q v (affinePull c s z) ξ) ∧
        (∀ z ∈ Metric.ball (0 : E2) 4,
          matrixHessian (affineMatrix c s a) (affineSolution c s v) z =
            s ^ 2 * matrixHessian a v (affinePull c s z)) ∧
        LinearClassicalEquation (Metric.ball (0 : E2) 4)
          (affineMatrix c s a) (affineSource c s f) (affineSolution c s v) := by
    classical
    have hholder (m : ℕ) (hm : m ≤ 2) (B D : Set E2)
        (u : E2 → ℝ) (x₀ : E2) (r α K : NNReal) (hr : 0 < r)
        (hmap : MapsTo (fun y => x₀+(r:ℝ) • y) D B)
        (hu : PlanarHolderJetBound m u B α K) :
        PlanarHolderJetBound m (fun y => u (x₀+(r:ℝ) • y)) D α
          ((1+r+r^2)*(1+r^(α:ℝ))*K) := by
      have hjet (q : ℕ) (x : E2) :
          iteratedFDeriv ℝ q (fun y => u (x₀+(r:ℝ) • y)) x =
            (r:ℝ)^q • iteratedFDeriv ℝ q u (x₀+(r:ℝ) • x) := by
        let g : E2 ≃L[ℝ] E2 :=
          { toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E2 (r:ℝ) (NNReal.coe_pos.mpr hr).ne'
            continuous_toFun := by
              change Continuous (fun z : E2 => (r:ℝ) • z)
              fun_prop
            continuous_invFun := by
              change Continuous (fun z : E2 => (r:ℝ)⁻¹ • z)
              fun_prop }
        have h := g.iteratedFDerivWithin_comp_right (fun z => u (x₀+z))
          uniqueDiffOn_univ (x := x) (Set.mem_univ _) q
        simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at h
        change iteratedFDeriv ℝ q ((fun z => u (x₀+z)) ∘ g) x = _
        rw [h,iteratedFDeriv_comp_add_left]
        ext ξ
        simp [g,ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.map_smul_univ]
      let A : NNReal := (1+r+r^2)*(1+r^(α:ℝ))*K
      have hQ (q : ℕ) (hq : q ≤ m) : (r:ℝ)^q ≤ 1+(r:ℝ)+(r:ℝ)^2 := by
        have hq2 := hq.trans hm
        interval_cases q <;> norm_num <;> nlinarith [r.coe_nonneg,sq_nonneg (r:ℝ)]
      have hcost (q : ℕ) (hq : q ≤ m) : (r:ℝ)^q*(K:ℝ)*(r:ℝ)^(α:ℝ) ≤ (A:ℝ) := by
        simp only [A,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_rpow]
        calc
          _ ≤ (1+(r:ℝ)+(r:ℝ)^2)*(K:ℝ)*(1+(r:ℝ)^(α:ℝ)) := by
            gcongr
            · exact hQ q hq
            · exact le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
          _ = _ := by ring
      have hnormCost (q : ℕ) (hq : q ≤ m) : (r:ℝ)^q*(K:ℝ) ≤ (A:ℝ) := by
        simp only [A,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_one,NNReal.coe_pow,NNReal.coe_rpow]
        calc
          _ ≤ (1+(r:ℝ)+(r:ℝ)^2)*(K:ℝ) := mul_le_mul_of_nonneg_right (hQ q hq) K.coe_nonneg
          _ ≤ ((1+(r:ℝ)+(r:ℝ)^2)*(K:ℝ))*(1+(r:ℝ)^(α:ℝ)) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left
              (show (1:ℝ) ≤ 1+(r:ℝ)^(α:ℝ) from le_add_of_nonneg_right (Real.rpow_nonneg r.coe_nonneg (α:ℝ))) (by positivity : 0 ≤ (1+(r:ℝ)+(r:ℝ)^2)*(K:ℝ))
          _ = _ := by ring
      refine ⟨hu.1.comp (by fun_prop) hmap,fun q hq => ⟨?_,?_⟩⟩
      · intro x hx
        rw [hjet,norm_smul,Real.norm_of_nonneg (pow_nonneg r.coe_nonneg q)]
        exact (mul_le_mul_of_nonneg_left ((hu.2 q hq).1 _ (hmap hx)) (pow_nonneg r.coe_nonneg q)).trans (hnormCost q hq)
      · intro x hx y hy
        have hd : dist (x₀+(r:ℝ) • x) (x₀+(r:ℝ) • y) = (r:ℝ)*dist x y := by
          rw [dist_eq_norm,show x₀+(r:ℝ) • x-(x₀+(r:ℝ) • y) = (r:ℝ) • (x-y) by module]
          rw [norm_smul,Real.norm_of_nonneg r.coe_nonneg,dist_eq_norm]
        have hh := ((hu.2 q hq).2).dist_le (hmap hx) (hmap hy)
        rw [hd,Real.mul_rpow r.coe_nonneg dist_nonneg] at hh
        have hreal : dist (iteratedFDeriv ℝ q (fun y => u (x₀+(r:ℝ) • y)) x)
            (iteratedFDeriv ℝ q (fun y => u (x₀+(r:ℝ) • y)) y) ≤ (A:ℝ)*dist x y^(α:ℝ) := by
          rw [hjet,hjet,dist_eq_norm,← smul_sub,norm_smul,Real.norm_of_nonneg (pow_nonneg r.coe_nonneg q)]
          rw [dist_eq_norm] at hh
          calc
            _ ≤ (r:ℝ)^q*((K:ℝ)*((r:ℝ)^(α:ℝ)*dist x y^(α:ℝ))) := mul_le_mul_of_nonneg_left hh (pow_nonneg r.coe_nonneg q)
            _ = ((r:ℝ)^q*(K:ℝ)*(r:ℝ)^(α:ℝ))*dist x y^(α:ℝ) := by ring
            _ ≤ (A:ℝ)*dist x y^(α:ℝ) := mul_le_mul_of_nonneg_right (hcost q hq) (Real.rpow_nonneg dist_nonneg _)
        simpa only [edist_dist,ENNReal.ofReal_mul A.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hreal
    let r : NNReal := Real.toNNReal s
    have hr : 0 < r := Real.toNNReal_pos.mpr hs
    have hrs : (r : ℝ) = s := Real.coe_toNNReal s hs.le
    let Cost : NNReal := (1+r+r^2)*(1+r^(α:ℝ))
    let Cf : NNReal := r^2*(1+r^(α:ℝ))
    refine ⟨Cost,Cost,Cf,?_⟩
    intro c B hmap a f v U K₂ F hv1 hv2 hf heq
    let u := v
    have hjet (q : ℕ) (x : E2) :
        iteratedFDeriv ℝ q (fun y => u (c+s • y)) x =
          s^q • iteratedFDeriv ℝ q u (c+s • x) := by
      let g : E2 ≃L[ℝ] E2 :=
        { toLinearEquiv := LinearEquiv.smulOfNeZero ℝ E2 s hs.ne'
          continuous_toFun := by
            change Continuous (fun z : E2 => s • z)
            fun_prop
          continuous_invFun := by
            change Continuous (fun z : E2 => s⁻¹ • z)
            fun_prop }
      have h := g.iteratedFDerivWithin_comp_right (fun z => u (c+z))
        uniqueDiffOn_univ (x := x) (Set.mem_univ _) q
      simp only [Set.preimage_univ,iteratedFDerivWithin_univ] at h
      change iteratedFDeriv ℝ q ((fun z => u (c+z)) ∘ g) x = _
      rw [h,iteratedFDeriv_comp_add_left]
      ext ξ
      simp [g,ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.map_smul_univ]
    have hh (y : E2) (i j : Fin 2) :
        planarHessian (fun z => u (c+s • z)) y i j =
          s^2 * planarHessian u (c+s • y) i j := by
      let ξ : Fin 2 → E2 := ![coordinateVector 2 i,coordinateVector 2 j]
      have h := congrArg (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E2) ℝ => L ξ) (hjet 2 y)
      simpa [ContinuousMultilinearMap.smul_apply,smul_eq_mul,iteratedFDeriv_two_apply,
        ξ,planarHessian] using h
    have hPH1 : PlanarHolderJetBound 1 (affineSolution c s v) (Metric.ball (0 : E2) 4) α (Cost*U) := by
      simpa only [affineSolution,Function.comp_def,affinePull,Cost,hrs] using
        hholder 1 (by norm_num) B (Metric.ball (0 : E2) 4) v c r α U hr (by intro z hz; simpa only [hrs,affinePull] using hmap z hz) hv1
    have hPH2 : PlanarHolderJetBound 2 (affineSolution c s v) (Metric.ball (0 : E2) 4) α (Cost*K₂) := by
      simpa only [affineSolution,Function.comp_def,affinePull,Cost,hrs] using
        hholder 2 le_rfl B (Metric.ball (0 : E2) 4) v c r α K₂ hr (by intro z hz; simpa only [hrs,affinePull] using hmap z hz) hv2
    have hsource : ScalarHolderBound (affineSource c s f) (Metric.ball (0 : E2) 4) α (Cf*F) := by
      constructor
      · intro z hz
        simp only [affineSource,Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg s)]
        have hb := hf.1 _ (hmap z hz)
        dsimp only [Cf]
        simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_add,NNReal.coe_one,NNReal.coe_rpow,hrs]
        calc
          s^2*|f (affinePull c s z)| ≤ s^2*(F:ℝ) := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
          _ ≤ s^2*(1+s^(α:ℝ))*(F:ℝ) := by
            gcongr
            exact le_mul_of_one_le_right (sq_nonneg s) (le_add_of_nonneg_right (Real.rpow_nonneg hs.le _))
      · intro x hx y hy
        have hd : dist (affinePull c s x) (affinePull c s y) = s*dist x y := by
          simp only [affinePull,dist_eq_norm]
          rw [show c+s • x-(c+s • y) = s • (x-y) by module,norm_smul,Real.norm_of_nonneg hs.le]
        have hb := hf.2.dist_le (hmap x hx) (hmap y hy)
        rw [hd,Real.mul_rpow hs.le dist_nonneg] at hb
        have hb' : dist (affineSource c s f x) (affineSource c s f y) ≤ ((Cf*F:NNReal):ℝ)*dist x y^(α:ℝ) := by
          simp only [affineSource,Real.dist_eq,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg s)]
          dsimp only [Cf]
          simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_add,NNReal.coe_one,NNReal.coe_rpow,hrs]
          calc
            _ ≤ s^2*((F:ℝ)*(s^(α:ℝ)*dist x y^(α:ℝ))) := mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hb) (sq_nonneg s)
            _ = s^2*s^(α:ℝ)*(F:ℝ)*dist x y^(α:ℝ) := by ring
            _ ≤ s^2*(1+s^(α:ℝ))*(F:ℝ)*dist x y^(α:ℝ) := by
              gcongr
              exact le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
        simpa only [edist_dist,ENNReal.ofReal_mul (Cf*F).coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hb'
    have hm (z : E2) : matrixHessian (affineMatrix c s a) (affineSolution c s v) z =
        s^2*matrixHessian a v (affinePull c s z) := by
      simp only [matrixHessian,affineMatrix,affineSolution,Function.comp_def,affinePull,u] at *
      simp_rw [hh,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    refine ⟨hPH1,hPH2,hsource,?_,fun z _ => hm z,?_⟩
    · intro q _ z _ ξ
      simpa only [affineSolution,Function.comp_def,affinePull,u,ContinuousMultilinearMap.smul_apply,smul_eq_mul] using
        congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin q => E2) ℝ => T ξ) (hjet q z)
    · intro z hz
      rw [hm z]
      exact congrArg (fun b : ℝ => s^2*b) (heq _ (hmap z hz))
  have hscaleProvider
      (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
      (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ s : ℝ, 0 < s ∧ 8 * s < R ∧ ∀ (x₀ : E2) (a : E2 → PlanarMatrix),
        PlanarCoefficientControl a (Metric.ball x₀ (2 * R)) κ Λ H α →
        ∀ c ∈ Metric.ball x₀ R,
          (∀ z ∈ Metric.ball (0 : E2) 4, affinePull c s z ∈ Metric.ball x₀ (2 * R)) ∧
          (∀ i j, HolderOnWith (scaledEntryHolder H α s) α
            (fun z => a (affinePull c s z) i j) (Metric.ball (0 : E2) 2)) ∧
          (∀ i j z, z ∈ Metric.ball (0 : E2) 2 →
            |a (affinePull c s z) i j - a c i j| ≤
              (normalizedEntryOscillation (scaledEntryHolder H α s) α : ℝ)) ∧
          (∀ hA : (a c).PosDef,
            spdLaplacianSchauderDefectConst (a c) hA α
              (4 * (normalizedEntryOscillation (scaledEntryHolder H α s) α +
                scaledEntryHolder H α s))
              (4 * normalizedEntryOscillation (scaledEntryHolder H α s) α) ≤ 1 / 2) := by
    classical
    obtain ⟨C,hC,hcost⟩ := hfrozenProvider κ Λ hκ hΛ α hα hαone
    let g : ℝ → ℝ := fun s => (C:ℝ) *
      (4*((H:ℝ)*|s|^(α:ℝ)*2^(α:ℝ)+(H:ℝ)*|s|^(α:ℝ))+
       4*((H:ℝ)*|s|^(α:ℝ)*2^(α:ℝ)))
    have hg : ContinuousAt g 0 := by
      dsimp [g]
      have hp : ContinuousAt (fun s : ℝ => |s|^(α:ℝ)) 0 :=
        continuous_abs.continuousAt.rpow_const (Or.inr α.coe_nonneg)
      fun_prop
    have hg0 : g 0 = 0 := by
      simp [g,Real.zero_rpow (show (α:ℝ) ≠ 0 from by exact_mod_cast hα.ne')]
    have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), g s < 1/2 := by
      have ht := hg.tendsto.eventually (eventually_lt_nhds (show g 0 < (1/2:ℝ) by rw [hg0]; norm_num))
      exact ht
    obtain ⟨δ,hδ,hδsmall⟩ := Metric.eventually_nhds_iff.mp hsmall
    let s := min δ (R/8) / 2
    have hs : 0 < s := by dsimp [s]; positivity
    have hsδ : s < δ := by have hh := min_le_left δ (R/8);dsimp [s];linarith
    have hsR : 8*s < R := by have hh := min_le_right δ (R/8);dsimp [s];linarith
    refine ⟨s,hs,hsR,?_⟩
    intro x₀ a ha c hc
    have hmap (z : E2) (hz : z ∈ Metric.ball (0:E2) 4) : affinePull c s z ∈ Metric.ball x₀ (2*R) := by
      have hz' : ‖z‖ < 4 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
      have hc' := Metric.mem_ball.mp hc
      rw [Metric.mem_ball]
      calc
        dist (affinePull c s z) x₀ ≤ dist (affinePull c s z) c + dist c x₀ := dist_triangle _ _ _
        _ = s*‖z‖+dist c x₀ := by simp [affinePull,dist_eq_norm,norm_smul,Real.norm_of_nonneg hs.le]
        _ < 2*R := by nlinarith
    have hinner : ∀ z ∈ Metric.ball (0:E2) 2, affinePull c s z ∈ Metric.ball x₀ (2*R) :=
      fun z hz => hmap z (Metric.ball_subset_ball (by norm_num) hz)
    have hholder (i j : Fin 2) : HolderOnWith (scaledEntryHolder H α s) α
        (fun z => a (affinePull c s z) i j) (Metric.ball (0:E2) 2) := by
      intro x hx y hy
      have hd : dist (affinePull c s x) (affinePull c s y) = s*dist x y := by
        simp only [affinePull,dist_eq_norm]
        rw [show c+s • x-(c+s • y) = s • (x-y) by module,norm_smul,Real.norm_of_nonneg hs.le]
      have hb := (ha.holder i j).dist_le (hinner x hx) (hinner y hy)
      rw [hd,Real.mul_rpow hs.le dist_nonneg] at hb
      have hr : dist (a (affinePull c s x) i j) (a (affinePull c s y) i j) ≤
          (scaledEntryHolder H α s : ℝ)*dist x y^(α:ℝ) := by
        simpa only [scaledEntryHolder,NNReal.coe_mul,Real.coe_toNNReal _ (Real.rpow_nonneg hs.le _),mul_assoc] using hb
      simpa only [edist_dist,ENNReal.ofReal_mul (scaledEntryHolder H α s).coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal hr
    refine ⟨hmap,hholder,?_,?_⟩
    · intro i j z hz
      have hb := (hholder i j).dist_le hz (Metric.mem_ball_self (by norm_num))
      have hd : dist z (0:E2) ≤ 2 := (Metric.mem_ball.mp hz).le
      have hp := Real.rpow_le_rpow (dist_nonneg : 0 ≤ dist z (0:E2)) hd α.coe_nonneg
      have hlast := mul_le_mul_of_nonneg_left hp (scaledEntryHolder H α s).coe_nonneg
      simpa only [affinePull,smul_zero,add_zero,Real.dist_eq,normalizedEntryOscillation,
        NNReal.coe_mul,NNReal.coe_rpow,NNReal.coe_ofNat] using hb.trans hlast
    · intro hA
      have hcenter : c ∈ Metric.ball x₀ (2*R) := Metric.ball_subset_ball (by linarith) hc
      have hb := (hcost (a c) hA (ha.coercive c hcenter) (ha.bounded c hcenter)
        (4*(normalizedEntryOscillation (scaledEntryHolder H α s) α+scaledEntryHolder H α s))
        (4*normalizedEntryOscillation (scaledEntryHolder H α s) α)).1
      apply hb.trans
      apply NNReal.coe_le_coe.mp
      have hgs := hδsmall (show dist s 0 < δ by simpa [dist_zero_right,Real.norm_of_nonneg hs.le] using hsδ)
      dsimp only [g] at hgs
      simpa only [NNReal.coe_mul,NNReal.coe_add,NNReal.coe_ofNat,NNReal.coe_div,
        normalizedEntryOscillation,scaledEntryHolder,NNReal.coe_rpow,NNReal.coe_one,
        Real.coe_toNNReal _ (Real.rpow_nonneg hs.le _),abs_of_pos hs] using hgs.le
  have hactualFields
      (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
      (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ Cost : NNReal, 0 < Cost ∧ ∀ (a : E2 → PlanarMatrix) (f v : E2 → ℝ)
        (U F K₂ : NNReal),
        PlanarCoefficientControl a (Metric.ball (0 : E2) 4) κ Λ H α →
        ScalarHolderBound f (Metric.ball (0 : E2) 4) α F →
        PlanarHolderJetBound 1 v (Metric.ball (0 : E2) 4) α U →
        PlanarHolderJetBound 2 v (Metric.ball (0 : E2) 4) α K₂ →
        ∃ Kapp : NNReal, Kapp ≤ Cost * K₂ ∧
          normalizedWitness a f v κ Λ H α U F Cost Kapp := by
    classical
    have hext (R : ℝ) (hR : 0 < R) (α : NNReal) (hα : 0 < α) (hαone : α < 1) :
        ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), m ≤ 2 → ∀ (x₀ : E2) (u : E2 → ℝ) (K : NNReal),
        PlanarHolderJetBound m u (Metric.ball x₀ (2 * R)) α K →
        ∃ (χ : E2 → ℝ) (K' : NNReal),
          χ = (show ContDiffBump x₀ from ⟨R, 3*R/2, hR, by linarith⟩) ∧
          ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) ∧
          (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ Metric.ball x₀ R, χ x = 1) ∧
          (∀ q : ℕ, q ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ q χ x‖ ≤ C / R ^ q) ∧
          (K' : ℝ) ≤ C * (K : ℝ) ∧
          PlanarHolderJetBound m (fun x => χ x * u x) Set.univ α K' := by
      classical
      let χ₀ : ContDiffBump (0 : E2) := ⟨R, 3 * R / 2, hR, by linarith⟩
      have hχ₀ : ContDiff ℝ ∞ (χ₀ : E2 → ℝ) := χ₀.contDiff
      obtain ⟨D, hD0, hD⟩ := χ₀.hasCompactSupport.exists_bound_iteratedFDeriv hχ₀ 3
      let A : NNReal := Real.toNNReal (D + 1)
      have hA : (A : ℝ) = D + 1 := Real.coe_toNNReal _ (by positivity)
      have hAb (j : ℕ) (hj : j ≤ 3) (x : E2) :
          ‖iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x‖ ≤ (A : ℝ) := by
        rw [hA]
        linarith [hD j hj x]
      have hχ₀jetH (j : ℕ) (hj : j ≤ 2) :
          HolderWith (3 * A) α (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) := by
        have hLip : LipschitzWith A (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) := by
          apply lipschitzWith_of_nnnorm_fderiv_le
            (hχ₀.differentiable_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j))
          intro x
          apply NNReal.coe_le_coe.mp
          change ‖fderiv ℝ (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ)) x‖ ≤ (A : ℝ)
          simpa only [norm_fderiv_iteratedFDeriv] using hAb (j+1) (by omega) x
        intro x y
        have hr : dist (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x)
            (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) y) ≤ (3 * A : NNReal) * dist x y ^ (α : ℝ) := by
          by_cases hsmall : dist x y ≤ 1
          · calc
              _ ≤ (A : ℝ) * dist x y := hLip.dist_le_mul x y
              _ ≤ (3 * A : NNReal) * dist x y ^ (α : ℝ) := by
                simp only [NNReal.coe_mul, NNReal.coe_ofNat]
                have hd := Real.self_le_rpow_of_le_one dist_nonneg hsmall
                  (by exact_mod_cast hαone.le)
                exact (mul_le_mul_of_nonneg_left hd A.coe_nonneg).trans (mul_le_mul_of_nonneg_right (by linarith [A.coe_nonneg]) (Real.rpow_nonneg dist_nonneg (α : ℝ)))
          · have hn : dist (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) x)
                (iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) y) ≤ 2 * (A : ℝ) :=
              (dist_le_norm_add_norm _ _).trans (by linarith [hAb j (by omega) x, hAb j (by omega) y])
            have hp : 1 ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow (by linarith) α.coe_nonneg
            simp only [NNReal.coe_mul, NNReal.coe_ofNat]
            nlinarith [A.coe_nonneg]
        simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
      let C : ℝ := (A : ℝ) * (1 + R + R^2 + R^3) + 16 * (A : ℝ) + 1
      have hCpos : 0 < C := by dsimp [C]; positivity
      have h16 : 16 * (A : ℝ) ≤ C := by dsimp [C]; nlinarith [mul_nonneg A.coe_nonneg (show 0 ≤ 1+R+R^2+R^3 by positivity)]
      refine ⟨C, hCpos, ?_⟩
      intro m hm x₀ u K hu
      let χ : E2 → ℝ := fun x => χ₀ (x - x₀)
      have hχsmooth : ContDiff ℝ ∞ χ := hχ₀.comp (contDiff_id.sub contDiff_const)
      have hχid : χ = (show ContDiffBump x₀ from ⟨R, 3 * R / 2, hR, by linarith⟩) := by
        funext x
        simp only [χ, ContDiffBump.apply, χ₀, sub_zero]
      have hχsupp : tsupport χ = Metric.closedBall x₀ (3 * R / 2) := by
        rw [hχid, ContDiffBump.tsupport_eq]
      have hχtr (j : ℕ) (x : E2) : iteratedFDeriv ℝ j χ x =
          iteratedFDeriv ℝ j (χ₀ : E2 → ℝ) (x - x₀) := by
        exact iteratedFDeriv_comp_sub j x₀ x
      have hχb (j : ℕ) (hj : j ≤ 3) (x : E2) : ‖iteratedFDeriv ℝ j χ x‖ ≤ (A : ℝ) := by
        rw [hχtr]
        exact hAb j hj _
      have hχjetH (j : ℕ) (hj : j ≤ 2) : HolderWith (3 * A) α (iteratedFDeriv ℝ j χ) := by
        intro x y
        simpa only [hχtr, edist_sub_right] using hχ₀jetH j hj (x-x₀) (y-x₀)
      let B : Set E2 := Metric.ball x₀ (2 * R)
      have hB : IsOpen B := Metric.isOpen_ball
      have hχoutside (x : E2) (hx : x ∉ B) : χ =ᶠ[𝓝 x] 0 := by
        apply notMem_tsupport_iff_eventuallyEq.mp
        rw [hχsupp]
        exact fun hy => hx (Metric.closedBall_subset_ball (by linarith) hy)
      have hvoutside (x : E2) (hx : x ∉ B) :
          (fun z => χ z * u z) =ᶠ[𝓝 x] 0 := by
        filter_upwards [hχoutside x hx] with z hz
        simp [hz]
      have hvzero (j : ℕ) (x : E2) (hx : x ∉ B) :
          iteratedFDeriv ℝ j (fun z => χ z * u z) x = 0 := by
        simpa only [iteratedFDeriv_zero, Pi.zero_apply] using ((hvoutside x hx).iteratedFDeriv ℝ j).eq_of_nhds
      have hvC2 : ContDiffOn ℝ m (fun z => χ z * u z) Set.univ := by
        intro x _
        apply ContDiffAt.contDiffWithinAt
        by_cases hx : x ∈ B
        · exact ((hχsmooth.of_le (by simp)).contDiffAt).mul (hu.1.contDiffAt (hB.mem_nhds hx))
        · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hvoutside x hx)
      have hmul {t : Set E2} (ht : IsOpen t) {x : E2} (hx : x ∈ t)
          {f g : E2 → ℝ} (hf : ContDiffOn ℝ m f t) (hg : ContDiffOn ℝ m g t)
          {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
          (hfb : ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j f x‖ ≤ A)
          (hgb : ∀ j : ℕ, j ≤ m → ‖iteratedFDeriv ℝ j g x‖ ≤ B)
          (q : ℕ) (hq : q ≤ m) :
          ‖iteratedFDeriv ℝ q (fun z => f z * g z) x‖ ≤ 4 * A * B := by
          have hs := norm_iteratedFDerivWithin_mul_le hf hg ht.uniqueDiffOn hx (n := q)
            (by exact_mod_cast hq)
          simp_rw [iteratedFDerivWithin_of_isOpen _ ht hx] at hs
          apply hs.trans
          have hsum : (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
              ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (q-i) g x‖) ≤
              ∑ i ∈ Finset.range (q+1), (q.choose i : ℝ) * A * B := by
            apply Finset.sum_le_sum
            intro i hi
            have hiq : i ≤ q := by have := Finset.mem_range.mp hi; omega
            gcongr
            · exact hfb i (hiq.trans hq)
            · exact hgb (q-i) ((Nat.sub_le _ _).trans hq)
          apply hsum.trans
          have hq2 : q ≤ 2 := hq.trans hm
          interval_cases q <;> norm_num [Finset.sum_range_succ] <;> nlinarith
    
      let K' : NNReal := Real.toNNReal C * K
      have hK' : (K' : ℝ) = C * (K : ℝ) := by
        simp only [K', NNReal.coe_mul, Real.coe_toNNReal _ hCpos.le]
      refine ⟨χ, K', hχid, hχsmooth, ?_, hχsupp.subset, ?_, ?_, ?_, hK'.le, hvC2, ?_⟩
      · rw [hχid]
        exact ContDiffBump.hasCompactSupport _
      · intro x
        exact ⟨χ₀.nonneg, χ₀.le_one⟩
      · intro x hx
        rw [hχid]
        exact ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hx)
      · intro q hq x
        have hb := hχb q hq x
        have hp : R ^ q ≤ 1 + R + R^2 + R^3 := by
          interval_cases q <;> norm_num <;> nlinarith [pow_nonneg hR.le 3, sq_nonneg R]
        apply (le_div_iff₀ (pow_pos hR q)).mpr
        calc
          _ ≤ (A : ℝ) * R ^ q := mul_le_mul_of_nonneg_right hb (pow_pos hR q).le
          _ ≤ (A : ℝ) * (1 + R + R^2 + R^3) := mul_le_mul_of_nonneg_left hp A.coe_nonneg
          _ ≤ C := by dsimp [C]; nlinarith [A.coe_nonneg]
      intro q hq
      constructor
      · intro x _
        rw [hK']
        by_cases hx : x ∈ B
        · exact (hmul hB hx ((hχsmooth.of_le (by simp)).contDiffOn) hu.1
            A.coe_nonneg K.coe_nonneg (fun j hj => hχb j (by omega) x)
            (fun j hj => (hu.2 j hj).1 x hx) q hq).trans
            (mul_le_mul_of_nonneg_right (by linarith : 4 * (A : ℝ) ≤ C) K.coe_nonneg)
        · rw [hvzero q x hx, norm_zero]
          positivity
      · intro x _ y _
        have hχzero (j : ℕ) (z : E2) (hz : z ∉ B) : iteratedFDeriv ℝ j χ z = 0 := by
          simpa only [iteratedFDeriv_zero, Pi.zero_apply] using
            ((hχoutside z hz).iteratedFDeriv ℝ j).eq_of_nhds
        have hgeneral (x y : E2) (hx : x ∈ B) :
            ‖iteratedFDeriv ℝ q (fun z => χ z * u z) x -
              iteratedFDeriv ℝ q (fun z => χ z * u z) y‖ ≤
              16 * (A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ) := by
          let T : Set E2 := (fun z => z+x) ⁻¹' B ∩ (fun z => z+y) ⁻¹' B
          have hT : IsOpen T := (hB.preimage (continuous_id.add continuous_const)).inter
            (hB.preimage (continuous_id.add continuous_const))
          have hχx : ContDiffOn ℝ m (fun z => χ (z+x)) T :=
            ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
          have hχy : ContDiffOn ℝ m (fun z => χ (z+y)) T :=
            ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
          have hχxq : ContDiffAt ℝ q (fun z => χ (z+x)) 0 :=
            (((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
              (by simp)).contDiffAt : ContDiffAt ℝ q (fun z => χ (z+x)) 0)
          have hχyq : ContDiffAt ℝ q (fun z => χ (z+y)) 0 :=
            (((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
              (by simp)).contDiffAt : ContDiffAt ℝ q (fun z => χ (z+y)) 0)
          have hχdiff (j : ℕ) (hj : j ≤ 2) :
              ‖iteratedFDeriv ℝ j (fun z => χ (z+x) - χ (z+y)) 0‖ ≤
                3 * (A : ℝ) * dist x y ^ (α : ℝ) := by
            have hc := (hχjetH j hj).dist_le x y
            rw [dist_eq_norm] at hc
            rw [fun_iteratedFDeriv_sub_apply (f := fun z => χ (z+x)) (g := fun z => χ (z+y))
              ((((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
                (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt) :
                ContDiffAt ℝ j (fun z => χ (z+x)) 0)
              ((((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le
                (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt) :
                ContDiffAt ℝ j (fun z => χ (z+y)) 0),
              iteratedFDeriv_comp_add_right, iteratedFDeriv_comp_add_right, zero_add, zero_add]
            simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using hc
          have htransprod (z : E2) :
              iteratedFDeriv ℝ q (fun w => χ (w+z) * u (w+z)) 0 =
                iteratedFDeriv ℝ q (fun w => χ w * u w) z := by
            simpa only [zero_add] using
              (iteratedFDeriv_comp_add_right (f := fun w => χ w * u w) q z (0 : E2))
          by_cases hy : y ∈ B
          · have hT0 : (0 : E2) ∈ T := by simpa only [T, Set.mem_inter_iff, Set.mem_preimage, zero_add] using And.intro hx hy
            have hux : ContDiffOn ℝ m (fun z => u (z+x)) T := hu.1.comp
              (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.1)
            have huy : ContDiffOn ℝ m (fun z => u (z+y)) T := hu.1.comp
              (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.2)
            have huxb (j : ℕ) (hj : j ≤ m) : ‖iteratedFDeriv ℝ j (fun z => u (z+x)) 0‖ ≤ (K : ℝ) := by
              simpa only [iteratedFDeriv_comp_add_right, zero_add] using (hu.2 j hj).1 x hx
            have huyχb (j : ℕ) (hj : j ≤ m) : ‖iteratedFDeriv ℝ j (fun z => χ (z+y)) 0‖ ≤ (A : ℝ) := by
              simpa only [iteratedFDeriv_comp_add_right, zero_add] using hχb j (by omega) y
            have hudiff (j : ℕ) (hj : j ≤ m) :
                ‖iteratedFDeriv ℝ j (fun z => u (z+x) - u (z+y)) 0‖ ≤
                  (K : ℝ) * dist x y ^ (α : ℝ) := by
              have hc := ((hu.2 j hj).2).dist_le hx hy
              rw [dist_eq_norm] at hc
              simpa only [fun_iteratedFDeriv_sub_apply
                ((hux.of_le (by exact_mod_cast hj)).contDiffAt (hT.mem_nhds hT0))
                ((huy.of_le (by exact_mod_cast hj)).contDiffAt (hT.mem_nhds hT0)),
                iteratedFDeriv_comp_add_right, zero_add] using hc
            have hb1 := hmul hT hT0 (hχx.sub hχy) hux
              (by positivity : 0 ≤ 3 * (A : ℝ) * dist x y ^ (α : ℝ)) K.coe_nonneg
              (fun j hj => hχdiff j (hj.trans hm)) huxb q hq
            have hb2 := hmul hT hT0 hχy (hux.sub huy) A.coe_nonneg
              (by positivity : 0 ≤ (K : ℝ) * dist x y ^ (α : ℝ))
              huyχb hudiff q hq
            have hvxq : ContDiffAt ℝ q (fun z => χ (z+x) * u (z+x)) 0 :=
              ((hχx.mul hux).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0)
            have hvyq : ContDiffAt ℝ q (fun z => χ (z+y) * u (z+y)) 0 :=
              ((hχy.mul huy).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0)
            have he : (fun z => χ (z+x) * u (z+x) - χ (z+y) * u (z+y)) =
                (fun z => (χ (z+x) - χ (z+y)) * u (z+x) + χ (z+y) * (u (z+x) - u (z+y))) := by
              funext z
              ring
            have hd := congrArg (fun f : E2 → ℝ => iteratedFDeriv ℝ q f 0) he
            rw [fun_iteratedFDeriv_sub_apply hvxq hvyq,
              fun_iteratedFDeriv_add_apply
                ((((hχx.sub hχy).mul hux).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0))
                (((hχy.mul (hux.sub huy)).of_le (by exact_mod_cast hq)).contDiffAt (hT.mem_nhds hT0))] at hd
            rw [htransprod x, htransprod y] at hd
            rw [hd]
            exact (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans_eq (by ring))
          · let S : Set E2 := (fun z => z+x) ⁻¹' B
            have hS : IsOpen S := hB.preimage (continuous_id.add continuous_const)
            have hS0 : (0 : E2) ∈ S := by simpa only [S, Set.mem_preimage, zero_add] using hx
            have hsχ : ContDiffOn ℝ m (fun z => χ (z+x)) S :=
              ((hχsmooth.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffOn
            have hsu : ContDiffOn ℝ m (fun z => u (z+x)) S := hu.1.comp
              (contDiffOn_id.add contDiffOn_const) (fun z hz => hz)
            have hsb (j : ℕ) (hj : j ≤ 2) : ‖iteratedFDeriv ℝ j (fun z => χ (z+x)) 0‖ ≤
                3 * (A : ℝ) * dist x y ^ (α : ℝ) := by
              have hc := (hχjetH j hj).dist_le x y
              rw [dist_eq_norm, hχzero j y hy, sub_zero] at hc
              simpa only [iteratedFDeriv_comp_add_right, zero_add, NNReal.coe_mul, NNReal.coe_ofNat] using hc
            have hb := hmul hS hS0 hsχ hsu
              (by positivity : 0 ≤ 3 * (A : ℝ) * dist x y ^ (α : ℝ)) K.coe_nonneg (fun j hj => hsb j (hj.trans hm))
              (fun j hj => by simpa only [iteratedFDeriv_comp_add_right, zero_add] using (hu.2 j hj).1 x hx) q hq
            rw [hvzero q y hy, sub_zero]
            rw [htransprod x] at hb
            apply hb.trans
            calc
              _ = 12 * ((A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ)) := by ring
              _ ≤ 16 * ((A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ)) :=
                mul_le_mul_of_nonneg_right (by norm_num)
                  (mul_nonneg (mul_nonneg A.coe_nonneg K.coe_nonneg) (Real.rpow_nonneg dist_nonneg _))
              _ = _ := by ring
        have hr : dist (iteratedFDeriv ℝ q (fun z => χ z * u z) x)
            (iteratedFDeriv ℝ q (fun z => χ z * u z) y) ≤ (K' : ℝ) * dist x y ^ (α : ℝ) := by
          rw [dist_eq_norm, hK']
          have hcost : 16 * (A : ℝ) * (K : ℝ) * dist x y ^ (α : ℝ) ≤
              C * (K : ℝ) * dist x y ^ (α : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h16 K.coe_nonneg)
              (Real.rpow_nonneg dist_nonneg _)
          by_cases hx : x ∈ B
          · exact (hgeneral x y hx).trans hcost
          · by_cases hy : y ∈ B
            · rw [norm_sub_rev, dist_comm x y]
              exact (hgeneral y x hy).trans (by simpa only [dist_comm] using hcost)
            · rw [hvzero q x hx, hvzero q y hy, sub_self, norm_zero]
              positivity
        simpa only [edist_dist, ENNReal.ofReal_mul K'.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    
    
    
    have hprod (B : Set E2) (p f : E2 → ℝ) (α A M : NNReal)
        (hp : ScalarHolderBound p univ α A) (hf : ScalarHolderBound f B α M)
        (hz : ∀ x, x ∉ B → p x = 0) :
        ScalarHolderBound (fun x => p x * f x) univ α (2*A*M) := by
      constructor
      · intro x hx
        by_cases hxB : x ∈ B
        · have hb := mul_le_mul (hp.1 x (mem_univ x)) (hf.1 x hxB) (abs_nonneg _) A.coe_nonneg
          rw [abs_mul]
          simp only [NNReal.coe_mul, NNReal.coe_ofNat]
          exact hb.trans (by nlinarith [A.coe_nonneg,M.coe_nonneg])
        · simp only [hz x hxB, zero_mul, abs_zero]
          positivity
      · intro x hx y hy
        have hr : dist (p x*f x) (p y*f y) ≤ (2*A*M : NNReal)*dist x y^(α:ℝ) := by
          by_cases hxB : x ∈ B
          · by_cases hyB : y ∈ B
            · rw [Real.dist_eq]
              have he : p x*f x-p y*f y = (p x-p y)*f x+p y*(f x-f y) := by ring
              rw [he]
              have hc1 := hp.2.dist_le (mem_univ x) (mem_univ y)
              have hc2 := hf.2.dist_le hxB hyB
              rw [Real.dist_eq] at hc1 hc2
              calc
                _ ≤ |p x-p y| *|f x| +|p y| *|f x-f y| := by simpa only [abs_mul] using abs_add_le ((p x-p y)*f x) (p y*(f x-f y))
                _ ≤ ((A:ℝ)*dist x y^(α:ℝ))*(M:ℝ)+(A:ℝ)*((M:ℝ)*dist x y^(α:ℝ)) :=
                  add_le_add (mul_le_mul hc1 (hf.1 x hxB) (abs_nonneg _) (by positivity))
                    (mul_le_mul (hp.1 y (mem_univ y)) hc2 (abs_nonneg _) (by positivity))
                _ = _ := by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; ring
            · rw [hz y hyB,zero_mul,dist_zero_right,Real.norm_eq_abs,abs_mul]
              have hc := hp.2.dist_le (mem_univ x) (mem_univ y)
              rw [hz y hyB, dist_zero_right, Real.norm_eq_abs] at hc
              exact (mul_le_mul hc (hf.1 x hxB) (abs_nonneg _) (by positivity)).trans
                (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; nlinarith [mul_nonneg (mul_nonneg A.coe_nonneg M.coe_nonneg) (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) (α:ℝ))])
          · by_cases hyB : y ∈ B
            · rw [hz x hxB,zero_mul,dist_zero_left,Real.norm_eq_abs,abs_mul]
              have hc := hp.2.dist_le (mem_univ x) (mem_univ y)
              rw [hz x hxB,dist_zero_left,Real.norm_eq_abs] at hc
              exact (mul_le_mul hc (hf.1 y hyB) (abs_nonneg _) (by positivity)).trans
                (by simp only [NNReal.coe_mul,NNReal.coe_ofNat]; nlinarith [mul_nonneg (mul_nonneg A.coe_nonneg M.coe_nonneg) (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x y) (α:ℝ))])
            · simp only [hz x hxB,hz y hyB,zero_mul,dist_self]
              positivity
        simpa only [edist_dist,ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
    have hfields (v : E2 → ℝ) (α U K : NNReal) (hl : PlanarHolderJetBound 1 v univ α U)
        (hv : PlanarHolderJetBound 2 v univ α K) :
        ∃ (u : BoundedContinuousFunction E2 ℝ)
          (du : BoundedContinuousFunction E2 (E2 →L[ℝ] ℝ))
          (d2u : BoundedContinuousFunction E2 (E2 →L[ℝ] E2 →L[ℝ] ℝ)),
          (∀ x, u x = v x) ∧ (∀ x, du x = fderiv ℝ v x) ∧
          (∀ x, d2u x = fderiv ℝ (fderiv ℝ v) x) ∧
          (∀ x, HasFDerivAt (u : E2 → ℝ) (du x) x) ∧
          (∀ x, HasFDerivAt (du : E2 → E2 →L[ℝ] ℝ) (d2u x) x) ∧
          ‖u‖ ≤ (U : ℝ) ∧ ‖du‖ ≤ (U : ℝ) ∧ ‖d2u‖ ≤ (K : ℝ) ∧
          HolderWith U α (u : E2 → ℝ) ∧ HolderWith U α (du : E2 → E2 →L[ℝ] ℝ) ∧
          HolderWith K α (d2u : E2 → E2 →L[ℝ] E2 →L[ℝ] ℝ) := by
      have hvC : ContDiff ℝ 2 v := contDiffOn_univ.mp hv.1
      have hdC : ContDiff ℝ 1 (fderiv ℝ v) := hvC.fderiv_right (by norm_num)
      have hd2C : Continuous (fderiv ℝ (fderiv ℝ v)) := hdC.continuous_fderiv (by norm_num)
      have h0b (x : E2) : ‖v x‖ ≤ (U : ℝ) := by
        simpa only [norm_iteratedFDeriv_zero] using (hl.2 0 (by omega)).1 x (mem_univ x)
      have h1b (x : E2) : ‖fderiv ℝ v x‖ ≤ (U : ℝ) := by
        simpa only [norm_iteratedFDeriv_one] using (hl.2 1 (by omega)).1 x (mem_univ x)
      let S := (continuousMultilinearCurryFin1 ℝ E2 (E2 →L[ℝ] ℝ)).symm.trans
        (continuousMultilinearCurryRightEquiv' ℝ 1 E2 ℝ).symm
      have hS (x : E2) : iteratedFDeriv ℝ 2 v x = S (fderiv ℝ (fderiv ℝ v) x) := by
        ext ξ
        rw [iteratedFDeriv_two_apply]
        simp [S, Fin.init]
      have h2b (x : E2) : ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ (K : ℝ) := by
        simpa only [hS, LinearIsometryEquiv.norm_map] using (hv.2 2 (by omega)).1 x (mem_univ x)
      let u := BoundedContinuousFunction.ofNormedAddCommGroup v hvC.continuous (U : ℝ) h0b
      let du := BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ v) hdC.continuous (U : ℝ) h1b
      let d2u := BoundedContinuousFunction.ofNormedAddCommGroup (fderiv ℝ (fderiv ℝ v)) hd2C (K : ℝ) h2b
      refine ⟨u, du, d2u, fun _ => rfl, fun _ => rfl, fun _ => rfl,
        fun x => (hvC.differentiable (by norm_num) x).hasFDerivAt,
        fun x => (hdC.differentiable (by norm_num) x).hasFDerivAt,
        BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ U.coe_nonneg h0b,
        BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ U.coe_nonneg h1b,
        BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ K.coe_nonneg h2b, ?_, ?_, ?_⟩
      · intro x y
        change edist (v x) (v y) ≤ _
        have hc := (hl.2 0 (by omega)).2 x (mem_univ x) y (mem_univ y)
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq] using hc
      · let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
        have hL (x : E2) : iteratedFDeriv ℝ 1 v x = L (fderiv ℝ v x) := by
          ext ξ
          simp [L, iteratedFDeriv_one_apply]
        intro x y
        change edist (fderiv ℝ v x) (fderiv ℝ v y) ≤ _
        simpa only [hL, L.isometry.edist_eq] using (hl.2 1 (by omega)).2 x (mem_univ x) y (mem_univ y)
      · intro x y
        change edist (fderiv ℝ (fderiv ℝ v) x) (fderiv ℝ (fderiv ℝ v) y) ≤ _
        simpa only [hS, S.isometry.edist_eq] using (hv.2 2 (by omega)).2 x (mem_univ x) y (mem_univ y)
    have hglobal
        (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
        (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
        ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : E2) (a : E2 → PlanarMatrix),
          PlanarCoefficientControl a (Metric.ball x₀ (2 * R)) κ Λ H α →
          ∃ (χ : E2 → ℝ) (H' : NNReal),
            ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
            tsupport χ ⊆ Metric.closedBall x₀ (3 * R / 2) ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ Metric.ball x₀ R, χ x = 1) ∧
            (H' : ℝ) ≤ C * (Λ + (H : ℝ)) ∧
            PlanarCoefficientControl (cutoffMatrix χ a (a x₀)) Set.univ κ Λ H' α ∧
            (∀ x ∈ Metric.ball x₀ R, cutoffMatrix χ a (a x₀) x = a x) := by
      classical
      let χ₀ : ContDiffBump (0 : E2) := ⟨R, 3 * R / 2, hR, by linarith⟩
      have hχ₀ : ContDiff ℝ ∞ (χ₀ : E2 → ℝ) := χ₀.contDiff
      obtain ⟨D, hD⟩ := (isCompact_closedBall (0 : E2) (3 * R / 2)).exists_bound_of_continuousOn
        (hχ₀.continuous_fderiv (by simp)).continuousOn
      let L : NNReal := Real.toNNReal D
      have hderbound (x : E2) : ‖fderiv ℝ (χ₀ : E2 → ℝ) x‖₊ ≤ L := by
        apply NNReal.coe_le_coe.mp
        by_cases hx : x ∈ Metric.closedBall (0 : E2) (3 * R / 2)
        · exact (hD x hx).trans (Real.le_coe_toNNReal _)
        · have hz : fderiv ℝ (χ₀ : E2 → ℝ) x = 0 := by
            apply fderiv_of_notMem_tsupport
            simpa only [χ₀.tsupport_eq] using hx
          simp only [hz, nnnorm_zero, NNReal.coe_zero]
          exact L.coe_nonneg
      have hχLip : LipschitzWith L (χ₀ : E2 → ℝ) :=
        lipschitzWith_of_nnnorm_fderiv_le (hχ₀.differentiable (by simp)) hderbound
      let Aχ := L + 2
      have hχH : HolderWith Aχ α (χ₀ : E2 → ℝ) := by
        intro x y
        have hr : dist (χ₀ x) (χ₀ y) ≤ (Aχ : ℝ) * dist x y ^ (α : ℝ) := by
          by_cases hsmall : dist x y ≤ 1
          · exact (hχLip.dist_le_mul x y).trans
              (mul_le_mul ((le_add_of_nonneg_right (show (0 : ℝ) ≤ 2 by norm_num)))
                (Real.self_le_rpow_of_le_one dist_nonneg hsmall (by exact_mod_cast hαone.le))
                dist_nonneg (by dsimp [Aχ]; positivity))
          · have hdiff : dist (χ₀ x) (χ₀ y) ≤ 2 := by
              rw [Real.dist_eq]
              exact (abs_sub _ _).trans (by rw [abs_of_nonneg χ₀.nonneg, abs_of_nonneg χ₀.nonneg]; linarith [χ₀.le_one (x := x), χ₀.le_one (x := y)])
            have hrpow : 1 ≤ dist x y ^ (α : ℝ) := Real.one_le_rpow (by linarith) α.coe_nonneg
            exact hdiff.trans (by dsimp [Aχ]; nlinarith [L.coe_nonneg])
        simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
      refine ⟨2 * (Aχ : ℝ) + 1, by positivity, ?_⟩
      intro x₀ a ha
      let χ : E2 → ℝ := fun x => χ₀ (x - x₀)
      have hχsmooth : ContDiff ℝ ∞ χ := hχ₀.comp (contDiff_id.sub contDiff_const)
      have hχid : χ = (show ContDiffBump x₀ from ⟨R, 3 * R / 2, hR, by linarith⟩) := by
        funext x
        simp only [χ, ContDiffBump.apply, χ₀, sub_zero]
      have hχsupp : tsupport χ = Metric.closedBall x₀ (3 * R / 2) := by
        rw [hχid, ContDiffBump.tsupport_eq]
      have hχrange (x : E2) : 0 ≤ χ x ∧ χ x ≤ 1 := ⟨χ₀.nonneg, χ₀.le_one⟩
      have hχone (x : E2) (hx : x ∈ Metric.ball x₀ R) : χ x = 1 := by
        rw [hχid]
        exact ContDiffBump.one_of_mem_closedBall _ (Metric.ball_subset_closedBall hx)
      have hχHolder : HolderWith Aχ α χ := by
        intro x y
        have h := hχH (x - x₀) (y - x₀)
        simpa only [χ, edist_sub_right] using h
      have hχzero (x : E2) (hx : x ∉ Metric.ball x₀ (2 * R)) : χ x = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        rw [hχsupp]
        exact fun hy => hx (Metric.closedBall_subset_ball (by linarith) hy)
      have hΛ0 : 0 < Λ := hκ.trans_le hΛ
      let H' : NNReal := H + 2 * Real.toNNReal Λ * Aχ
      have hH' : (H' : ℝ) ≤ (2 * (Aχ : ℝ) + 1) * (Λ + (H : ℝ)) := by
        simp only [H', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal Λ hΛ0.le]
        nlinarith [H.coe_nonneg, Aχ.coe_nonneg]
      refine ⟨χ, H', hχsmooth, ?_, hχsupp.subset, hχrange, hχone, hH', ?_, ?_⟩
      · rw [hχid]
        exact ContDiffBump.hasCompactSupport _
      · constructor
        · intro x hx i j
          by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
          · simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
            rw [ha.symmetric x hxB i j, ha.symmetric x₀ (Metric.mem_ball_self (by linarith)) i j]
          · simp only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul]
            exact ha.symmetric x₀ (Metric.mem_ball_self (by linarith)) i j
        · intro x hx ξ
          by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
          · have h1 := ha.coercive x hxB ξ
            have h0 := ha.coercive x₀ (Metric.mem_ball_self (by linarith)) ξ
            have hχ := hχrange x
            have he : (∑ i : Fin 2, ∑ j : Fin 2, cutoffMatrix χ a (a x₀) x i j * ξ i * ξ j) =
                χ x * (∑ i : Fin 2, ∑ j : Fin 2, a x i j * ξ i * ξ j) +
                (1 - χ x) * (∑ i : Fin 2, ∑ j : Fin 2, a x₀ i j * ξ i * ξ j) := by
              simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
              ring
            rw [he]
            nlinarith [mul_le_mul_of_nonneg_left h1 hχ.1,
              mul_le_mul_of_nonneg_left h0 (by linarith : 0 ≤ 1 - χ x)]
          · simpa only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul] using
              ha.coercive x₀ (Metric.mem_ball_self (by linarith)) ξ
        · intro x hx i j
          by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
          · have hχ := hχrange x
            simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
            calc
              |χ x * a x i j + (1 - χ x) * a x₀ i j| ≤
                  χ x * |a x i j| + (1 - χ x) * |a x₀ i j| := by
                simpa only [abs_mul, abs_of_nonneg hχ.1, abs_of_nonneg (by linarith : 0 ≤ 1 - χ x)] using abs_add_le (χ x * a x i j) ((1 - χ x) * a x₀ i j)
              _ ≤ χ x * Λ + (1 - χ x) * Λ := add_le_add
                (mul_le_mul_of_nonneg_left (ha.bounded x hxB i j) hχ.1)
                (mul_le_mul_of_nonneg_left (ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j) (by linarith))
              _ = Λ := by ring
          · simpa only [cutoffMatrix, hχzero x hxB, zero_smul, zero_add, sub_zero, one_smul] using
              ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j
        · intro i j x hx y hy
          have hdist : dist (cutoffMatrix χ a (a x₀) x i j) (cutoffMatrix χ a (a x₀) y i j) ≤
              (H' : ℝ) * dist x y ^ (α : ℝ) := by
            have hzero := hχzero
            have hfreeze : |a x₀ i j| ≤ Λ := ha.bounded x₀ (Metric.mem_ball_self (by linarith)) i j
            have hbd (z : E2) (hz : z ∈ Metric.ball x₀ (2 * R)) : |a z i j - a x₀ i j| ≤ 2 * Λ :=
              (abs_sub _ _).trans (by linarith [ha.bounded z hz i j])
            have hgeneral (x y : E2) (hxB : x ∈ Metric.ball x₀ (2 * R)) :
                |cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j| ≤
                  ((H : ℝ) + 2 * Λ * (Aχ : ℝ)) * dist x y ^ (α : ℝ) := by
              by_cases hyB : y ∈ Metric.ball x₀ (2 * R)
              · have hc := hχHolder.dist_le x y
                have hh := (ha.holder i j).dist_le hxB hyB
                have he : cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j =
                    χ x * (a x i j - a y i j) + (χ x - χ y) * (a y i j - a x₀ i j) := by
                  simp only [cutoffMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
                  ring
                rw [he]
                have hχ := hχrange x
                calc
                  _ ≤ |χ x| * |a x i j - a y i j| + |χ x - χ y| * |a y i j - a x₀ i j| := by simpa only [abs_mul] using abs_add_le (χ x * (a x i j - a y i j)) ((χ x - χ y) * (a y i j - a x₀ i j))
                  _ ≤ (H : ℝ) * dist x y ^ (α : ℝ) + (Aχ : ℝ) * dist x y ^ (α : ℝ) * (2 * Λ) := by
                    apply add_le_add
                    · have hh' : |a x i j - a y i j| ≤ (H : ℝ) * dist x y ^ (α : ℝ) := by simpa only [Real.dist_eq] using hh
                      rw [abs_of_nonneg hχ.1]
                      exact (mul_le_mul hχ.2 hh' (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
                    · exact mul_le_mul (by simpa only [Real.dist_eq] using hc) (hbd y hyB) (abs_nonneg _) (by positivity)
                  _ = _ := by ring
              · have hc := hχHolder.dist_le x y
                rw [hzero y hyB] at hc
                simp only [Real.dist_eq, sub_zero, abs_of_nonneg (hχrange x).1] at hc
                have he : cutoffMatrix χ a (a x₀) x i j - cutoffMatrix χ a (a x₀) y i j =
                    χ x * (a x i j - a x₀ i j) := by
                  simp only [cutoffMatrix, hzero y hyB, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
                  ring
                rw [he, abs_mul, abs_of_nonneg (hχrange x).1]
                have hm := mul_le_mul hc (hbd x hxB) (abs_nonneg _) (mul_nonneg Aχ.coe_nonneg (Real.rpow_nonneg dist_nonneg _))
                exact hm.trans (by
                  have hnn := mul_nonneg H.coe_nonneg (Real.rpow_nonneg (show 0 ≤ dist x y from dist_nonneg) (α : ℝ))
                  nlinarith)
            have hcast : (H' : ℝ) = (H : ℝ) + 2 * Λ * (Aχ : ℝ) := by
              simp only [H', NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal Λ hΛ0.le]
            rw [hcast, Real.dist_eq]
            by_cases hxB : x ∈ Metric.ball x₀ (2 * R)
            · exact hgeneral x y hxB
            · by_cases hyB : y ∈ Metric.ball x₀ (2 * R)
              · simpa only [abs_sub_comm, dist_comm] using hgeneral y x hyB
              · simp only [cutoffMatrix, hzero x hxB, hzero y hyB, zero_smul, zero_add, sub_zero, one_smul, sub_self, abs_zero]
                positivity
          simpa only [edist_dist, ENNReal.ofReal_mul H'.coe_nonneg,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
            ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hdist
      · intro x hx
        simp only [cutoffMatrix, hχone x hx, one_smul, sub_self, zero_smul, add_zero]
    obtain ⟨Cs,hCs,hCsdata⟩ := hext 2 (by norm_num) α hα hαone
    obtain ⟨Cg,hCg,hCgdata⟩ := hglobal κ Λ 2 hκ hΛ (by norm_num) H α hα hαone
    norm_num only at hCsdata hCgdata
    let CsN := Real.toNNReal Cs
    let CgN := Real.toNNReal Cg
    let A : NNReal := CsN+2
    let Cost : NNReal := CsN+CgN+2*A+1
    have hCost : 0 < Cost := by dsimp [Cost]; positivity
    have hCsN : CsN ≤ Cost := by dsimp [Cost];exact le_add_right (le_add_right (le_add_right le_rfl))
    have hCgN : CgN ≤ Cost := by dsimp [Cost];exact le_add_right (le_add_right (le_add_left le_rfl))
    have h2A : 2*A ≤ Cost := by dsimp [Cost];exact le_add_right (le_add_left le_rfl)
    have hCsCost : Cs ≤ (Cost:ℝ) := by
      have hh : (CsN:ℝ) ≤ (Cost:ℝ) := by exact_mod_cast hCsN
      simpa only [CsN,Real.coe_toNNReal Cs hCs.le] using hh
    have hCgCost : Cg ≤ (Cost:ℝ) := by
      have hh : (CgN:ℝ) ≤ (Cost:ℝ) := by exact_mod_cast hCgN
      simpa only [CgN,Real.coe_toNNReal Cg hCg.le] using hh
    refine ⟨Cost,hCost,?_⟩
    intro a f v U F K₂ ha hf hv1 hv2
    obtain ⟨χ,K₁,hχid,hχsmooth,hχcompact,hχsupp,hχrange,hχone,hχder,hK₁,hPH1⟩ := hCsdata 1 (by norm_num) 0 v U hv1
    obtain ⟨χ₂,Kapp,hχ₂id,_,_,_,_,_,_,hKapp,hPH2⟩ := hCsdata 2 le_rfl 0 v K₂ hv2
    have hχeq : χ₂ = χ := hχ₂id.trans hχid.symm
    rw [hχeq] at hPH2
    have hK₁Cost : K₁ ≤ Cost*U := by
      apply NNReal.coe_le_coe.mp
      exact hK₁.trans (mul_le_mul_of_nonneg_right
        hCsCost U.coe_nonneg)
    have hKappCost : Kapp ≤ Cost*K₂ := by
      apply NNReal.coe_le_coe.mp
      exact hKapp.trans (mul_le_mul_of_nonneg_right
        hCsCost K₂.coe_nonneg)
    have hPH1Cost : PlanarHolderJetBound 1 (fun x => χ x*v x) univ α (Cost*U) :=
      ⟨hPH1.1,fun q hq => ⟨fun x hx => ((hPH1.2 q hq).1 x hx).trans (by exact_mod_cast hK₁Cost),
        ((hPH1.2 q hq).2).mono_const hK₁Cost⟩⟩
    have hχzero (x : E2) (hx : x ∉ Metric.ball (0:E2) 4) : χ x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun ht => hx ((Metric.closedBall_subset_ball (show (3:ℝ) < 4 by norm_num)) (by simpa using hχsupp ht))
    have hχLip : LipschitzWith CsN χ := by
      apply lipschitzWith_of_nnnorm_fderiv_le (hχsmooth.differentiable (by simp))
      intro x
      apply NNReal.coe_le_coe.mp
      have hn := hχder 1 (by norm_num) x
      simp only [norm_iteratedFDeriv_one,pow_one] at hn
      exact hn.trans (by change Cs/2 ≤ (Real.toNNReal Cs:ℝ);rw [Real.coe_toNNReal Cs hCs.le];linarith)
    have hχSH : ScalarHolderBound χ univ α A := by
      constructor
      · intro x _
        rw [abs_of_nonneg (hχrange x).1]
        exact (hχrange x).2.trans (by change 1 ≤ (CsN:ℝ)+2;linarith [CsN.coe_nonneg])
      · intro x _ y _
        have hb : dist (χ x) (χ y) ≤ (A:ℝ)*dist x y^(α:ℝ) := by
          by_cases hd : dist x y ≤ 1
          · exact (hχLip.dist_le_mul x y).trans
              (mul_le_mul (by change (CsN:ℝ) ≤ (CsN:ℝ)+2;linarith)
                (Real.self_le_rpow_of_le_one dist_nonneg hd (by exact_mod_cast hαone.le)) dist_nonneg (by positivity))
          · have hp := Real.one_le_rpow (show 1 ≤ dist x y by linarith) α.coe_nonneg
            have hn : dist (χ x) (χ y) ≤ 2 := by rw [Real.dist_eq];exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hχrange x).1,abs_of_nonneg (hχrange y).1];linarith [(hχrange x).2,(hχrange y).2])
            change dist (χ x) (χ y) ≤ ((CsN:ℝ)+2)*dist x y^(α:ℝ)
            nlinarith [CsN.coe_nonneg]
        simpa only [edist_dist,ENNReal.ofReal_mul A.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hb
    have hsource := hprod (Metric.ball (0:E2) 4) χ f α A F hχSH hf hχzero
    have hsourceCost : ScalarHolderBound (fun x => χ x*f x) univ α (Cost*F) :=
      ⟨fun x hx => (hsource.1 x hx).trans (by exact_mod_cast mul_le_mul_of_nonneg_right h2A (show 0 ≤ F from bot_le)),
        hsource.2.mono_const (mul_le_mul_of_nonneg_right h2A (show 0 ≤ F from bot_le))⟩
    obtain ⟨sol,first,second,hsol,hfirst,hsecond,hdf,hds,hnsol,hnfirst,hnsecond,hhsol,hhfirst,hhsecond⟩ :=
      hfields (fun x => χ x*v x) α (Cost*U) Kapp hPH1Cost hPH2
    have hsfH : HolderWith (Cost*F) α (fun x => χ x*f x) :=
      fun x y => hsourceCost.2 x (mem_univ x) y (mem_univ y)
    let source := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => χ x*f x)
      (hsfH.continuous hα) (Cost*F:NNReal) (fun x => by simpa only [Real.norm_eq_abs] using hsourceCost.1 x (mem_univ x))
    have hnsource : ‖source‖₊ ≤ Cost*F := by
      apply NNReal.coe_le_coe.mp
      exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (Cost*F).coe_nonneg _
    obtain ⟨ψ,H',hψsmooth,hψcompact,hψsupp,hψrange,hψone,hH',hcoeff,_⟩ := hCgdata 0 a ha
    have hHCost : H' ≤ Cost*(Real.toNNReal Λ+H) := by
      apply NNReal.coe_le_coe.mp
      have hΛ0 : 0 ≤ Λ := (hκ.trans_le hΛ).le
      simp only [NNReal.coe_mul,NNReal.coe_add,Real.coe_toNNReal Λ hΛ0]
      exact hH'.trans (mul_le_mul_of_nonneg_right
        hCgCost (by positivity))
    let coeff (i j : Fin 2) : BoundedContinuousFunction E2 ℝ :=
      BoundedContinuousFunction.ofNormedAddCommGroup (fun x => cutoffMatrix ψ a (a 0) x i j)
        ((holderOnWith_univ.mp (hcoeff.holder i j)).continuous hα) Λ
        (fun x => by simpa only [Real.norm_eq_abs] using hcoeff.bounded x (mem_univ x) i j)
    refine ⟨Kapp,hKappCost,χ,ψ,sol,first,second,source,coeff,
      hχsmooth,?_,hχrange,?_,?_,hψsmooth,?_,hψrange,?_,
      hsol,hfirst,hsecond,(fun _ => rfl),(fun _ _ _ => rfl),hdf,hds,
      (by exact_mod_cast hnsol),(by exact_mod_cast hnfirst),hnsource,
      (by exact_mod_cast hnsecond),hhsol,hhfirst,hsfH,hhsecond,
      { symmetric := hcoeff.symmetric
        coercive := hcoeff.coercive
        bounded := hcoeff.bounded
        holder := fun i j => (hcoeff.holder i j).mono_const hHCost }⟩
    · simpa using hχsupp
    · simpa using hχone
    · intro q hq x
      exact (hχder q hq x).trans ((div_le_self hCs.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))).trans
        hCsCost)
    · simpa using hψsupp
    · simpa using hψone
  have hnormalizedProvider
      (κ Λ : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
      (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ C : NNReal, 0 < C ∧ ∀ (a : E2 → PlanarMatrix) (f v : E2 → ℝ)
        (U F K₂ : NNReal),
        PlanarCoefficientControl a (Metric.ball (0 : E2) 4) κ Λ H α →
        ScalarHolderBound f (Metric.ball (0 : E2) 4) α F →
        PlanarHolderJetBound 1 v (Metric.ball (0 : E2) 4) α U →
        PlanarHolderJetBound 2 v (Metric.ball (0 : E2) 4) α K₂ →
        LinearClassicalEquation (Metric.ball (0 : E2) 4) a f v →
        (∀ hA : (a 0).PosDef, spdLaplacianSchauderDefectConst (a 0) hA α
          (4 * (normalizedEntryOscillation H α + H))
          (4 * normalizedEntryOscillation H α) ≤ 1 / 2) →
        eContDiffHolderGaugeOn 2 α (Metric.closedBall (0 : E2) 1) v ≤
          (C * (U + F) : NNReal) := by
    classical
    obtain ⟨Cost,hCost,hfields⟩ := hactualFields κ Λ hκ hΛ H α hα hαone
    obtain ⟨Cp,hCp,hprovider⟩ := hfrozenProvider κ Λ hκ hΛ α hα hαone
    let χ := ballCutoffBoundedContinuousFunction (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num) (show (3/2:ℝ) < 2 by norm_num)
    let Md := ‖ballCutoffFDerivBoundedContinuousFunction (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num) (show (3/2:ℝ) < 2 by norm_num)‖₊
    let Md₂ := Real.toNNReal (DifferentialGeometry.Analysis.ballCutoffFDeriv2Bound (3/2) 2)
    let Kχ := ballCutoffHolderConst (3/2) 2
    let Kd := ballCutoffFDerivHolderConst (3/2) 2
    let Kd₂ := ballCutoffFDeriv2HolderConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num) (show (3/2:ℝ) < 2 by norm_num)
    let A := Real.toNNReal Λ
    let S := ‖χ‖₊*Cost+4*(2*(A*Md*Cost)+A*Md₂*Cost)
    let Hc := ‖χ‖₊*Cost+Cost*Kχ+
      4*(2*((A*Md)*Cost+Cost*(A*Kd+Md*H))+(A*Md₂)*Cost+Cost*(A*Kd₂+Md₂*H))
    let D := 1+Hc+S+‖χ‖₊*Cost
    refine ⟨2*Cp*D,by dsimp [D];positivity,?_⟩
    intro a f v U F K₂ ha hf hv1 hv2 heq hsmall
    obtain ⟨Kapp,_,cutoffField,coefficientCutoffField,solutionField,firstField,secondField,sourceField,coefficientFields,cutoffSmoothFact,cutoffSupportFact,cutoffRangeFact,cutoffInnerFact,cutoffDerivativesFact,coefficientCutoffSmoothFact,coefficientCutoffSupportFact,coefficientCutoffRangeFact,coefficientCutoffInnerFact,solutionValueFact,firstValueFact,secondValueFact,sourceValueFact,coefficientsValueFact,derivativeFirstFact,derivativeSecondFact,solutionNormFact,firstNormFact,sourceNormFact,secondNormFact,solutionHolderFact,firstHolderFact,sourceHolderFact,secondHolderFact,coefficientControlFact⟩ := hfields a f v U F K₂ ha hf hv1 hv2
    have hpv : EqOn (solutionField : E2 → ℝ) v (Metric.ball (0:E2) 2) := by
      intro x hx
      rw [solutionValueFact,cutoffInnerFact x hx,one_mul]
    have hpa (x : E2) (hx : x ∈ Metric.ball (0:E2) 2) :
        (fun i j => coefficientFields i j x) = a x := by
      ext i j
      rw [coefficientsValueFact]
      simp [cutoffMatrix,coefficientCutoffInnerFact x hx]
    have hpaij (x : E2) (hx : x ∈ Metric.ball (0:E2) 2) (i j : Fin 2) : coefficientFields i j x = a x i j :=
      congrArg (fun A : PlanarMatrix => A i j) (hpa x hx)
    have hA : (a 0).PosDef := by
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · rw [Matrix.isHermitian_iff_isSymm]
        ext i j
        exact ha.symmetric 0 (Metric.mem_ball_self (by norm_num)) j i
      · intro ξ hξ
        let ξ' : E2 := WithLp.toLp 2 ξ
        have hξ' : ξ' ≠ 0 := by
          intro hz
          apply hξ
          simpa only [ξ',WithLp.ofLp_toLp,WithLp.ofLp_zero] using congrArg WithLp.ofLp hz
        have hp := mul_pos hκ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hξ'))
        have hb := hp.trans_le (ha.coercive 0 (Metric.mem_ball_self (by norm_num)) ξ')
        convert hb using 1
        simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,ξ',PiLp.toLp_apply]
        congr 1
        funext i
        congr 1
        funext j
        ring
    have hAp : (show PlanarMatrix from fun i j => coefficientFields i j 0).PosDef := by
      simpa only [hpa 0 (Metric.mem_ball_self (by norm_num))] using hA
    have hsource (x : E2) (hx : x ∈ Metric.ball (0:E2) 2) :
        variableMatrixLap coefficientFields secondField x = sourceField x := by
      have hn : (fun y => cutoffField y*v y) =ᶠ[𝓝 x] v :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hx)
          (fun y hy => by rw [cutoffInnerFact y hy,one_mul])
      have hsecond : secondField x = actualSecondJet v x := by
        rw [secondValueFact]
        exact ((hn.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds
      simp only [variableMatrixLap,BoundedContinuousFunction.sum_apply]
      change (∑ i : Fin 2, ∑ j : Fin 2, coefficientFields i j x *
        secondField x (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)) = _
      have he : (∑ i : Fin 2, ∑ j : Fin 2, coefficientFields i j x *
          secondField x (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
          matrixHessian a v x := by
        simp only [hsecond,hpaij x hx,EuclideanSpace.basisFun_apply,coordinateVector,actualSecondJet,matrixHessian,planarHessian]
      rw [he,sourceValueFact,cutoffInnerFact x hx,one_mul]
      exact heq x (Metric.ball_subset_ball (by norm_num) hx)
    have hha (i j : Fin 2) : HolderWith H α
        ((Metric.ball (0:E2) 2).domRestrict (coefficientFields i j : E2 → ℝ)) := by
      intro x y
      simpa only [domRestrict_apply,hpaij x x.property,hpaij y y.property,Subtype.edist_eq] using
        ha.holder i j x (Metric.ball_subset_ball (by norm_num) x.property) y (Metric.ball_subset_ball (by norm_num) y.property)
    have homega (i j : Fin 2) (x : E2) (hx : x ∈ Metric.ball (0:E2) 2) :
        ‖coefficientFields i j 0-coefficientFields i j x‖ ≤ (normalizedEntryOscillation H α:ℝ) := by
      have hh := (ha.holder i j).dist_le (Metric.mem_ball_self (by norm_num)) (Metric.ball_subset_ball (by norm_num) hx)
      have hd : dist (0:E2) x ≤ 2 := by rw [dist_comm];exact (Metric.mem_ball.mp hx).le
      simpa only [hpaij 0 (Metric.mem_ball_self (by norm_num)),hpaij x hx,Real.norm_eq_abs,Real.dist_eq,
        normalizedEntryOscillation,NNReal.coe_mul,NNReal.coe_rpow,NNReal.coe_ofNat] using
        hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd α.coe_nonneg) H.coe_nonneg)
    have han (i j : Fin 2) (x : E2) (hx : x ∈ Metric.ball (0:E2) 2) : ‖coefficientFields i j x‖ ≤ (A:ℝ) := by
      have hb := ha.bounded x (Metric.ball_subset_ball (by norm_num) hx) i j
      simpa only [hpaij x hx,Real.norm_eq_abs,A,Real.coe_toNNReal Λ (hκ.trans_le hΛ).le] using hb
    have hsmp : spdLaplacianSchauderDefectConst (fun i j => coefficientFields i j 0) hAp α
        (∑ _i : Fin 2, ∑ _j : Fin 2, (normalizedEntryOscillation H α+H))
        (∑ _i : Fin 2, ∑ _j : Fin 2, normalizedEntryOscillation H α) ≤ 1/2 := by
      simpa only [hpa 0 (Metric.mem_ball_self (by norm_num)),Fin.sum_univ_two,← two_mul,← mul_assoc,show (2:NNReal)*2=4 by norm_num] using hsmall hA
    have hest := variable_coefficient_ball_interior_schauder_estimate_of_coefficient_oscillation
      (center := (0:E2)) (rho := 1) (r := 3/2) (R := 2) (by norm_num) (by norm_num) (by norm_num)
      hα hαone coefficientFields hAp sourceField solutionField firstField secondField
      derivativeFirstFact derivativeSecondFact hsource (fun _ _ => A) (fun _ _ => H)
      (fun _ _ => normalizedEntryOscillation H α) hha homega han
      sourceHolderFact firstHolderFact solutionHolderFact secondHolderFact
      (fun x => (secondField.norm_coe_le_norm x).trans (by exact_mod_cast secondNormFact))
      (hsmp.trans_lt (by norm_num))
    have hcost (K B : NNReal) (u : BoundedContinuousFunction E2 ℝ) :=
      (hprovider (a 0) hA
        (ha.coercive 0 (Metric.mem_ball_self (by norm_num)))
        (ha.bounded 0 (Metric.mem_ball_self (by norm_num))) K B).2 u
    have hCF : Cost*F ≤ Cost*(U+F) := by gcongr; exact le_add_of_nonneg_left (by positivity)
    have hCU : Cost*U ≤ Cost*(U+F) := by gcongr; exact le_add_of_nonneg_right (by positivity)
    have hnF : ‖sourceField‖₊ ≤ Cost*(U+F) := sourceNormFact.trans hCF
    have hnDu : ‖firstField‖₊ ≤ Cost*(U+F) := firstNormFact.trans hCU
    have hnU : ‖solutionField‖₊ ≤ Cost*(U+F) := solutionNormFact.trans hCU
    have hHcost : variableBallCutoffSourceHolderConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) (fun _ _ : Fin 2 => H)
        (Cost*F) (Cost*U) Kd₂ (Cost*U) sourceField solutionField firstField ≤ Hc*(U+F) := by
      dsimp only [variableBallCutoffSourceHolderConst,variableCutoffSourceHolderConst,
        cutoffValueHolderConst,matrixCutoffCommutatorHolderConst]
      simp only [Fin.sum_univ_two]
      change ‖χ‖₊*(Cost*F)+‖sourceField‖₊*Kχ+
        ((2*((A*Md)*(Cost*U)+‖firstField‖₊*(A*Kd+Md*H))+
          (A*Md₂)*(Cost*U)+‖solutionField‖₊*(A*Kd₂+Md₂*H))+
        (2*((A*Md)*(Cost*U)+‖firstField‖₊*(A*Kd+Md*H))+
          (A*Md₂)*(Cost*U)+‖solutionField‖₊*(A*Kd₂+Md₂*H))+
        ((2*((A*Md)*(Cost*U)+‖firstField‖₊*(A*Kd+Md*H))+
          (A*Md₂)*(Cost*U)+‖solutionField‖₊*(A*Kd₂+Md₂*H))+
        (2*((A*Md)*(Cost*U)+‖firstField‖₊*(A*Kd+Md*H))+
          (A*Md₂)*(Cost*U)+‖solutionField‖₊*(A*Kd₂+Md₂*H)))) ≤ _
      calc
        _ ≤ ‖χ‖₊*(Cost*(U+F))+(Cost*(U+F))*Kχ+
            ((2*((A*Md)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd+Md*H))+
              (A*Md₂)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd₂+Md₂*H))+
            (2*((A*Md)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd+Md*H))+
              (A*Md₂)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd₂+Md₂*H))+
            ((2*((A*Md)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd+Md*H))+
              (A*Md₂)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd₂+Md₂*H))+
            (2*((A*Md)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd+Md*H))+
              (A*Md₂)*(Cost*(U+F))+(Cost*(U+F))*(A*Kd₂+Md₂*H)))) := by
          gcongr <;> assumption
        _ = _ := by dsimp only [Hc];ring
    have hScost : variableBallCutoffSourceSupConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) sourceField solutionField firstField ≤ S*(U+F) := by
      dsimp only [variableBallCutoffSourceSupConst,variableCutoffSourceSupConst,cutoffValueSupConst,matrixCutoffCommutatorSupConst]
      simp only [Fin.sum_univ_two]
      change ‖χ‖₊*‖sourceField‖₊+
        ((2*(A*Md*‖firstField‖₊)+2*(A*Md*‖firstField‖₊)+(2*(A*Md*‖firstField‖₊)+2*(A*Md*‖firstField‖₊)))+
        (A*Md₂*‖solutionField‖₊+A*Md₂*‖solutionField‖₊+(A*Md₂*‖solutionField‖₊+A*Md₂*‖solutionField‖₊))) ≤ _
      calc
        _ ≤ ‖χ‖₊*(Cost*(U+F))+
            ((2*(A*Md*(Cost*(U+F)))+2*(A*Md*(Cost*(U+F)))+(2*(A*Md*(Cost*(U+F)))+2*(A*Md*(Cost*(U+F)))))+
            (A*Md₂*(Cost*(U+F))+A*Md₂*(Cost*(U+F))+(A*Md₂*(Cost*(U+F))+A*Md₂*(Cost*(U+F))))) := by
          gcongr <;> assumption
        _ = _ := by dsimp only [S];ring
    have hvalue : ‖cutoffValue χ solutionField‖₊ ≤ (‖χ‖₊*Cost)*(U+F) := by
      have hn : ‖cutoffValue χ solutionField‖₊ ≤ ‖χ‖₊*‖solutionField‖₊ := by
        exact_mod_cast norm_cutoffValue_le χ solutionField
      calc
        _ ≤ ‖χ‖₊*(Cost*(U+F)) := hn.trans (mul_le_mul_of_nonneg_left hnU (by positivity))
        _ = _ := by ring
    rw [← eContDiffHolderGaugeOn_congr_of_eqOn_open Metric.isOpen_ball
      (Metric.closedBall_subset_ball (show (1:ℝ) < 2 by norm_num)) hpv 2 α]
    apply hest.trans
    apply ENNReal.coe_le_coe.mpr
    unfold variableBallInteriorSchauderConst
    have hden : (1/2:NNReal) ≤ 1-spdLaplacianSchauderDefectConst (fun i j => coefficientFields i j 0) hAp α
        (∑ _i : Fin 2, ∑ _j : Fin 2, (normalizedEntryOscillation H α+H))
        (∑ _i : Fin 2, ∑ _j : Fin 2, normalizedEntryOscillation H α) := by
      exact le_tsub_of_add_le_left (by nlinarith [hsmp])
    apply (div_le_iff₀ ((show (0:NNReal) < 1/2 by norm_num).trans_le hden)).mpr
    have hb := hcost
      (variableBallCutoffSourceHolderConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) (fun _ _ : Fin 2 => H)
        (Cost*F) (Cost*U) Kd₂ (Cost*U) sourceField solutionField firstField)
      (variableBallCutoffSourceSupConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) sourceField solutionField firstField)
      (cutoffValue χ solutionField)
    have hb' : spdLaplacianSchauderConst (fun i j => coefficientFields i j 0) hAp α
      (variableBallCutoffSourceHolderConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) (fun _ _ : Fin 2 => H)
        (Cost*F) (Cost*U) Kd₂ (Cost*U) sourceField solutionField firstField)
      (variableBallCutoffSourceSupConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) sourceField solutionField firstField)
      (cutoffValue χ solutionField) ≤ Cp*
      (variableBallCutoffSourceHolderConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) (fun _ _ : Fin 2 => H)
        (Cost*F) (Cost*U) Kd₂ (Cost*U) sourceField solutionField firstField+
      variableBallCutoffSourceSupConst (0:E2) (show (0:ℝ) ≤ 3/2 by norm_num)
        (show (3/2:ℝ) < 2 by norm_num) (fun _ _ : Fin 2 => A) sourceField solutionField firstField+
      ‖cutoffValue χ solutionField‖₊) := by
      simpa only [hpa 0 (Metric.mem_ball_self (by norm_num))] using hb
    apply hb'.trans
    calc
      Cp*(_+_+‖cutoffValue χ solutionField‖₊) ≤ Cp*(Hc*(U+F)+S*(U+F)+(‖χ‖₊*Cost)*(U+F)) := by gcongr <;> assumption
      _ ≤ (2*Cp*D*(U+F))*(1/2) := by dsimp only [D];ring_nf;nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  have hlocalProvider
      (κ Λ R : ℝ) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hR : 0 < R)
      (H α : NNReal) (hα : 0 < α) (hαone : α < 1) :
      ∃ s : ℝ, ∃ C : NNReal, 0 < s ∧ 8 * s < R ∧ 0 < C ∧
        ∀ (x₀ : E2) (a : E2 → PlanarMatrix) (f v : E2 → ℝ) (U F K₂ : NNReal),
        PlanarCoefficientControl a (Metric.ball x₀ (2 * R)) κ Λ H α →
        ScalarHolderBound f (Metric.ball x₀ (2 * R)) α F →
        PlanarHolderJetBound 1 v (Metric.ball x₀ (2 * R)) α U →
        PlanarHolderJetBound 2 v (Metric.ball x₀ (2 * R)) α K₂ →
        LinearClassicalEquation (Metric.ball x₀ (2 * R)) a f v →
        ∀ c ∈ Metric.ball x₀ R,
          (∀ x ∈ Metric.closedBall c s, ‖iteratedFDeriv ℝ 2 v x‖ ≤ (C * (U + F) : NNReal)) ∧
          HolderOnWith (C * (U + F)) α (iteratedFDeriv ℝ 2 v) (Metric.closedBall c s) := by
    classical
    obtain ⟨s,hs,hsR,hscale⟩ := hscaleProvider κ Λ R hκ hΛ hR H α hα hαone
    obtain ⟨C₁,C₂,Cf,hdata⟩ := haffineProvider s hs α hα hαone
    obtain ⟨Cn,hCn,hest⟩ := hnormalizedProvider κ Λ hκ hΛ
      (scaledEntryHolder H α s) α hα hαone
    let T : NNReal := Cn*(C₁+Cf)
    let Kn : NNReal := Real.toNNReal (s⁻¹^2)*T
    let Kh : NNReal := Real.toNNReal (s⁻¹^2*(s⁻¹)^(α:ℝ))*T
    let C : NNReal := Kn+Kh+1
    refine ⟨s,C,hs,hsR,by dsimp [C];positivity,?_⟩
    intro x₀ a f v U F K₂ ha hf hv1 hv2 heq c hc
    obtain ⟨hmap,_,_,hsmall⟩ := hscale x₀ a ha c hc
    obtain ⟨h1,h2,hf',hjets,_,heq'⟩ := hdata c (Metric.ball x₀ (2*R)) hmap a f v U K₂ F hv1 hv2 hf heq
    have hac : PlanarCoefficientControl (affineMatrix c s a) (Metric.ball (0:E2) 4)
        κ Λ (scaledEntryHolder H α s) α := by
      refine ⟨?_,?_,?_,?_⟩
      · intro z hz i j; exact ha.symmetric _ (hmap z hz) i j
      · intro z hz ξ; exact ha.coercive _ (hmap z hz) ξ
      · intro z hz i j; exact ha.bounded _ (hmap z hz) i j
      · intro i j x hx y hy
        have hd : dist (affinePull c s x) (affinePull c s y) = s*dist x y := by
          simp only [affinePull,dist_eq_norm]
          rw [show c+s • x-(c+s • y) = s • (x-y) by module,norm_smul,Real.norm_of_nonneg hs.le]
        have hb := (ha.holder i j).dist_le (hmap x hx) (hmap y hy)
        rw [hd,Real.mul_rpow hs.le dist_nonneg] at hb
        have hr : dist (affineMatrix c s a x i j) (affineMatrix c s a y i j) ≤
            (scaledEntryHolder H α s:ℝ)*dist x y^(α:ℝ) := by
          simpa only [affineMatrix,Function.comp_def,scaledEntryHolder,NNReal.coe_mul,
            Real.coe_toNNReal _ (Real.rpow_nonneg hs.le _),mul_assoc] using hb
        simpa only [edist_dist,ENNReal.ofReal_mul (scaledEntryHolder H α s).coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
    have hsmp : ∀ hA : (affineMatrix c s a 0).PosDef,
        spdLaplacianSchauderDefectConst (affineMatrix c s a 0) hA α
          (4*(normalizedEntryOscillation (scaledEntryHolder H α s) α+scaledEntryHolder H α s))
          (4*normalizedEntryOscillation (scaledEntryHolder H α s) α) ≤ 1/2 := by
      simpa only [affineMatrix,Function.comp_def,affinePull,smul_zero,add_zero] using hsmall
    have hg := hest (affineMatrix c s a) (affineSource c s f) (affineSolution c s v)
      (C₁*U) (Cf*F) (C₂*K₂) hac hf' h1 h2 heq' hsmp
    have hprior : Cn*(C₁*U+Cf*F) ≤ T*(U+F) := by
      dsimp only [T]
      nlinarith [mul_nonneg C₁.coe_nonneg F.coe_nonneg,mul_nonneg Cf.coe_nonneg U.coe_nonneg]
    have hg' : eContDiffHolderGaugeOn 2 α (Metric.closedBall (0:E2) 1) (affineSolution c s v) ≤
        (T*(U+F):NNReal) := hg.trans (ENNReal.coe_le_coe.mpr hprior)
    let z : E2 → E2 := fun x => s⁻¹ • (x-c)
    have hz (x : E2) (hx : x ∈ Metric.closedBall c s) : z x ∈ Metric.closedBall (0:E2) 1 := by
      have hn : ‖x-c‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hx
      simp only [Metric.mem_closedBall,dist_zero_right,z,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le)]
      exact (mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hs.le)).trans_eq (inv_mul_cancel₀ hs.ne')
    have hzpull (x : E2) : affinePull c s (z x) = x := by
      dsimp only [affinePull,z]
      rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
      abel
    have hjet (x : E2) (hx : x ∈ Metric.closedBall c s) :
        iteratedFDeriv ℝ 2 v x = s⁻¹^2 • iteratedFDeriv ℝ 2 (affineSolution c s v) (z x) := by
      have ht : iteratedFDeriv ℝ 2 (affineSolution c s v) (z x) =
          s^2 • iteratedFDeriv ℝ 2 v x := by
        ext ξ
        simpa only [hzpull,smul_apply,smul_eq_mul] using
          hjets 2 (by norm_num) (z x) (Metric.closedBall_subset_ball (by norm_num) (hz x hx)) ξ
      rw [ht,smul_smul,← mul_pow,inv_mul_cancel₀ hs.ne',one_pow,one_smul]
    have hKn : Kn ≤ C := by dsimp [C];exact le_add_right (le_add_right le_rfl)
    have hKh : Kh ≤ C := by dsimp [C];exact le_add_right (le_add_left le_rfl)
    constructor
    · intro x hx
      rw [hjet x hx,norm_smul,Real.norm_of_nonneg (sq_nonneg (s⁻¹))]
      have hn := spatialJet_norm_le hg' (show 2 ≤ 2 by rfl) (hz x hx)
      calc
        _ ≤ s⁻¹^2*((T*(U+F):NNReal):ℝ) := mul_le_mul_of_nonneg_left hn (sq_nonneg _)
        _ = ((Kn*(U+F):NNReal):ℝ) := by
          dsimp only [Kn]
          simp only [NNReal.coe_mul,Real.coe_toNNReal _ (sq_nonneg _)];ring
        _ ≤ _ := by exact_mod_cast mul_le_mul_of_nonneg_right hKn (show (0:NNReal) ≤ U+F by positivity)
    · intro x hx y hy
      have hh := topSpatialJet_holderWith_restrict hg'
      have hb := hh.dist_le (⟨z x,hz x hx⟩) (⟨z y,hz y hy⟩)
      have hd : dist (z x) (z y) = s⁻¹*dist x y := by
        dsimp only [z]
        rw [dist_eq_norm,← smul_sub,show x-c-(y-c)=x-y by abel,norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hs.le),dist_eq_norm]
      simp only [domRestrict_apply,Subtype.dist_eq,hd] at hb
      rw [Real.mul_rpow (inv_nonneg.mpr hs.le) dist_nonneg] at hb
      have hr : dist (iteratedFDeriv ℝ 2 v x) (iteratedFDeriv ℝ 2 v y) ≤
          ((C*(U+F):NNReal):ℝ)*dist x y^(α:ℝ) := by
        rw [hjet x hx,hjet y hy,dist_eq_norm,← smul_sub,norm_smul,
          Real.norm_of_nonneg (sq_nonneg (s⁻¹))]
        rw [dist_eq_norm] at hb
        calc
          _ ≤ s⁻¹^2*(((T*(U+F):NNReal):ℝ)*((s⁻¹)^(α:ℝ)*dist x y^(α:ℝ))) :=
            mul_le_mul_of_nonneg_left hb (sq_nonneg _)
          _ = ((Kh*(U+F):NNReal):ℝ)*dist x y^(α:ℝ) := by
            dsimp only [Kh]
            simp only [NNReal.coe_mul,Real.coe_toNNReal _ (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (inv_nonneg.mpr hs.le) _))]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (by exact_mod_cast mul_le_mul_of_nonneg_right hKh (show (0:NNReal) ≤ U+F by positivity))
            (Real.rpow_nonneg dist_nonneg _)
      simpa only [edist_dist,ENNReal.ofReal_mul (C*(U+F)).coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal hr
  have hlocal := hlocalProvider κ Λ R hκ hΛ hR H α hα hαone
  obtain ⟨s,C,hs,hsR,hC,hlocal⟩ := hlocal
  let C₀ : NNReal := 1+C+2*C/(Real.toNNReal s)^(α:ℝ)
  have hC₀ : 0 < C₀ := by dsimp [C₀];positivity
  refine ⟨C₀,hC₀,?_⟩
  intro x₀ a ha f v F U K₂ hf hU hK₂ heq
  let K' : NNReal := C₀*(U+F)
  refine ⟨K',by simp [K',NNReal.coe_add],hK₂.1.mono (Metric.ball_subset_ball (by linarith)),?_⟩
  have hUU : U ≤ K' := by
    have hCU : 1 ≤ C₀ := by dsimp [C₀];exact le_add_right (le_add_right le_rfl)
    exact (le_mul_of_one_le_left (show 0 ≤ U from zero_le) hCU).trans (by dsimp [K'];gcongr;exact le_add_right le_rfl)
  intro q hq
  by_cases hq1 : q ≤ 1
  · exact ⟨fun x hx => ((hU.2 q hq1).1 x (Metric.ball_subset_ball (by linarith) hx)).trans (by exact_mod_cast hUU),
      ((hU.2 q hq1).2.mono (Metric.ball_subset_ball (by linarith))).mono_const hUU⟩
  · have hq2 : q=2 := by omega
    subst q
    have hCB : C*(U+F) ≤ K' := by
      dsimp [K',C₀]
      gcongr
      exact le_add_right (le_add_left le_rfl)
    constructor
    · intro x hx
      exact ((hlocal x₀ a f v U F K₂ ha hf hU hK₂ heq x hx).1 x
        (Metric.mem_closedBall_self hs.le)).trans (by exact_mod_cast hCB)
    · intro x hx y hy
      have hxb := (hlocal x₀ a f v U F K₂ ha hf hU hK₂ heq x hx).1 x (Metric.mem_closedBall_self hs.le)
      have hyb := (hlocal x₀ a f v U F K₂ ha hf hU hK₂ heq y hy).1 y (Metric.mem_closedBall_self hs.le)
      have hd : dist (iteratedFDeriv ℝ 2 v x) (iteratedFDeriv ℝ 2 v y) ≤ (K':ℝ)*dist x y^(α:ℝ) := by
        by_cases hxy : dist x y ≤ s
        · have hyx : y ∈ Metric.closedBall x s := by rwa [Metric.mem_closedBall,dist_comm]
          exact ((hlocal x₀ a f v U F K₂ ha hf hU hK₂ heq x hx).2.dist_le
            (Metric.mem_closedBall_self hs.le) hyx).trans (mul_le_mul_of_nonneg_right
              (by exact_mod_cast hCB) (Real.rpow_nonneg dist_nonneg _))
        · have hdxy : s ≤ dist x y := (lt_of_not_ge hxy).le
          have hp : 0 < s^(α:ℝ) := Real.rpow_pos_of_pos hs _
          have hr : s^(α:ℝ) ≤ dist x y^(α:ℝ) := Real.rpow_le_rpow hs.le hdxy α.coe_nonneg
          have hn := (norm_sub_le (iteratedFDeriv ℝ 2 v x) (iteratedFDeriv ℝ 2 v y)).trans (add_le_add hxb hyb)
          rw [dist_eq_norm]
          have hsp : ((Real.toNNReal s):ℝ)^(α:ℝ) = s^(α:ℝ) := by rw [Real.coe_toNNReal _ hs.le]
          have hKcost : 2*(C:ℝ)*((U:ℝ)+(F:ℝ))/(s^(α:ℝ)) ≤ (K':ℝ) := by
            dsimp [K',C₀]
            change 2*(C:ℝ)*((U:ℝ)+(F:ℝ))/(s^(α:ℝ)) ≤
              (1+(C:ℝ)+2*(C:ℝ)/(s.toNNReal:ℝ)^(α:ℝ))*((U:ℝ)+(F:ℝ))
            rw [hsp]
            have hc : 0 ≤ (C:ℝ) := C.coe_nonneg
            have huf : 0 ≤ (U:ℝ)+(F:ℝ) := add_nonneg U.coe_nonneg F.coe_nonneg
            have heq : 2*(C:ℝ)*((U:ℝ)+(F:ℝ))/(s^(α:ℝ)) = (2*(C:ℝ)/(s^(α:ℝ)))*((U:ℝ)+(F:ℝ)) := by ring
            rw [heq]
            gcongr
            nlinarith
          have hh : (2*(C:ℝ)*((U:ℝ)+(F:ℝ))/(s^(α:ℝ)))*dist x y^(α:ℝ) ≥
              (C*(U+F):NNReal)+(C*(U+F):NNReal) := by
            simp only [NNReal.coe_mul,NNReal.coe_add]
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hp).mpr
            nlinarith [mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(C:ℝ)*((U:ℝ)+(F:ℝ)) by positivity)]
          exact hn.trans (hh.trans (by gcongr))
      simpa only [edist_dist,ENNReal.ofReal_mul K'.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal hd

def shiftedMatrix (a : E2 → PlanarMatrix) (k : Fin 2) (h : ℝ) : E2 → PlanarMatrix :=
  fun x => a (shift k h x)

def classicalDifferenceSource (a : E2 → PlanarMatrix) (f w : E2 → ℝ)
    (k : Fin 2) (h : ℝ) (x : E2) : ℝ :=
  differenceQuotient f k h x - ∑ i : Fin 2, ∑ j : Fin 2,
    differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j

/-- Exact linear equation for nonzero finite differences of an already
C2,alpha function. The shifted coefficient remains principal. -/
theorem R5_linear_difference_equation
    (x₀ : E2) (R : ℝ) (hR : 0 < R) (a : E2 → PlanarMatrix) (f w : E2 → ℝ)
    (hw : ContDiffOn ℝ 2 w (Metric.ball x₀ (4 * R)))
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R)) a f w)
    (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hsmall : |h| < R) :
    LinearClassicalEquation (Metric.ball x₀ (2 * R)) (shiftedMatrix a k h)
      (classicalDifferenceSource a f w k h) (differenceQuotient w k h) := by
  have hsub : Metric.ball x₀ (2 * R) ⊆ Metric.ball x₀ (4 * R) :=
    Metric.ball_subset_ball (by linarith)
  have hshift (x : E2) (hx : x ∈ Metric.ball x₀ (2 * R)) :
      shift k h x ∈ Metric.ball x₀ (4 * R) := by
    have he : ‖coordinateVector 2 k‖ = 1 := by
      simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
    have hs : dist (shift k h x) x = |h| := by
      simp [shift, dist_eq_norm, norm_smul, he, Real.norm_eq_abs]
    have := dist_triangle (shift k h x) x x₀
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hhne : h ≠ 0 := (abs_pos.mp hh)
  intro x hx
  have hwat : ContDiffAt ℝ 2 w x := hw.contDiffAt (Metric.isOpen_ball.mem_nhds (hsub hx))
  have hswat : ContDiffAt ℝ 2 (fun y => w (y + h • coordinateVector 2 k)) x :=
    (hw.contDiffAt (Metric.isOpen_ball.mem_nhds (hshift x hx))).comp x
      (contDiff_id.add contDiff_const).contDiffAt
  have hδ : iteratedFDeriv ℝ 2 (differenceQuotient w k h) x =
      h⁻¹ • (iteratedFDeriv ℝ 2 w (shift k h x) - iteratedFDeriv ℝ 2 w x) := by
    have heq : differenceQuotient w k h =
        h⁻¹ • ((fun y => w (y + h • coordinateVector 2 k)) - w) := by
      funext y
      simp [differenceQuotient, shift, div_eq_mul_inv, mul_comm]
    rw [heq]
    change iteratedFDeriv ℝ 2
      (h⁻¹ • (fun y => w (y + h • coordinateVector 2 k) - w y)) x = _
    rw [iteratedFDeriv_const_smul_apply (a := h⁻¹) (hswat.sub hwat)]
    change h⁻¹ • iteratedFDeriv ℝ 2
      ((fun y => w (y + h • coordinateVector 2 k)) - w) x = _
    rw [iteratedFDeriv_sub_apply hswat hwat,
      iteratedFDeriv_comp_add_right]
    rfl
  have hess (i j : Fin 2) : planarHessian (differenceQuotient w k h) x i j =
      (planarHessian w (shift k h x) i j - planarHessian w x i j) / h := by
    have hm := congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E2) ℝ =>
      A ![coordinateVector 2 i, coordinateVector 2 j]) hδ
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.sub_apply,
      smul_eq_mul, planarHessian, div_eq_mul_inv, mul_comm] using hm
  have hfx := heq x (hsub hx)
  have hfs := heq (shift k h x) (hshift x hx)
  unfold matrixHessian at hfx hfs ⊢
  simp only [shiftedMatrix, classicalDifferenceSource, hess, differenceQuotient]
  rw [← hfx, ← hfs]
  simp only [Fin.sum_univ_two]
  field_simp
  ring

/-- Uniform C2 estimate for differences. The original input norm M, not
the individual C2 norm of delta_h w, determines the output constant. -/
theorem R5_uniform_difference_C2_estimate
    (x₀ : E2) (R κ Λ : ℝ) (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
    (a : E2 → PlanarMatrix) (f w : E2 → ℝ) (H α M : NNReal)
    (hα : 0 < α) (hαone : α < 1)
    (ha : PlanarCoefficientControl a (Metric.ball x₀ (4 * R)) κ Λ H α)
    (haC1 : ∀ i j, PlanarHolderJetBound 1 (fun x => a x i j)
      (Metric.ball x₀ (4 * R)) α M)
    (hfC1 : PlanarHolderJetBound 1 f (Metric.ball x₀ (4 * R)) α M)
    (hwC2 : PlanarHolderJetBound 2 w (Metric.ball x₀ (4 * R)) α M)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R)) a f w) :
    ∃ C : NNReal, ∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < R →
      PlanarHolderJetBound 2 (differenceQuotient w k h)
        (Metric.ball x₀ R) α C := by
  classical
  let B := Metric.ball x₀ (4 * R)
  let D := Metric.ball x₀ (2 * R)
  have hB : IsOpen B := Metric.isOpen_ball
  have hD : IsOpen D := Metric.isOpen_ball
  have hsub : D ⊆ B := Metric.ball_subset_ball (by linarith)
  have hcurry1 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : E2 → F) (B : Set E2) (α M : NNReal)
      (h : HolderOnWith M α (iteratedFDeriv ℝ 1 g) B) :
      HolderOnWith M α (fderiv ℝ g) B := by
    let L := (continuousMultilinearCurryFin1 ℝ E2 F).symm
    have hg (x : E2) : iteratedFDeriv ℝ 1 g x = L (fderiv ℝ g x) := by
      ext v
      simp [L, iteratedFDeriv_one_apply]
    intro x hx y hy
    simpa only [hg, L.isometry.edist_eq] using h x hx y hy
  let S := (continuousMultilinearCurryFin1 ℝ E2 (E2 →L[ℝ] ℝ)).symm.trans
    (continuousMultilinearCurryRightEquiv' ℝ 1 E2 ℝ).symm
  have hS (x : E2) : iteratedFDeriv ℝ 2 w x = S (fderiv ℝ (fderiv ℝ w) x) := by
    ext ξ
    rw [iteratedFDeriv_two_apply]
    simp [S, Fin.init]
  have hHess : HolderOnWith M α (fderiv ℝ (fderiv ℝ w)) B := by
    intro x hx y hy
    simpa only [hS, S.isometry.edist_eq] using (hwC2.2 2 (by omega)).2 x hx y hy
  have hHessb (x : E2) (hx : x ∈ B) : ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ (M : ℝ) := by
    simpa only [hS, LinearIsometryEquiv.norm_map] using (hwC2.2 2 (by omega)).1 x hx
  have hFTC {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (g : E2 → F) (hg : ContDiffOn ℝ 1 g B)
      (hgb : ∀ x ∈ B, ‖fderiv ℝ g x‖ ≤ (M : ℝ))
      (hgh : HolderOnWith M α (fderiv ℝ g) B)
      (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hsmall : |h| < R) :
      (∀ x ∈ D, ‖h⁻¹ • (g (shift k h x) - g x)‖ ≤ (M : ℝ)) ∧
      HolderOnWith M α (fun x => h⁻¹ • (g (shift k h x) - g x)) D := by
    have he : ‖coordinateVector 2 k‖ = 1 := by
      simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
    have hs (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
        x + t • (h • coordinateVector 2 k) ∈ Metric.ball x₀ (4*R) := by
      have hn : ‖t • (h • coordinateVector 2 k)‖ ≤ |h| := by
        simp only [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg ht.1]
        exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)).trans_eq (one_mul _)
      have hd := dist_triangle (x + t • (h • coordinateVector 2 k)) x x₀
      rw [dist_self_add_left] at hd
      rw [Metric.mem_ball] at hx ⊢
      linarith
    let G (x : E2) (t : ℝ) : F := fderiv ℝ g (x + t • (h • coordinateVector 2 k)) (coordinateVector 2 k)
    have hGc (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) : ContinuousOn (G x) (Icc (0:ℝ) 1) :=
      ((hg.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).comp
        (by fun_prop : ContinuousOn (fun t : ℝ => x+t • (h • coordinateVector 2 k)) (Icc (0:ℝ) 1))
        (hs x hx)).clm_apply continuousOn_const
    have hGi (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) : IntervalIntegrable (G x) volume 0 1 :=
      (hGc x hx).intervalIntegrable_of_Icc (by norm_num)
    have hrep (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) :
        h⁻¹ • (g (shift k h x) - g x) = ∫ t in (0:ℝ)..1, G x t := by
      have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
          HasDerivAt (fun t => g (x + t • (h • coordinateVector 2 k))) (h • G x t) t := by
        have hpath : HasDerivAt (fun t : ℝ => x+t • (h • coordinateVector 2 k))
            (h • coordinateVector 2 k) t := by
          convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (h • coordinateVector 2 k)) using 1 <;> simp only [zero_add, one_smul, id_eq]
          funext z
          rfl
        have hhpath := ((hg.contDiffAt (Metric.isOpen_ball.mem_nhds (hs x hx t (by simpa using ht)))).differentiableAt
          (by norm_num)).hasFDerivAt.comp_hasDerivAt t hpath
        convert hhpath using 1 <;> simp only [map_smul, G, Function.comp_def]
      have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hGi x hx).smul h)
      rw [intervalIntegral.integral_smul] at hi
      simp only [one_smul, zero_smul, add_zero] at hi
      change h • (∫ t in (0:ℝ)..1, G x t) = g (shift k h x) - g x at hi
      rw [← hi, smul_smul, inv_mul_cancel₀ (abs_pos.mp hh), one_smul]
    constructor
    · intro x hx
      rw [hrep x hx]
      have hb : ∀ t ∈ Ι (0:ℝ) 1, ‖G x t‖ ≤ (M : ℝ) := by
        intro t ht
        have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using Set.uIoc_subset_uIcc ht
        have hb := hgb _ (hs x hx t (by simpa using ht'))
        exact ((fderiv ℝ g _).le_opNorm _).trans (by rw [he, mul_one]; exact hb)
      simpa only [sub_zero, abs_one, one_mul, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
    · intro x hx y hy
      have hr : dist (h⁻¹ • (g (shift k h x) - g x))
          (h⁻¹ • (g (shift k h y) - g y)) ≤ (M : ℝ) * dist x y ^ (α : ℝ) := by
        rw [dist_eq_norm, hrep x hx, hrep y hy, ← intervalIntegral.integral_sub (hGi x hx) (hGi y hy)]
        have hb : ∀ t ∈ Ι (0:ℝ) 1, ‖G x t - G y t‖ ≤ (M : ℝ) * dist x y ^ (α : ℝ) := by
          intro t ht
          have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using Set.uIoc_subset_uIcc ht
          have hc := hgh.dist_le (hs x hx t ht') (hs y hy t ht')
          rw [dist_eq_norm, dist_add_right] at hc
          change ‖(fderiv ℝ g (x+t • (h • coordinateVector 2 k)) -
            fderiv ℝ g (y+t • (h • coordinateVector 2 k))) (coordinateVector 2 k)‖ ≤ _
          exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [he, mul_one]; exact hc)
        simpa only [sub_zero, abs_one, one_mul, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
      simpa only [edist_dist, ENNReal.ofReal_mul M.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  let F : NNReal := M + 8 * M * M
  obtain ⟨A, hA, hest⟩ := R5_classical_schauder_apriori κ Λ R hκ hΛ hR H α hα hαone
  let C : NNReal := Real.toNNReal (A * ((M : ℝ) + (F : ℝ)))
  refine ⟨C, ?_⟩
  intro k h hh hsmall
  have hne : h ≠ 0 := abs_pos.mp hh
  have he (i : Fin 2) : ‖coordinateVector 2 i‖ = 1 := by
    simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
  have hshift (x : E2) (hx : x ∈ D) : shift k h x ∈ B := by
    have hd := dist_triangle (shift k h x) x x₀
    have hs : dist (shift k h x) x = |h| := by simp [shift, dist_eq_norm, norm_smul, he, Real.norm_eq_abs]
    rw [hs] at hd
    rw [Metric.mem_ball] at hx ⊢
    linarith
  have hshiftC : ContDiff ℝ ∞ (shift k h) := by unfold shift; fun_prop
  have hδC2 : ContDiffOn ℝ 2 (differenceQuotient w k h) D := by
    have ht := (hwC2.1.comp ((hshiftC.of_le (by simp)).contDiffOn) hshift).sub (hwC2.1.mono hsub)
    have heq : differenceQuotient w k h = h⁻¹ • (w ∘ shift k h - w) := by
      funext x
      simp [differenceQuotient, div_eq_mul_inv, mul_comm]
    rw [heq]
    exact ht.const_smul h⁻¹
  have hδjet (q : ℕ) (hq : q ≤ 2) (x : E2) (hx : x ∈ D) :
      iteratedFDeriv ℝ q (differenceQuotient w k h) x =
        h⁻¹ • (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w x) := by
    have hwx : ContDiffAt ℝ q w x := (hwC2.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds (hsub hx))
    have hws : ContDiffAt ℝ q (fun z => w (z+h • coordinateVector 2 k)) x :=
      ((hwC2.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds (hshift x hx))).comp x
        (contDiff_id.add contDiff_const).contDiffAt
    have heq : differenceQuotient w k h = h⁻¹ • ((fun z => w (z+h • coordinateVector 2 k))-w) := by
      funext z
      simp [differenceQuotient, shift, div_eq_mul_inv, mul_comm]
    rw [heq]
    change iteratedFDeriv ℝ q (h⁻¹ • (fun z => w (z+h • coordinateVector 2 k) - w z)) x = _
    rw [iteratedFDeriv_const_smul_apply (a := h⁻¹) (hws.sub hwx)]
    change h⁻¹ • iteratedFDeriv ℝ q ((fun z => w (z+h • coordinateVector 2 k))-w) x = _
    rw [iteratedFDeriv_sub_apply hws hwx, iteratedFDeriv_comp_add_right]
    rfl
  let Kh : NNReal := 2 * Real.toNNReal |h|⁻¹ * M
  have hKh : (Kh : ℝ) = 2 * |h|⁻¹ * (M : ℝ) := by
    simp only [Kh, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg h))]
  have hδindividual : PlanarHolderJetBound 2 (differenceQuotient w k h) D α Kh := by
    refine ⟨hδC2, ?_⟩
    intro q hq
    constructor
    · intro x hx
      rw [hδjet q hq x hx, norm_smul, Real.norm_eq_abs, abs_inv, hKh]
      calc
        _ ≤ |h|⁻¹ * (2 * (M : ℝ)) := mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (by linarith [(hwC2.2 q hq).1 _ (hshift x hx), (hwC2.2 q hq).1 x (hsub hx)]))
          (inv_nonneg.mpr (abs_nonneg h))
        _ = _ := by ring
    · intro x hx y hy
      have hr : dist (iteratedFDeriv ℝ q (differenceQuotient w k h) x)
          (iteratedFDeriv ℝ q (differenceQuotient w k h) y) ≤ (Kh : ℝ) * dist x y ^ (α : ℝ) := by
        rw [hδjet q hq x hx, hδjet q hq y hy, dist_eq_norm, ← smul_sub, norm_smul,
          Real.norm_eq_abs, abs_inv, hKh]
        have hc1 := ((hwC2.2 q hq).2).dist_le (hshift x hx) (hshift y hy)
        have hc2 := ((hwC2.2 q hq).2).dist_le (hsub hx) (hsub hy)
        simp only [shift, dist_add_right] at hc1
        rw [dist_eq_norm] at hc1 hc2
        have heq : (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w x) -
            (iteratedFDeriv ℝ q w (shift k h y) - iteratedFDeriv ℝ q w y) =
            (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w (shift k h y)) -
            (iteratedFDeriv ℝ q w x - iteratedFDeriv ℝ q w y) := by abel
        rw [heq]
        have hn := (norm_sub_le _ _).trans (add_le_add hc1 hc2)
        calc
          _ ≤ |h|⁻¹ * ((M : ℝ) * dist x y ^ (α : ℝ) + (M : ℝ) * dist x y ^ (α : ℝ)) := mul_le_mul_of_nonneg_left hn (by positivity)
          _ = _ := by ring
      simpa only [edist_dist, ENNReal.ofReal_mul Kh.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  have hscalar (g : E2 → ℝ) (hg : PlanarHolderJetBound 1 g B α M) :
      ScalarHolderBound (differenceQuotient g k h) D α M := by
    have hb (x : E2) (hx : x ∈ B) : ‖fderiv ℝ g x‖ ≤ (M : ℝ) := by
      simpa only [norm_iteratedFDeriv_one] using (hg.2 1 (by omega)).1 x hx
    have ht := hFTC g hg.1 hb (hcurry1 g B α M (hg.2 1 (by omega)).2) k h hh hsmall
    have heq : differenceQuotient g k h = fun x => h⁻¹ • (g (shift k h x)-g x) := by
      funext x
      simp only [differenceQuotient, div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [heq]
    simpa only [ScalarHolderBound, Real.norm_eq_abs] using ht
  have hδw0 := hscalar w ⟨hwC2.1.of_le (by norm_num), fun q hq => hwC2.2 q (by omega)⟩
  have hδdu := hFTC (fderiv ℝ w) (hwC2.1.fderiv_of_isOpen hB (by norm_num)) hHessb hHess k h hh hsmall
  have hδder (x : E2) (hx : x ∈ D) : fderiv ℝ (differenceQuotient w k h) x =
      h⁻¹ • (fderiv ℝ w (shift k h x) - fderiv ℝ w x) := by
    let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ)
    have heq := congrArg L (hδjet 1 (by omega) x hx)
    have hL (g : E2 → ℝ) (z : E2) : L (iteratedFDeriv ℝ 1 g z) = fderiv ℝ g z := by
      ext ξ
      simp [L, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    simpa only [map_smul, map_sub, hL] using heq
  have hδlower : PlanarHolderJetBound 1 (differenceQuotient w k h) D α M := by
    refine ⟨hδC2.of_le (by norm_num), ?_⟩
    intro q hq
    interval_cases q
    · constructor
      · intro x hx
        simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hδw0.1 x hx
      · let L := (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm
        have heq (x : E2) : iteratedFDeriv ℝ 0 (differenceQuotient w k h) x = L (differenceQuotient w k h x) := rfl
        intro x hx y hy
        simpa only [heq, L.isometry.edist_eq] using hδw0.2 x hx y hy
    · constructor
      · intro x hx
        simpa only [norm_iteratedFDeriv_one, hδder x hx] using hδdu.1 x hx
      · let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
        have heq (x : E2) : iteratedFDeriv ℝ 1 (differenceQuotient w k h) x = L (fderiv ℝ (differenceQuotient w k h) x) := by
          ext v
          simp [L, iteratedFDeriv_one_apply]
        intro x hx y hy
        simpa only [heq, L.isometry.edist_eq, hδder x hx, hδder y hy] using hδdu.2 x hx y hy
  have hcoeff : PlanarCoefficientControl (shiftedMatrix a k h) D κ Λ H α := by
    constructor
    · intro x hx i j
      exact ha.symmetric _ (hshift x hx) i j
    · intro x hx ξ
      exact ha.coercive _ (hshift x hx) ξ
    · intro x hx i j
      exact ha.bounded _ (hshift x hx) i j
    · intro i j x hx y hy
      simpa only [shiftedMatrix, shift, edist_add_right] using ha.holder i j _ (hshift x hx) _ (hshift y hy)
  have hprod (p q : E2 → ℝ) (hp : ScalarHolderBound p D α M)
      (hq : ScalarHolderBound q D α M) :
      ScalarHolderBound (fun x => p x * q x) D α (2*M*M) := by
    constructor
    · intro x hx
      rw [abs_mul]
      have hn := mul_le_mul (hp.1 x hx) (hq.1 x hx) (abs_nonneg _) M.coe_nonneg
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
      nlinarith [M.coe_nonneg]
    · intro x hx y hy
      have hr : dist (p x * q x) (p y * q y) ≤ (2*M*M : NNReal) * dist x y ^ (α : ℝ) := by
        rw [Real.dist_eq]
        have heq : p x*q x - p y*q y = (p x-p y)*q x + p y*(q x-q y) := by ring
        rw [heq]
        have hpH := hp.2.dist_le hx hy
        have hqH := hq.2.dist_le hx hy
        rw [Real.dist_eq] at hpH hqH
        calc
          _ ≤ |p x-p y| *|q x| + |p y| *|q x-q y| := by
            simpa only [abs_mul] using abs_add_le ((p x-p y)*q x) (p y*(q x-q y))
          _ ≤ ((M : ℝ)*dist x y^(α:ℝ))*(M : ℝ) + (M : ℝ)*((M : ℝ)*dist x y^(α:ℝ)) :=
            add_le_add (mul_le_mul hpH (hq.1 x hx) (abs_nonneg _) (by positivity))
              (mul_le_mul (hp.1 y hy) hqH (abs_nonneg _) M.coe_nonneg)
          _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
      simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  have hessSB (i j : Fin 2) : ScalarHolderBound (fun x => planarHessian w x i j) D α M := by
    have hn (T : E2 →L[ℝ] E2 →L[ℝ] ℝ) : |T (coordinateVector 2 i) (coordinateVector 2 j)| ≤ ‖T‖ := by
      calc
        _ ≤ ‖T (coordinateVector 2 i)‖ * ‖coordinateVector 2 j‖ := by
          simpa only [Real.norm_eq_abs] using (T (coordinateVector 2 i)).le_opNorm (coordinateVector 2 j)
        _ ≤ (‖T‖ * ‖coordinateVector 2 i‖) * ‖coordinateVector 2 j‖ :=
          mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
        _ = ‖T‖ := by rw [he i, he j, mul_one, mul_one]
    constructor
    · intro x hx
      exact (hn _).trans (hHessb x (hsub hx))
    · intro x hx y hy
      have hr : dist (planarHessian w x i j) (planarHessian w y i j) ≤
          (M : ℝ) * dist x y ^ (α : ℝ) := by
        rw [Real.dist_eq]
        have hc := hHess.dist_le (hsub hx) (hsub hy)
        rw [dist_eq_norm] at hc
        have heq : planarHessian w x i j-planarHessian w y i j =
          (fderiv ℝ (fderiv ℝ w) x-fderiv ℝ (fderiv ℝ w) y) (coordinateVector 2 i) (coordinateVector 2 j) := rfl
        rw [heq]
        exact (hn _).trans hc
      simpa only [edist_dist, ENNReal.ofReal_mul M.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  have hP (i j : Fin 2) : ScalarHolderBound
      (fun x => differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j) D α (2*M*M) :=
    hprod _ _ (hscalar _ (haC1 i j)) (hessSB i j)
  have hfinite (Z : Fin 2 → Fin 2 → ℝ) (P : ℝ) (hz : ∀ i j, |Z i j| ≤ P) :
      |∑ i : Fin 2, ∑ j : Fin 2, Z i j| ≤ 4*P := by
    calc
      _ ≤ ∑ i : Fin 2, |∑ j : Fin 2, Z i j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Z i j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, P := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hz i j))
      _ = 4*P := by simp only [Fin.sum_univ_two]; ring
  have hsource : ScalarHolderBound (classicalDifferenceSource a f w k h) D α F := by
    have hf := hscalar f hfC1
    constructor
    · intro x hx
      dsimp [classicalDifferenceSource]
      have hb := hfinite (fun i j => differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)
        (2*M*M : NNReal) (fun i j => (hP i j).1 x hx)
      exact (abs_sub _ _).trans ((add_le_add (hf.1 x hx) hb).trans_eq (by
        simp only [F, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]; ring))
    · intro x hx y hy
      have hr : dist (classicalDifferenceSource a f w k h x) (classicalDifferenceSource a f w k h y) ≤
          (F : ℝ)*dist x y^(α:ℝ) := by
        rw [Real.dist_eq]
        have heq : classicalDifferenceSource a f w k h x-classicalDifferenceSource a f w k h y =
          (differenceQuotient f k h x-differenceQuotient f k h y) -
          ∑ i : Fin 2, ∑ j : Fin 2,
            ((differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)-
             (differenceQuotient (fun y => a y i j) k h y * planarHessian w y i j)) := by
          simp only [classicalDifferenceSource, Fin.sum_univ_two]
          ring
        rw [heq]
        have hb := hfinite
          (fun i j => (differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)-
            (differenceQuotient (fun y => a y i j) k h y * planarHessian w y i j))
          ((2*M*M : NNReal)*dist x y^(α:ℝ)) (fun i j => by
            simpa only [Real.dist_eq] using ((hP i j).2).dist_le hx hy)
        have hfH := hf.2.dist_le hx hy
        rw [Real.dist_eq] at hfH
        exact (abs_sub _ _).trans ((add_le_add hfH hb).trans_eq (by
          simp only [F, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]; ring))
      simpa only [edist_dist, ENNReal.ofReal_mul F.coe_nonneg,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
  obtain ⟨K', hK', hv⟩ := hest x₀ _ hcoeff _ _ F M Kh hsource hδlower hδindividual
    (R5_linear_difference_equation x₀ R hR a f w hwC2.1 heq k h hh hsmall)
  have hKC : K' ≤ C := NNReal.coe_le_coe.mp (hK'.trans (Real.le_coe_toNNReal _))
  exact ⟨hv.1, fun q hq => ⟨fun x hx => ((hv.2 q hq).1 x hx).trans (NNReal.coe_le_coe.mpr hKC),
    ((hv.2 q hq).2).mono_const hKC⟩⟩

set_option maxHeartbeats 2000000 in
/-- Uniform bounds on actual difference Hessians recover C3,alpha/2 of
the same w. Only the already C2 jet is an input. -/
theorem R5_difference_limit_C3
    (x₀ : E2) (R : ℝ) (hR : 0 < R) (w : E2 → ℝ) (α M C : NNReal)
    (hα : 0 < α) (hαone : α < 1)
    (hwC2 : PlanarHolderJetBound 2 w (Metric.ball x₀ (2 * R)) α M)
    (hdifference : ∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < R →
      PlanarHolderJetBound 2 (differenceQuotient w k h) (Metric.ball x₀ R) α C) :
    ∃ K : NNReal,
      PlanarHolderJetBound 3 w (Metric.ball x₀ (R / 2)) (α / 2) K := by
  classical
  let actualSecondJet (v : E2 → ℝ) (x : E2) : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ v) x
  let differenceLimitStep (R : ℝ) (n : ℕ) : ℝ := R / ((n:ℝ)+2)
  have hcompact
      {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      (K : Set E2) (hK : IsCompact K) (α M : NNReal) (hα : 0 < α)
      (g : ℕ → K → F) (hcontinuous : ∀ n, Continuous (g n))
      (hnorm : ∀ n x, ‖g n x‖ ≤ (M : ℝ))
      (hholder : ∀ n, HolderWith M α (g n)) :
      ∃ (σ : ℕ → ℕ) (G : K → F), StrictMono σ ∧
        TendstoUniformly (fun n => g (σ n)) G atTop ∧ Continuous G ∧
        (∀ x, ‖G x‖ ≤ (M : ℝ)) ∧ HolderWith M α G := by
    classical
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let f : ℕ → BoundedContinuousFunction K F := fun n =>
      BoundedContinuousFunction.mkOfCompact ⟨g n, hcontinuous n⟩
    have hequi : Equicontinuous (fun n x => f n x) := by
      apply Metric.equicontinuous_of_continuity_modulus
        (fun d : ℝ => (M : ℝ) * |d| ^ (α : ℝ))
      · have hp : ContinuousAt (fun d : ℝ => |d| ^ (α : ℝ)) 0 :=
          (continuous_abs.continuousAt).rpow_const (Or.inr (by exact_mod_cast hα.le))
        have hn : (α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
        have ht : Tendsto (fun d : ℝ => |d| ^ (α : ℝ)) (𝓝 0) (𝓝 0) := by
          simpa only [abs_zero, Real.zero_rpow hn] using hp.tendsto
        simpa only [mul_zero] using ht.const_mul (M : ℝ)
      · intro x y n
        simpa only [f, BoundedContinuousFunction.mkOfCompact_apply,
          ContinuousMap.coe_mk, abs_of_nonneg dist_nonneg] using (hholder n).dist_le x y
    have hc : IsCompact (closure (range f)) :=
      BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : F) (M : ℝ))
        (isCompact_closedBall _ _) (range f)
        (by rintro _ x ⟨n, rfl⟩; simpa only [f, BoundedContinuousFunction.mkOfCompact_apply,
          ContinuousMap.coe_mk, Metric.mem_closedBall, dist_zero_right] using hnorm n x)
        (by
          convert hequi.comp (fun n : range f => n.property.choose) using 1
          funext n x
          exact congrArg (fun u : BoundedContinuousFunction K F => u x) n.property.choose_spec.symm)
    obtain ⟨G, _, σ, hσ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
    have hunif : TendstoUniformly (fun n => g (σ n)) G atTop :=
      BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim
    have hpoint (x : K) : Tendsto (fun n => g (σ n) x) atTop (𝓝 (G x)) := hunif.tendsto_at x
    refine ⟨σ, G, hσ, hunif, G.continuous, ?_, ?_⟩
    · intro x
      exact le_of_tendsto ((hpoint x).norm) (Filter.Eventually.of_forall (fun n => hnorm (σ n) x))
    · intro x y
      have hbound : dist (G x) (G y) ≤ (M : ℝ) * dist x y ^ (α : ℝ) :=
        le_of_tendsto ((hpoint x).dist (hpoint y))
          (Filter.Eventually.of_forall (fun n => (hholder (σ n)).dist_le x y))
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul M.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal hbound
  have hlimits
      (x₀ : E2) (R : ℝ) (hR : 0 < R) (w : E2 → ℝ) (α M C : NNReal)
      (hα : 0 < α) (hαone : α < 1)
      (hw : PlanarHolderJetBound 2 w (Metric.ball x₀ (2 * R)) α M)
      (hdifference : ∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < R →
        PlanarHolderJetBound 2 (differenceQuotient w k h) (Metric.ball x₀ R) α C) :
      ∃ (σ : ℕ → ℕ) (z : Fin 2 → E2 → ℝ)
        (d : Fin 2 → E2 → (E2 →L[ℝ] ℝ))
        (d2 : Fin 2 → E2 → (E2 →L[ℝ] E2 →L[ℝ] ℝ)),
        StrictMono σ ∧
        (∀ k, TendstoUniformlyOn (fun n => differenceQuotient w k (differenceLimitStep R (σ n)))
          (z k) atTop (Metric.closedBall x₀ (3*R/4))) ∧
        (∀ k, TendstoUniformlyOn (fun n => fderiv ℝ (differenceQuotient w k (differenceLimitStep R (σ n))))
          (d k) atTop (Metric.closedBall x₀ (3*R/4))) ∧
        (∀ k, TendstoUniformlyOn (fun n => actualSecondJet (differenceQuotient w k (differenceLimitStep R (σ n))))
          (d2 k) atTop (Metric.closedBall x₀ (3*R/4))) ∧
        (∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖z k x‖ ≤ (C:ℝ)) ∧
        (∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖d k x‖ ≤ (C:ℝ)) ∧
        (∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖d2 k x‖ ≤ (C:ℝ)) ∧
        (∀ k, HolderOnWith C α (z k) (Metric.closedBall x₀ (3*R/4))) ∧
        (∀ k, HolderOnWith C α (d k) (Metric.closedBall x₀ (3*R/4))) ∧
        (∀ k, HolderOnWith C α (d2 k) (Metric.closedBall x₀ (3*R/4))) := by
    classical
    let K : Set E2 := Metric.closedBall x₀ (3 * R / 4)
    have hKB : K ⊆ Metric.ball x₀ R := by
      intro x hx
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith)
    let v : ℕ → Fin 2 → E2 → ℝ := fun n k =>
      differenceQuotient w k (differenceLimitStep R n)
    have hstep (n : ℕ) : 0 < |differenceLimitStep R n| ∧ |differenceLimitStep R n| < R := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hp : 0 < differenceLimitStep R n := div_pos hR (by positivity)
      rw [abs_of_pos hp]
      refine ⟨hp, ?_⟩
      change R / ((n : ℝ) + 2) < R
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hjet (n : ℕ) (k : Fin 2) :
        PlanarHolderJetBound 2 (v n k) (Metric.ball x₀ R) α C :=
      hdifference k _ (hstep n).1 (hstep n).2
    let I₁ := continuousMultilinearCurryFin1 ℝ E2 ℝ
    let I₂ := (continuousMultilinearCurryFin1 ℝ E2 ℝ).toLinearIsometry.postcomp.comp
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E2) ℝ).toLinearIsometry
    have hI₁ (f : E2 → ℝ) (x : E2) : I₁ (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
      ext ξ
      simp [I₁,iteratedFDeriv_one_apply]
    have hI₂ (f : E2 → ℝ) (x : E2) : I₂ (iteratedFDeriv ℝ 2 f x) = actualSecondJet f x := by
      ext ξ η
      change (continuousMultilinearCurryFin1 ℝ E2 ℝ)
        ((iteratedFDeriv ℝ 2 f x).curryLeft ξ) η = _
      simp only [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply,
        iteratedFDeriv_two_apply,Fin.cons_zero,actualSecondJet]
      rfl
    let F := Fin 2 → ℝ × (E2 →L[ℝ] ℝ) × (E2 →L[ℝ] E2 →L[ℝ] ℝ)
    let g : ℕ → K → F := fun n x k =>
      (v n k x, fderiv ℝ (v n k) x, actualSecondJet (v n k) x)
    have hgcont (n : ℕ) : Continuous (g n) := by
      apply continuous_pi
      intro k
      have hv := (hjet n k).1
      have hz := hv.continuousOn.mono hKB
      have hf := (hv.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).mono hKB
      have hd : ContDiffOn ℝ 1 (fderiv ℝ (v n k)) (Metric.ball x₀ R) :=
        hv.fderiv_of_isOpen Metric.isOpen_ball (by norm_num)
      have hs := (hd.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).mono hKB
      exact hz.restrict.prodMk (hf.restrict.prodMk hs.restrict)
    have hgBound (n : ℕ) (x : K) : ‖g n x‖ ≤ (C : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg C.coe_nonneg).mpr
      intro k
      rw [Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff]
      refine ⟨?_,?_,?_⟩
      · simpa only [norm_iteratedFDeriv_zero] using ((hjet n k).2 0 (by omega)).1 x (hKB x.property)
      · change ‖fderiv ℝ (v n k) x‖ ≤ _
        rw [← hI₁,I₁.norm_map]
        exact ((hjet n k).2 1 (by omega)).1 x (hKB x.property)
      · change ‖actualSecondJet (v n k) x‖ ≤ _
        rw [← hI₂,I₂.norm_map]
        exact ((hjet n k).2 2 (by omega)).1 x (hKB x.property)
    have hgholder (n : ℕ) : HolderWith C α (g n) := by
      intro x y
      apply edist_pi_le_iff.mpr
      intro k
      simp only [g,Prod.edist_eq,max_le_iff]
      refine ⟨?_,?_,?_⟩
      · simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
          (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq,
          Subtype.edist_eq] using ((hjet n k).2 0 (by omega)).2 x (hKB x.property) y (hKB y.property)
      · simpa only [← hI₁,I₁.isometry.edist_eq,Subtype.edist_eq] using
          ((hjet n k).2 1 (by omega)).2 x (hKB x.property) y (hKB y.property)
      · simpa only [← hI₂,I₂.isometry.edist_eq,Subtype.edist_eq] using
          ((hjet n k).2 2 (by omega)).2 x (hKB x.property) y (hKB y.property)
    obtain ⟨σ,G,hσ,hlim,hGcont,hGb,hGh⟩ := hcompact K
      (isCompact_closedBall _ _) α C hα g hgcont hgBound hgholder
    let GG : E2 → F := fun x => if hx : x ∈ K then G ⟨x,hx⟩ else 0
    have hGG (x : K) : GG x = G x := dif_pos x.property
    let p0 : F → Fin 2 → ℝ := fun z k => (z k).1
    let p1 : F → Fin 2 → (E2 →L[ℝ] ℝ) := fun z k => (z k).2.1
    let p2 : F → Fin 2 → (E2 →L[ℝ] E2 →L[ℝ] ℝ) := fun z k => (z k).2.2
    have hl0 (k : Fin 2) : TendstoUniformlyOn (fun n => v (σ n) k)
        (fun x => p0 (GG x) k) atTop K := by
      apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      have huc : UniformContinuous (fun z : F => (z k).1) :=
        uniformContinuous_fst.comp (uniformContinuous_pi.mp uniformContinuous_id k)
      simpa only [Function.comp_def,g,p0,hGG] using huc.comp_tendstoUniformly hlim
    have hl1 (k : Fin 2) : TendstoUniformlyOn (fun n => fderiv ℝ (v (σ n) k))
        (fun x => p1 (GG x) k) atTop K := by
      apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      have huc : UniformContinuous (fun z : F => (z k).2.1) :=
        uniformContinuous_fst.comp (uniformContinuous_snd.comp
          (uniformContinuous_pi.mp uniformContinuous_id k))
      simpa only [Function.comp_def,g,p1,hGG] using huc.comp_tendstoUniformly hlim
    have hl2 (k : Fin 2) : TendstoUniformlyOn (fun n => actualSecondJet (v (σ n) k))
        (fun x => p2 (GG x) k) atTop K := by
      apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
      have huc : UniformContinuous (fun z : F => (z k).2.2) :=
        uniformContinuous_snd.comp (uniformContinuous_snd.comp
          (uniformContinuous_pi.mp uniformContinuous_id k))
      simpa only [Function.comp_def,g,p2,hGG] using huc.comp_tendstoUniformly hlim
    have hbounds (k : Fin 2) (x : E2) (hx : x ∈ K) :
        ‖p0 (GG x) k‖ ≤ (C : ℝ) ∧ ‖p1 (GG x) k‖ ≤ (C : ℝ) ∧ ‖p2 (GG x) k‖ ≤ (C : ℝ) := by
      have hh := (pi_norm_le_iff_of_nonneg C.coe_nonneg).mp (hGb ⟨x,hx⟩) k
      simpa only [p0,p1,p2,show GG x = G ⟨x,hx⟩ from dif_pos hx,Prod.norm_def,
        max_le_iff] using hh
    have hholders (k : Fin 2) : HolderOnWith C α (fun x => p0 (GG x) k) K ∧
        HolderOnWith C α (fun x => p1 (GG x) k) K ∧
        HolderOnWith C α (fun x => p2 (GG x) k) K := by
      have hh (x : E2) (hx : x ∈ K) (y : E2) (hy : y ∈ K) :
          edist (p0 (GG x) k) (p0 (GG y) k) ≤ (C : ENNReal) * edist x y ^ (α : ℝ) ∧
          edist (p1 (GG x) k) (p1 (GG y) k) ≤ (C : ENNReal) * edist x y ^ (α : ℝ) ∧
          edist (p2 (GG x) k) (p2 (GG y) k) ≤ (C : ENNReal) * edist x y ^ (α : ℝ) := by
        simpa only [p0,p1,p2,show GG x = G ⟨x,hx⟩ from dif_pos hx,
          show GG y = G ⟨y,hy⟩ from dif_pos hy,Prod.edist_eq,max_le_iff,Subtype.edist_eq] using
          (edist_pi_le_iff.mp (hGh ⟨x,hx⟩ ⟨y,hy⟩)) k
      constructor
      · intro x hx y hy
        exact (hh x hx y hy).1
      constructor
      · intro x hx y hy
        exact (hh x hx y hy).2.1
      · intro x hx y hy
        exact (hh x hx y hy).2.2
    exact ⟨σ, (fun k x => p0 (GG x) k), (fun k x => p1 (GG x) k),
      (fun k x => p2 (GG x) k), hσ, hl0, hl1, hl2,
      (fun k x hx => (hbounds k x hx).1),
      (fun k x hx => (hbounds k x hx).2.1),
      (fun k x hx => (hbounds k x hx).2.2),
      (fun k => (hholders k).1), (fun k => (hholders k).2.1), (fun k => (hholders k).2.2)⟩
  have hidentify
      (x₀ : E2) (R : ℝ) (hR : 0 < R) (w : E2 → ℝ) (α M C : NNReal)
      (hα : 0 < α) (hαone : α < 1)
      (hw : PlanarHolderJetBound 2 w (Metric.ball x₀ (2 * R)) α M)
      (σ : ℕ → ℕ) (hσ : StrictMono σ)
      (zeroField : Fin 2 → E2 → ℝ)
      (firstField : Fin 2 → E2 → (E2 →L[ℝ] ℝ))
      (secondField : Fin 2 → E2 → (E2 →L[ℝ] E2 →L[ℝ] ℝ))
      (zeroLimit : ∀ k, TendstoUniformlyOn (fun n => differenceQuotient w k (differenceLimitStep R (σ n)))
        (zeroField k) atTop (Metric.closedBall x₀ (3*R/4)))
      (firstLimit : ∀ k, TendstoUniformlyOn (fun n => fderiv ℝ (differenceQuotient w k (differenceLimitStep R (σ n))))
        (firstField k) atTop (Metric.closedBall x₀ (3*R/4)))
      (secondLimit : ∀ k, TendstoUniformlyOn (fun n => actualSecondJet (differenceQuotient w k (differenceLimitStep R (σ n))))
        (secondField k) atTop (Metric.closedBall x₀ (3*R/4)))
      (zeroBound : ∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖zeroField k x‖ ≤ (C:ℝ))
      (firstBound : ∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖firstField k x‖ ≤ (C:ℝ))
      (secondBound : ∀ k x, x ∈ Metric.closedBall x₀ (3*R/4) → ‖secondField k x‖ ≤ (C:ℝ))
      (zeroHolder : ∀ k, HolderOnWith C α (zeroField k) (Metric.closedBall x₀ (3*R/4)))
      (firstHolder : ∀ k, HolderOnWith C α (firstField k) (Metric.closedBall x₀ (3*R/4)))
      (secondHolder : ∀ k, HolderOnWith C α (secondField k) (Metric.closedBall x₀ (3*R/4))) :
      ∀ k : Fin 2,
        (∀ x ∈ Metric.ball x₀ (3 * R / 4),
          zeroField k x = scalarPartial w k x ∧
          HasFDerivAt (scalarPartial w k) (firstField k x) x ∧
          HasFDerivAt (firstField k) (secondField k x) x ∧
          firstField k x = fderiv ℝ (scalarPartial w k) x ∧
          secondField k x = actualSecondJet (scalarPartial w k) x) ∧
        PlanarHolderJetBound 2 (scalarPartial w k)
          (Metric.ball x₀ (3 * R / 4)) α C := by
    classical
    let U := Metric.ball x₀ (3 * R / 4)
    let K := Metric.closedBall x₀ (3 * R / 4)
    have hUK : U ⊆ K := Metric.ball_subset_closedBall
    have hU2 : U ⊆ Metric.ball x₀ (2 * R) := by
      apply Metric.ball_subset_ball
      linarith
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hstep0 : Tendsto (fun n => differenceLimitStep R n) atTop (𝓝 0) := by
      have hh := (tendsto_const_div_atTop_nhds_zero_nat R).comp (tendsto_add_atTop_nat 2)
      simpa only [differenceLimitStep,Function.comp_def,Nat.cast_add,Nat.cast_ofNat] using hh
    have hstep (n : ℕ) : 0 < differenceLimitStep R n ∧ differenceLimitStep R n < R := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hp : 0 < differenceLimitStep R n := div_pos hR (by positivity)
      refine ⟨hp,?_⟩
      change R / ((n : ℝ) + 2) < R
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have hsteps : Tendsto (fun n => differenceLimitStep R (σ n)) atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hstep0.comp hσ.tendsto_atTop,?_⟩
      exact Filter.Eventually.of_forall (fun n => (hstep (σ n)).1.ne')
    intro k
    let v : ℕ → E2 → ℝ := fun n => differenceQuotient w k (differenceLimitStep R (σ n))
    have hzero (x : E2) (hx : x ∈ U) :
        Tendsto (fun n => v n x) atTop (𝓝 (scalarPartial w k x)) := by
      have hd := (hw.1.contDiffAt (Metric.isOpen_ball.mem_nhds (hU2 hx))).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      have hl : HasDerivAt (fun t : ℝ => w (x + t • coordinateVector 2 k))
          (fderiv ℝ w x (coordinateVector 2 k)) 0 := by
        have ht : HasDerivAt (fun t : ℝ => x + t • coordinateVector 2 k) (coordinateVector 2 k) 0 := by
          convert ((hasDerivAt_const (0 : ℝ) x).add
              ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector 2 k))) using 1 <;>
            ext i <;> simp
        have hh : HasFDerivAt w (fderiv ℝ w x) (x + (0 : ℝ) • coordinateVector 2 k) := by
          simpa using hd.hasFDerivAt
        exact hh.comp_hasDerivAt 0 ht
      simpa only [v,differenceQuotient,shift,scalarPartial,Function.comp_def,zero_add,
        zero_smul,add_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using hl.tendsto_slope_zero.comp hsteps
    have hzEq (x : E2) (hx : x ∈ U) : zeroField k x = scalarPartial w k x :=
      tendsto_nhds_unique ((zeroLimit k).tendsto_at (hUK hx)) (hzero x hx)
    have hv (n : ℕ) : ContDiffOn ℝ 2 (v n) U := by
      have hh : |differenceLimitStep R (σ n)| < R := by
        rw [abs_of_pos (hstep _).1]
        exact (hstep _).2
      have hs : MapsTo (shift k (differenceLimitStep R (σ n))) U
          (Metric.ball x₀ (2 * R)) := by
        intro x hx
        rw [Metric.mem_ball] at hx ⊢
        have he : ‖coordinateVector 2 k‖ = 1 := by
          simp [coordinateVector,EuclideanSpace.single,PiLp.norm_single]
        calc
          dist (shift k (differenceLimitStep R (σ n)) x) x₀ ≤
              dist (shift k (differenceLimitStep R (σ n)) x) x + dist x x₀ :=
            dist_triangle _ _ _
          _ = |differenceLimitStep R (σ n)| + dist x x₀ := by
            simp only [shift,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,he,mul_one]
          _ < 2 * R := by linarith
      have hc : ContDiffOn ℝ 2 (shift k (differenceLimitStep R (σ n))) U := by
        unfold shift
        fun_prop
      exact (((hw.1.comp hc hs).sub (hw.1.mono hU2)).div_const _)
    have hfirst (x : E2) (hx : x ∈ U) : HasFDerivAt (scalarPartial w k) (firstField k x) x :=
      hasFDerivAt_of_tendstoUniformlyOn hUopen ((firstLimit k).mono hUK)
        (fun n y hy => ((hv n).contDiffAt (hUopen.mem_nhds hy)).differentiableAt
          (by norm_num : (2 : WithTop ℕ∞) ≠ 0) |>.hasFDerivAt) hzero hx
    have hsecond (x : E2) (hx : x ∈ U) : HasFDerivAt (firstField k) (secondField k x) x :=
      hasFDerivAt_of_tendstoUniformlyOn hUopen ((secondLimit k).mono hUK)
        (fun n y hy =>
          have hd : ContDiffOn ℝ 1 (fderiv ℝ (v n)) U :=
            (hv n).fderiv_of_isOpen hUopen (by norm_num)
          ((hd.contDiffAt (hUopen.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt)
        (fun y hy => (firstLimit k).tendsto_at (hUK hy)) hx
    have hfEq (x : E2) (hx : x ∈ U) : firstField k x = fderiv ℝ (scalarPartial w k) x :=
      (hfirst x hx).fderiv.symm
    have hsEq (x : E2) (hx : x ∈ U) : secondField k x = actualSecondJet (scalarPartial w k) x := by
      have he : firstField k =ᶠ[𝓝 x] fderiv ℝ (scalarPartial w k) :=
        Filter.eventuallyEq_of_mem (hUopen.mem_nhds hx) hfEq
      exact (hsecond x hx).fderiv.symm.trans (he.fderiv_eq)
    have hp1 : ContDiffOn ℝ 1 (firstField k) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (𝕜 := ℝ)
        (n := (0 : WithTop ℕ∞)) hUopen.uniqueDiffOn).mpr
      refine ⟨by norm_num,secondField k,contDiffOn_zero.mpr ((secondHolder k).continuousOn hα |>.mono hUK),?_⟩
      intro x hx
      exact (hsecond x hx).hasFDerivWithinAt
    have hc2 : ContDiffOn ℝ 2 (scalarPartial w k) U := by
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (𝕜 := ℝ)
        (n := (1 : WithTop ℕ∞)) hUopen.uniqueDiffOn).mpr
      refine ⟨by norm_num,firstField k,hp1,?_⟩
      intro x hx
      exact (hfirst x hx).hasFDerivWithinAt
    constructor
    · intro x hx
      exact ⟨hzEq x hx,hfirst x hx,hsecond x hx,hfEq x hx,hsEq x hx⟩
    · refine ⟨hc2,?_⟩
      let I₁ := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
      let I₂ := (continuousMultilinearCurryFin1 ℝ E2 ℝ).toLinearIsometry.postcomp.comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E2) ℝ).toLinearIsometry
      have hI₁ (x : E2) : iteratedFDeriv ℝ 1 (scalarPartial w k) x = I₁ (fderiv ℝ (scalarPartial w k) x) := by
        ext ξ
        simp [I₁,iteratedFDeriv_one_apply]
      have hI₂ (x : E2) : I₂ (iteratedFDeriv ℝ 2 (scalarPartial w k) x) = actualSecondJet (scalarPartial w k) x := by
        ext ξ η
        change (continuousMultilinearCurryFin1 ℝ E2 ℝ)
          ((iteratedFDeriv ℝ 2 (scalarPartial w k) x).curryLeft ξ) η = _
        simp only [continuousMultilinearCurryFin1_apply,ContinuousMultilinearMap.curryLeft_apply,
          iteratedFDeriv_two_apply,Fin.cons_zero,actualSecondJet]
        rfl
      intro q hq
      interval_cases q
      · constructor
        · intro x hx
          rw [norm_iteratedFDeriv_zero,← hzEq x hx]
          exact zeroBound k x (hUK hx)
        · intro x hx y hy
          simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
            (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq,hzEq x hx,hzEq y hy] using
            zeroHolder k x (hUK hx) y (hUK hy)
      · constructor
        · intro x hx
          rw [hI₁,I₁.norm_map,← hfEq x hx]
          exact firstBound k x (hUK hx)
        · intro x hx y hy
          simpa only [hI₁,I₁.isometry.edist_eq,hfEq x hx,hfEq y hy] using
            firstHolder k x (hUK hx) y (hUK hy)
      · constructor
        · intro x hx
          rw [← I₂.norm_map (iteratedFDeriv ℝ 2 (scalarPartial w k) x),hI₂,← hsEq x hx]
          exact secondBound k x (hUK hx)
        · intro x hx y hy
          rw [← I₂.isometry.edist_eq,hI₂,hI₂,← hsEq x hx,← hsEq y hy]
          exact secondHolder k x (hUK hx) y (hUK hy)
  have hreconstruct
      (x₀ : E2) (R : ℝ) (hR : 0 < R) (w : E2 → ℝ) (α M C : NNReal)
      (hα : 0 < α) (hαone : α < 1)
      (hw : PlanarHolderJetBound 2 w (Metric.ball x₀ (2 * R)) α M)
      (hpartials : ∀ k : Fin 2, PlanarHolderJetBound 2 (scalarPartial w k)
        (Metric.ball x₀ (3 * R / 4)) α C) :
      ContDiffOn ℝ 3 w (Metric.ball x₀ (3 * R / 4)) ∧
        (∀ x ∈ Metric.ball x₀ (3 * R / 4), ∀ ξ : Fin 3 → E2,
          iteratedFDeriv ℝ 3 w x ξ =
            ∑ k : Fin 2, ξ 2 k * actualSecondJet (scalarPartial w k) x (ξ 0) (ξ 1)) ∧
        ∃ K : NNReal, PlanarHolderJetBound 3 w (Metric.ball x₀ (R / 2)) (α / 2) K := by
    classical
    let U := Metric.ball x₀ (3 * R / 4)
    let B := Metric.ball x₀ (R / 2)
    have hU : IsOpen U := Metric.isOpen_ball
    have hUB : U ⊆ Metric.ball x₀ (2 * R) := Metric.ball_subset_ball (by linarith)
    have hBU : B ⊆ U := Metric.ball_subset_ball (by linarith)
    have hrep (x y : E2) : fderiv ℝ w x y = ∑ k : Fin 2, y k * scalarPartial w k x := by
      have hy : y = y 0 • coordinateVector 2 0 + y 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector]
      conv_lhs => rw [hy]
      simp [Fin.sum_univ_two, scalarPartial]
    have hd2 : ContDiffOn ℝ 2 (fderiv ℝ w) U := by
      apply contDiffOn_clm_apply.mpr
      intro y
      exact (ContDiffOn.sum (fun k _ => contDiffOn_const.mul (hpartials k).1)).congr
        (fun x _ => hrep x y)
    have hc3 : ContDiffOn ℝ 3 w U := by
      apply (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := (2 : WithTop ℕ∞)) hU).mpr
      exact ⟨(hw.1.mono hUB).differentiableOn (by norm_num), by norm_num, hd2⟩
    have hthird (x : E2) (hx : x ∈ U) (ξ : Fin 3 → E2) :
        iteratedFDeriv ℝ 3 w x ξ =
          ∑ k : Fin 2, ξ 2 k * actualSecondJet (scalarPartial w k) x (ξ 0) (ξ 1) := by
      let e : (E2 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (ξ 2)
      have he := e.iteratedFDeriv_comp_left ((hd2 x hx).contDiffAt (hU.mem_nhds hx)) (i := 2) (by norm_num)
      rw [iteratedFDeriv_succ_apply_right]
      change (e.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 (fderiv ℝ w) x)) (Fin.init ξ) = _
      rw [← he]
      have hfun : e ∘ fderiv ℝ w = fun z => ∑ k : Fin 2, ξ 2 k * scalarPartial w k z :=
        funext (fun z => hrep z (ξ 2))
      rw [hfun, iteratedFDeriv_fun_sum_apply (fun k _ =>
        contDiffAt_const.mul (((hpartials k).1 x hx).contDiffAt (hU.mem_nhds hx))),
        ContinuousMultilinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [show (fun z => ξ 2 k * scalarPartial w k z) = ξ 2 k • scalarPartial w k from rfl,
        iteratedFDeriv_const_smul_apply (((hpartials k).1 x hx).contDiffAt (hU.mem_nhds hx))]
      simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul,
        iteratedFDeriv_two_apply, actualSecondJet, Fin.init, Fin.castSucc_zero, Fin.castSucc_one]
    have hestimate (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E2) ℝ)
        (b : Fin 2 → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E2) ℝ)
        (D : ℝ) (hD : 0 ≤ D) (hb : ∀ k, ‖b k‖ ≤ D)
        (ht : ∀ ξ, T ξ = ∑ k : Fin 2, ξ 2 k * b k (Fin.init ξ)) : ‖T‖ ≤ 2 * D := by
      apply T.opNorm_le_bound (by positivity)
      intro ξ
      rw [ht]
      calc
        ‖∑ k : Fin 2, ξ 2 k * b k (Fin.init ξ)‖ ≤ ∑ k : Fin 2, ‖ξ 2 k * b k (Fin.init ξ)‖ := norm_sum_le _ _
        _ ≤ ∑ _k : Fin 2, ‖ξ 2‖ * (D * (‖ξ 0‖ * ‖ξ 1‖)) := by
          apply Finset.sum_le_sum
          intro k _
          rw [norm_mul]
          apply mul_le_mul (PiLp.norm_apply_le (ξ 2) k)
          · simpa [Fin.prod_univ_two, Fin.init] using
              ((b k).le_opNorm (Fin.init ξ)).trans
                (mul_le_mul_of_nonneg_right (hb k) (by positivity))
          · exact norm_nonneg _
          · positivity
        _ = (2 * D) * ∏ i : Fin 3, ‖ξ i‖ := by simp [Fin.sum_univ_two, Fin.prod_univ_three]; ring
    have hn3 (x : E2) (hx : x ∈ U) : ‖iteratedFDeriv ℝ 3 w x‖ ≤ ((2 * C : NNReal) : ℝ) := by
      apply hestimate _ (fun k => iteratedFDeriv ℝ 2 (scalarPartial w k) x) C C.coe_nonneg
        (fun k => ((hpartials k).2 2 le_rfl).1 x hx)
      intro ξ
      simpa only [iteratedFDeriv_two_apply, actualSecondJet, Fin.init, Fin.castSucc_zero, Fin.castSucc_one] using hthird x hx ξ
    have hh3 : HolderOnWith (2 * C) α (iteratedFDeriv ℝ 3 w) U := by
      intro x hx y hy
      have hb (k : Fin 2) : ‖iteratedFDeriv ℝ 2 (scalarPartial w k) x - iteratedFDeriv ℝ 2 (scalarPartial w k) y‖ ≤
          (C : ℝ) * dist x y ^ (α : ℝ) := by
        simpa only [dist_eq_norm] using (((hpartials k).2 2 le_rfl).2.dist_le hx hy)
      have ht : ‖iteratedFDeriv ℝ 3 w x - iteratedFDeriv ℝ 3 w y‖ ≤
          2 * ((C : ℝ) * dist x y ^ (α : ℝ)) := by
        apply hestimate _ (fun k => iteratedFDeriv ℝ 2 (scalarPartial w k) x -
          iteratedFDeriv ℝ 2 (scalarPartial w k) y) _ (by positivity) hb
        intro ξ
        simp only [ContinuousMultilinearMap.sub_apply, hthird x hx, hthird y hy,
          iteratedFDeriv_two_apply, actualSecondJet, Fin.init, Fin.castSucc_zero, Fin.castSucc_one, mul_sub, Finset.sum_sub_distrib]
      rw [edist_dist, dist_eq_norm, edist_dist,
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (2 * C).coe_nonneg]
      apply ENNReal.ofReal_le_ofReal
      simpa only [NNReal.coe_mul, NNReal.coe_ofNat, mul_assoc] using ht
    let D : NNReal := Real.toNNReal R + 1
    let K : NNReal := (M + 2 * C) * (1 + D ^ ((α : ℝ) - ((α / 2 : NNReal) : ℝ)))
    have hdiam : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ D := by
      intro x hx y hy
      have hr : dist x y ≤ R := by
        have hx' := Metric.mem_ball.mp hx
        have hy' := Metric.mem_ball.mp hy
        calc
          dist x y ≤ dist x x₀ + dist y x₀ := dist_triangle_right _ _ _
          _ ≤ R := by linarith
      rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      apply hr.trans
      dsimp only [D]
      simp only [NNReal.coe_add, Real.coe_toNNReal R hR.le, NNReal.coe_one]
      linarith
    have hMK : M ≤ K := calc
      M ≤ M + 2 * C := le_add_of_nonneg_right (by positivity)
      _ ≤ K := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity))
    have hCK : 2 * C ≤ K := calc
      2 * C ≤ M + 2 * C := le_add_of_nonneg_left (by positivity)
      _ ≤ K := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity))
    have hcost (A : NNReal) (hA : A ≤ M + 2 * C) :
        A * D ^ ((α : ℝ) - ((α / 2 : NNReal) : ℝ)) ≤ K := by
      exact mul_le_mul hA (le_add_of_nonneg_left (by positivity)) (by positivity) (by positivity)
    have hexp : α / 2 ≤ α := div_le_self (by positivity) (by norm_num)
    refine ⟨hc3, hthird, K, hc3.mono hBU, ?_⟩
    intro q hq
    by_cases hq2 : q ≤ 2
    · refine ⟨fun x hx => (((hw.2 q hq2).1 x (hUB (hBU hx))).trans (by exact_mod_cast hMK)), ?_⟩
      exact (((hw.2 q hq2).2.mono (hBU.trans hUB)).of_le hdiam hexp).mono_const
        (hcost M (le_add_of_nonneg_right (by positivity)))
    · have hq3 : q = 3 := by omega
      subst q
      refine ⟨fun x hx => (hn3 x (hBU hx)).trans (by exact_mod_cast hCK), ?_⟩
      exact ((hh3.mono hBU).of_le hdiam hexp).mono_const
        (hcost (2 * C) (le_add_of_nonneg_left (by positivity)))
  obtain ⟨σ,z,d,d2,hσ,hz,hd,hd2,hzb,hdb,hd2b,hzh,hdh,hd2h⟩ :=
    hlimits x₀ R hR w α M C hα hαone hwC2 hdifference
  have hpartials : ∀ k : Fin 2, PlanarHolderJetBound 2 (scalarPartial w k)
      (Metric.ball x₀ (3*R/4)) α C := fun k =>
    (hidentify x₀ R hR w α M C hα hαone hwC2 σ hσ z d d2 hz hd hd2 hzb hdb hd2b hzh hdh hd2h k).2
  exact (hreconstruct x₀ R hR w α M C hα hαone hwC2 hpartials).2.2

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- Concrete m=2 nonlinear input: compose the actual first jet with smooth
Q and obtain C1,alpha principal coefficients/source. Finite differences
are C2,alpha individually; their source and lower jets have common bounds. -/
theorem R5_m2_difference_data
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ)
    (x₀ : E2) (R κ M : ℝ) (hR : 0 < R) (T : Set Jet)
    (hball : Metric.closedBall x₀ (4 * R) ⊆ Ω)
    (hT : Convex ℝ T) (hTJ : closure T ⊆ J)
    (hTcompact : IsCompact (closure T))
    (hjetsT : ∀ x ∈ Metric.closedBall x₀ (4 * R), firstJet u x ∈ T)
    (hbound : JetTubeBounds Q u x₀ R κ M T)
    (α K : NNReal) (hα : 0 < α) (hαone : α < 1)
    (hu : PlanarHolderJetBound 2 u (Metric.ball x₀ (4 * R)) α K)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R))
      (principalMatrix Q u) (classicalSource Q u) u) :
    ∃ Λ : ℝ, ∃ H U F : NNReal, κ ≤ Λ ∧
      (∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < R →
        PlanarCoefficientControl (shiftedMatrix (principalMatrix Q u) k h)
          (Metric.ball x₀ (2 * R)) κ Λ H α ∧
        LinearClassicalEquation (Metric.ball x₀ (2 * R))
          (shiftedMatrix (principalMatrix Q u) k h)
          (classicalDifferenceSource (principalMatrix Q u) (classicalSource Q u) u k h)
          (differenceQuotient u k h) ∧
        ScalarHolderBound
          (classicalDifferenceSource (principalMatrix Q u) (classicalSource Q u) u k h)
          (Metric.ball x₀ (2 * R)) α F ∧
        PlanarHolderJetBound 1 (differenceQuotient u k h)
          (Metric.ball x₀ (2 * R)) α U ∧
        ∃ Kh : NNReal, PlanarHolderJetBound 2 (differenceQuotient u k h)
          (Metric.ball x₀ (2 * R)) α Kh) := by
  classical
  have hcompose (B : Set E2) (hB : IsOpen B) (J T : Set Jet) (hJ : IsOpen J)
    (hT : IsCompact T) (hTJ : T ⊆ J) (f : Jet → ℝ)
    (hf : ContDiffOn ℝ 2 f J) (G : E2 → Jet) (hG : ContDiffOn ℝ 1 G B)
    (hGT : MapsTo G B T) (α C D L : NNReal)
    (hGH : HolderOnWith C α G B)
    (hDG : HolderOnWith D α (fderiv ℝ G) B)
    (hLb : ∀ x ∈ B, ‖fderiv ℝ G x‖ ≤ (L:ℝ)) :
    ∃ M : NNReal, PlanarHolderJetBound 1 (fun x => f (G x)) B α M := by
    have hlocal : LocallyLipschitzOn J f := by
      intro z hz
      obtain ⟨A,U,hU,hA⟩ := ((hf.of_le (by norm_num)).contDiffAt (hJ.mem_nhds hz)).exists_lipschitzOnWith
      exact ⟨A,U,mem_nhdsWithin_of_mem_nhds hU,hA⟩
    obtain ⟨A,hA⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hT (hlocal.mono hTJ)
    obtain ⟨N,hN⟩ := hT.exists_bound_of_continuousOn (hf.continuousOn.mono hTJ)
    have hfD : ContDiffOn ℝ 1 (fderiv ℝ f) J := hf.fderiv_of_isOpen hJ (by norm_num)
    let U : Set (Jet × (E2 →L[ℝ] Jet)) := Prod.fst ⁻¹' J
    have hU : IsOpen U := hJ.preimage continuous_fst
    let F : Jet × (E2 →L[ℝ] Jet) → E2 →L[ℝ] ℝ := fun z => (fderiv ℝ f z.1).comp z.2
    have hfst : ContDiffOn ℝ 1 (fun z : Jet × (E2 →L[ℝ] Jet) => z.1) U := by
      fun_prop
    have hsnd : ContDiffOn ℝ 1 (fun z : Jet × (E2 →L[ℝ] Jet) => z.2) U := by
      fun_prop
    have hF : ContDiffOn ℝ 1 F U :=
      (hfD.comp hfst (fun z hz => hz)).clm_comp hsnd
    let K : Set (Jet × (E2 →L[ℝ] Jet)) := T ×ˢ Metric.closedBall 0 L
    have hK : IsCompact K := hT.prod (isCompact_closedBall _ _)
    have hKU : K ⊆ U := fun z hz => hTJ hz.1
    have hlocalF : LocallyLipschitzOn U F := by
      intro z hz
      obtain ⟨A,V,hV,hA⟩ := (hF.contDiffAt (hU.mem_nhds hz)).exists_lipschitzOnWith
      exact ⟨A,V,mem_nhdsWithin_of_mem_nhds hV,hA⟩
    obtain ⟨A₁,hA₁⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK (hlocalF.mono hKU)
    obtain ⟨N₁,hN₁⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
    have hPK (x : E2) (hx : x ∈ B) : (G x,fderiv ℝ G x) ∈ K := by
      exact ⟨hGT hx,by simpa only [Metric.mem_closedBall,dist_zero_right] using hLb x hx⟩
    have hprod : HolderOnWith (C+D) α (fun x => (G x,fderiv ℝ G x)) B := by
      intro x hx y hy
      have hr : dist (G x,fderiv ℝ G x) (G y,fderiv ℝ G y) ≤ ((C+D:NNReal):ℝ)*dist x y^(α:ℝ) := by
        rw [Prod.dist_eq]
        apply max_le
        · exact (hGH.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (le_add_right le_rfl : C ≤ C+D)) (Real.rpow_nonneg dist_nonneg _))
        · exact (hDG.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (le_add_left le_rfl : D ≤ C+D)) (Real.rpow_nonneg dist_nonneg _))
      simpa only [edist_dist,ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal hr
    have h0H : HolderOnWith (A*C) α (fun x => f (G x)) B := by
      have hh := hA.holderOnWith.comp hGH hGT
      simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def] using hh
    have h1H : HolderOnWith (A₁*(C+D)) α (fun x => F (G x,fderiv ℝ G x)) B := by
      have hh := hA₁.holderOnWith.comp hprod hPK
      simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def] using hh
    have hder (x : E2) (hx : x ∈ B) : fderiv ℝ (fun x => f (G x)) x = F (G x,fderiv ℝ G x) :=
      ((hf.contDiffAt (hJ.mem_nhds (hTJ (hGT hx)))).differentiableAt (by norm_num)).hasFDerivAt.comp x
        ((hG.contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt |>.fderiv
    let M : NNReal := Real.toNNReal N+Real.toNNReal N₁+A*C+A₁*(C+D)
    have hM0 : Real.toNNReal N ≤ M := by
      dsimp [M]
      exact le_add_right (le_add_right (le_add_right le_rfl))
    have hM1 : Real.toNNReal N₁ ≤ M := by
      dsimp [M]
      exact le_add_right (le_add_right (le_add_left le_rfl))
    have h0b (x : E2) (hx : x ∈ B) : ‖f (G x)‖ ≤ (M:ℝ) := by
      have hh := (hN _ (hGT hx)).trans (Real.le_coe_toNNReal N)
      exact hh.trans (by exact_mod_cast hM0)
    have h1b (x : E2) (hx : x ∈ B) : ‖fderiv ℝ (fun x => f (G x)) x‖ ≤ (M:ℝ) := by
      rw [hder x hx]
      have hh := (hN₁ _ (hPK x hx)).trans (Real.le_coe_toNNReal N₁)
      exact hh.trans (by exact_mod_cast hM1)
    have h0M : A*C ≤ M := by dsimp [M]; exact le_add_right (le_add_left le_rfl)
    have h1M : A₁*(C+D) ≤ M := by dsimp [M]; exact le_add_left le_rfl
    refine ⟨M, (hf.of_le (by norm_num)).comp hG (fun x hx => hTJ (hGT hx)),?_⟩
    intro q hq
    interval_cases q
    · constructor
      · intro x hx
        simpa only [norm_iteratedFDeriv_zero] using h0b x hx
      · intro x hx y hy
        simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
          (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq]
          using (h0H.mono_const h0M) x hx y hy
    · let I := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
      have hI (x : E2) : iteratedFDeriv ℝ 1 (fun x => f (G x)) x = I (fderiv ℝ (fun x => f (G x)) x) := by
        ext ξ
        simp [I,iteratedFDeriv_one_apply]
      constructor
      · intro x hx
        simpa only [norm_iteratedFDeriv_one] using h1b x hx
      · intro x hx y hy
        simpa only [hI,hder x hx,hder y hy,I.isometry.edist_eq]
          using (h1H.mono_const h1M) x hx y hy
  have hfirstJet (u : E2 → ℝ) (c : E2) (r : ℝ) (α K : NNReal) (hαone : α < 1)
    (hu : PlanarHolderJetBound 2 u (Metric.ball c r) α K) :
    ∃ C D L : NNReal,
      ContDiffOn ℝ 1 (firstJet u) (Metric.ball c r) ∧
      HolderOnWith C α (firstJet u) (Metric.ball c r) ∧
      HolderOnWith D α (fderiv ℝ (firstJet u)) (Metric.ball c r) ∧
      (∀ x ∈ Metric.ball c r, ‖fderiv ℝ (firstJet u) x‖ ≤ (L:ℝ)) := by
    let B := Metric.ball c r
    have hB : IsOpen B := Metric.isOpen_ball
    let Lg : (E2 →L[ℝ] ℝ) →L[ℝ] E2 :=
      ∑ i : Fin 2, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 i)).smulRight (coordinateVector 2 i)
    have hLg (x : E2) : Lg (fderiv ℝ u x) = planarGradient u x := by
      simp [Lg,planarGradient]
    have hdu : ContDiffOn ℝ 1 (fderiv ℝ u) B := hu.1.fderiv_of_isOpen hB (by norm_num)
    have hg : ContDiffOn ℝ 1 (planarGradient u) B := by
      simpa only [Function.comp_def,hLg] using Lg.contDiff.comp_contDiffOn hdu
    have hj : ContDiffOn ℝ 1 (firstJet u) B :=
      contDiffOn_id.prodMk ((hu.1.of_le (by norm_num)).prodMk hg)
    let I := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
    have hI (x : E2) : iteratedFDeriv ℝ 1 u x = I (fderiv ℝ u x) := by
      ext ξ
      simp [I,iteratedFDeriv_one_apply]
    have huH : HolderOnWith K α u B := by
      intro x hx y hy
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq] using (hu.2 0 (by omega)).2 x hx y hy
    have hduH : HolderOnWith K α (fderiv ℝ u) B := by
      intro x hx y hy
      simpa only [hI,I.isometry.edist_eq] using (hu.2 1 (by omega)).2 x hx y hy
    let S := (continuousMultilinearCurryFin1 ℝ E2 (E2 →L[ℝ] ℝ)).symm.trans
      (continuousMultilinearCurryRightEquiv' ℝ 1 E2 ℝ).symm
    have hS (x : E2) : iteratedFDeriv ℝ 2 u x = S (fderiv ℝ (fderiv ℝ u) x) := by
      ext ξ
      rw [iteratedFDeriv_two_apply]
      simp [S,Fin.init]
    have hH : HolderOnWith K α (fderiv ℝ (fderiv ℝ u)) B := by
      intro x hx y hy
      simpa only [hS,S.isometry.edist_eq] using (hu.2 2 (by omega)).2 x hx y hy
    have hDub (x : E2) (hx : x ∈ B) : ‖fderiv ℝ u x‖ ≤ (K:ℝ) := by
      simpa only [norm_iteratedFDeriv_one] using (hu.2 1 (by omega)).1 x hx
    have hHb (x : E2) (hx : x ∈ B) : ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ (K:ℝ) := by
      simpa only [hS,S.norm_map] using (hu.2 2 (by omega)).1 x hx
    have hgradH : HolderOnWith (‖Lg‖₊*K) α (planarGradient u) B := by
      simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def,hLg]
        using Lg.lipschitzWith.holderWith.comp_holderOnWith hduH
    have hprod {X F G : Type} [PseudoMetricSpace X] [NormedAddCommGroup F] [NormedAddCommGroup G]
        {A : Set X} {f : X → F} {g : X → G} {C D : NNReal}
        (hf : HolderOnWith C α f A) (hg : HolderOnWith D α g A) :
        HolderOnWith (C+D) α (fun x => (f x,g x)) A := by
      intro x hx y hy
      have hr : dist (f x,g x) (f y,g y) ≤ ((C+D:NNReal):ℝ)*dist x y^(α:ℝ) := by
        rw [Prod.dist_eq]
        apply max_le
        · exact (hf.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (le_add_right le_rfl : C ≤ C+D)) (Real.rpow_nonneg dist_nonneg _))
        · exact (hg.dist_le hx hy).trans (mul_le_mul_of_nonneg_right
            (by exact_mod_cast (le_add_left le_rfl : D ≤ C+D)) (Real.rpow_nonneg dist_nonneg _))
      simpa only [edist_dist,ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
        using ENNReal.ofReal_le_ofReal hr
    let Db : NNReal := (Metric.ediam (Metric.closedBall c r)).toNNReal
    have hDb : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ (Db:ENNReal) := by
      intro x hx y hy
      dsimp [Db]
      rw [ENNReal.coe_toNNReal (isCompact_closedBall _ _).isBounded.ediam_ne_top]
      exact Metric.edist_le_ediam_of_mem (Metric.ball_subset_closedBall hx) (Metric.ball_subset_closedBall hy)
    have hid : HolderOnWith (Db ^ ((1:ℝ)-(α:ℝ))) α (fun x : E2 => x) B := by
      change HolderOnWith (Db ^ ((1:ℝ)-(α:ℝ))) α id B
      simpa only [NNReal.coe_one,one_mul,id_eq] using
        (LipschitzWith.id.holderWith.holderOnWith B).of_le hDb hαone.le
    have hD (x : E2) (hx : x ∈ B) : fderiv ℝ (firstJet u) x =
        (ContinuousLinearMap.id ℝ E2).prod ((fderiv ℝ u x).prod (Lg.comp (fderiv ℝ (fderiv ℝ u) x))) := by
      have hgD : HasFDerivAt (planarGradient u) (Lg.comp (fderiv ℝ (fderiv ℝ u) x)) x := by
        simpa only [Function.comp_def,hLg] using Lg.hasFDerivAt.comp x
          ((hdu.contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
      exact ((hasFDerivAt_id x).prodMk
        (((hu.1.contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt.prodMk hgD)).fderiv
    let D : NNReal := K+‖Lg‖₊*K
    have hnorm : ‖ContinuousLinearMap.compL ℝ E2 (E2 →L[ℝ] ℝ) E2 Lg‖₊ ≤ ‖Lg‖₊ := by
      apply NNReal.coe_le_coe.mp
      exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Lg) (fun H => Lg.opNorm_comp_le H)
    have hLgH : HolderOnWith (‖Lg‖₊*K) α
        (fun x => Lg.comp (fderiv ℝ (fderiv ℝ u) x)) B := by
      have hh := (ContinuousLinearMap.compL ℝ E2 (E2 →L[ℝ] ℝ) E2 Lg).lipschitzWith.holderWith.comp_holderOnWith hH
      simp only [NNReal.coe_one,NNReal.rpow_one,one_mul,Function.comp_def,
        ContinuousLinearMap.compL_apply] at hh
      exact hh.mono_const (by gcongr)
    have hDH : HolderOnWith D α (fderiv ℝ (firstJet u)) B := by
      intro x hx y hy
      have hd := hprod hduH hLgH
      have hh := hd x hx y hy
      have he : edist (fderiv ℝ (firstJet u) x) (fderiv ℝ (firstJet u) y) =
          edist (fderiv ℝ u x,Lg.comp (fderiv ℝ (fderiv ℝ u) x))
            (fderiv ℝ u y,Lg.comp (fderiv ℝ (fderiv ℝ u) y)) := by
        rw [hD x hx,hD y hy,edist_dist,edist_dist]
        simp only [dist_eq_norm]
        have hesub : (ContinuousLinearMap.id ℝ E2).prod ((fderiv ℝ u x).prod (Lg.comp (fderiv ℝ (fderiv ℝ u) x))) -
            (ContinuousLinearMap.id ℝ E2).prod ((fderiv ℝ u y).prod (Lg.comp (fderiv ℝ (fderiv ℝ u) y))) =
            (0 : E2 →L[ℝ] E2).prod (((fderiv ℝ u x)-(fderiv ℝ u y)).prod
              (Lg.comp (fderiv ℝ (fderiv ℝ u) x)-Lg.comp (fderiv ℝ (fderiv ℝ u) y))) := by
          ext ξ <;> simp
        rw [hesub]
        simp [ContinuousLinearMap.opNorm_prod,Prod.norm_def]
      rw [he]
      exact hd x hx y hy
    refine ⟨_,D,1+K+‖Lg‖₊*K,hj,hprod hid (hprod huH hgradH),hDH,?_⟩
    intro x hx
    simp only [hD x hx,ContinuousLinearMap.opNorm_prod,Prod.norm_def,
      NNReal.coe_add,NNReal.coe_one,NNReal.coe_mul,coe_nnnorm]
    apply max_le
    · exact (ContinuousLinearMap.norm_id_le).trans (by nlinarith [K.coe_nonneg,norm_nonneg Lg])
    · apply max_le
      · exact (hDub x hx).trans (by nlinarith [K.coe_nonneg,norm_nonneg Lg])
      · exact (Lg.opNorm_comp_le _).trans ((mul_le_mul_of_nonneg_left (hHb x hx) (norm_nonneg _)).trans (by nlinarith [K.coe_nonneg]))
  have hscalarSmooth (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J) :
    (∀ i j : Fin 2, ContDiffOn ℝ 2 (fun z : Jet => (1/2:ℝ) *
      (((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 j))) i +
       ((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 i))) j)) J) ∧
    ContDiffOn ℝ 2 (fun z : Jet => -Q.lowerOrder z - ∑ i : Fin 2,
      (((fderiv ℝ Q.flux z) (coordinateVector 2 i,(0,0))) i +
       ((fderiv ℝ Q.flux z) (0,(1,0))) i * z.2.2 i)) J := by
    have hd : ContDiffOn ℝ 2 (fderiv ℝ Q.flux) J := Q.flux_smooth.fderiv_of_isOpen hJ (by simp)
    have he (v : Jet) (i : Fin 2) : ContDiffOn ℝ 2 (fun z : Jet => fderiv ℝ Q.flux z v i) J := by
      simpa only [Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply] using
        (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hd.clm_apply contDiffOn_const)
    have hp (i : Fin 2) : ContDiffOn ℝ 2 (fun z : Jet => z.2.2 i) J := by
      have hp0 : ContDiffOn ℝ 2 (fun z : Jet => z.2.2) J := by fun_prop
      simpa only [Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply] using
        (EuclideanSpace.proj i).contDiff.comp_contDiffOn hp0
    constructor
    · intro i j
      exact contDiffOn_const.mul ((he _ i).add (he _ j))
    · exact (Q.lowerOrder_smooth.of_le (by simp)).neg.sub
        (ContDiffOn.sum (fun i _ => (he _ i).add ((he _ i).mul (hp i))))
  have hscalarEq (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
    (u : E2 → ℝ) (x : E2) (hx : firstJet u x ∈ J) :
    (∀ i j : Fin 2, principalMatrix Q u x i j = (1/2:ℝ) *
      (((fderiv ℝ Q.flux (firstJet u x)) (0,(0,coordinateVector 2 j))) i +
       ((fderiv ℝ Q.flux (firstJet u x)) (0,(0,coordinateVector 2 i))) j)) ∧
    classicalSource Q u x = -Q.lowerOrder (firstJet u x) - ∑ i : Fin 2,
      (((fderiv ℝ Q.flux (firstJet u x)) (coordinateVector 2 i,(0,0))) i +
       ((fderiv ℝ Q.flux (firstJet u x)) (0,(1,0))) i * (firstJet u x).2.2 i) := by
    have hq := (Q.flux_smooth.contDiffAt (hJ.mem_nhds hx)).differentiableAt (by simp)
    constructor
    · intro i j
      unfold principalMatrix rawPrincipalMatrix fluxDp
      rw [Helpers.fderiv_p_slice Q.flux (firstJet u x) hq]
      simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,
        ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
      rfl
    · unfold classicalSource fluxDx fluxDz
      rw [Helpers.fderiv_x_slice Q.flux (firstJet u x) hq,
        Helpers.fderiv_z_slice Q.flux (firstJet u x) hq]
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
        ContinuousLinearMap.inr_apply,firstJet]
      rfl
  have hprincipal (J : Set Jet) (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ)
    (x₀ : E2) (R κ M : ℝ) (T : Set Jet) (α H : NNReal)
    (hj : ∀ x ∈ Metric.ball x₀ (4*R), firstJet u x ∈ T)
    (hb : JetTubeBounds Q u x₀ R κ M T)
    (hH : ∀ i j, HolderOnWith H α (fun x => principalMatrix Q u x i j) (Metric.ball x₀ (4*R))) :
    ∃ Λ : ℝ, κ ≤ Λ ∧ PlanarCoefficientControl (principalMatrix Q u)
      (Metric.ball x₀ (4*R)) κ Λ H α := by
    refine ⟨max κ M,le_max_left _ _,?_,⟩
    constructor
    · intro x hx i j
      simp only [principalMatrix,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul]
      ring
    · intro x hx ξ
      have hbQ := hb.2.2.2.2.2 (firstJet u x) (subset_closure (hj x hx)) ξ
      have he : (∑ i : Fin 2, ∑ j : Fin 2, principalMatrix Q u x i j*ξ i*ξ j) =
          inner ℝ (fluxDp Q (firstJet u x) ξ) ξ := by
        have hv : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
          ext i
          fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
        conv_rhs => rw [hv]
        simp only [principalMatrix,rawPrincipalMatrix,Matrix.smul_apply,Matrix.add_apply,
          Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,
          map_add,map_smul,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
        simp [coordinateVector,EuclideanSpace.single]
        ring
      rw [he]
      exact hbQ
    · intro x hx i j
      have hdp := (hb.2.2.2.1 (firstJet u x) (subset_closure (hj x hx))).2.2.2.2.1
      have he (k : Fin 2) : ‖coordinateVector 2 k‖ = 1 := by
        simp [coordinateVector,EuclideanSpace.single,PiLp.norm_single]
      have hraw (i j : Fin 2) : |rawPrincipalMatrix Q u x i j| ≤ M := by
        have h := PiLp.norm_apply_le (fluxDp Q (firstJet u x) (coordinateVector 2 j)) i
        rw [Real.norm_eq_abs] at h
        exact h.trans (((fluxDp Q (firstJet u x)).le_opNorm _).trans (by rw [he,mul_one];exact hdp))
      simp only [principalMatrix,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,abs_mul]
      have h1 := hraw i j
      have h2 := hraw j i
      have h3 := abs_add_le (rawPrincipalMatrix Q u x i j) (rawPrincipalMatrix Q u x j i)
      apply le_trans _ (le_max_right κ M)
      norm_num
      linarith
    · exact hH
  have hdiffData
    (x₀ : E2) (R κ Λ : ℝ) (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ)
    (a : E2 → PlanarMatrix) (f w : E2 → ℝ) (H α M : NNReal)
    (hα : 0 < α) (hαone : α < 1)
    (ha : PlanarCoefficientControl a (Metric.ball x₀ (4 * R)) κ Λ H α)
    (haC1 : ∀ i j, PlanarHolderJetBound 1 (fun x => a x i j)
      (Metric.ball x₀ (4 * R)) α M)
    (hfC1 : PlanarHolderJetBound 1 f (Metric.ball x₀ (4 * R)) α M)
    (hwC2 : PlanarHolderJetBound 2 w (Metric.ball x₀ (4 * R)) α M)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R)) a f w) :
    ∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < R →
      PlanarCoefficientControl (shiftedMatrix a k h) (Metric.ball x₀ (2*R)) κ Λ H α ∧
      LinearClassicalEquation (Metric.ball x₀ (2*R)) (shiftedMatrix a k h)
        (classicalDifferenceSource a f w k h) (differenceQuotient w k h) ∧
      ScalarHolderBound (classicalDifferenceSource a f w k h)
        (Metric.ball x₀ (2*R)) α (M+8*M*M) ∧
      PlanarHolderJetBound 1 (differenceQuotient w k h) (Metric.ball x₀ (2*R)) α M ∧
      ∃ Kh : NNReal, PlanarHolderJetBound 2 (differenceQuotient w k h)
        (Metric.ball x₀ (2*R)) α Kh := by
    classical
    let B := Metric.ball x₀ (4 * R)
    let D := Metric.ball x₀ (2 * R)
    have hB : IsOpen B := Metric.isOpen_ball
    have hD : IsOpen D := Metric.isOpen_ball
    have hsub : D ⊆ B := Metric.ball_subset_ball (by linarith)
    have hcurry1 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
        (g : E2 → F) (B : Set E2) (α M : NNReal)
        (h : HolderOnWith M α (iteratedFDeriv ℝ 1 g) B) :
        HolderOnWith M α (fderiv ℝ g) B := by
      let L := (continuousMultilinearCurryFin1 ℝ E2 F).symm
      have hg (x : E2) : iteratedFDeriv ℝ 1 g x = L (fderiv ℝ g x) := by
        ext v
        simp [L, iteratedFDeriv_one_apply]
      intro x hx y hy
      simpa only [hg, L.isometry.edist_eq] using h x hx y hy
    let S := (continuousMultilinearCurryFin1 ℝ E2 (E2 →L[ℝ] ℝ)).symm.trans
      (continuousMultilinearCurryRightEquiv' ℝ 1 E2 ℝ).symm
    have hS (x : E2) : iteratedFDeriv ℝ 2 w x = S (fderiv ℝ (fderiv ℝ w) x) := by
      ext ξ
      rw [iteratedFDeriv_two_apply]
      simp [S, Fin.init]
    have hHess : HolderOnWith M α (fderiv ℝ (fderiv ℝ w)) B := by
      intro x hx y hy
      simpa only [hS, S.isometry.edist_eq] using (hwC2.2 2 (by omega)).2 x hx y hy
    have hHessb (x : E2) (hx : x ∈ B) : ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ (M : ℝ) := by
      simpa only [hS, LinearIsometryEquiv.norm_map] using (hwC2.2 2 (by omega)).1 x hx
    have hFTC {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
        (g : E2 → F) (hg : ContDiffOn ℝ 1 g B)
        (hgb : ∀ x ∈ B, ‖fderiv ℝ g x‖ ≤ (M : ℝ))
        (hgh : HolderOnWith M α (fderiv ℝ g) B)
        (k : Fin 2) (h : ℝ) (hh : 0 < |h|) (hsmall : |h| < R) :
        (∀ x ∈ D, ‖h⁻¹ • (g (shift k h x) - g x)‖ ≤ (M : ℝ)) ∧
        HolderOnWith M α (fun x => h⁻¹ • (g (shift k h x) - g x)) D := by
      have he : ‖coordinateVector 2 k‖ = 1 := by
        simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
      have hs (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
          x + t • (h • coordinateVector 2 k) ∈ Metric.ball x₀ (4*R) := by
        have hn : ‖t • (h • coordinateVector 2 k)‖ ≤ |h| := by
          simp only [norm_smul, Real.norm_eq_abs, he, mul_one, abs_of_nonneg ht.1]
          exact (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg h)).trans_eq (one_mul _)
        have hd := dist_triangle (x + t • (h • coordinateVector 2 k)) x x₀
        rw [dist_self_add_left] at hd
        rw [Metric.mem_ball] at hx ⊢
        linarith
      let G (x : E2) (t : ℝ) : F := fderiv ℝ g (x + t • (h • coordinateVector 2 k)) (coordinateVector 2 k)
      have hGc (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) : ContinuousOn (G x) (Icc (0:ℝ) 1) :=
        ((hg.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_num)).comp
          (by fun_prop : ContinuousOn (fun t : ℝ => x+t • (h • coordinateVector 2 k)) (Icc (0:ℝ) 1))
          (hs x hx)).clm_apply continuousOn_const
      have hGi (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) : IntervalIntegrable (G x) volume 0 1 :=
        (hGc x hx).intervalIntegrable_of_Icc (by norm_num)
      have hrep (x : E2) (hx : x ∈ Metric.ball x₀ (2*R)) :
          h⁻¹ • (g (shift k h x) - g x) = ∫ t in (0:ℝ)..1, G x t := by
        have hd (t : ℝ) (ht : t ∈ uIcc (0:ℝ) 1) :
            HasDerivAt (fun t => g (x + t • (h • coordinateVector 2 k))) (h • G x t) t := by
          have hpath : HasDerivAt (fun t : ℝ => x+t • (h • coordinateVector 2 k))
              (h • coordinateVector 2 k) t := by
            convert (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (h • coordinateVector 2 k)) using 1 <;> simp only [zero_add, one_smul, id_eq]
            funext z
            rfl
          have hhpath := ((hg.contDiffAt (Metric.isOpen_ball.mem_nhds (hs x hx t (by simpa using ht)))).differentiableAt
            (by norm_num)).hasFDerivAt.comp_hasDerivAt t hpath
          convert hhpath using 1 <;> simp only [map_smul, G, Function.comp_def]
        have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((hGi x hx).smul h)
        rw [intervalIntegral.integral_smul] at hi
        simp only [one_smul, zero_smul, add_zero] at hi
        change h • (∫ t in (0:ℝ)..1, G x t) = g (shift k h x) - g x at hi
        rw [← hi, smul_smul, inv_mul_cancel₀ (abs_pos.mp hh), one_smul]
      constructor
      · intro x hx
        rw [hrep x hx]
        have hb : ∀ t ∈ Ι (0:ℝ) 1, ‖G x t‖ ≤ (M : ℝ) := by
          intro t ht
          have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using Set.uIoc_subset_uIcc ht
          have hb := hgb _ (hs x hx t (by simpa using ht'))
          exact ((fderiv ℝ g _).le_opNorm _).trans (by rw [he, mul_one]; exact hb)
        simpa only [sub_zero, abs_one, one_mul, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
      · intro x hx y hy
        have hr : dist (h⁻¹ • (g (shift k h x) - g x))
            (h⁻¹ • (g (shift k h y) - g y)) ≤ (M : ℝ) * dist x y ^ (α : ℝ) := by
          rw [dist_eq_norm, hrep x hx, hrep y hy, ← intervalIntegral.integral_sub (hGi x hx) (hGi y hy)]
          have hb : ∀ t ∈ Ι (0:ℝ) 1, ‖G x t - G y t‖ ≤ (M : ℝ) * dist x y ^ (α : ℝ) := by
            intro t ht
            have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using Set.uIoc_subset_uIcc ht
            have hc := hgh.dist_le (hs x hx t ht') (hs y hy t ht')
            rw [dist_eq_norm, dist_add_right] at hc
            change ‖(fderiv ℝ g (x+t • (h • coordinateVector 2 k)) -
              fderiv ℝ g (y+t • (h • coordinateVector 2 k))) (coordinateVector 2 k)‖ ≤ _
            exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [he, mul_one]; exact hc)
          simpa only [sub_zero, abs_one, one_mul, mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const hb
        simpa only [edist_dist, ENNReal.ofReal_mul M.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    let F : NNReal := M + 8 * M * M
    intro k h hh hsmall
    have hne : h ≠ 0 := abs_pos.mp hh
    have he (i : Fin 2) : ‖coordinateVector 2 i‖ = 1 := by
      simp [coordinateVector, EuclideanSpace.single, PiLp.norm_single]
    have hshift (x : E2) (hx : x ∈ D) : shift k h x ∈ B := by
      have hd := dist_triangle (shift k h x) x x₀
      have hs : dist (shift k h x) x = |h| := by simp [shift, dist_eq_norm, norm_smul, he, Real.norm_eq_abs]
      rw [hs] at hd
      rw [Metric.mem_ball] at hx ⊢
      linarith
    have hshiftC : ContDiff ℝ ∞ (shift k h) := by unfold shift; fun_prop
    have hδC2 : ContDiffOn ℝ 2 (differenceQuotient w k h) D := by
      have ht := (hwC2.1.comp ((hshiftC.of_le (by simp)).contDiffOn) hshift).sub (hwC2.1.mono hsub)
      have heq : differenceQuotient w k h = h⁻¹ • (w ∘ shift k h - w) := by
        funext x
        simp [differenceQuotient, div_eq_mul_inv, mul_comm]
      rw [heq]
      exact ht.const_smul h⁻¹
    have hδjet (q : ℕ) (hq : q ≤ 2) (x : E2) (hx : x ∈ D) :
        iteratedFDeriv ℝ q (differenceQuotient w k h) x =
          h⁻¹ • (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w x) := by
      have hwx : ContDiffAt ℝ q w x := (hwC2.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds (hsub hx))
      have hws : ContDiffAt ℝ q (fun z => w (z+h • coordinateVector 2 k)) x :=
        ((hwC2.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds (hshift x hx))).comp x
          (contDiff_id.add contDiff_const).contDiffAt
      have heq : differenceQuotient w k h = h⁻¹ • ((fun z => w (z+h • coordinateVector 2 k))-w) := by
        funext z
        simp [differenceQuotient, shift, div_eq_mul_inv, mul_comm]
      rw [heq]
      change iteratedFDeriv ℝ q (h⁻¹ • (fun z => w (z+h • coordinateVector 2 k) - w z)) x = _
      rw [iteratedFDeriv_const_smul_apply (a := h⁻¹) (hws.sub hwx)]
      change h⁻¹ • iteratedFDeriv ℝ q ((fun z => w (z+h • coordinateVector 2 k))-w) x = _
      rw [iteratedFDeriv_sub_apply hws hwx, iteratedFDeriv_comp_add_right]
      rfl
    let Kh : NNReal := 2 * Real.toNNReal |h|⁻¹ * M
    have hKh : (Kh : ℝ) = 2 * |h|⁻¹ * (M : ℝ) := by
      simp only [Kh, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal _ (inv_nonneg.mpr (abs_nonneg h))]
    have hδindividual : PlanarHolderJetBound 2 (differenceQuotient w k h) D α Kh := by
      refine ⟨hδC2, ?_⟩
      intro q hq
      constructor
      · intro x hx
        rw [hδjet q hq x hx, norm_smul, Real.norm_eq_abs, abs_inv, hKh]
        calc
          _ ≤ |h|⁻¹ * (2 * (M : ℝ)) := mul_le_mul_of_nonneg_left
            ((norm_sub_le _ _).trans (by linarith [(hwC2.2 q hq).1 _ (hshift x hx), (hwC2.2 q hq).1 x (hsub hx)]))
            (inv_nonneg.mpr (abs_nonneg h))
          _ = _ := by ring
      · intro x hx y hy
        have hr : dist (iteratedFDeriv ℝ q (differenceQuotient w k h) x)
            (iteratedFDeriv ℝ q (differenceQuotient w k h) y) ≤ (Kh : ℝ) * dist x y ^ (α : ℝ) := by
          rw [hδjet q hq x hx, hδjet q hq y hy, dist_eq_norm, ← smul_sub, norm_smul,
            Real.norm_eq_abs, abs_inv, hKh]
          have hc1 := ((hwC2.2 q hq).2).dist_le (hshift x hx) (hshift y hy)
          have hc2 := ((hwC2.2 q hq).2).dist_le (hsub hx) (hsub hy)
          simp only [shift, dist_add_right] at hc1
          rw [dist_eq_norm] at hc1 hc2
          have heq : (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w x) -
              (iteratedFDeriv ℝ q w (shift k h y) - iteratedFDeriv ℝ q w y) =
              (iteratedFDeriv ℝ q w (shift k h x) - iteratedFDeriv ℝ q w (shift k h y)) -
              (iteratedFDeriv ℝ q w x - iteratedFDeriv ℝ q w y) := by abel
          rw [heq]
          have hn := (norm_sub_le _ _).trans (add_le_add hc1 hc2)
          calc
            _ ≤ |h|⁻¹ * ((M : ℝ) * dist x y ^ (α : ℝ) + (M : ℝ) * dist x y ^ (α : ℝ)) := mul_le_mul_of_nonneg_left hn (by positivity)
            _ = _ := by ring
        simpa only [edist_dist, ENNReal.ofReal_mul Kh.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    have hscalar (g : E2 → ℝ) (hg : PlanarHolderJetBound 1 g B α M) :
        ScalarHolderBound (differenceQuotient g k h) D α M := by
      have hb (x : E2) (hx : x ∈ B) : ‖fderiv ℝ g x‖ ≤ (M : ℝ) := by
        simpa only [norm_iteratedFDeriv_one] using (hg.2 1 (by omega)).1 x hx
      have ht := hFTC g hg.1 hb (hcurry1 g B α M (hg.2 1 (by omega)).2) k h hh hsmall
      have heq : differenceQuotient g k h = fun x => h⁻¹ • (g (shift k h x)-g x) := by
        funext x
        simp only [differenceQuotient, div_eq_mul_inv, smul_eq_mul, mul_comm]
      rw [heq]
      simpa only [ScalarHolderBound, Real.norm_eq_abs] using ht
    have hδw0 := hscalar w ⟨hwC2.1.of_le (by norm_num), fun q hq => hwC2.2 q (by omega)⟩
    have hδdu := hFTC (fderiv ℝ w) (hwC2.1.fderiv_of_isOpen hB (by norm_num)) hHessb hHess k h hh hsmall
    have hδder (x : E2) (hx : x ∈ D) : fderiv ℝ (differenceQuotient w k h) x =
        h⁻¹ • (fderiv ℝ w (shift k h x) - fderiv ℝ w x) := by
      let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ)
      have heq := congrArg L (hδjet 1 (by omega) x hx)
      have hL (g : E2 → ℝ) (z : E2) : L (iteratedFDeriv ℝ 1 g z) = fderiv ℝ g z := by
        ext ξ
        simp [L, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
      simpa only [map_smul, map_sub, hL] using heq
    have hδlower : PlanarHolderJetBound 1 (differenceQuotient w k h) D α M := by
      refine ⟨hδC2.of_le (by norm_num), ?_⟩
      intro q hq
      interval_cases q
      · constructor
        · intro x hx
          simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hδw0.1 x hx
        · let L := (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm
          have heq (x : E2) : iteratedFDeriv ℝ 0 (differenceQuotient w k h) x = L (differenceQuotient w k h x) := rfl
          intro x hx y hy
          simpa only [heq, L.isometry.edist_eq] using hδw0.2 x hx y hy
      · constructor
        · intro x hx
          simpa only [norm_iteratedFDeriv_one, hδder x hx] using hδdu.1 x hx
        · let L := (continuousMultilinearCurryFin1 ℝ E2 ℝ).symm
          have heq (x : E2) : iteratedFDeriv ℝ 1 (differenceQuotient w k h) x = L (fderiv ℝ (differenceQuotient w k h) x) := by
            ext v
            simp [L, iteratedFDeriv_one_apply]
          intro x hx y hy
          simpa only [heq, L.isometry.edist_eq, hδder x hx, hδder y hy] using hδdu.2 x hx y hy
    have hcoeff : PlanarCoefficientControl (shiftedMatrix a k h) D κ Λ H α := by
      constructor
      · intro x hx i j
        exact ha.symmetric _ (hshift x hx) i j
      · intro x hx ξ
        exact ha.coercive _ (hshift x hx) ξ
      · intro x hx i j
        exact ha.bounded _ (hshift x hx) i j
      · intro i j x hx y hy
        simpa only [shiftedMatrix, shift, edist_add_right] using ha.holder i j _ (hshift x hx) _ (hshift y hy)
    have hprod (p q : E2 → ℝ) (hp : ScalarHolderBound p D α M)
        (hq : ScalarHolderBound q D α M) :
        ScalarHolderBound (fun x => p x * q x) D α (2*M*M) := by
      constructor
      · intro x hx
        rw [abs_mul]
        have hn := mul_le_mul (hp.1 x hx) (hq.1 x hx) (abs_nonneg _) M.coe_nonneg
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        nlinarith [M.coe_nonneg]
      · intro x hx y hy
        have hr : dist (p x * q x) (p y * q y) ≤ (2*M*M : NNReal) * dist x y ^ (α : ℝ) := by
          rw [Real.dist_eq]
          have heq : p x*q x - p y*q y = (p x-p y)*q x + p y*(q x-q y) := by ring
          rw [heq]
          have hpH := hp.2.dist_le hx hy
          have hqH := hq.2.dist_le hx hy
          rw [Real.dist_eq] at hpH hqH
          calc
            _ ≤ |p x-p y| *|q x| + |p y| *|q x-q y| := by
              simpa only [abs_mul] using abs_add_le ((p x-p y)*q x) (p y*(q x-q y))
            _ ≤ ((M : ℝ)*dist x y^(α:ℝ))*(M : ℝ) + (M : ℝ)*((M : ℝ)*dist x y^(α:ℝ)) :=
              add_le_add (mul_le_mul hpH (hq.1 x hx) (abs_nonneg _) (by positivity))
                (mul_le_mul (hp.1 y hy) hqH (abs_nonneg _) M.coe_nonneg)
            _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring
        simpa only [edist_dist, ENNReal.ofReal_mul (NNReal.coe_nonneg _),
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    have hessSB (i j : Fin 2) : ScalarHolderBound (fun x => planarHessian w x i j) D α M := by
      have hn (T : E2 →L[ℝ] E2 →L[ℝ] ℝ) : |T (coordinateVector 2 i) (coordinateVector 2 j)| ≤ ‖T‖ := by
        calc
          _ ≤ ‖T (coordinateVector 2 i)‖ * ‖coordinateVector 2 j‖ := by
            simpa only [Real.norm_eq_abs] using (T (coordinateVector 2 i)).le_opNorm (coordinateVector 2 j)
          _ ≤ (‖T‖ * ‖coordinateVector 2 i‖) * ‖coordinateVector 2 j‖ :=
            mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
          _ = ‖T‖ := by rw [he i, he j, mul_one, mul_one]
      constructor
      · intro x hx
        exact (hn _).trans (hHessb x (hsub hx))
      · intro x hx y hy
        have hr : dist (planarHessian w x i j) (planarHessian w y i j) ≤
            (M : ℝ) * dist x y ^ (α : ℝ) := by
          rw [Real.dist_eq]
          have hc := hHess.dist_le (hsub hx) (hsub hy)
          rw [dist_eq_norm] at hc
          have heq : planarHessian w x i j-planarHessian w y i j =
            (fderiv ℝ (fderiv ℝ w) x-fderiv ℝ (fderiv ℝ w) y) (coordinateVector 2 i) (coordinateVector 2 j) := rfl
          rw [heq]
          exact (hn _).trans hc
        simpa only [edist_dist, ENNReal.ofReal_mul M.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    have hP (i j : Fin 2) : ScalarHolderBound
        (fun x => differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j) D α (2*M*M) :=
      hprod _ _ (hscalar _ (haC1 i j)) (hessSB i j)
    have hfinite (Z : Fin 2 → Fin 2 → ℝ) (P : ℝ) (hz : ∀ i j, |Z i j| ≤ P) :
        |∑ i : Fin 2, ∑ j : Fin 2, Z i j| ≤ 4*P := by
      calc
        _ ≤ ∑ i : Fin 2, |∑ j : Fin 2, Z i j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, |Z i j| := Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i : Fin 2, ∑ j : Fin 2, P := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hz i j))
        _ = 4*P := by simp only [Fin.sum_univ_two]; ring
    have hsource : ScalarHolderBound (classicalDifferenceSource a f w k h) D α F := by
      have hf := hscalar f hfC1
      constructor
      · intro x hx
        dsimp [classicalDifferenceSource]
        have hb := hfinite (fun i j => differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)
          (2*M*M : NNReal) (fun i j => (hP i j).1 x hx)
        exact (abs_sub _ _).trans ((add_le_add (hf.1 x hx) hb).trans_eq (by
          simp only [F, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]; ring))
      · intro x hx y hy
        have hr : dist (classicalDifferenceSource a f w k h x) (classicalDifferenceSource a f w k h y) ≤
            (F : ℝ)*dist x y^(α:ℝ) := by
          rw [Real.dist_eq]
          have heq : classicalDifferenceSource a f w k h x-classicalDifferenceSource a f w k h y =
            (differenceQuotient f k h x-differenceQuotient f k h y) -
            ∑ i : Fin 2, ∑ j : Fin 2,
              ((differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)-
               (differenceQuotient (fun y => a y i j) k h y * planarHessian w y i j)) := by
            simp only [classicalDifferenceSource, Fin.sum_univ_two]
            ring
          rw [heq]
          have hb := hfinite
            (fun i j => (differenceQuotient (fun y => a y i j) k h x * planarHessian w x i j)-
              (differenceQuotient (fun y => a y i j) k h y * planarHessian w y i j))
            ((2*M*M : NNReal)*dist x y^(α:ℝ)) (fun i j => by
              simpa only [Real.dist_eq] using ((hP i j).2).dist_le hx hy)
          have hfH := hf.2.dist_le hx hy
          rw [Real.dist_eq] at hfH
          exact (abs_sub _ _).trans ((add_le_add hfH hb).trans_eq (by
            simp only [F, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]; ring))
        simpa only [edist_dist, ENNReal.ofReal_mul F.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
          ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hr
    exact ⟨hcoeff, R5_linear_difference_equation x₀ R hR a f w hwC2.1 heq k h hh hsmall,
      hsource, hδlower, Kh, hδindividual⟩
  let B := Metric.ball x₀ (4*R)
  have hB : IsOpen B := Metric.isOpen_ball
  obtain ⟨C,D,L,hG,hGH,hDG,hDL⟩ := hfirstJet u x₀ (4*R) α K hαone hu
  have hGT : MapsTo (firstJet u) B (closure T) := by
    intro x hx
    exact subset_closure (hjetsT x (Metric.ball_subset_closedBall hx))
  let coeff (i j : Fin 2) (z : Jet) : ℝ := (1/2:ℝ) *
    (((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 j))) i +
     ((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 i))) j)
  let source (z : Jet) : ℝ := -Q.lowerOrder z - ∑ i : Fin 2,
    (((fderiv ℝ Q.flux z) (coordinateVector 2 i,(0,0))) i +
     ((fderiv ℝ Q.flux z) (0,(1,0))) i * z.2.2 i)
  have hcoeffExist (i j : Fin 2) : ∃ A : NNReal,
      PlanarHolderJetBound 1 (fun x => coeff i j (firstJet u x)) B α A :=
    hcompose B hB J (closure T) hJ hTcompact hTJ (coeff i j)
      ((hscalarSmooth J hJ Q).1 i j) (firstJet u) hG hGT α C D L hGH hDG hDL
  have hsourceExist : ∃ A : NNReal, PlanarHolderJetBound 1
      (fun x => source (firstJet u x)) B α A :=
    hcompose B hB J (closure T) hJ hTcompact hTJ source
      (hscalarSmooth J hJ Q).2 (firstJet u) hG hGT α C D L hGH hDG hDL
  choose A hA using hcoeffExist
  obtain ⟨As,hs⟩ := hsourceExist
  let M₁ : NNReal := K+As+∑ i : Fin 2, ∑ j : Fin 2, A i j
  have hK : K ≤ M₁ := by dsimp [M₁];exact le_add_right (le_add_right le_rfl)
  have hAs : As ≤ M₁ := by dsimp [M₁];exact le_add_right (le_add_left le_rfl)
  have hAij (i j : Fin 2) : A i j ≤ M₁ := by
    have hh : A i j ≤ ∑ i : Fin 2, ∑ j : Fin 2, A i j :=
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => show 0 ≤ A i j from zero_le) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => show 0 ≤ ∑ j : Fin 2, A i j from zero_le) (Finset.mem_univ i))
    exact hh.trans (by dsimp [M₁];exact le_add_left le_rfl)
  have hboundMono (f : E2 → ℝ) (m : ℕ) (A M₁ : NNReal) (hAM : A ≤ M₁)
      (hf : PlanarHolderJetBound m f B α A) : PlanarHolderJetBound m f B α M₁ := by
    refine ⟨hf.1,fun q hq => ⟨fun x hx => ((hf.2 q hq).1 x hx).trans ?_,
      ((hf.2 q hq).2).mono_const hAM⟩⟩
    exact_mod_cast hAM
  have hjetJ (x : E2) (hx : x ∈ B) : firstJet u x ∈ J := hTJ (hGT hx)
  have hboundCongr (f g : E2 → ℝ) (m : ℕ) (M₁ : NNReal)
      (hf : PlanarHolderJetBound m f B α M₁) (he : EqOn f g B) :
      PlanarHolderJetBound m g B α M₁ := by
    have hi (q : ℕ) (x : E2) (hx : x ∈ B) :
        iteratedFDeriv ℝ q f x = iteratedFDeriv ℝ q g x := by
      have hn : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hB.mem_nhds hx) he
      exact (hn.iteratedFDeriv ℝ q).eq_of_nhds
    refine ⟨hf.1.congr he.symm,fun q hq => ⟨?_,?_⟩⟩
    · intro x hx
      rw [← hi q x hx]
      exact (hf.2 q hq).1 x hx
    · intro x hx y hy
      rw [← hi q x hx,← hi q y hy]
      exact (hf.2 q hq).2 x hx y hy
  have haC1 (i j : Fin 2) : PlanarHolderJetBound 1
      (fun x => principalMatrix Q u x i j) B α M₁ := by
    have he : EqOn (fun x => coeff i j (firstJet u x)) (fun x => principalMatrix Q u x i j) B := by
      intro x hx
      exact ((hscalarEq J hJ Q u x (hjetJ x hx)).1 i j).symm
    have hb := hboundMono _ _ _ _ (hAij i j) (hA i j)
    exact hboundCongr _ _ 1 M₁ hb he
  have hfC1 : PlanarHolderJetBound 1 (classicalSource Q u) B α M₁ := by
    apply hboundCongr _ _ 1 M₁ (hboundMono _ _ _ _ hAs hs)
    intro x hx
    exact (hscalarEq J hJ Q u x (hjetJ x hx)).2.symm
  obtain ⟨Λ,hΛ,ha⟩ := hprincipal J Q u x₀ R κ M T α M₁
    (fun x hx => hjetsT x (Metric.ball_subset_closedBall hx)) hbound
    (fun i j => by
      intro x hx y hy
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq]
        using ((haC1 i j).2 0 (by omega)).2 x hx y hy)
  exact ⟨Λ,M₁,M₁,M₁+8*M₁*M₁,hΛ,
    hdiffData x₀ R κ Λ hR hbound.1 hΛ (principalMatrix Q u) (classicalSource Q u) u
      M₁ α M₁ hα hαone ha haC1 hfC1 (hboundMono u 2 K M₁ hK hu) heq⟩

/-- First nonlinear classical bootstrap step, stated separately so m=2
cannot hide a missing derivative. The exponent may decrease. -/
theorem R5_m2_gain
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R)
    (hball : Metric.closedBall x₀ (4 * R) ⊆ Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (α K : NNReal) (hα : 0 < α) (hαone : α < 1)
    (hu : PlanarHolderJetBound 2 u (Metric.ball x₀ (4 * R)) α K)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R))
      (principalMatrix Q u) (classicalSource Q u) u) :
    ∃ s : ℝ, ∃ K' : NNReal, 0 < s ∧ s ≤ R / 2 ∧
      PlanarHolderJetBound 3 u (Metric.ball x₀ (2 * s)) (α / 2) K' := by
  let Ω' := Metric.ball x₀ (4 * R)
  have huC1 : ContDiffOn ℝ 1 u Ω' := hu.1.of_le (by norm_num)
  obtain ⟨r, κ, M, T, hr, hrlocal, hTo, hTc, hTcompact, hTJ, hjT, hb⟩ :=
    R1_local_jet_tube Ω' Metric.isOpen_ball J hJ Q helliptic u huC1
      (fun x hx => hjets x (hball (Metric.ball_subset_closedBall hx))) x₀
      (Metric.mem_ball_self (by linarith))
  let t := min r (R / 2)
  have ht : 0 < t := lt_min hr (by positivity)
  have htr : t ≤ r := min_le_left _ _
  have htR : t ≤ R / 2 := min_le_right _ _
  have hclosed : Metric.closedBall x₀ (4 * t) ⊆ Metric.closedBall x₀ (4 * r) :=
    Metric.closedBall_subset_closedBall (by gcongr)
  have hlocal : Metric.closedBall x₀ (4 * t) ⊆ Ω' := hclosed.trans hrlocal
  have hballt : Metric.closedBall x₀ (4 * t) ⊆ Ω :=
    hlocal.trans (Metric.ball_subset_closedBall.trans hball)
  have hbt : JetTubeBounds Q u x₀ t κ M T :=
    ⟨hb.1, hb.2.1, fun x hx => hb.2.2.1 x (hclosed hx), hb.2.2.2⟩
  have hut : PlanarHolderJetBound 2 u (Metric.ball x₀ (4 * t)) α K :=
    ⟨hu.1.mono (Metric.ball_subset_closedBall.trans hlocal),
      fun q hq => ⟨fun x hx => (hu.2 q hq).1 x
        (hlocal (Metric.ball_subset_closedBall hx)),
        ((hu.2 q hq).2).mono (Metric.ball_subset_closedBall.trans hlocal)⟩⟩
  have heqt : LinearClassicalEquation (Metric.ball x₀ (4 * t))
      (principalMatrix Q u) (classicalSource Q u) u :=
    fun x hx => heq x (hlocal (Metric.ball_subset_closedBall hx))
  obtain ⟨Λ, H, U, F, hκΛ, hdata⟩ := R5_m2_difference_data Ω hΩ J hJ Q u x₀ t κ M ht T
    hballt hTc hTJ hTcompact (fun x hx => hjT x (hclosed hx)) hbt α K hα hαone hut heqt
  obtain ⟨A, hA, hest⟩ := R5_classical_schauder_apriori κ Λ t hb.1 hκΛ ht H α hα hαone
  let C := Real.toNNReal (A * ((U : ℝ) + (F : ℝ)))
  have hC (Kh : NNReal) (hKh : (Kh : ℝ) ≤ A * ((U : ℝ) + (F : ℝ))) : Kh ≤ C :=
    NNReal.coe_le_coe.mp (hKh.trans (Real.le_coe_toNNReal _))
  have hd : ∀ k : Fin 2, ∀ h : ℝ, 0 < |h| → |h| < t →
      PlanarHolderJetBound 2 (differenceQuotient u k h) (Metric.ball x₀ t) α C := by
    intro k h hh hsmall
    obtain ⟨ha, he, hf, hv1, Kh, hv2⟩ := hdata k h hh hsmall
    obtain ⟨K', hK', hp⟩ := hest x₀ _ ha _ _ F U Kh hf hv1 hv2 he
    refine ⟨hp.1, fun q hq => ⟨?_, (hp.2 q hq).2.mono_const (hC K' hK')⟩⟩
    intro x hx
    exact ((hp.2 q hq).1 x hx).trans (NNReal.coe_le_coe.mpr (hC K' hK'))
  have hut2 : PlanarHolderJetBound 2 u (Metric.ball x₀ (2 * t)) α K :=
    ⟨hut.1.mono (Metric.ball_subset_ball (by linarith)),
      fun q hq => ⟨fun x hx => (hut.2 q hq).1 x
        (Metric.ball_subset_ball (by linarith) hx),
        (hut.2 q hq).2.mono (Metric.ball_subset_ball (by linarith))⟩⟩
  obtain ⟨K', hgain⟩ := R5_difference_limit_C3 x₀ t ht u α K C hα hαone hut2 hd
  refine ⟨t / 4, K', by positivity, by linarith, ?_⟩
  convert hgain using 2 <;> ring

/-- Leibniz commutator source after differentiating the classical equation
along a finite coordinate word. This is a recursive formula, not a PDE
assertion or a final regularity field. -/
def derivedSource (a : E2 → PlanarMatrix) (f u : E2 → ℝ) :
    List (Fin 2) → E2 → ℝ
  | [] => f
  | k :: w => fun x => scalarPartial (derivedSource a f u w) k x -
      ∑ i : Fin 2, ∑ j : Fin 2, scalarPartial (fun y => a y i j) k x *
        planarHessian (partialWord u w) x i j

/-- Needed higher-order input producer. At word length m-2, the actual
partialWord has C2,alpha, and its source and the common principal field
have C1,alpha, all on one smaller ball with common bounds. -/
theorem R5_higher_classical_data
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R)
    (hball : Metric.closedBall x₀ (4 * R) ⊆ Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (m : ℕ) (hm : 3 ≤ m) (α K : NNReal) (hα : 0 < α) (hαone : α < 1)
    (hu : PlanarHolderJetBound m u (Metric.ball x₀ (4 * R)) α K)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R))
      (principalMatrix Q u) (classicalSource Q u) u) :
    ∃ s κ Λ : ℝ, ∃ H M : NNReal, 0 < s ∧ 4 * s ≤ R ∧ 0 < κ ∧ κ ≤ Λ ∧
      PlanarCoefficientControl (principalMatrix Q u) (Metric.ball x₀ (4 * s)) κ Λ H α ∧
      (∀ i j, PlanarHolderJetBound 1 (fun x => principalMatrix Q u x i j)
        (Metric.ball x₀ (4 * s)) α M) ∧
      (∀ w : List (Fin 2), w.length = m - 2 →
        PlanarHolderJetBound 2 (partialWord u w) (Metric.ball x₀ (4 * s)) α M ∧
        PlanarHolderJetBound 1
          (derivedSource (principalMatrix Q u) (classicalSource Q u) u w)
          (Metric.ball x₀ (4 * s)) α M ∧
        LinearClassicalEquation (Metric.ball x₀ (4 * s)) (principalMatrix Q u)
          (derivedSource (principalMatrix Q u) (classicalSource Q u) u w)
          (partialWord u w)) := by
  classical
  have hprincipalProvider
      (J T : Set Jet) (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ)
      (x₀ : E2) (R κ M : ℝ) (hR : 0 < R)
      (hjets : ∀ x ∈ Metric.closedBall x₀ (4 * R), firstJet u x ∈ T)
      (hbound : JetTubeBounds Q u x₀ R κ M T)
      (α M₁ : NNReal)
      (hcoeff : ∀ i j, PlanarHolderJetBound 1 (fun x => principalMatrix Q u x i j)
        (Metric.ball x₀ (4 * R)) α M₁) :
      ∃ Λ : ℝ, κ ≤ Λ ∧
        PlanarCoefficientControl (principalMatrix Q u) (Metric.ball x₀ (4 * R)) κ Λ M₁ α ∧
        (∀ x ∈ Metric.ball x₀ (4 * R), ∀ ξ : E2,
          (∑ i : Fin 2, ∑ j : Fin 2, principalMatrix Q u x i j * ξ i * ξ j) =
            inner ℝ (fluxDp Q (firstJet u x) ξ) ξ) := by
    classical
    have hprincipal (J : Set Jet) (Q : SmoothQuasilinearOperator J) (u : E2 → ℝ)
      (x₀ : E2) (R κ M : ℝ) (T : Set Jet) (α H : NNReal)
      (hj : ∀ x ∈ Metric.ball x₀ (4*R), firstJet u x ∈ T)
      (hb : JetTubeBounds Q u x₀ R κ M T)
      (hH : ∀ i j, HolderOnWith H α (fun x => principalMatrix Q u x i j) (Metric.ball x₀ (4*R))) :
      ∃ Λ : ℝ, κ ≤ Λ ∧ PlanarCoefficientControl (principalMatrix Q u)
        (Metric.ball x₀ (4*R)) κ Λ H α := by
      refine ⟨max κ M,le_max_left _ _,?_,⟩
      constructor
      · intro x hx i j
        simp only [principalMatrix,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul]
        ring
      · intro x hx ξ
        have hbQ := hb.2.2.2.2.2 (firstJet u x) (subset_closure (hj x hx)) ξ
        have he : (∑ i : Fin 2, ∑ j : Fin 2, principalMatrix Q u x i j*ξ i*ξ j) =
            inner ℝ (fluxDp Q (firstJet u x) ξ) ξ := by
          have hv : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
            ext i
            fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
          conv_rhs => rw [hv]
          simp only [principalMatrix,rawPrincipalMatrix,Matrix.smul_apply,Matrix.add_apply,
            Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,
            map_add,map_smul,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
          simp [coordinateVector,EuclideanSpace.single]
          ring
        rw [he]
        exact hbQ
      · intro x hx i j
        have hdp := (hb.2.2.2.1 (firstJet u x) (subset_closure (hj x hx))).2.2.2.2.1
        have he (k : Fin 2) : ‖coordinateVector 2 k‖ = 1 := by
          simp [coordinateVector,EuclideanSpace.single,PiLp.norm_single]
        have hraw (i j : Fin 2) : |rawPrincipalMatrix Q u x i j| ≤ M := by
          have h := PiLp.norm_apply_le (fluxDp Q (firstJet u x) (coordinateVector 2 j)) i
          rw [Real.norm_eq_abs] at h
          exact h.trans (((fluxDp Q (firstJet u x)).le_opNorm _).trans (by rw [he,mul_one];exact hdp))
        simp only [principalMatrix,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,abs_mul]
        have h1 := hraw i j
        have h2 := hraw j i
        have h3 := abs_add_le (rawPrincipalMatrix Q u x i j) (rawPrincipalMatrix Q u x j i)
        apply le_trans _ (le_max_right κ M)
        norm_num
        linarith
      · exact hH
    have hh (i j : Fin 2) : HolderOnWith M₁ α (fun x => principalMatrix Q u x i j) (Metric.ball x₀ (4*R)) := by
      intro x hx y hy
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq]
        using ((hcoeff i j).2 0 (by omega)).2 x hx y hy
    obtain ⟨Λ,hΛ,ha⟩ := hprincipal J Q u x₀ R κ M T α M₁
      (fun x hx => hjets x (Metric.ball_subset_closedBall hx)) hbound hh
    have hform (x : E2) (ξ : E2) : (∑ i : Fin 2, ∑ j : Fin 2, principalMatrix Q u x i j*ξ i*ξ j) =
        inner ℝ (fluxDp Q (firstJet u x) ξ) ξ := by
      have hv : ξ = ξ 0 • coordinateVector 2 0 + ξ 1 • coordinateVector 2 1 := by
        ext i
        fin_cases i <;> simp [coordinateVector,EuclideanSpace.single]
      conv_rhs => rw [hv]
      simp only [principalMatrix,rawPrincipalMatrix,Matrix.smul_apply,Matrix.add_apply,
        Matrix.transpose_apply,smul_eq_mul,Fin.sum_univ_two,PiLp.add_apply,PiLp.smul_apply,
        map_add,map_smul,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
      simp [coordinateVector,EuclideanSpace.single]
      ring
    exact ⟨Λ,hΛ,ha,fun x _ ξ => hform x ξ⟩
  have hwordProvider
      (B : Set E2) (hB : IsOpen B) (u : E2 → ℝ) (m : ℕ) (α K : NNReal)
      (hu : PlanarHolderJetBound m u B α K) (w : List (Fin 2)) (hw : w.length ≤ m) :
      PlanarHolderJetBound (m - w.length) (partialWord u w) B α K ∧
        (∀ q : ℕ, q + w.length ≤ m → ∀ x ∈ B, ∀ ξ : Fin q → E2,
          iteratedFDeriv ℝ q (partialWord u w) x ξ =
            iteratedFDeriv ℝ (q + w.length) u x
              (Fin.append ξ (fun j : Fin w.length => coordinateVector 2 (w.get j)))) := by
    classical
    have hpartial (n : ℕ) (hn : 1 ≤ n) (v : E2 → ℝ)
        (hv : PlanarHolderJetBound n v B α K) (k : Fin 2) :
        PlanarHolderJetBound (n-1) (scalarPartial v k) B α K ∧
        (∀ q : ℕ, q+1 ≤ n → ∀ x ∈ B, ∀ ξ : Fin q → E2,
          iteratedFDeriv ℝ q (scalarPartial v k) x ξ =
            iteratedFDeriv ℝ (q+1) v x (Fin.snoc ξ (coordinateVector 2 k))) := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 k)
      have he : ‖e‖ ≤ 1 := by
        apply e.opNorm_le_bound (by norm_num)
        intro L
        simpa only [e,ContinuousLinearMap.apply_apply,show ‖coordinateVector 2 k‖ = 1 by
          simp [coordinateVector,EuclideanSpace.single,PiLp.norm_single],mul_one,one_mul] using L.le_opNorm (coordinateVector 2 k)
      have hD : ContDiffOn ℝ (↑(n-1) : ℕ∞ω) (fderiv ℝ v) B :=
        hv.1.fderiv_of_isOpen hB (by exact_mod_cast (Nat.sub_add_cancel hn).le)
      have hjet (q : ℕ) (hq : q+1 ≤ n) (x : E2) (hx : x ∈ B) :
          iteratedFDeriv ℝ q (scalarPartial v k) x =
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x) := by
        change iteratedFDeriv ℝ q (e ∘ fderiv ℝ v) x = _
        apply e.iteratedFDeriv_comp_left (hD.contDiffAt (hB.mem_nhds hx))
        exact_mod_cast (show q ≤ n-1 by omega)
      have hmap (q : ℕ) (hq : q+1 ≤ n) (x : E2) (hx : x ∈ B) :
          ‖iteratedFDeriv ℝ q (scalarPartial v k) x‖ ≤ (K:ℝ) := by
        rw [hjet q hq x hx]
        calc
          _ ≤ ‖e‖*‖iteratedFDeriv ℝ q (fderiv ℝ v) x‖ := e.norm_compContinuousMultilinearMap_le _
          _ ≤ ‖iteratedFDeriv ℝ q (fderiv ℝ v) x‖  := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)
          _ = ‖iteratedFDeriv ℝ (q+1) v x‖ := norm_iteratedFDeriv_fderiv
          _ ≤ _ := (hv.2 (q+1) hq).1 x hx
      have hHolder (q : ℕ) (hq : q+1 ≤ n) :
          HolderOnWith K α (iteratedFDeriv ℝ q (scalarPartial v k)) B := by
        intro x hx y hy
        let I := (continuousMultilinearCurryRightEquiv' ℝ q E2 ℝ).symm
        have hdiff : dist (iteratedFDeriv ℝ q (fderiv ℝ v) x)
            (iteratedFDeriv ℝ q (fderiv ℝ v) y) =
            dist (iteratedFDeriv ℝ (q+1) v x) (iteratedFDeriv ℝ (q+1) v y) := by
          rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
          exact (I.isometry.dist_eq _ _).symm
        have hsub : e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x)-
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) y) =
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x-
              iteratedFDeriv ℝ q (fderiv ℝ v) y) := by
          ext ξ; simp [map_sub]
        have hh := ((hv.2 (q+1) hq).2).dist_le hx hy
        have hr : dist (iteratedFDeriv ℝ q (scalarPartial v k) x)
            (iteratedFDeriv ℝ q (scalarPartial v k) y) ≤ (K:ℝ)*dist x y^(α:ℝ) := by
          rw [hjet q hq x hx,hjet q hq y hy,dist_eq_norm,hsub]
          calc
            _ ≤ ‖e‖*‖iteratedFDeriv ℝ q (fderiv ℝ v) x-iteratedFDeriv ℝ q (fderiv ℝ v) y‖ := e.norm_compContinuousMultilinearMap_le _
            _ ≤ ‖iteratedFDeriv ℝ q (fderiv ℝ v) x-iteratedFDeriv ℝ q (fderiv ℝ v) y‖ := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)
            _ = dist (iteratedFDeriv ℝ (q+1) v x) (iteratedFDeriv ℝ (q+1) v y) := by rw [← dist_eq_norm,hdiff]
            _ ≤ _ := hh
        simpa only [edist_dist,ENNReal.ofReal_mul K.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
      refine ⟨⟨e.contDiff.comp_contDiffOn hD,?_⟩,?_⟩
      · intro q hq; exact ⟨hmap q (by omega),hHolder q (by omega)⟩
      · intro q hq x hx ξ
        rw [hjet q hq x hx]
        change (iteratedFDeriv ℝ q (fderiv ℝ v) x ξ) (coordinateVector 2 k) = _
        simp only [iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last]
    have hcast (r t : ℕ) (he : r=t) (x : E2) (η : Fin r → E2) :
        iteratedFDeriv ℝ r u x η =
          iteratedFDeriv ℝ t u x (η ∘ Fin.cast he.symm) := by
      subst t
      rfl
    induction w generalizing m with
    | nil =>
      refine ⟨by simpa only [partialWord,List.length_nil,Nat.sub_zero] using hu,?_⟩
      intro q hq x hx ξ
      simp only [partialWord,List.length_nil,Nat.add_zero,Fin.append_right_nil,Fin.cast_eq_self,Function.comp_id]
      congr 1
    | cons k w ih =>
      obtain ⟨hv,hvjet⟩ := ih m hu (by simpa only [List.length_cons] using Nat.le_of_succ_le hw)
      obtain ⟨hp,hpjet⟩ := hpartial (m-w.length) (by simp only [List.length_cons] at hw;omega)
        (partialWord u w) hv k
      refine ⟨?_,?_⟩
      · simpa only [partialWord,List.length_cons,Nat.sub_sub,Nat.add_comm w.length 1] using hp
      · intro q hq x hx ξ
        have hcons : (fun j : Fin (k::w).length => coordinateVector 2 ((k::w).get j)) =
            Fin.cons (coordinateVector 2 k) (fun j : Fin w.length => coordinateVector 2 (w.get j)) := by
          funext j
          cases j using Fin.cases <;> simp
        have he : q+1+w.length=q+(k::w).length := by simp only [List.length_cons];omega
        calc
          _ = iteratedFDeriv ℝ (q+1) (partialWord u w) x (Fin.snoc ξ (coordinateVector 2 k)) :=
            hpjet q (by simp only [List.length_cons] at hq;omega) x hx ξ
          _ = iteratedFDeriv ℝ (q+1+w.length) u x
              (Fin.append (Fin.snoc ξ (coordinateVector 2 k)) (fun j => coordinateVector 2 (w.get j))) :=
            hvjet (q+1) (by simp only [List.length_cons] at hq;omega) x hx _
          _ = _ := by
            rw [hcast _ _ he x,Fin.append_left_snoc,hcons]
            congr 1
  have hdifferentiationProvider
      (B : Set E2) (hB : IsOpen B) (a : E2 → PlanarMatrix) (f v : E2 → ℝ)
      (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) B)
      (hf : ContDiffOn ℝ 1 f B) (hv : ContDiffOn ℝ 3 v B)
      (heq : LinearClassicalEquation B a f v) (k : Fin 2) :
      LinearClassicalEquation B a
        (fun x => scalarPartial f k x - ∑ i : Fin 2, ∑ j : Fin 2,
          scalarPartial (fun y => a y i j) k x * planarHessian v x i j)
        (scalarPartial v k) := by
    classical
    have hP (g : E2 → ℝ) (n : ℕ) (hg : ContDiffOn ℝ (n+1) g B) (i : Fin 2) :
        ContDiffOn ℝ (↑n : ℕ∞ω) (scalarPartial g i) B := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 i)
      exact e.contDiff.comp_contDiffOn (hg.fderiv_of_isOpen hB (by simp))
    have hS (g : E2 → ℝ) (hg : ContDiffOn ℝ 2 g B)
        (x : E2) (hx : x ∈ B) (i j : Fin 2) :
        scalarPartial (scalarPartial g j) i x = planarHessian g x i j := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
      have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
        ((hg.fderiv_of_isOpen hB (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num)
      have hh := e.hasFDerivAt.comp x hd.hasFDerivAt
      have he := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hh.fderiv
      change (fderiv ℝ (fun y => fderiv ℝ g y (coordinateVector 2 j)) x) (coordinateVector 2 i) = _
      simpa only [planarHessian,Function.comp_def,ContinuousLinearMap.comp_apply,e,ContinuousLinearMap.apply_apply] using he
    have hcomm (g : E2 → ℝ) (hg : ContDiffOn ℝ 2 g B)
        (x : E2) (hx : x ∈ B) (i j : Fin 2) :
        scalarPartial (scalarPartial g j) i x = scalarPartial (scalarPartial g i) j x := by
      rw [hS g hg x hx i j,hS g hg x hx j i]
      exact (hg.contDiffAt (hB.mem_nhds hx)).isSymmSndFDerivAt (by norm_num)
        (coordinateVector 2 i) (coordinateVector 2 j)
    have hv2 : ContDiffOn ℝ 2 v B := hv.of_le (by norm_num)
    have hp2 (i : Fin 2) : ContDiffOn ℝ 2 (scalarPartial v i) B := hP v 2 hv i
    have hH1 (i j : Fin 2) : ContDiffOn ℝ 1 (fun x => planarHessian v x i j) B := by
      exact (hP (scalarPartial v j) 1 (hp2 j) i).congr (fun x hx => (hS v hv2 x hx i j).symm)
    have hH (x : E2) (hx : x ∈ B) (i j : Fin 2) :
        planarHessian (scalarPartial v k) x i j = scalarPartial (fun y => planarHessian v y i j) k x := by
      rw [← hS (scalarPartial v k) (hp2 k) x hx i j]
      have he : (fun y => scalarPartial (scalarPartial v k) j y) =ᶠ[𝓝 x]
          (fun y => scalarPartial (scalarPartial v j) k y) :=
        Filter.eventuallyEq_of_mem (hB.mem_nhds hx) (fun y hy => hcomm v hv2 y hy j k)
      have he' : (fun y => scalarPartial (scalarPartial v j) i y) =ᶠ[𝓝 x]
          (fun y => planarHessian v y i j) :=
        Filter.eventuallyEq_of_mem (hB.mem_nhds hx) (fun y hy => hS v hv2 y hy i j)
      calc
        _ = scalarPartial (scalarPartial (scalarPartial v j) k) i x :=
          congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) ((he.fderiv (𝕜 := ℝ)).eq_of_nhds)
        _ = scalarPartial (scalarPartial (scalarPartial v j) i) k x := hcomm (scalarPartial v j) (hp2 j) x hx i k
        _ = _ := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 k)) ((he'.fderiv (𝕜 := ℝ)).eq_of_nhds)
    intro x hx
    have hda (i j : Fin 2) := ((ha i j).contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num : (1:ℕ∞ω) ≠ 0)
    have hdH (i j : Fin 2) := ((hH1 i j).contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num : (1:ℕ∞ω) ≠ 0)
    have hd : HasFDerivAt (fun y => ∑ i : Fin 2, ∑ j : Fin 2, a y i j*planarHessian v y i j)
        (∑ i : Fin 2, ∑ j : Fin 2, (a x i j • fderiv ℝ (fun y => planarHessian v y i j) x+
          planarHessian v x i j • fderiv ℝ (fun y => a y i j) x)) x := by
      exact HasFDerivAt.fun_sum (fun i _ => HasFDerivAt.fun_sum (fun j _ =>
        (hda i j).hasFDerivAt.mul (hdH i j).hasFDerivAt))
    have he : (fun y => ∑ i : Fin 2, ∑ j : Fin 2, a y i j*planarHessian v y i j) =ᶠ[𝓝 x] f :=
      Filter.eventuallyEq_of_mem (hB.mem_nhds hx) (fun y hy => heq y hy)
    have he' := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 k))
      (hd.fderiv.symm.trans ((he.fderiv (𝕜 := ℝ)).eq_of_nhds))
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul] at he'
    change (∑ i : Fin 2, ∑ j : Fin 2, a x i j*planarHessian (scalarPartial v k) x i j) = _
    simp_rw [hH x hx]
    simp only [scalarPartial] at he' ⊢
    simp only [Fin.sum_univ_two] at he' ⊢
    nlinarith [he']
  have hnonlinearProvider
      (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
      (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
      (u : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R)
      (hball : Metric.closedBall x₀ (4 * R) ⊆ Ω)
      (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
      (m : ℕ) (hm : 3 ≤ m) (α K : NNReal) (hα : 0 < α) (hαone : α < 1)
      (hu : PlanarHolderJetBound m u (Metric.ball x₀ (4 * R)) α K) :
      ∃ s κ Λ : ℝ, ∃ H M : NNReal, 0 < s ∧ 4 * s ≤ R ∧ 0 < κ ∧ κ ≤ Λ ∧
        PlanarCoefficientControl (principalMatrix Q u) (Metric.ball x₀ (4 * s)) κ Λ H α ∧
        (∀ i j, PlanarHolderJetBound (m - 1) (fun x => principalMatrix Q u x i j)
          (Metric.ball x₀ (4 * s)) α M) ∧
        PlanarHolderJetBound (m - 1) (classicalSource Q u)
          (Metric.ball x₀ (4 * s)) α M := by
    classical
    have hcompose (B : Set E2) (hB : IsOpen B) (J T : Set Jet) (hJ : IsOpen J)
        (hT : IsCompact T) (hTJ : T ⊆ J) (f : Jet → ℝ) (hf : ContDiffOn ℝ ∞ f J)
        (G : E2 → Jet) (n : ℕ) (hG : ContDiffOn ℝ n G B) (hGT : MapsTo G B T)
        (α C : NNReal) (hGH : HolderOnWith C α G B)
        (hGj : ∀ q : ℕ, q ≤ n → (∀ x ∈ B, ‖iteratedFDeriv ℝ q G x‖ ≤ (C:ℝ)) ∧
          HolderOnWith C α (iteratedFDeriv ℝ q G) B) :
        ∃ M : NNReal, PlanarHolderJetBound n (fun x => f (G x)) B α M := by
      classical
      have hfd (r : ℕ) : FiniteDimensional ℝ (E2 [×r]→L[ℝ] Jet) := by
        induction r with
        | zero =>
          exact FiniteDimensional.of_injective
            (continuousMultilinearCurryFin0 ℝ E2 Jet).toLinearMap
            (continuousMultilinearCurryFin0 ℝ E2 Jet).injective
        | succ r ih =>
          letI := ih
          exact FiniteDimensional.of_injective
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => E2) Jet).toLinearMap
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => E2) Jet).injective
      have hq (q : ℕ) (hq : q ≤ n) : ∃ M : NNReal,
          (∀ x ∈ B, ‖iteratedFDeriv ℝ q (fun x => f (G x)) x‖ ≤ (M:ℝ)) ∧
          HolderOnWith M α (iteratedFDeriv ℝ q (fun x => f (G x))) B := by
        have hterm (c : OrderedFinpartition q) : ∃ M : NNReal,
            (∀ x ∈ B, ‖c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (G x))
              (fun i => iteratedFDeriv ℝ (c.partSize i) G x)‖ ≤ (M:ℝ)) ∧
            HolderOnWith M α (fun x => c.compAlongOrderedFinpartition
              (iteratedFDeriv ℝ c.length f (G x)) (fun i => iteratedFDeriv ℝ (c.partSize i) G x)) B := by
          let V := ∀ i : Fin c.length, E2 [×c.partSize i]→L[ℝ] Jet
          letI (i : Fin c.length) : FiniteDimensional ℝ (E2 [×c.partSize i]→L[ℝ] Jet) := hfd _
          let U : Set (Jet × V) := Prod.fst ⁻¹' J
          let A := c.compAlongOrderedFinpartitionL ℝ E2 Jet ℝ
          let F : Jet × V → E2 [×q]→L[ℝ] ℝ := fun z => A (iteratedFDeriv ℝ c.length f z.1) z.2
          have hU : IsOpen U := hJ.preimage continuous_fst
          have hj : ContDiffOn ℝ 1 (iteratedFDeriv ℝ c.length f) J := by
            intro z hz
            exact ((hf.contDiffAt (hJ.mem_nhds hz)).iteratedFDeriv_right (by simp)).contDiffWithinAt
          have hF : ContDiffOn ℝ 1 F U := by
            have hprod : ContDiffOn ℝ 1 (fun z : Jet × V => (iteratedFDeriv ℝ c.length f z.1,z.2)) U :=
              (hj.comp contDiffOn_fst (fun z hz => hz)).prodMk contDiffOn_snd
            exact (A.analyticOnNhd_uncurry_of_multilinear.contDiff.contDiffOn).comp hprod (mapsTo_univ _ _)
          let K : Set (Jet × V) := T ×ˢ Metric.closedBall 0 C
          have hK : IsCompact K := hT.prod (isCompact_closedBall _ _)
          have hKU : K ⊆ U := fun z hz => hTJ hz.1
          have hlocal : LocallyLipschitzOn U F := by
            intro z hz
            obtain ⟨D,W,hW,hD⟩ := (hF.contDiffAt (hU.mem_nhds hz)).exists_lipschitzOnWith
            exact ⟨D,W,mem_nhdsWithin_of_mem_nhds hW,hD⟩
          obtain ⟨D,hD⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK (hlocal.mono hKU)
          obtain ⟨N,hN⟩ := hK.exists_bound_of_continuousOn (hF.continuousOn.mono hKU)
          let P : E2 → Jet × V := fun x => (G x,fun i => iteratedFDeriv ℝ (c.partSize i) G x)
          have hPK : MapsTo P B K := by
            intro x hx
            refine ⟨hGT hx,?_⟩
            rw [Metric.mem_closedBall,dist_zero_right]
            exact (pi_norm_le_iff_of_nonneg C.coe_nonneg).mpr (fun i => (hGj _ ((c.partSize_le i).trans hq)).1 x hx)
          have hPH : HolderOnWith C α P B := by
            intro x hx y hy
            have hr : dist (P x) (P y) ≤ (C:ℝ)*dist x y^(α:ℝ) := by
              rw [Prod.dist_eq]
              apply max_le ((hGH.dist_le hx hy))
              apply (dist_pi_le_iff (by positivity)).mpr
              intro i
              exact ((hGj _ ((c.partSize_le i).trans hq)).2).dist_le hx hy
            simpa only [edist_dist,ENNReal.ofReal_mul C.coe_nonneg,
              ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
              using ENNReal.ofReal_le_ofReal hr
          have hH : HolderOnWith (D*C) α (F ∘ P) B := by
            simpa only [NNReal.coe_one,NNReal.rpow_one,one_mul] using hD.holderOnWith.comp hPH hPK
          refine ⟨Real.toNNReal N+D*C,?_,?_⟩
          · intro x hx
            exact (hN _ (hPK hx)).trans ((Real.le_coe_toNNReal N).trans (by simp only [NNReal.coe_add];exact le_add_of_nonneg_right (by positivity)))
          · exact hH.mono_const (le_add_left le_rfl)
        choose M hM using hterm
        let S : NNReal := ∑ c : OrderedFinpartition q, M c
        have he (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q (fun x => f (G x)) x =
            ∑ c : OrderedFinpartition q, c.compAlongOrderedFinpartition
              (iteratedFDeriv ℝ c.length f (G x)) (fun i => iteratedFDeriv ℝ (c.partSize i) G x) := by
          exact iteratedFDeriv_comp ((hf.of_le (by simp)).contDiffAt (hJ.mem_nhds (hTJ (hGT hx))))
            (hG.contDiffAt (hB.mem_nhds hx)) (by exact_mod_cast hq)
        refine ⟨S,?_,?_⟩
        · intro x hx
          rw [he x hx]
          exact (norm_sum_le _ _).trans (by simpa only [S,NNReal.coe_sum] using Finset.sum_le_sum (fun c _ => (hM c).1 x hx))
        · intro x hx y hy
          have hr : dist (iteratedFDeriv ℝ q (fun x => f (G x)) x)
              (iteratedFDeriv ℝ q (fun x => f (G x)) y) ≤ (S:ℝ)*dist x y^(α:ℝ) := by
            rw [he x hx,he y hy,dist_eq_norm,← Finset.sum_sub_distrib]
            calc
              _ ≤ ∑ c : OrderedFinpartition q, ‖c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (G x))
                  (fun i => iteratedFDeriv ℝ (c.partSize i) G x)-
                c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length f (G y))
                  (fun i => iteratedFDeriv ℝ (c.partSize i) G y)‖ := norm_sum_le _ _
              _ ≤ ∑ c : OrderedFinpartition q, (M c:ℝ)*dist x y^(α:ℝ) := Finset.sum_le_sum (fun c _ => by
                simpa only [dist_eq_norm] using ((hM c).2).dist_le hx hy)
              _ = _ := by simp only [S,NNReal.coe_sum,Finset.sum_mul]
          simpa only [edist_dist,ENNReal.ofReal_mul S.coe_nonneg,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
            using ENNReal.ofReal_le_ofReal hr
      choose M hM using (fun q : Fin (n+1) => hq q (by omega))
      let S : NNReal := ∑ q : Fin (n+1), M q
      refine ⟨S,(hf.of_le (by simp)).comp hG (fun x hx => hTJ (hGT hx)),?_⟩
      intro q hq
      have hle : M ⟨q,by omega⟩ ≤ S := Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ _)
      exact ⟨fun x hx => ((hM ⟨q,by omega⟩).1 x hx).trans (by exact_mod_cast hle),
        ((hM ⟨q,by omega⟩).2).mono_const hle⟩
    have hidentity (c : E2) (r : ℝ) (n : ℕ) (α : NNReal) (hαone : α < 1) :
        ∃ C : NNReal, ∀ q : ℕ, q ≤ n →
          (∀ x ∈ Metric.ball c r, ‖iteratedFDeriv ℝ q (id : E2 → E2) x‖ ≤ (C:ℝ)) ∧
          HolderOnWith C α (iteratedFDeriv ℝ q (id : E2 → E2)) (Metric.ball c r) := by
      classical
      have hq (q : ℕ) : ∃ C : NNReal,
          (∀ x ∈ Metric.ball c r, ‖iteratedFDeriv ℝ q (id : E2 → E2) x‖ ≤ (C:ℝ)) ∧
          HolderOnWith C α (iteratedFDeriv ℝ q (id : E2 → E2)) (Metric.ball c r) := by
        have hId : ContDiff ℝ ∞ (id : E2 → E2) := contDiff_id
        obtain ⟨N,hN⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
          (hId.continuous_iteratedFDeriv (m := q) (by simp)).continuousOn
        obtain ⟨D,hD⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
          (hId.continuous_iteratedFDeriv (m := q+1) (by simp)).continuousOn
        let A : NNReal := Real.toNNReal N+Real.toNNReal D+1
        have hn (x : E2) (hx : x ∈ Metric.ball c r) : ‖iteratedFDeriv ℝ q (id : E2 → E2) x‖ ≤ (A:ℝ) :=
          (hN x (Metric.ball_subset_closedBall hx)).trans ((Real.le_coe_toNNReal N).trans (by
            change _ ≤ (Real.toNNReal N:ℝ)+(Real.toNNReal D:ℝ)+1
            nlinarith [(Real.toNNReal N).coe_nonneg,(Real.toNNReal D).coe_nonneg]))
        have hl : LipschitzOnWith A (iteratedFDeriv ℝ q (id : E2 → E2)) (Metric.ball c r) := by
          apply (convex_ball c r).lipschitzOnWith_of_nnnorm_fderiv_le
            (fun x _ => (hId.differentiable_iteratedFDeriv (ENat.natCast_lt_of_coe_top_le_withTop le_rfl q)) x)
          intro x hx
          apply NNReal.coe_le_coe.mp
          change ‖fderiv ℝ (iteratedFDeriv ℝ q (id : E2 → E2)) x‖ ≤ (A:ℝ)
          rw [norm_fderiv_iteratedFDeriv]
          exact (hD x (Metric.ball_subset_closedBall hx)).trans ((Real.le_coe_toNNReal D).trans (by
            change _ ≤ (Real.toNNReal N:ℝ)+(Real.toNNReal D:ℝ)+1
            nlinarith [(Real.toNNReal N).coe_nonneg,(Real.toNNReal D).coe_nonneg]))
        refine ⟨3*A,fun x hx => (hn x hx).trans (by simp only [NNReal.coe_mul,NNReal.coe_ofNat];nlinarith [A.coe_nonneg]),?_⟩
        intro x hx y hy
        have hr : dist (iteratedFDeriv ℝ q (id : E2 → E2) x) (iteratedFDeriv ℝ q (id : E2 → E2) y) ≤
            ((3*A:NNReal):ℝ)*dist x y^(α:ℝ) := by
          simp only [NNReal.coe_mul,NNReal.coe_ofNat]
          by_cases hd : dist x y ≤ 1
          · have hb := hl.dist_le_mul x hx y hy
            have hp := Real.self_le_rpow_of_le_one dist_nonneg hd (by exact_mod_cast hαone.le)
            exact (hb.trans (mul_le_mul_of_nonneg_left hp A.coe_nonneg)).trans
              (mul_le_mul_of_nonneg_right (by nlinarith [A.coe_nonneg]) (Real.rpow_nonneg dist_nonneg _))
          · have hb := (dist_le_norm_add_norm _ _).trans (add_le_add (hn x hx) (hn y hy))
            have hp := Real.one_le_rpow (by linarith : 1 ≤ dist x y) α.coe_nonneg
            nlinarith [A.coe_nonneg]
        simpa only [edist_dist,ENNReal.ofReal_mul (3*A).coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
      choose C hC using (fun q : Fin (n+1) => hq q)
      let S : NNReal := ∑ q : Fin (n+1), C q
      refine ⟨S,?_⟩
      intro q hq
      have hle : C ⟨q,by omega⟩ ≤ S := Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ _)
      exact ⟨fun x hx => ((hC ⟨q,by omega⟩).1 x hx).trans (by exact_mod_cast hle),
        ((hC ⟨q,by omega⟩).2).mono_const hle⟩
    have hfirst (B : Set E2) (hB : IsOpen B) (u : E2 → ℝ) (m : ℕ) (hm : 1 ≤ m)
        (α K I : NNReal) (hu : PlanarHolderJetBound m u B α K)
        (hId : ∀ q : ℕ, q ≤ m-1 → (∀ x ∈ B, ‖iteratedFDeriv ℝ q (id : E2 → E2) x‖ ≤ (I:ℝ)) ∧
          HolderOnWith I α (iteratedFDeriv ℝ q (id : E2 → E2)) B) :
        ∃ C : NNReal, ContDiffOn ℝ (↑(m-1):ℕ∞ω) (firstJet u) B ∧
          HolderOnWith C α (firstJet u) B ∧
          ∀ q : ℕ, q ≤ m-1 → (∀ x ∈ B, ‖iteratedFDeriv ℝ q (firstJet u) x‖ ≤ (C:ℝ)) ∧
            HolderOnWith C α (iteratedFDeriv ℝ q (firstJet u)) B := by
      classical
      let L : (E2 →L[ℝ] ℝ) →L[ℝ] E2 :=
        ∑ i : Fin 2, (ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 i)).smulRight (coordinateVector 2 i)
      have hL (x : E2) : L (fderiv ℝ u x) = planarGradient u x := by simp [L,planarGradient]
      have hdu : ContDiffOn ℝ (↑(m-1):ℕ∞ω) (fderiv ℝ u) B :=
        hu.1.fderiv_of_isOpen hB (by exact_mod_cast (Nat.sub_add_cancel hm).le)
      have hgrad : ContDiffOn ℝ (↑(m-1):ℕ∞ω) (planarGradient u) B := by
        simpa only [Function.comp_def,hL] using L.contDiff.comp_contDiffOn hdu
      have huc : ContDiffOn ℝ (↑(m-1):ℕ∞ω) u B := hu.1.of_le (by exact_mod_cast Nat.sub_le m 1)
      have hG : ContDiffOn ℝ (↑(m-1):ℕ∞ω) (firstJet u) B := contDiffOn_id.prodMk (huc.prodMk hgrad)
      let C : NNReal := I+K+‖L‖₊*K
      have hIK : (I:ℝ) ≤ (C:ℝ) := by change _ ≤ (I:ℝ)+(K:ℝ)+‖L‖*(K:ℝ);nlinarith [I.coe_nonneg,K.coe_nonneg,norm_nonneg L,mul_nonneg (norm_nonneg L) K.coe_nonneg]
      have hKK : (K:ℝ) ≤ (C:ℝ) := by change _ ≤ (I:ℝ)+(K:ℝ)+‖L‖*(K:ℝ);nlinarith [I.coe_nonneg,K.coe_nonneg,norm_nonneg L,mul_nonneg (norm_nonneg L) K.coe_nonneg]
      have hLK : ‖L‖*(K:ℝ) ≤ (C:ℝ) := by change _ ≤ (I:ℝ)+(K:ℝ)+‖L‖*(K:ℝ);nlinarith [I.coe_nonneg,K.coe_nonneg,norm_nonneg L]
      have hQ (q : ℕ) (hq : q ≤ m-1) : (∀ x ∈ B, ‖iteratedFDeriv ℝ q (firstJet u) x‖ ≤ (C:ℝ)) ∧
          HolderOnWith C α (iteratedFDeriv ℝ q (firstJet u)) B := by
        have hq' : q+1 ≤ m := by omega
        have hgq (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q (planarGradient u) x =
            L.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ u) x) := by
          change iteratedFDeriv ℝ q (L ∘ fderiv ℝ u) x = _
          exact L.iteratedFDeriv_comp_left (hdu.contDiffAt (hB.mem_nhds hx)) (by exact_mod_cast hq)
        have he (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q (firstJet u) x =
            (iteratedFDeriv ℝ q (id : E2 → E2) x).prod
            ((iteratedFDeriv ℝ q u x).prod (iteratedFDeriv ℝ q (planarGradient u) x)) := by
          change iteratedFDeriv ℝ q (fun y => (id y,(u y,planarGradient u y))) x = _
          rw [iteratedFDeriv_prodMk contDiffAt_id ((huc.prodMk hgrad).contDiffAt (hB.mem_nhds hx)) (by exact_mod_cast hq)]
          rw [iteratedFDeriv_prodMk (huc.contDiffAt (hB.mem_nhds hx)) (hgrad.contDiffAt (hB.mem_nhds hx)) (by exact_mod_cast hq)]
        constructor
        · intro x hx
          rw [he x hx,ContinuousMultilinearMap.opNorm_prod,ContinuousMultilinearMap.opNorm_prod]
          apply max_le ((hId q hq).1 x hx |>.trans hIK)
          apply max_le (((hu.2 q (by omega)).1 x hx).trans hKK)
          rw [hgq x hx]
          exact (L.norm_compContinuousMultilinearMap_le _).trans (by
            rw [norm_iteratedFDeriv_fderiv]
            exact (mul_le_mul_of_nonneg_left ((hu.2 (q+1) hq').1 x hx) (norm_nonneg _)).trans hLK)
        · intro x hx y hy
          have hprod {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
              (A A' : E2 [×q]→L[ℝ] F) (D D' : E2 [×q]→L[ℝ] G) :
              ‖A.prod D-A'.prod D'‖ = max ‖A-A'‖ ‖D-D'‖ := by
            have he : A.prod D-A'.prod D'=(A-A').prod (D-D') := by ext ξ <;> rfl
            rw [he,ContinuousMultilinearMap.opNorm_prod]
          have hdiff : ‖iteratedFDeriv ℝ q (fderiv ℝ u) x-iteratedFDeriv ℝ q (fderiv ℝ u) y‖ =
              ‖iteratedFDeriv ℝ (q+1) u x-iteratedFDeriv ℝ (q+1) u y‖ := by
            rw [← dist_eq_norm,← dist_eq_norm,iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
            exact ((continuousMultilinearCurryRightEquiv' ℝ q E2 ℝ).symm.isometry.dist_eq _ _).symm
          have hsub : L.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ u) x)-
              L.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ u) y)=
              L.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ u) x-iteratedFDeriv ℝ q (fderiv ℝ u) y) := by
            ext ξ; simp [map_sub]
          have hr : dist (iteratedFDeriv ℝ q (firstJet u) x) (iteratedFDeriv ℝ q (firstJet u) y) ≤
              (C:ℝ)*dist x y^(α:ℝ) := by
            rw [he x hx,he y hy,dist_eq_norm,hprod,hprod]
            apply max_le
            · exact ((by simpa only [dist_eq_norm] using ((hId q hq).2).dist_le hx hy):
                ‖iteratedFDeriv ℝ q (id : E2 → E2) x-iteratedFDeriv ℝ q (id : E2 → E2) y‖ ≤ (I:ℝ)*dist x y^(α:ℝ)).trans
                (mul_le_mul_of_nonneg_right hIK (Real.rpow_nonneg dist_nonneg _))
            · apply max_le
              · simpa only [dist_eq_norm] using (((hu.2 q (by omega)).2).dist_le hx hy).trans
                  (mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg dist_nonneg _))
              · rw [hgq x hx,hgq y hy,hsub]
                calc
                  _ ≤ ‖L‖*‖iteratedFDeriv ℝ q (fderiv ℝ u) x-iteratedFDeriv ℝ q (fderiv ℝ u) y‖ := L.norm_compContinuousMultilinearMap_le _
                  _ ≤ ‖L‖*((K:ℝ)*dist x y^(α:ℝ)) := by
                    rw [hdiff]
                    exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using ((hu.2 (q+1) hq').2).dist_le hx hy) (norm_nonneg _)
                  _ = (‖L‖*(K:ℝ))*dist x y^(α:ℝ) := by ring
                  _ ≤ _ := mul_le_mul_of_nonneg_right hLK (Real.rpow_nonneg dist_nonneg _)
          simpa only [edist_dist,ENNReal.ofReal_mul C.coe_nonneg,
            ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
            using ENNReal.ofReal_le_ofReal hr
      refine ⟨C,hG,?_,hQ⟩
      intro x hx y hy
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
        (continuousMultilinearCurryFin0 ℝ E2 Jet).symm.isometry.edist_eq] using (hQ 0 (by omega)).2 x hx y hy
    have hscalarSmooth (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J) :
      (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun z : Jet => (1/2:ℝ) *
        (((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 j))) i +
         ((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 i))) j)) J) ∧
      ContDiffOn ℝ ∞ (fun z : Jet => -Q.lowerOrder z - ∑ i : Fin 2,
        (((fderiv ℝ Q.flux z) (coordinateVector 2 i,(0,0))) i +
         ((fderiv ℝ Q.flux z) (0,(1,0))) i * z.2.2 i)) J := by
      have hd : ContDiffOn ℝ ∞ (fderiv ℝ Q.flux) J := Q.flux_smooth.fderiv_of_isOpen hJ (by simp)
      have he (v : Jet) (i : Fin 2) : ContDiffOn ℝ ∞ (fun z : Jet => fderiv ℝ Q.flux z v i) J := by
        simpa only [Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply] using
          (EuclideanSpace.proj i).contDiff.comp_contDiffOn (hd.clm_apply contDiffOn_const)
      have hp (i : Fin 2) : ContDiffOn ℝ ∞ (fun z : Jet => z.2.2 i) J := by
        have hp0 : ContDiffOn ℝ ∞ (fun z : Jet => z.2.2) J := by fun_prop
        simpa only [Function.comp_def,EuclideanSpace.proj,PiLp.proj_apply] using
          (EuclideanSpace.proj i).contDiff.comp_contDiffOn hp0
      constructor
      · intro i j
        exact contDiffOn_const.mul ((he _ i).add (he _ j))
      · exact (Q.lowerOrder_smooth.of_le (by simp)).neg.sub
          (ContDiffOn.sum (fun i _ => (he _ i).add ((he _ i).mul (hp i))))
    have hscalarEq (J : Set Jet) (hJ : IsOpen J) (Q : SmoothQuasilinearOperator J)
      (u : E2 → ℝ) (x : E2) (hx : firstJet u x ∈ J) :
      (∀ i j : Fin 2, principalMatrix Q u x i j = (1/2:ℝ) *
        (((fderiv ℝ Q.flux (firstJet u x)) (0,(0,coordinateVector 2 j))) i +
         ((fderiv ℝ Q.flux (firstJet u x)) (0,(0,coordinateVector 2 i))) j)) ∧
      classicalSource Q u x = -Q.lowerOrder (firstJet u x) - ∑ i : Fin 2,
        (((fderiv ℝ Q.flux (firstJet u x)) (coordinateVector 2 i,(0,0))) i +
         ((fderiv ℝ Q.flux (firstJet u x)) (0,(1,0))) i * (firstJet u x).2.2 i) := by
      have hq := (Q.flux_smooth.contDiffAt (hJ.mem_nhds hx)).differentiableAt (by simp)
      constructor
      · intro i j
        unfold principalMatrix rawPrincipalMatrix fluxDp
        rw [Helpers.fderiv_p_slice Q.flux (firstJet u x) hq]
        simp only [Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,
          ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
        rfl
      · unfold classicalSource fluxDx fluxDz
        rw [Helpers.fderiv_x_slice Q.flux (firstJet u x) hq,
          Helpers.fderiv_z_slice Q.flux (firstJet u x) hq]
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply,firstJet]
        rfl
    let B := Metric.ball x₀ (4*R)
    have hB : IsOpen B := Metric.isOpen_ball
    have hC1 : ContDiffOn ℝ 1 u B := hu.1.of_le (by exact_mod_cast (show 1 ≤ m by omega))
    have hjB (x : E2) (hx : x ∈ B) : firstJet u x ∈ J := hjets x (hball (Metric.ball_subset_closedBall hx))
    obtain ⟨r,κ,L,T,hr,_,_,hT,hTcompact,hTJ,hjT,hbound⟩ :=
      R1_local_jet_tube B hB J hJ Q helliptic u hC1 hjB x₀ (Metric.mem_ball_self (by positivity))
    let s := min r (R/4)
    have hs : 0 < s := lt_min hr (by positivity)
    have hsr : s ≤ r := min_le_left _ _
    have hsR : 4*s ≤ R := by have := min_le_right r (R/4);dsimp only [s] at *;linarith
    have hsmallB : Metric.ball x₀ (4*s) ⊆ B := Metric.ball_subset_ball (by linarith)
    have hjT' (x : E2) (hx : x ∈ Metric.closedBall x₀ (4*s)) : firstJet u x ∈ T :=
      hjT x (Metric.closedBall_subset_closedBall (by linarith) hx)
    have hbound' : JetTubeBounds Q u x₀ s κ L T := by
      refine ⟨hbound.1,hbound.2.1,?_,hbound.2.2.2⟩
      intro x hx
      exact hbound.2.2.1 x (Metric.closedBall_subset_closedBall (by linarith) hx)
    let D := Metric.ball x₀ (4*s)
    have hD : IsOpen D := Metric.isOpen_ball
    have huD : PlanarHolderJetBound m u D α K :=
      ⟨hu.1.mono hsmallB,fun q hq => ⟨fun x hx => (hu.2 q hq).1 x (hsmallB hx),((hu.2 q hq).2).mono hsmallB⟩⟩
    obtain ⟨Id,hId⟩ := hidentity x₀ (4*s) (m-1) α hαone
    obtain ⟨Cg,hG,hGH,hGj⟩ := hfirst D hD u m (by omega) α K Id huD hId
    have hGT : MapsTo (firstJet u) D (closure T) := fun x hx => subset_closure (hjT' x (Metric.ball_subset_closedBall hx))
    let coeff (i j : Fin 2) (z : Jet) : ℝ := (1/2:ℝ)*
      (((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 j))) i+
       ((fderiv ℝ Q.flux z) (0,(0,coordinateVector 2 i))) j)
    let source (z : Jet) : ℝ := -Q.lowerOrder z-∑ i : Fin 2,
      (((fderiv ℝ Q.flux z) (coordinateVector 2 i,(0,0))) i+
       ((fderiv ℝ Q.flux z) (0,(1,0))) i*z.2.2 i)
    have hcExist (i j : Fin 2) : ∃ A : NNReal,
        PlanarHolderJetBound (m-1) (fun x => coeff i j (firstJet u x)) D α A :=
      hcompose D hD J (closure T) hJ hTcompact hTJ (coeff i j) ((hscalarSmooth J hJ Q).1 i j)
        (firstJet u) (m-1) hG hGT α Cg hGH hGj
    have hsExist : ∃ A : NNReal, PlanarHolderJetBound (m-1)
        (fun x => source (firstJet u x)) D α A :=
      hcompose D hD J (closure T) hJ hTcompact hTJ source (hscalarSmooth J hJ Q).2
        (firstJet u) (m-1) hG hGT α Cg hGH hGj
    choose A hA using hcExist
    obtain ⟨As,hAs⟩ := hsExist
    let M : NNReal := As+∑ i : Fin 2,∑ j : Fin 2,A i j
    have hcost (i j : Fin 2) : A i j ≤ M := by
      have hh : A i j ≤ ∑ i : Fin 2, ∑ j : Fin 2, A i j :=
        (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => show 0 ≤ A i j from zero_le) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => show 0 ≤ ∑ j : Fin 2, A i j from zero_le) (Finset.mem_univ i))
      exact hh.trans (le_add_left le_rfl)
    have hmono (f : E2 → ℝ) (C : NNReal) (hC : C ≤ M)
        (hf : PlanarHolderJetBound (m-1) f D α C) : PlanarHolderJetBound (m-1) f D α M := by
      exact ⟨hf.1,fun q hq => ⟨fun x hx => ((hf.2 q hq).1 x hx).trans (by exact_mod_cast hC),((hf.2 q hq).2).mono_const hC⟩⟩
    have hcongr (f g : E2 → ℝ) (hf : PlanarHolderJetBound (m-1) f D α M) (he : EqOn f g D) :
        PlanarHolderJetBound (m-1) g D α M := by
      have hi (q : ℕ) (x : E2) (hx : x ∈ D) : iteratedFDeriv ℝ q f x=iteratedFDeriv ℝ q g x :=
        ((Filter.eventuallyEq_of_mem (hD.mem_nhds hx) he).iteratedFDeriv ℝ q).eq_of_nhds
      refine ⟨hf.1.congr he.symm,fun q hq => ⟨?_,?_⟩⟩
      · intro x hx;rw [← hi q x hx];exact (hf.2 q hq).1 x hx
      · intro x hx y hy;rw [← hi q x hx,← hi q y hy];exact (hf.2 q hq).2 x hx y hy
    have hcoeff (i j : Fin 2) : PlanarHolderJetBound (m-1) (fun x => principalMatrix Q u x i j) D α M := by
      apply hcongr _ _ (hmono _ _ (hcost i j) (hA i j))
      intro x hx
      exact ((hscalarEq J hJ Q u x (hjB x (hsmallB hx))).1 i j).symm
    have hsource : PlanarHolderJetBound (m-1) (classicalSource Q u) D α M := by
      apply hcongr _ _ (hmono _ _ (le_add_right le_rfl) hAs)
      intro x hx
      exact (hscalarEq J hJ Q u x (hjB x (hsmallB hx))).2.symm
    have hc1 (i j : Fin 2) : PlanarHolderJetBound 1 (fun x => principalMatrix Q u x i j) D α M :=
      ⟨(hcoeff i j).1.of_le (by exact_mod_cast (show 1 ≤ m-1 by omega)),
        fun q hq => (hcoeff i j).2 q (by omega)⟩
    obtain ⟨Λ,hκΛ,ha,_⟩ := hprincipalProvider J T Q u x₀ s κ L hs hjT' hbound' α M hc1
    exact ⟨s,κ,Λ,M,M,hs,hsR,hbound.1,hκΛ,ha,hcoeff,hsource⟩
  have hderiveProvider
      (B : Set E2) (hB : IsOpen B) (a : E2 → PlanarMatrix) (f u : E2 → ℝ)
      (m : ℕ) (hm : 3 ≤ m) (α K M : NNReal)
      (hu : PlanarHolderJetBound m u B α K)
      (ha : ∀ i j, PlanarHolderJetBound (m - 1) (fun x => a x i j) B α M)
      (hf : PlanarHolderJetBound (m - 1) f B α M)
      (heq : LinearClassicalEquation B a f u) :
      ∀ w : List (Fin 2), w.length ≤ m - 2 → ∃ L : NNReal,
        PlanarHolderJetBound (m - w.length) (partialWord u w) B α L ∧
        PlanarHolderJetBound (m - 1 - w.length) (derivedSource a f u w) B α L ∧
        LinearClassicalEquation B a (derivedSource a f u w) (partialWord u w) := by
      classical
    have hproduct (B : Set E2) (hB : IsOpen B) (f g : E2 → ℝ) (n : ℕ) (α A D : NNReal)
        (hf : PlanarHolderJetBound n f B α A) (hg : PlanarHolderJetBound n g B α D) :
        PlanarHolderJetBound n (fun x => f x*g x) B α (2^(n+1)*A*D) := by
      classical
      have hmul {S : Set E2} (hS : IsOpen S) {x : E2} (hx : x ∈ S) {f g : E2 → ℝ}
          (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g S) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
          (hfb : ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j f x‖ ≤ C)
          (hgb : ∀ j : ℕ, j ≤ n → ‖iteratedFDeriv ℝ j g x‖ ≤ D)
          (q : ℕ) (hq : q ≤ n) : ‖iteratedFDeriv ℝ q (fun z => f z*g z) x‖ ≤ 2^n*C*D := by
        have hs := norm_iteratedFDerivWithin_mul_le hf hg hS.uniqueDiffOn hx (n := q) (by exact_mod_cast hq)
        simp_rw [iteratedFDerivWithin_of_isOpen _ hS hx] at hs
        apply hs.trans
        calc
          _ ≤ ∑ i ∈ Finset.range (q+1), (q.choose i:ℝ)*C*D := by
            apply Finset.sum_le_sum
            intro i hi
            have hiq : i ≤ q := by have := Finset.mem_range.mp hi;omega
            gcongr
            · exact hfb i (hiq.trans hq)
            · exact hgb (q-i) ((Nat.sub_le _ _).trans hq)
          _ = 2^q*C*D := by
            rw [← Finset.sum_mul,← Finset.sum_mul]
            congr 2
            exact_mod_cast Nat.sum_range_choose q
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hq) hC) hD
      refine ⟨hf.1.mul hg.1,fun q hq => ⟨?_,?_⟩⟩
      · intro x hx
        have hb := hmul hB hx hf.1 hg.1 A.coe_nonneg D.coe_nonneg
          (fun j hj => (hf.2 j hj).1 x hx) (fun j hj => (hg.2 j hj).1 x hx) q hq
        exact hb.trans (by simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,pow_succ];nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n,mul_nonneg A.coe_nonneg D.coe_nonneg])
      · intro x hx y hy
        let S : Set E2 := (fun z => z+x) ⁻¹' B ∩ (fun z => z+y) ⁻¹' B
        have hS : IsOpen S := (hB.preimage (continuous_id.add continuous_const)).inter
          (hB.preimage (continuous_id.add continuous_const))
        have hS0 : (0:E2) ∈ S := by simpa only [S,Set.mem_inter_iff,Set.mem_preimage,zero_add] using And.intro hx hy
        have hfx : ContDiffOn ℝ n (fun z => f (z+x)) S := hf.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.1)
        have hfy : ContDiffOn ℝ n (fun z => f (z+y)) S := hf.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.2)
        have hgx : ContDiffOn ℝ n (fun z => g (z+x)) S := hg.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.1)
        have hgy : ContDiffOn ℝ n (fun z => g (z+y)) S := hg.1.comp
          (contDiffOn_id.add contDiffOn_const) (fun z hz => hz.2)
        have hfxb (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j (fun z => f (z+x)) 0‖ ≤ (A:ℝ) := by
          simpa only [iteratedFDeriv_comp_add_right,zero_add] using (hf.2 j hj).1 x hx
        have hgyb (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j (fun z => g (z+y)) 0‖ ≤ (D:ℝ) := by
          simpa only [iteratedFDeriv_comp_add_right,zero_add] using (hg.2 j hj).1 y hy
        have hdiff (f : E2 → ℝ) (A : NNReal) (hf : PlanarHolderJetBound n f B α A)
            (hfX : ContDiffOn ℝ n (fun z => f (z+x)) S) (hfY : ContDiffOn ℝ n (fun z => f (z+y)) S)
            (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j (fun z => f (z+x)-f (z+y)) 0‖ ≤
              (A:ℝ)*dist x y^(α:ℝ) := by
          have hc := ((hf.2 j hj).2).dist_le hx hy
          rw [dist_eq_norm] at hc
          simpa only [fun_iteratedFDeriv_sub_apply
            ((hfX.of_le (by exact_mod_cast hj)).contDiffAt (hS.mem_nhds hS0))
            ((hfY.of_le (by exact_mod_cast hj)).contDiffAt (hS.mem_nhds hS0)),
            iteratedFDeriv_comp_add_right,zero_add] using hc
        have hb1 := hmul hS hS0 hfx (hgx.sub hgy) A.coe_nonneg
          (by positivity : 0 ≤ (D:ℝ)*dist x y^(α:ℝ)) hfxb (fun j hj => hdiff g D hg hgx hgy j hj) q hq
        have hb2 := hmul hS hS0 (hfx.sub hfy) hgy
          (by positivity : 0 ≤ (A:ℝ)*dist x y^(α:ℝ)) D.coe_nonneg
          (fun j hj => hdiff f A hf hfx hfy j hj) hgyb q hq
        have he : (fun z => f (z+x)*g (z+x)-f (z+y)*g (z+y)) =
            (fun z => f (z+x)*(g (z+x)-g (z+y))+(f (z+x)-f (z+y))*g (z+y)) := by funext z;ring
        have hd := congrArg (fun F : E2 → ℝ => iteratedFDeriv ℝ q F 0) he
        rw [fun_iteratedFDeriv_sub_apply
          (((hfx.mul hgx).of_le (by exact_mod_cast hq)).contDiffAt (hS.mem_nhds hS0))
          (((hfy.mul hgy).of_le (by exact_mod_cast hq)).contDiffAt (hS.mem_nhds hS0)),
          fun_iteratedFDeriv_add_apply
          (((hfx.mul (hgx.sub hgy)).of_le (by exact_mod_cast hq)).contDiffAt (hS.mem_nhds hS0))
          ((((hfx.sub hfy).mul hgy).of_le (by exact_mod_cast hq)).contDiffAt (hS.mem_nhds hS0))] at hd
        have ht (z : E2) : iteratedFDeriv ℝ q (fun x => f (x+z)*g (x+z)) 0=
            iteratedFDeriv ℝ q (fun x => f x*g x) z := by
          simpa only [zero_add] using iteratedFDeriv_comp_add_right (f := fun x => f x*g x) q z (0:E2)
        rw [ht x,ht y] at hd
        have hr : dist (iteratedFDeriv ℝ q (fun x => f x*g x) x)
            (iteratedFDeriv ℝ q (fun x => f x*g x) y) ≤ ((2^(n+1)*A*D:NNReal):ℝ)*dist x y^(α:ℝ) := by
          rw [dist_eq_norm,hd]
          exact (norm_add_le _ _).trans ((add_le_add hb1 hb2).trans_eq (by
            simp only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,pow_succ];ring))
        simpa only [edist_dist,ENNReal.ofReal_mul (2^(n+1)*A*D).coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
    have hmono (n : ℕ) (f : E2 → ℝ) (A D : NNReal) (hAD : A ≤ D)
        (hf : PlanarHolderJetBound n f B α A) : PlanarHolderJetBound n f B α D :=
      ⟨hf.1,fun q hq => ⟨fun x hx => ((hf.2 q hq).1 x hx).trans (by exact_mod_cast hAD),((hf.2 q hq).2).mono_const hAD⟩⟩
    have hreduce (n r : ℕ) (hr : r ≤ n) (f : E2 → ℝ) (A : NNReal)
        (hf : PlanarHolderJetBound n f B α A) : PlanarHolderJetBound r f B α A :=
      ⟨hf.1.of_le (by exact_mod_cast hr),fun q hq => hf.2 q (hq.trans hr)⟩
    have hcongr (n : ℕ) (f g : E2 → ℝ) (A : NNReal) (hf : PlanarHolderJetBound n f B α A) (he : EqOn f g B) :
        PlanarHolderJetBound n g B α A := by
      have hi (q : ℕ) (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q f x=iteratedFDeriv ℝ q g x :=
        ((Filter.eventuallyEq_of_mem (hB.mem_nhds hx) he).iteratedFDeriv ℝ q).eq_of_nhds
      refine ⟨hf.1.congr he.symm,fun q hq => ⟨?_,?_⟩⟩
      · intro x hx;rw [← hi q x hx];exact (hf.2 q hq).1 x hx
      · intro x hx y hy;rw [← hi q x hx,← hi q y hy];exact (hf.2 q hq).2 x hx y hy
    have hadd (n : ℕ) (f g : E2 → ℝ) (A D : NNReal)
        (hf : PlanarHolderJetBound n f B α A) (hg : PlanarHolderJetBound n g B α D) :
        PlanarHolderJetBound n (fun x => f x+g x) B α (A+D) := by
      refine ⟨hf.1.add hg.1,?_⟩
      intro q hq
      have he (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q (fun x => f x+g x) x =
          iteratedFDeriv ℝ q f x+iteratedFDeriv ℝ q g x :=
        fun_iteratedFDeriv_add_apply ((hf.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds hx))
          ((hg.1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds hx))
      constructor
      · intro x hx
        rw [he x hx]
        exact (norm_add_le _ _).trans (by exact_mod_cast add_le_add ((hf.2 q hq).1 x hx) ((hg.2 q hq).1 x hx))
      · intro x hx y hy
        have hr : dist (iteratedFDeriv ℝ q (fun x => f x+g x) x) (iteratedFDeriv ℝ q (fun x => f x+g x) y) ≤
            ((A+D:NNReal):ℝ)*dist x y^(α:ℝ) := by
          rw [he x hx,he y hy]
          exact (dist_add_add_le _ _ _ _).trans ((add_le_add ((hf.2 q hq).2.dist_le hx hy) ((hg.2 q hq).2.dist_le hx hy)).trans_eq (by simp only [NNReal.coe_add];ring))
        simpa only [edist_dist,ENNReal.ofReal_mul (A+D).coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
    have hneg (n : ℕ) (f : E2 → ℝ) (A : NNReal) (hf : PlanarHolderJetBound n f B α A) :
        PlanarHolderJetBound n (fun x => -f x) B α A := by
      refine ⟨hf.1.neg,?_⟩
      intro q hq
      have he (x : E2) (hx : x ∈ B) : iteratedFDeriv ℝ q (fun x => -f x) x = -iteratedFDeriv ℝ q f x :=
        iteratedFDeriv_neg_apply
      constructor
      · intro x hx;simpa only [he x hx,norm_neg] using (hf.2 q hq).1 x hx
      · intro x hx y hy;simpa only [he x hx,he y hy,edist_neg_neg] using (hf.2 q hq).2 x hx y hy
    have hS (v : E2 → ℝ) (hv : ContDiffOn ℝ 2 v B) (x : E2) (hx : x ∈ B) (i j : Fin 2) :
        scalarPartial (scalarPartial v j) i x = planarHessian v x i j := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
      have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
        ((hv.fderiv_of_isOpen hB (by norm_num : (1:ℕ∞ω)+1 ≤ 2)).contDiffAt (hB.mem_nhds hx)).differentiableAt (by norm_num)
      have he := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) (e.hasFDerivAt.comp x hd.hasFDerivAt).fderiv
      change (fderiv ℝ (fun y => fderiv ℝ v y (coordinateVector 2 j)) x) (coordinateVector 2 i) = _
      simpa only [planarHessian,Function.comp_def,ContinuousLinearMap.comp_apply,e,ContinuousLinearMap.apply_apply] using he
    intro w
    induction w with
    | nil =>
      intro hw
      refine ⟨K+M,hmono m u K (K+M) (le_add_right le_rfl) hu,?_,heq⟩
      simpa only [derivedSource,List.length_nil,Nat.sub_zero] using hmono (m-1) f M (K+M) (le_add_left le_rfl) hf
    | cons k w ih =>
      intro hw
      simp only [List.length_cons] at hw
      have hw' : w.length ≤ m-2 := by omega
      obtain ⟨L,_,hsource,heqw⟩ := ih hw'
      obtain ⟨hword,_⟩ := hwordProvider B hB u m α K hu w (by omega)
      obtain ⟨hword',_⟩ := hwordProvider B hB u m α K hu (k::w) (by simpa only [List.length_cons] using (show w.length+1 ≤ m by omega))
      obtain ⟨hsource',_⟩ := hwordProvider B hB (derivedSource a f u w) (m-1-w.length) α L hsource [k] (by simp;omega)
      let n := m-1-(k::w).length
      have hs : PlanarHolderJetBound n (scalarPartial (derivedSource a f u w) k) B α L := by
        have hn : m-1-w.length-1 = n := by dsimp [n];omega
        simpa only [partialWord,List.length_cons,List.length_nil,hn] using hsource'
      have hac (i j : Fin 2) : PlanarHolderJetBound n (scalarPartial (fun x => a x i j) k) B α M := by
        obtain ⟨hc,_⟩ := hwordProvider B hB (fun x => a x i j) (m-1) α M (ha i j) [k] (by simp;omega)
        exact hreduce (m-2) n (by dsimp [n];omega) _ M (by simpa only [partialWord,List.length_cons,List.length_nil,Nat.zero_add,Nat.sub_sub] using hc)
      have hhc (i j : Fin 2) : PlanarHolderJetBound n (fun x => planarHessian (partialWord u w) x i j) B α K := by
        obtain ⟨hh,_⟩ := hwordProvider B hB (partialWord u w) (m-w.length) α K hword [i,j] (by simp;omega)
        have hh' : PlanarHolderJetBound n (partialWord (partialWord u w) [i,j]) B α K :=
          hreduce _ n (by dsimp [n];omega) _ K hh
        exact hcongr n _ _ K hh' (fun x hx => hS (partialWord u w) (hword.1.of_le (by exact_mod_cast (show 2 ≤ m-w.length by omega))) x hx i j)
      let P : NNReal := 2^(n+1)*M*K
      have hp (i j : Fin 2) : PlanarHolderJetBound n (fun x => scalarPartial (fun y => a y i j) k x*
          planarHessian (partialWord u w) x i j) B α P := hproduct B hB _ _ n α M K (hac i j) (hhc i j)
      have hsum : PlanarHolderJetBound n (fun x => ∑ i : Fin 2, ∑ j : Fin 2,
          scalarPartial (fun y => a y i j) k x*planarHessian (partialWord u w) x i j) B α ((P+P)+(P+P)) := by
        simpa only [Fin.sum_univ_two] using hadd n _ _ (P+P) (P+P)
          (hadd n _ _ P P (hp 0 0) (hp 0 1)) (hadd n _ _ P P (hp 1 0) (hp 1 1))
      have hdsource : PlanarHolderJetBound n (derivedSource a f u (k::w)) B α (L+((P+P)+(P+P))) := by
        simpa only [derivedSource,sub_eq_add_neg] using hadd n _ _ L ((P+P)+(P+P)) hs (hneg n _ _ hsum)
      let Cost := K+(L+((P+P)+(P+P)))
      refine ⟨Cost,hmono _ _ K Cost (le_add_right le_rfl) hword',hmono _ _ _ Cost (le_add_left le_rfl) hdsource,?_⟩
      exact hdifferentiationProvider B hB a (derivedSource a f u w) (partialWord u w)
        (fun i j => (ha i j).1.of_le (by exact_mod_cast (show 1 ≤ m-1 by omega)))
        (hsource.1.of_le (by exact_mod_cast (show 1 ≤ m-1-w.length by omega)))
        (hword.1.of_le (by exact_mod_cast (show 3 ≤ m-w.length by omega))) heqw k
  have hnonlinear : ∃ s κ Λ : ℝ, ∃ H A : NNReal,
      0 < s ∧ 4*s ≤ R ∧ 0 < κ ∧ κ ≤ Λ ∧
      PlanarCoefficientControl (principalMatrix Q u) (Metric.ball x₀ (4*s)) κ Λ H α ∧
      (∀ i j, PlanarHolderJetBound (m-1) (fun x => principalMatrix Q u x i j)
        (Metric.ball x₀ (4*s)) α A) ∧
      PlanarHolderJetBound (m-1) (classicalSource Q u) (Metric.ball x₀ (4*s)) α A := by
    exact hnonlinearProvider Ω hΩ J hJ Q helliptic u x₀ R hR hball hjets m hm α K hα hαone hu
  have hderive (B : Set E2) (hB : IsOpen B) (a : E2 → PlanarMatrix) (f : E2 → ℝ)
      (A : NNReal) (huB : PlanarHolderJetBound m u B α K)
      (haB : ∀ i j, PlanarHolderJetBound (m-1) (fun x => a x i j) B α A)
      (hfB : PlanarHolderJetBound (m-1) f B α A)
      (heqB : LinearClassicalEquation B a f u) :
      ∀ w : List (Fin 2), w.length ≤ m-2 → ∃ L : NNReal,
        PlanarHolderJetBound (m-w.length) (partialWord u w) B α L ∧
        PlanarHolderJetBound (m-1-w.length) (derivedSource a f u w) B α L ∧
        LinearClassicalEquation B a (derivedSource a f u w) (partialWord u w) := by
    exact hderiveProvider B hB a f u m hm α K A huB haB hfB heqB
  obtain ⟨s,κ,Λ,H,A,hs,hsR,hκ,hΛ,ha,hcoeff,hsource⟩ := hnonlinear
  have hsub : Metric.ball x₀ (4*s) ⊆ Metric.ball x₀ (4*R) := Metric.ball_subset_ball (by linarith)
  have huB : PlanarHolderJetBound m u (Metric.ball x₀ (4*s)) α K :=
    ⟨hu.1.mono hsub,fun q hq => ⟨fun x hx => (hu.2 q hq).1 x (hsub hx),((hu.2 q hq).2).mono hsub⟩⟩
  have heqB : LinearClassicalEquation (Metric.ball x₀ (4*s))
      (principalMatrix Q u) (classicalSource Q u) u := fun x hx => heq x (hsub hx)
  have hper (w : List (Fin 2)) (hw : w.length=m-2) : ∃ L : NNReal,
      PlanarHolderJetBound 2 (partialWord u w) (Metric.ball x₀ (4*s)) α L ∧
      PlanarHolderJetBound 1 (derivedSource (principalMatrix Q u) (classicalSource Q u) u w)
        (Metric.ball x₀ (4*s)) α L ∧
      LinearClassicalEquation (Metric.ball x₀ (4*s)) (principalMatrix Q u)
        (derivedSource (principalMatrix Q u) (classicalSource Q u) u w) (partialWord u w) := by
    have hi := hderive _ Metric.isOpen_ball (principalMatrix Q u) (classicalSource Q u) A huB hcoeff hsource heqB w hw.le
    simpa only [hw,show m-(m-2)=2 by omega,show m-1-(m-2)=1 by omega] using hi
  have hvec (ξ : Fin (m-2) → Fin 2) := hper (List.ofFn ξ) (by simp)
  choose L hL using hvec
  let M : NNReal := A+∑ ξ : Fin (m-2) → Fin 2, L ξ
  have hAM : A ≤ M := by dsimp [M];exact le_add_right le_rfl
  have hmono (v : E2 → ℝ) (q : ℕ) (L : NNReal) (hLM : L ≤ M)
      (hv : PlanarHolderJetBound q v (Metric.ball x₀ (4*s)) α L) :
      PlanarHolderJetBound q v (Metric.ball x₀ (4*s)) α M := by
    exact ⟨hv.1,fun j hj => ⟨fun x hx => ((hv.2 j hj).1 x hx).trans (by exact_mod_cast hLM),
      ((hv.2 j hj).2).mono_const hLM⟩⟩
  refine ⟨s,κ,Λ,H,M,hs,hsR,hκ,hΛ,ha,?_,?_⟩
  · intro i j
    have hc := hcoeff i j
    exact hmono _ 1 A hAM ⟨hc.1.of_le (by exact_mod_cast (show 1 ≤ m-1 by omega)),
      fun q hq => hc.2 q (by omega)⟩
  · intro w hw
    let ξ : Fin (m-2) → Fin 2 := fun i => w.get (Fin.cast hw.symm i)
    have he : List.ofFn ξ = w := (List.ofFn_congr hw w.get).symm.trans (List.ofFn_get w)
    have hLM : L ξ ≤ M := by
      have hh : L ξ ≤ ∑ ξ : Fin (m-2) → Fin 2, L ξ :=
        Finset.single_le_sum (fun ξ (_ : ξ ∈ Finset.univ) => show 0 ≤ L ξ from zero_le) (Finset.mem_univ ξ)
      exact hh.trans (by dsimp [M];exact le_add_left le_rfl)
    have hh := hL ξ
    rw [he] at hh
    exact ⟨hmono _ 2 _ hLM hh.1,hmono _ 1 _ hLM hh.2.1,hh.2.2⟩


/-- Higher finite-order nonlinear gain through the displayed differentiated
equations and uniform finite-difference estimate, with actual u preserved. -/
theorem R5_higher_finite_gain
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (x₀ : E2) (R : ℝ) (hR : 0 < R)
    (hball : Metric.closedBall x₀ (4 * R) ⊆ Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (m : ℕ) (hm : 3 ≤ m) (α K : NNReal) (hα : 0 < α) (hαone : α < 1)
    (hu : PlanarHolderJetBound m u (Metric.ball x₀ (4 * R)) α K)
    (heq : LinearClassicalEquation (Metric.ball x₀ (4 * R))
      (principalMatrix Q u) (classicalSource Q u) u) :
    ∃ s : ℝ, ∃ K' : NNReal, 0 < s ∧ s ≤ R / 2 ∧
      PlanarHolderJetBound (m + 1) u (Metric.ball x₀ (2 * s)) (α / 2) K' := by
  classical
  have hwordProvider
      (B : Set E2) (hB : IsOpen B) (u : E2 → ℝ) (m : ℕ) (α K : NNReal)
      (hu : PlanarHolderJetBound m u B α K) (w : List (Fin 2)) (hw : w.length ≤ m) :
      PlanarHolderJetBound (m - w.length) (partialWord u w) B α K ∧
        (∀ q : ℕ, q + w.length ≤ m → ∀ x ∈ B, ∀ ξ : Fin q → E2,
          iteratedFDeriv ℝ q (partialWord u w) x ξ =
            iteratedFDeriv ℝ (q + w.length) u x
              (Fin.append ξ (fun j : Fin w.length => coordinateVector 2 (w.get j)))) := by
    classical
    have hpartial (n : ℕ) (hn : 1 ≤ n) (v : E2 → ℝ)
        (hv : PlanarHolderJetBound n v B α K) (k : Fin 2) :
        PlanarHolderJetBound (n-1) (scalarPartial v k) B α K ∧
        (∀ q : ℕ, q+1 ≤ n → ∀ x ∈ B, ∀ ξ : Fin q → E2,
          iteratedFDeriv ℝ q (scalarPartial v k) x ξ =
            iteratedFDeriv ℝ (q+1) v x (Fin.snoc ξ (coordinateVector 2 k))) := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 k)
      have he : ‖e‖ ≤ 1 := by
        apply e.opNorm_le_bound (by norm_num)
        intro L
        simpa only [e,ContinuousLinearMap.apply_apply,show ‖coordinateVector 2 k‖ = 1 by
          simp [coordinateVector,EuclideanSpace.single,PiLp.norm_single],mul_one,one_mul] using L.le_opNorm (coordinateVector 2 k)
      have hD : ContDiffOn ℝ (↑(n-1) : ℕ∞ω) (fderiv ℝ v) B :=
        hv.1.fderiv_of_isOpen hB (by exact_mod_cast (Nat.sub_add_cancel hn).le)
      have hjet (q : ℕ) (hq : q+1 ≤ n) (x : E2) (hx : x ∈ B) :
          iteratedFDeriv ℝ q (scalarPartial v k) x =
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x) := by
        change iteratedFDeriv ℝ q (e ∘ fderiv ℝ v) x = _
        apply e.iteratedFDeriv_comp_left (hD.contDiffAt (hB.mem_nhds hx))
        exact_mod_cast (show q ≤ n-1 by omega)
      have hmap (q : ℕ) (hq : q+1 ≤ n) (x : E2) (hx : x ∈ B) :
          ‖iteratedFDeriv ℝ q (scalarPartial v k) x‖ ≤ (K:ℝ) := by
        rw [hjet q hq x hx]
        calc
          _ ≤ ‖e‖*‖iteratedFDeriv ℝ q (fderiv ℝ v) x‖ := e.norm_compContinuousMultilinearMap_le _
          _ ≤ ‖iteratedFDeriv ℝ q (fderiv ℝ v) x‖  := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)
          _ = ‖iteratedFDeriv ℝ (q+1) v x‖ := norm_iteratedFDeriv_fderiv
          _ ≤ _ := (hv.2 (q+1) hq).1 x hx
      have hHolder (q : ℕ) (hq : q+1 ≤ n) :
          HolderOnWith K α (iteratedFDeriv ℝ q (scalarPartial v k)) B := by
        intro x hx y hy
        let I := (continuousMultilinearCurryRightEquiv' ℝ q E2 ℝ).symm
        have hdiff : dist (iteratedFDeriv ℝ q (fderiv ℝ v) x)
            (iteratedFDeriv ℝ q (fderiv ℝ v) y) =
            dist (iteratedFDeriv ℝ (q+1) v x) (iteratedFDeriv ℝ (q+1) v y) := by
          rw [iteratedFDeriv_succ_eq_comp_right,iteratedFDeriv_succ_eq_comp_right]
          exact (I.isometry.dist_eq _ _).symm
        have hsub : e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x)-
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) y) =
            e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x-
              iteratedFDeriv ℝ q (fderiv ℝ v) y) := by
          ext ξ; simp [map_sub]
        have hh := ((hv.2 (q+1) hq).2).dist_le hx hy
        have hr : dist (iteratedFDeriv ℝ q (scalarPartial v k) x)
            (iteratedFDeriv ℝ q (scalarPartial v k) y) ≤ (K:ℝ)*dist x y^(α:ℝ) := by
          rw [hjet q hq x hx,hjet q hq y hy,dist_eq_norm,hsub]
          calc
            _ ≤ ‖e‖*‖iteratedFDeriv ℝ q (fderiv ℝ v) x-iteratedFDeriv ℝ q (fderiv ℝ v) y‖ := e.norm_compContinuousMultilinearMap_le _
            _ ≤ ‖iteratedFDeriv ℝ q (fderiv ℝ v) x-iteratedFDeriv ℝ q (fderiv ℝ v) y‖ := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg _)
            _ = dist (iteratedFDeriv ℝ (q+1) v x) (iteratedFDeriv ℝ (q+1) v y) := by rw [← dist_eq_norm,hdiff]
            _ ≤ _ := hh
        simpa only [edist_dist,ENNReal.ofReal_mul K.coe_nonneg,
          ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,ENNReal.ofReal_coe_nnreal]
          using ENNReal.ofReal_le_ofReal hr
      refine ⟨⟨e.contDiff.comp_contDiffOn hD,?_⟩,?_⟩
      · intro q hq; exact ⟨hmap q (by omega),hHolder q (by omega)⟩
      · intro q hq x hx ξ
        rw [hjet q hq x hx]
        change (iteratedFDeriv ℝ q (fderiv ℝ v) x ξ) (coordinateVector 2 k) = _
        simp only [iteratedFDeriv_succ_apply_right,Fin.init_snoc,Fin.snoc_last]
    have hcast (r t : ℕ) (he : r=t) (x : E2) (η : Fin r → E2) :
        iteratedFDeriv ℝ r u x η =
          iteratedFDeriv ℝ t u x (η ∘ Fin.cast he.symm) := by
      subst t
      rfl
    induction w generalizing m with
    | nil =>
      refine ⟨by simpa only [partialWord,List.length_nil,Nat.sub_zero] using hu,?_⟩
      intro q hq x hx ξ
      simp only [partialWord,List.length_nil,Nat.add_zero,Fin.append_right_nil,Fin.cast_eq_self,Function.comp_id]
      congr 1
    | cons k w ih =>
      obtain ⟨hv,hvjet⟩ := ih m hu (by simpa only [List.length_cons] using Nat.le_of_succ_le hw)
      obtain ⟨hp,hpjet⟩ := hpartial (m-w.length) (by simp only [List.length_cons] at hw;omega)
        (partialWord u w) hv k
      refine ⟨?_,?_⟩
      · simpa only [partialWord,List.length_cons,Nat.sub_sub,Nat.add_comm w.length 1] using hp
      · intro q hq x hx ξ
        have hcons : (fun j : Fin (k::w).length => coordinateVector 2 ((k::w).get j)) =
            Fin.cons (coordinateVector 2 k) (fun j : Fin w.length => coordinateVector 2 (w.get j)) := by
          funext j
          cases j using Fin.cases <;> simp
        have he : q+1+w.length=q+(k::w).length := by simp only [List.length_cons];omega
        calc
          _ = iteratedFDeriv ℝ (q+1) (partialWord u w) x (Fin.snoc ξ (coordinateVector 2 k)) :=
            hpjet q (by simp only [List.length_cons] at hq;omega) x hx ξ
          _ = iteratedFDeriv ℝ (q+1+w.length) u x
              (Fin.append (Fin.snoc ξ (coordinateVector 2 k)) (fun j => coordinateVector 2 (w.get j))) :=
            hvjet (q+1) (by simp only [List.length_cons] at hq;omega) x hx _
          _ = _ := by
            rw [hcast _ _ he x,Fin.append_left_snoc,hcons]
            congr 1
  have hreconstructionProvider
      (x₀ : E2) (R : ℝ) (hR : 0 < R) (u : E2 → ℝ)
      (m : ℕ) (hm : 2 ≤ m) (α K Kw : NNReal) (hα : 0 < α) (hαone : α < 1)
      (hu : PlanarHolderJetBound m u (Metric.ball x₀ R) α K)
      (hwords : ∀ w : List (Fin 2), w.length = m - 2 →
        PlanarHolderJetBound 3 (partialWord u w) (Metric.ball x₀ R) (α / 2) Kw) :
      ∃ K' : NNReal, PlanarHolderJetBound (m + 1) u (Metric.ball x₀ R) (α / 2) K' := by
      classical
    have hlift (B : Set E2) (hB : IsOpen B) (v : E2 → ℝ) (n : ℕ) (β A C : NNReal)
        (hv : DifferentiableOn ℝ v B) (hb : ∀ x ∈ B, ‖v x‖ ≤ (A:ℝ))
        (hh : HolderOnWith A β v B)
        (hp : ∀ k : Fin 2, PlanarHolderJetBound n (scalarPartial v k) B β C) :
        PlanarHolderJetBound (n+1) v B β (A+2*C) := by
      classical
      have hrep (x y : E2) : fderiv ℝ v x y = ∑ k : Fin 2, y k * scalarPartial v k x := by
        have hy : y = y 0 • coordinateVector 2 0+y 1 • coordinateVector 2 1 := by
          ext i;fin_cases i <;> simp [coordinateVector]
        conv_lhs => rw [hy]
        simp [Fin.sum_univ_two,scalarPartial]
      have hd : ContDiffOn ℝ (↑n : ℕ∞ω) (fderiv ℝ v) B := by
        apply contDiffOn_clm_apply.mpr
        intro y
        exact (ContDiffOn.sum (fun k _ => contDiffOn_const.mul (hp k).1)).congr (fun x _ => hrep x y)
      have hc : ContDiffOn ℝ (↑(n+1) : ℕ∞ω) v B := by
        apply (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := (↑n : ℕ∞ω)) hB).mpr
        exact ⟨hv,by simp,hd⟩
      have hjet (q : ℕ) (hq : q ≤ n) (x : E2) (hx : x ∈ B) (ξ : Fin (q+1) → E2) :
          iteratedFDeriv ℝ (q+1) v x ξ = ∑ k : Fin 2, ξ (Fin.last q) k *
            iteratedFDeriv ℝ q (scalarPartial v k) x (Fin.init ξ) := by
        let e := ContinuousLinearMap.apply ℝ ℝ (ξ (Fin.last q))
        have he := e.iteratedFDeriv_comp_left (hd.contDiffAt (hB.mem_nhds hx)) (i := q) (by exact_mod_cast hq)
        rw [iteratedFDeriv_succ_apply_right]
        change (e.compContinuousMultilinearMap (iteratedFDeriv ℝ q (fderiv ℝ v) x)) (Fin.init ξ) = _
        rw [← he]
        have hfun : e ∘ fderiv ℝ v = fun z => ∑ k : Fin 2, ξ (Fin.last q) k * scalarPartial v k z :=
          funext (fun z => hrep z (ξ (Fin.last q)))
        rw [hfun,iteratedFDeriv_fun_sum_apply (fun k _ => contDiffAt_const.mul
          (((hp k).1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds hx))),
          ContinuousMultilinearMap.sum_apply]
        apply Finset.sum_congr rfl
        intro k _
        rw [show (fun z => ξ (Fin.last q) k * scalarPartial v k z) = ξ (Fin.last q) k • scalarPartial v k from rfl,
          iteratedFDeriv_const_smul_apply (((hp k).1.of_le (by exact_mod_cast hq)).contDiffAt (hB.mem_nhds hx))]
        rfl
      have hestimate (q : ℕ) (T : ContinuousMultilinearMap ℝ (fun _ : Fin (q+1) => E2) ℝ)
          (b : Fin 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => E2) ℝ)
          (D : ℝ) (hD : 0 ≤ D) (hb : ∀ k, ‖b k‖ ≤ D)
          (ht : ∀ ξ, T ξ = ∑ k : Fin 2, ξ (Fin.last q) k*b k (Fin.init ξ)) : ‖T‖ ≤ 2*D := by
        apply T.opNorm_le_bound (by positivity)
        intro ξ
        rw [ht]
        calc
          ‖∑ k : Fin 2, ξ (Fin.last q) k*b k (Fin.init ξ)‖ ≤ ∑ k : Fin 2, ‖ξ (Fin.last q) k*b k (Fin.init ξ)‖ := norm_sum_le _ _
          _ ≤ ∑ _k : Fin 2, ‖ξ (Fin.last q)‖*(D*∏ i : Fin q,‖ξ i.castSucc‖) := by
            apply Finset.sum_le_sum
            intro k _
            rw [norm_mul]
            apply mul_le_mul (PiLp.norm_apply_le (ξ (Fin.last q)) k)
            · exact ((b k).le_opNorm (Fin.init ξ)).trans (mul_le_mul_of_nonneg_right (hb k) (by positivity))
            · exact norm_nonneg _
            · positivity
          _ = (2*D)*∏ i : Fin (q+1),‖ξ i‖ := by simp only [Fin.sum_univ_two,Fin.prod_univ_castSucc];ring
      refine ⟨hc,?_⟩
      intro q hq
      cases q with
      | zero =>
        refine ⟨fun x hx => ?_,?_⟩
        · rw [norm_iteratedFDeriv_zero]
          exact (hb x hx).trans (by exact_mod_cast (show A ≤ A+2*C from le_add_right le_rfl))
        · intro x hx y hy
          simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
            (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq] using
            (hh.mono_const (le_add_right le_rfl : A ≤ A+2*C)) x hx y hy
      | succ q =>
        have hqn : q ≤ n := by omega
        have hn (x : E2) (hx : x ∈ B) : ‖iteratedFDeriv ℝ (q+1) v x‖ ≤ ((2*C:NNReal):ℝ) := by
          apply hestimate q _ (fun k => iteratedFDeriv ℝ q (scalarPartial v k) x) C C.coe_nonneg
            (fun k => ((hp k).2 q hqn).1 x hx) (hjet q hqn x hx)
        have hH : HolderOnWith (2*C) β (iteratedFDeriv ℝ (q+1) v) B := by
          intro x hx y hy
          have hb (k : Fin 2) : ‖iteratedFDeriv ℝ q (scalarPartial v k) x-iteratedFDeriv ℝ q (scalarPartial v k) y‖ ≤
              (C:ℝ)*dist x y^(β:ℝ) := by
            simpa only [dist_eq_norm] using ((hp k).2 q hqn).2.dist_le hx hy
          have ht : ‖iteratedFDeriv ℝ (q+1) v x-iteratedFDeriv ℝ (q+1) v y‖ ≤ 2*((C:ℝ)*dist x y^(β:ℝ)) := by
            apply hestimate q _ (fun k => iteratedFDeriv ℝ q (scalarPartial v k) x-iteratedFDeriv ℝ q (scalarPartial v k) y)
              _ (by positivity) hb
            intro ξ
            simp only [ContinuousMultilinearMap.sub_apply,hjet q hqn x hx,hjet q hqn y hy,mul_sub,Finset.sum_sub_distrib]
          rw [edist_dist,dist_eq_norm,edist_dist,ENNReal.ofReal_rpow_of_nonneg dist_nonneg β.coe_nonneg,
            ← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul (2*C).coe_nonneg]
          apply ENNReal.ofReal_le_ofReal
          simpa only [NNReal.coe_mul,NNReal.coe_ofNat,mul_assoc] using ht
        exact ⟨fun x hx => (hn x hx).trans (by exact_mod_cast (show 2*C ≤ A+2*C from le_add_left le_rfl)),
          hH.mono_const (le_add_left le_rfl)⟩
    let B := Metric.ball x₀ R
    have hB : IsOpen B := Metric.isOpen_ball
    let D : NNReal := Real.toNNReal (2*R)+1
    have hdiam : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ D := by
      intro x hx y hy
      have hr : dist x y ≤ 2*R := by
        have hx' := Metric.mem_ball.mp hx
        have hy' := Metric.mem_ball.mp hy
        calc
          dist x y ≤ dist x x₀+dist y x₀ := dist_triangle_right _ _ _
          _ ≤ 2*R := by linarith
      rw [edist_dist,← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      exact hr.trans (by dsimp [D];linarith [le_max_left (2*R) 0])
    have hexp : α/2 ≤ α := div_le_self (by positivity) (by norm_num)
    let K0 : NNReal := K*(1+D^((α:ℝ)-((α/2:NNReal):ℝ)))
    have hK0 : K ≤ K0 := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity))
    have hzero (v : E2 → ℝ) (r : ℕ) (hv : PlanarHolderJetBound r v B α K) :
        (∀ x ∈ B, ‖v x‖ ≤ (K0:ℝ)) ∧ HolderOnWith K0 (α/2) v B := by
      have hH : HolderOnWith K α v B := by
        intro x hx y hy
        simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
          (continuousMultilinearCurryFin0 ℝ E2 ℝ).symm.isometry.edist_eq] using (hv.2 0 (by omega)).2 x hx y hy
      refine ⟨fun x hx => ?_,(hH.of_le hdiam hexp).mono_const ?_⟩
      · have hh := (hv.2 0 (by omega)).1 x hx
        rw [norm_iteratedFDeriv_zero] at hh
        exact hh.trans (by exact_mod_cast hK0)
      · dsimp [K0]
        exact mul_le_mul_of_nonneg_left (le_add_left le_rfl) (by positivity)
    have happend (v : E2 → ℝ) (k : Fin 2) (w : List (Fin 2)) :
        partialWord (scalarPartial v k) w=partialWord v (w++[k]) := by
      induction w with
      | nil => rfl
      | cons i w ih => simp only [partialWord,List.cons_append,ih]
    have hgain (ℓ : ℕ) : ∀ v : E2 → ℝ,
        PlanarHolderJetBound (ℓ+2) v B α K →
        (∀ w : List (Fin 2), w.length=ℓ → PlanarHolderJetBound 3 (partialWord v w) B (α/2) Kw) →
        ∃ C : NNReal, PlanarHolderJetBound (ℓ+3) v B (α/2) C := by
      induction ℓ with
      | zero =>
        intro v hv hw
        exact ⟨Kw,by simpa only [partialWord] using hw [] rfl⟩
      | succ ℓ ih =>
        intro v hv hw
        have hp (k : Fin 2) : ∃ C : NNReal, PlanarHolderJetBound (ℓ+3) (scalarPartial v k) B (α/2) C := by
          have hvp : PlanarHolderJetBound (ℓ+2) (scalarPartial v k) B α K := by
            have hh := (hwordProvider B hB v (ℓ+1+2) α K hv [k] (by simp)).1
            simpa only [partialWord,List.length_cons,List.length_nil,Nat.zero_add,show ℓ+1+2-1=ℓ+2 by omega] using hh
          apply ih (scalarPartial v k) hvp
          intro w hwlen
          rw [happend]
          exact hw (w++[k]) (by simp only [List.length_append,List.length_cons,List.length_nil,hwlen,Nat.zero_add])
        choose C hC using hp
        let Csum : NNReal := ∑ k : Fin 2,C k
        have hparts (k : Fin 2) : PlanarHolderJetBound (ℓ+3) (scalarPartial v k) B (α/2) Csum := by
          have hcost : C k ≤ Csum := Finset.single_le_sum (fun k _ => zero_le) (Finset.mem_univ k)
          exact ⟨(hC k).1,fun q hq => ⟨fun x hx => ((hC k).2 q hq).1 x hx |>.trans (by exact_mod_cast hcost),
            ((hC k).2 q hq).2.mono_const hcost⟩⟩
        obtain ⟨hvb,hvH⟩ := hzero v (ℓ+1+2) hv
        exact ⟨K0+2*Csum,by simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using
          (hlift B hB v (ℓ+3) (α/2) K0 Csum
            (hv.1.differentiableOn (by simp)) hvb hvH hparts)⟩
    have hm2 : m-2+2=m := Nat.sub_add_cancel hm
    obtain ⟨C,hC⟩ := hgain (m-2) u (by simpa only [hm2] using hu) hwords
    exact ⟨C,by convert hC using 1 <;> omega⟩
  have hreconstruct (r : ℝ) (hr : 0 < r) (Kw : NNReal)
      (hp : PlanarHolderJetBound m u (Metric.ball x₀ r) α K)
      (hw : ∀ w : List (Fin 2), w.length = m-2 →
        PlanarHolderJetBound 3 (partialWord u w) (Metric.ball x₀ r) (α/2) Kw) :
      ∃ K' : NNReal, PlanarHolderJetBound (m+1) u (Metric.ball x₀ r) (α/2) K' := by
    exact hreconstructionProvider x₀ r hr u m (by omega) α K Kw hα hαone hp hw
  obtain ⟨s,κ,Λ,H,M,hs,hsR,hκ,hΛ,ha,haC1,hwords⟩ :=
    R5_higher_classical_data Ω hΩ J hJ Q helliptic u x₀ R hR hball hjets m hm α K hα hαone hu heq
  have hsub : Metric.ball x₀ (2*s) ⊆ Metric.ball x₀ (4*s) := Metric.ball_subset_ball (by linarith)
  have hbase (w : List (Fin 2)) (hw : w.length=m-2) :
      ∃ Kw : NNReal, PlanarHolderJetBound 3 (partialWord u w)
        (Metric.ball x₀ (s/2)) (α/2) Kw := by
    obtain ⟨hw2,hf1,heqw⟩ := hwords w hw
    obtain ⟨C,hC⟩ := R5_uniform_difference_C2_estimate x₀ s κ Λ hs hκ hΛ
      (principalMatrix Q u) (derivedSource (principalMatrix Q u) (classicalSource Q u) u w)
      (partialWord u w) H α M hα hαone ha haC1 hf1 hw2 heqw
    exact R5_difference_limit_C3 x₀ s hs (partialWord u w) α M C hα hαone
      ⟨hw2.1.mono hsub,fun q hq => ⟨fun x hx => (hw2.2 q hq).1 x (hsub hx),
        ((hw2.2 q hq).2).mono hsub⟩⟩ hC
  have hvector (ξ : Fin (m-2) → Fin 2) : ∃ Kw : NNReal,
      PlanarHolderJetBound 3 (partialWord u (List.ofFn ξ))
        (Metric.ball x₀ (s/2)) (α/2) Kw := hbase _ (by simp)
  choose Kw hKw using hvector
  let Kw₀ : NNReal := ∑ ξ : Fin (m-2) → Fin 2, Kw ξ
  have hwordBound (w : List (Fin 2)) (hw : w.length=m-2) :
      PlanarHolderJetBound 3 (partialWord u w) (Metric.ball x₀ (s/2)) (α/2) Kw₀ := by
    let ξ : Fin (m-2) → Fin 2 := fun i => w.get (Fin.cast hw.symm i)
    have he : List.ofFn ξ = w := by
      exact (List.ofFn_congr hw w.get).symm.trans (List.ofFn_get w)
    have hle : Kw ξ ≤ Kw₀ := by
      dsimp [Kw₀]
      exact Finset.single_le_sum (fun ξ (_ : ξ ∈ Finset.univ) => show 0 ≤ Kw ξ from zero_le) (Finset.mem_univ ξ)
    have hp := hKw ξ
    rw [he] at hp
    exact ⟨hp.1,fun q hq => ⟨fun x hx => ((hp.2 q hq).1 x hx).trans (by exact_mod_cast hle),
      ((hp.2 q hq).2).mono_const hle⟩⟩
  have huSmall : PlanarHolderJetBound m u (Metric.ball x₀ (s/2)) α K := by
    have hsub : Metric.ball x₀ (s/2) ⊆ Metric.ball x₀ (4*R) := Metric.ball_subset_ball (by linarith)
    exact ⟨hu.1.mono hsub,fun q hq => ⟨fun x hx => (hu.2 q hq).1 x (hsub hx),((hu.2 q hq).2).mono hsub⟩⟩
  obtain ⟨K',hp⟩ := hreconstruct (s/2) (by positivity) Kw₀ huSmall hwordBound
  refine ⟨s/4,K',by positivity,by linarith,?_⟩
  simpa only [show 2*(s/4)=s/2 by ring] using hp


/-- R6 quantitative local finite-order output from the original inputs.
Neither the exponent nor the radius must be uniform in x0 or m. -/
theorem R6_local_finite_orders
    (Ω : Set E2) (hΩ : IsOpen Ω) (J : Set Jet) (hJ : IsOpen J)
    (Q : SmoothQuasilinearOperator J) (helliptic : UniformlyEllipticOn J Q.flux)
    (u : E2 → ℝ) (hC1 : ContDiffOn ℝ 1 u Ω)
    (hjets : ∀ x ∈ Ω, firstJet u x ∈ J)
    (hweak : IsWeakDivergenceSolutionOn Ω Q.flux Q.lowerOrder u) :
    ∀ x₀ ∈ Ω, ∀ m : ℕ, 2 ≤ m →
      ∃ r : ℝ, ∃ α K : NNReal, 0 < r ∧ Metric.closedBall x₀ (4 * r) ⊆ Ω ∧
        0 < α ∧ α < 1 ∧ PlanarHolderJetBound m u (Metric.ball x₀ (2 * r)) α K := by
  intro x₀ hx₀ m hm
  have hbase : ∃ r : ℝ, ∃ α K : NNReal, 0 < r ∧
      Metric.closedBall x₀ (4 * r) ⊆ Ω ∧ 0 < α ∧ α < 1 ∧
      PlanarHolderJetBound 2 u (Metric.ball x₀ (2 * r)) α K := by
    obtain ⟨r, κ, M, T, hr, hball, _, hTc, _, hTJ, hjT, hb⟩ :=
      R1_local_jet_tube Ω hΩ J hJ Q helliptic u hC1 hjets x₀ hx₀
    obtain ⟨s, K, β, hs, hsr, hβ, hβone, hp⟩ :=
      R4_first_planar_gain Ω hΩ J hJ Q u hC1 hjets hweak x₀ r κ M hr T
        hball hTc hTJ hjT hb
    exact ⟨s, β, K, hs,
      (Metric.closedBall_subset_closedBall (by linarith)).trans hball, hβ, hβone, hp⟩
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    obtain ⟨r, α, K, hr, hball, hα, hαone, hp⟩ := ih
    let t := r / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have h4t : 4 * t = 2 * r := by dsimp [t]; ring
    have hballt : Metric.closedBall x₀ (4 * t) ⊆ Ω :=
      (Metric.closedBall_subset_closedBall (by dsimp [t]; linarith)).trans hball
    have hpt : PlanarHolderJetBound m u (Metric.ball x₀ (4 * t)) α K := by
      simpa only [h4t] using hp
    have hu2 : ContDiffOn ℝ 2 u (Metric.ball x₀ (4 * t)) :=
      hpt.1.of_le (by exact_mod_cast hm)
    have heq := (R5_weak_to_pointwise (Metric.ball x₀ (4 * t)) Metric.isOpen_ball J hJ Q u
      hu2 (fun x hx => hjets x (hballt (Metric.ball_subset_closedBall hx)))
      (R1_weak_equation_restrict Ω hΩ J hJ Q u hC1 hjets hweak
        (Metric.ball x₀ (4 * t)) Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans hballt))).2
    have hg : ∃ s : ℝ, ∃ K' : NNReal, 0 < s ∧ s ≤ t / 2 ∧
        PlanarHolderJetBound (m + 1) u (Metric.ball x₀ (2 * s)) (α / 2) K' := by
      rcases eq_or_lt_of_le hm with rfl | hm'
      · exact R5_m2_gain Ω hΩ J hJ Q helliptic u x₀ t ht hballt hjets
          α K hα hαone hpt heq
      · exact R5_higher_finite_gain Ω hΩ J hJ Q helliptic u x₀ t ht hballt hjets
          m (by omega) α K hα hαone hpt heq
    obtain ⟨s, K', hs, hst, hps⟩ := hg
    refine ⟨s, α / 2, K', hs,
      (Metric.closedBall_subset_closedBall ?_).trans hball, by positivity, ?_, hps⟩
    · dsimp [t] at hst
      linarith
    · exact (half_lt_self hα).trans hαone

/- The exact final assembly uses the existing
`contDiffOn_of_locally_contDiffOn` for each natural order (lower orders
come from order 2 by `ContDiffOn.of_le`), then `contDiffOn_infty`.
No additional classical estimate or high-regularity input is needed. -/

end SeifertSurfaces.QuasilinearBootstrap
