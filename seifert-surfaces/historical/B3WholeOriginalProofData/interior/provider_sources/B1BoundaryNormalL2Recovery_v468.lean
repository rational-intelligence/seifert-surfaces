import B1BoundaryClassicalTangential_v468
import NativeBoundaryFullGradientSobolev
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open SeifertSurfaces.QuasilinearProviderBridge
set_option maxHeartbeats 1000000

/-- Recover the missing normal Hessian entry from the actual divergence
 equation. The only derivative bounds used are the already obtained tangential
 L2 entries; no boundary C1 state is required. -/
theorem native_boundary_normal_L2_recovery_v468
    (q : ℝ) (h : E2 → ℝ) (hs : ContDiffOn ℝ ∞ h (halfDisc q))
    (hd : MemLp (planarGradient h) 2 (volume.restrict (halfDisc q)))
    (B : SmoothEllipticBilinearForm 2 univ)
    (S : E2 → ℝ) (hS : MemLp S 2 (volume.restrict (halfDisc q)))
    (heq : ∀ x ∈ halfDisc q,
      (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x
        (coordinateVector 2 i))+S x=0)
    (ht : ∀ i : Fin 2, MemLp
      (fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 0))
      2 (volume.restrict (halfDisc q))) :
    ∀ i : Fin 2, DeGiorgi.MemW1p 2 (fun y => planarGradient h y i) (halfDisc q) := by
  classical
  let U := halfDisc q
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  let H : E2 → Fin 2 → Fin 2 → ℝ := fun x i j =>
    fderiv ℝ (fun y => planarGradient h y j) x (coordinateVector 2 i)
  have hgs (j : Fin 2) : ContDiffOn ℝ ∞ (fun y => planarGradient h y j) U := by
    have he : (fun y => planarGradient h y j) = fun y => fderiv ℝ h y (coordinateVector 2 j) := by
      funext y
      exact QuasilinearLocalization.Helpers.gradient_apply h y j
    rw [he]
    exact (hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
  have hHij (i j : Fin 2) : ContinuousOn (fun x => H x i j) U :=
    ((hgs j).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hsym (x : E2) (hx : x∈U) (i j : Fin 2) : H x i j=H x j i := by
    have hf := (hs.contDiffAt (hU.mem_nhds hx))
    have hdf := (hs.fderiv_of_isOpen hU (m:=1) (by simp)).contDiffAt (hU.mem_nhds hx)
    have he (i j : Fin 2) : H x i j=fderiv ℝ (fderiv ℝ h) x (coordinateVector 2 i) (coordinateVector 2 j) := by
      let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
      have hg : (fun y => planarGradient h y j)=fun y => e (fderiv ℝ h y) := by
        funext y
        exact QuasilinearLocalization.Helpers.gradient_apply h y j
      dsimp [H]
      rw [hg]
      have he := e.hasFDerivAt.comp x (hdf.differentiableAt (by simp)).hasFDerivAt
      exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) he.fderiv
    rw [he i j,he j i]
    exact (hf.of_le (by simp : (2:ℕ∞ω)≤(∞:ℕ∞ω))).isSymmSndFDerivAt (by norm_num) |>.eq _ _
  have hH01 : MemLp (fun x => H x 0 1) 2 (volume.restrict U) := ht 1
  have hH00 : MemLp (fun x => H x 0 0) 2 (volume.restrict U) := ht 0
  have hH10 : MemLp (fun x => H x 1 0) 2 (volume.restrict U) := by
    refine hH01.ae_eq ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hsym x hx 0 1
  have hK : IsCompact (Metric.closedBall (0:E2) q) := isCompact_closedBall _ _
  have hcoeff {f : E2 → ℝ} (hf : Continuous f) : MemLp f ⊤ (volume.restrict U) := by
    obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
    apply memLp_top_of_bound hf.aestronglyMeasurable.restrict C
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hC x (Metric.ball_subset_closedBall hx.1)
  have ha (i j : Fin 2) : MemLp (fun x => B.a x i j) ⊤ (volume.restrict U) :=
    hcoeff (B.continuous_a i j)
  have hdA (i j : Fin 2) : MemLp
      (fun x => fderiv ℝ (fun y => B.a y i j) x (coordinateVector 2 i)) ⊤ (volume.restrict U) :=
    hcoeff (((B.smooth_a i j).continuous_fderiv (by simp)).clm_apply continuous_const)
  let L : E2 → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    fderiv ℝ (fun y => B.a y i j) x (coordinateVector 2 i)*planarGradient h x j
  have hL : MemLp L 2 (volume.restrict U) := by
    apply memLp_finsetSum
    intro i hi
    apply memLp_finsetSum
    intro j hj
    exact (hdA i j).mul (hd.eval_piLp j)
  have hdiv (x : E2) (hx : x∈U) :
      (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x (coordinateVector 2 i))=
        L x+∑ i : Fin 2, ∑ j : Fin 2, B.a x i j*H x i j := by
    have he (i : Fin 2) :
        fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x (coordinateVector 2 i)=
          ∑ j : Fin 2, (B.a x i j*H x i j+
            planarGradient h x j*fderiv ℝ (fun y => B.a y i j) x (coordinateVector 2 i)) := by
      change fderiv ℝ (fun y => ∑ j : Fin 2, B.a y i j*planarGradient h y j) x _ = _
      have hsum := fderiv_fun_sum (u:=Finset.univ)
        (A:=fun j (y:E2) => B.a y i j*planarGradient h y j)
        (fun j _ => ((B.smooth_a i j).differentiable (by simp) x).mul
          (((hgs j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)))
      calc
        _ = ∑ j : Fin 2, fderiv ℝ (fun y => B.a y i j*planarGradient h y j) x
            (coordinateVector 2 i) := by
          exact congrArg (fun T : E2 →L[ℝ] ℝ => T (coordinateVector 2 i)) hsum
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          have hm := fderiv_fun_mul ((B.smooth_a i j).differentiable (by simp) x)
            (((hgs j).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
          exact congrArg (fun T : E2 →L[ℝ] ℝ => T (coordinateVector 2 i)) hm
    simp_rw [he]
    dsimp [L]
    simp only [Fin.sum_univ_two]
    ring
  have hdiag (x : E2) : B.lam≤B.a x 1 1 := by
    have he := B.coercive x (mem_univ x) (coordinateVector 2 1)
    simpa [coordinateVector,DeGiorgi.matMulE,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
      Fin.sum_univ_two] using he
  have hInv : MemLp (fun x => (B.a x 1 1)⁻¹) ⊤ (volume.restrict U) := by
    apply memLp_top_of_bound
      ((B.continuous_a 1 1).inv₀ (fun x => (B.ellipticity_pos.trans_le (hdiag x)).ne')).aestronglyMeasurable.restrict
      B.lam⁻¹
    exact Eventually.of_forall fun x => by
      change |(B.a x 1 1)⁻¹|≤B.lam⁻¹
      rw [abs_of_pos (inv_pos.mpr (B.ellipticity_pos.trans_le (hdiag x)))]
      exact inv_anti₀ B.ellipticity_pos (hdiag x)
  let f : E2 → ℝ := fun x => -(L x+S x+
    B.a x 0 0*H x 0 0+B.a x 0 1*H x 0 1+B.a x 1 0*H x 1 0)*(B.a x 1 1)⁻¹
  have hf : MemLp f 2 (volume.restrict U) := by
    exact ((((hL.add hS).add ((ha 0 0).mul hH00)).add
      ((ha 0 1).mul hH01)).add ((ha 1 0).mul hH10) |>.neg).mul hInv
  have hH11 : MemLp (fun x => H x 1 1) 2 (volume.restrict U) := by
    refine hf.ae_eq ?_
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    have he := heq x hx
    rw [hdiv x hx] at he
    simp only [Fin.sum_univ_two] at he
    dsimp [f]
    have hn : B.a x 1 1≠0 := (B.ellipticity_pos.trans_le (hdiag x)).ne'
    field_simp
    linarith only [he]
  intro i
  have hgrad : MemLp (planarGradient (fun y => planarGradient h y i)) 2 (volume.restrict U) := by
    have h0 : MemLp (fun x => H x 0 i) 2 (volume.restrict U) := ht i
    have h1 : MemLp (fun x => H x 1 i) 2 (volume.restrict U) := by
      fin_cases i
      · exact hH10
      · exact hH11
    have hg := (h0.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 0))).add
      (h1.continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector 2 1)))
    convert hg using 1
    funext x
    simp only [planarGradient,Fin.sum_univ_two,H,ContinuousLinearMap.toSpanSingleton_apply]
    rfl
  exact BoundaryRegularity.native_memW1p_of_C1_and_actual_gradient_memLp U hU _
    ((hgs i).of_le (by simp)) (hd.eval_piLp i) hgrad
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_normal_L2_recovery_v468
