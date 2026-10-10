import B1BoundarySobolevOperations_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 1000000

/-- The normal Hessian is recovered at every Sobolev order from the actual
elliptic equation and the tangential Hessian, with no boundary C1 premise. -/
theorem native_boundary_normal_Wkp_recovery_v468
    (q : ℝ) (m : ℕ) (h : E2 → ℝ) (hs : ContDiffOn ℝ ∞ h (halfDisc q))
    (hd : ∀ i : Fin 2, MemWkp m 2 (fun x => planarGradient h x i) (halfDisc q))
    (B : SmoothEllipticBilinearForm 2 univ)
    (S : E2 → ℝ) (hS : MemWkp m 2 S (halfDisc q))
    (heq : ∀ x ∈ halfDisc q,
      (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x
        (coordinateVector 2 i))+S x=0)
    (ht : ∀ i : Fin 2, MemWkp m 2
      (fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 0)) (halfDisc q)) :
    MemWkp m 2 (fun x => fderiv ℝ (fun y => planarGradient h y 1) x
      (coordinateVector 2 1)) (halfDisc q) := by
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
  have hUc : IsCompact (closure U) := (isCompact_closedBall (0:E2) q).of_isClosed_subset
    isClosed_closure (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1) Metric.isClosed_closedBall)
  have hH01 : MemWkp m 2 (fun x => H x 0 1) U := ht 1
  have hH00 : MemWkp m 2 (fun x => H x 0 0) U := ht 0
  have hH10 : MemWkp m 2 (fun x => H x 1 0) U := by
    apply (MemWkp_congr_ae (by norm_num) hU _).mp hH01
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact hsym x hx 0 1
  let L : E2 → ℝ := fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    fderiv ℝ (fun y => B.a y i j) x (coordinateVector 2 i)*planarGradient h x j
  have hL : MemWkp m 2 L U := by
    have hp (i j : Fin 2) := native_compact_smooth_mul_Wkp_v468 U hU hUc
      (fun x => fderiv ℝ (fun y => B.a y i j) x (coordinateVector 2 i))
      (fun x => planarGradient h x j)
      (((B.smooth_a i j).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const) m (hd j)
    simpa only [L,Fin.sum_univ_two] using MemWkp.add (by norm_num) hU
      (MemWkp.add (by norm_num) hU (hp 0 0) (hp 0 1))
      (MemWkp.add (by norm_num) hU (hp 1 0) (hp 1 1))
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
  have hinv : ContDiff ℝ ∞ (fun x => (B.a x 1 1)⁻¹) :=
    (B.smooth_a 1 1).inv (fun x => (B.ellipticity_pos.trans_le (hdiag x)).ne')
  have h00 := native_compact_smooth_mul_Wkp_v468 U hU hUc _ _ (B.smooth_a 0 0) m hH00
  have h01 := native_compact_smooth_mul_Wkp_v468 U hU hUc _ _ (B.smooth_a 0 1) m hH01
  have h10 := native_compact_smooth_mul_Wkp_v468 U hU hUc _ _ (B.smooth_a 1 0) m hH10
  let f : E2 → ℝ := fun x => (B.a x 1 1)⁻¹ * -(L x+S x+
    B.a x 0 0*H x 0 0+B.a x 0 1*H x 0 1+B.a x 1 0*H x 1 0)
  have hf : MemWkp m 2 f U := native_compact_smooth_mul_Wkp_v468 U hU hUc _ _ hinv m
    (MemWkp.neg (by norm_num) hU (MemWkp.add (by norm_num) hU
      (MemWkp.add (by norm_num) hU (MemWkp.add (by norm_num) hU
        (MemWkp.add (by norm_num) hU hL hS) h00) h01) h10))
  apply (MemWkp_congr_ae (by norm_num) hU _).mp hf
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  have he := heq x hx
  rw [hdiv x hx] at he
  simp only [Fin.sum_univ_two] at he
  dsimp [f]
  have hn : B.a x 1 1≠0 := (B.ellipticity_pos.trans_le (hdiag x)).ne'
  field_simp
  linarith only [he]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_normal_Wkp_recovery_v468
