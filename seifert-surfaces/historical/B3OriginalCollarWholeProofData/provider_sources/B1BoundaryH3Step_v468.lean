import B1BoundaryNormalWkpRecovery_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 1000000

theorem native_smooth_memW1p_H1_v468 (U : Set E2) (hU : IsOpen U)
    (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u U) (hu : DeGiorgi.MemW1p 2 u U) :
    H1On U u (planarGradient u) := by
  let hw := hu.someWitness
  have hn := regular_witness_native_H1_v468 U u hw
  have hg := native_smooth_gradient_ae_v468 U hU u u hw.weakGrad hn hs EventuallyEq.rfl
  exact native_h1_congr_ae_v468 U u u hw.weakGrad _ hn EventuallyEq.rfl hg

theorem native_interior_hessian_symm_v468 (U : Set E2) (hU : IsOpen U)
    (h : E2 → ℝ) (hs : ContDiffOn ℝ ∞ h U) (x : E2) (hx : x∈U) (i j : Fin 2) :
    fderiv ℝ (fun y => planarGradient h y j) x (coordinateVector 2 i)=
      fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 j) := by
  have hf := hs.contDiffAt (hU.mem_nhds hx)
  have hdf := (hs.fderiv_of_isOpen hU (m:=1) (by simp)).contDiffAt (hU.mem_nhds hx)
  have he (i j : Fin 2) : fderiv ℝ (fun y => planarGradient h y j) x (coordinateVector 2 i)=
      fderiv ℝ (fderiv ℝ h) x (coordinateVector 2 i) (coordinateVector 2 j) := by
    let e := ContinuousLinearMap.apply ℝ ℝ (coordinateVector 2 j)
    have hg : (fun y => planarGradient h y j)=fun y => e (fderiv ℝ h y) := by
      funext y
      exact QuasilinearLocalization.Helpers.gradient_apply h y j
    rw [hg]
    have he := e.hasFDerivAt.comp x (hdf.differentiableAt (by simp)).hasFDerivAt
    exact congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) he.fderiv
  rw [he i j,he j i]
  exact (hf.of_le (by simp : (2:ℕ∞ω)≤(∞:ℕ∞ω))).isSymmSndFDerivAt (by norm_num) |>.eq _ _

/-- Boundary H2 of the actual tangential derivative and the literal equation
recover full boundary H3, including the previously missing normal third derivatives. -/
theorem native_boundary_full_H3_step_v468 (q : ℝ) (h : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ h (halfDisc q)) (hh : MemWkp 2 2 h (halfDisc q))
    (ht : MemWkp 2 2 (fun x => planarGradient h x 0) (halfDisc q))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ) (hS : MemWkp 1 2 S (halfDisc q))
    (heq : ∀ x ∈ halfDisc q,
      (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x
        (coordinateVector 2 i))+S x=0) : MemWkp 3 2 h (halfDisc q) := by
  let U := halfDisc q
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hgs (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => planarGradient h x i) U := by
    have he : (fun x => planarGradient h x i)=fun x => fderiv ℝ h x (coordinateVector 2 i) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply h x i
    rw [he]
    exact (hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
  have hd (i : Fin 2) : MemWkp 1 2 (fun x => planarGradient h x i) U :=
    native_smooth_partial_memWkp_v468 U hU h hs 1 hh i
  have htan (i : Fin 2) : MemWkp 1 2
      (fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 0)) U := by
    have hh := native_smooth_partial_memWkp_v468 U hU _ (hgs 0) 1 ht i
    apply (MemWkp_congr_ae (by norm_num) hU _).mp hh
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [QuasilinearLocalization.Helpers.gradient_apply]
    exact native_interior_hessian_symm_v468 U hU h hs x hx i 0
  have hnormal := native_boundary_normal_Wkp_recovery_v468 q 1 h hs hd B S hS heq htan
  have hrows (i : Fin 2) : MemWkp 2 2 (fun x => planarGradient h x i) U := by
    have hn := native_smooth_memW1p_H1_v468 U hU _ (hgs i) (hd i).memW1p
    let hw := native_regular_witness_v468 U _ _ hn
    apply MemWkp.of_weakGrad_memWkp (by norm_num) hU hw
    intro j
    change MemWkp 1 2 (fun x => planarGradient (fun y => planarGradient h y i) x j) U
    have hcoord : (fun x => planarGradient (fun y => planarGradient h y i) x j)=
        fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 j) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply _ x j
    rw [hcoord]
    fin_cases j
    · exact htan i
    · fin_cases i
      · apply (MemWkp_congr_ae (by norm_num) hU _).mp (htan 1)
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        exact native_interior_hessian_symm_v468 U hU h hs x hx 0 1
      · exact hnormal
  have hn := native_smooth_memW1p_H1_v468 U hU h hs hh.memW1p
  exact MemWkp.of_weakGrad_memWkp (by norm_num) hU (native_regular_witness_v468 U h _ hn) hrows
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_smooth_memW1p_H1_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_interior_hessian_symm_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_full_H3_step_v468
