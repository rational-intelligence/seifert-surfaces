import B1BoundaryH3Step_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
/-- Boundary H2 of the actual tangential derivative and the literal equation
recover full boundary H3, including the previously missing normal third derivatives. -/
theorem native_boundary_full_Hk_step_v474 (q : ℝ) (m : ℕ) (h : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ h (halfDisc q)) (hh : MemWkp (m+1) 2 h (halfDisc q))
    (ht : MemWkp (m+1) 2 (fun x => planarGradient h x 0) (halfDisc q))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ) (hS : MemWkp m 2 S (halfDisc q))
    (heq : ∀ x ∈ halfDisc q,
      (∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient h y) i) x
        (coordinateVector 2 i))+S x=0) : MemWkp (m+2) 2 h (halfDisc q) := by
  let U := halfDisc q
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hgs (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => planarGradient h x i) U := by
    have he : (fun x => planarGradient h x i)=fun x => fderiv ℝ h x (coordinateVector 2 i) := by
      funext x
      exact QuasilinearLocalization.Helpers.gradient_apply h x i
    rw [he]
    exact (hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const
  have hd (i : Fin 2) : MemWkp m 2 (fun x => planarGradient h x i) U :=
    native_smooth_partial_memWkp_v468 U hU h hs m hh i
  have htan (i : Fin 2) : MemWkp m 2
      (fun x => fderiv ℝ (fun y => planarGradient h y i) x (coordinateVector 2 0)) U := by
    have hh := native_smooth_partial_memWkp_v468 U hU _ (hgs 0) m ht i
    apply (MemWkp_congr_ae (by norm_num) hU _).mp hh
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [QuasilinearLocalization.Helpers.gradient_apply]
    exact native_interior_hessian_symm_v468 U hU h hs x hx i 0
  have hnormal := native_boundary_normal_Wkp_recovery_v468 q m h hs hd B S hS heq htan
  have hbase := native_smooth_memW1p_H1_v468 U hU h hs hh.memW1p
  have hgradientBase := native_boundary_normal_L2_recovery_v468 q h hs hbase.2.2 B S
    hS.memLp heq (fun i => (htan i).memLp)
  have hrows (i : Fin 2) : MemWkp (m+1) 2 (fun x => planarGradient h x i) U := by
    have hn := native_smooth_memW1p_H1_v468 U hU _ (hgs i) (hgradientBase i)
    let hw := native_regular_witness_v468 U _ _ hn
    apply MemWkp.of_weakGrad_memWkp (by norm_num) hU hw
    intro j
    change MemWkp m 2 (fun x => planarGradient (fun y => planarGradient h y i) x j) U
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
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_full_Hk_step_v474
