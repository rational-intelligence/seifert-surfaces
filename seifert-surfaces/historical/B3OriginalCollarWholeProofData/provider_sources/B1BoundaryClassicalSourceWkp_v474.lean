import B1BoundaryLowerSourceTower_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 60000
set_option maxRecDepth 1000
set_option backward.isDefEq.respectTransparency false

/-- A native weak L2 source agrees a.e. with the literal classical divergence
of an interior smooth solution. This identification needs no boundary trace. -/
theorem native_boundary_classical_source_Wkp_v474
    (R : ℝ) (m : ℕ) (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ)
    (hS : MemWkp m 2 S (halfDisc R))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-S x*phi x)=0) :
    MemWkp m 2 (fun x => -(∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i)))
      (halfDisc R) := by
  let U := halfDisc R
  let L : E2 → ℝ := classicalL B.a (fun _ => 0) (fun _ => 0) u
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const).smul contDiffOn_const
  have hflux (i : Fin 2) : ContDiffOn ℝ ∞
      (fun x => matrixAction (B.a x) (planarGradient u x) i) U := by
    change ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 2, B.a x i j * planarGradient u x j) U
    apply ContDiffOn.sum
    intro j hj
    exact (B.smooth_a i j).contDiffOn.mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp_contDiffOn hgrad)
  have hLc : ContinuousOn L U := by
    have hh : L=(fun x => ∑ i : Fin 2, fderiv ℝ
        (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i)) := by
      funext x
      simp [L,classicalL]
    rw [hh]
    apply continuousOn_finsetSum
    intro i hi
    exact ((hflux i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hz : ∀ᵐ x ∂volume.restrict U, L x+S x=0 := by
    rw [ae_restrict_iff' hU.measurableSet]
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hLc.locallyIntegrableOn hU.measurableSet).add
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hS.memLp.locallyIntegrable (by norm_num))))
    intro phi hp hc ht
    have hform := halfdisc_local_classical_form_identity_v468 R U hU (Subset.rfl)
      B.a (fun _ => 0) (fun _ => 0) u (fun i j => (B.smooth_a i j).contDiffOn)
      contDiffOn_const contDiffOn_const hs phi hp hc ht
    have hpLp : MemLp phi 2 (volume.restrict U) :=
      (hp.continuous.memLp_of_hasCompactSupport (μ:=volume) hc).restrict U
    have hiS : IntegrableOn (fun x => S x*phi x) U := hS.memLp.integrable_mul hpLp
    have hiSc : IntegrableOn (fun x => phi x*S x) U := by
      simpa only [mul_comm] using hiS
    have hiLc : IntegrableOn (fun x => phi x*L x) U := by
      simpa only [L,mul_comm] using hform.2.1
    have hiP : IntegrableOn (fun x => inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)) U := by
      simpa only [inner_zero_left,zero_mul,zero_add,sub_zero] using hform.1
    have hh := hweak phi hp hc ht
    have hh' : (∫ x in U, inner ℝ (matrixAction (B.a x) (planarGradient u x))
      (planarGradient phi x)) - ∫ x in U, S x*phi x = 0 := by
      calc
        _ = ∫ x in U, inner ℝ (matrixAction (B.a x) (planarGradient u x))
            (planarGradient phi x)-S x*phi x := (integral_sub hiP hiS).symm
        _ = 0 := by simpa only [Pi.mul_apply] using hh
    have hh := hh'
    have hparts : (∫ x in U, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x))=-(∫ x in U, L x*phi x) := by
      simpa only [inner_zero_left,zero_mul,zero_add,sub_zero,L] using hform.2.2
    rw [hparts] at hh
    have hzeroU : (∫ x in U, phi x * (L x+S x))=0 := by
      calc
        _ = ∫ x in U, (phi x*L x + phi x*S x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = (∫ x in U, phi x*L x) + ∫ x in U, phi x*S x := by
          exact integral_add hiLc hiSc
        _ = 0 := by
          have hL := (show (∫ x in U, L x*phi x)+(∫ x in U, S x*phi x)=0 by linarith)
          simpa only [mul_comm] using hL
    change (∫ x, phi x * (L x+S x))=0
    rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=U)
      (fun x hx => show phi x * (L x+S x)=0 by
        rw [image_eq_zero_of_notMem_tsupport (fun hy => hx (ht hy)),zero_mul])]
    simpa only [smul_eq_mul,Pi.add_apply] using hzeroU
  apply (MemWkp_congr_ae (by norm_num) hU _).mp hS
  filter_upwards [hz] with x hx
  change S x=-(∑ i : Fin 2, fderiv ℝ
    (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i))
  have hh : L x=∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i) := by
    simp [L,classicalL]
  rw [←hh]
  linarith
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_classical_source_Wkp_v474
