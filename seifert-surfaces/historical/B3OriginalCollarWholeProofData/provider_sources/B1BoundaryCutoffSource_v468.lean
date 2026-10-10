import B1BoundaryLowerSourceTower_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem native_compact_smooth_mul_L2_v468 (U : Set E2) (hU : MeasurableSet U)
    (hUc : IsCompact (closure U)) (a f : E2 → ℝ) (ha : Continuous a)
    (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun x => a x*f x) 2 (volume.restrict U) := by
  obtain ⟨C,hC⟩ := hUc.exists_bound_of_continuousOn ha.continuousOn
  have htop : MemLp a ⊤ (volume.restrict U) := by
    apply memLp_top_of_bound ha.aestronglyMeasurable.restrict C
    filter_upwards [ae_restrict_mem hU] with x hx
    exact hC x (subset_closure hx)
  exact htop.fun_mul hf

/-- Multiplication by a smooth compact cutoff preserves the actual principal
L2 source. The identity is proved in the open half-disc and the L2 bound is
valid up to its flat boundary. -/
theorem native_boundary_cutoff_source_L2_v468
    (R : ℝ) (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hu : H1On (halfDisc R) u (planarGradient u))
    (B : SmoothEllipticBilinearForm 2 univ)
    (hF : MemLp (fun x => matrixAction (B.a x) (planarGradient u x)) 2
      (volume.restrict (halfDisc R)))
    (hS : MemLp (fun x => -(∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i)))
      2 (volume.restrict (halfDisc R)))
    (chi : E2 → ℝ) (hc : ContDiff ℝ ∞ chi) :
    MemLp (fun x => -(∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient (fun z => chi z*u z) y) i) x
        (coordinateVector 2 i))) 2 (volume.restrict (halfDisc R)) := by
  classical
  let U := halfDisc R
  let v : E2 → ℝ := fun x => chi x*u x
  let F : E2 → E2 := fun x => matrixAction (B.a x) (planarGradient u x)
  let G : E2 → E2 := fun x => matrixAction (B.a x) (planarGradient chi x)
  let S : E2 → ℝ := fun x => -(∑ i : Fin 2, fderiv ℝ (fun y => F y i) x (coordinateVector 2 i))
  let T : E2 → ℝ := fun x => chi x*S x - ∑ i : Fin 2,
    (planarGradient chi x i*F x i + planarGradient u x i*G x i+
      u x*fderiv ℝ (fun y => G y i) x (coordinateVector 2 i))
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hUc : IsCompact (closure U) := (isCompact_closedBall (0:E2) R).of_isClosed_subset
    isClosed_closure (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1) Metric.isClosed_closedBall)
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    apply ContDiffOn.sum
    intro i hi
    exact ((hs.fderiv_of_isOpen hU (m:=∞) (by simp)).clm_apply contDiffOn_const).smul contDiffOn_const
  have hcg : ContDiff ℝ ∞ (planarGradient chi) := by
    unfold planarGradient
    apply ContDiff.sum
    intro i hi
    exact ((hc.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).smul contDiff_const
  have hFs (i : Fin 2) : ContDiffOn ℝ ∞ (fun x => F x i) U := by
    change ContDiffOn ℝ ∞ (fun x => ∑ j : Fin 2, B.a x i j*planarGradient u x j) U
    apply ContDiffOn.sum
    intro j hj
    exact (B.smooth_a i j).contDiffOn.mul
      ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp_contDiffOn hgrad)
  have hGs (i : Fin 2) : ContDiff ℝ ∞ (fun x => G x i) := by
    change ContDiff ℝ ∞ (fun x => ∑ j : Fin 2, B.a x i j*planarGradient chi x j)
    apply ContDiff.sum
    intro j hj
    exact (B.smooth_a i j).mul ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp hcg)
  have hTLp : MemLp T 2 (volume.restrict U) := by
    have hp := native_compact_smooth_mul_L2_v468 U hU.measurableSet hUc chi S hc.continuous hS
    have hsum : MemLp (fun x => ∑ i : Fin 2,
        (planarGradient chi x i*F x i + planarGradient u x i*G x i+
          u x*fderiv ℝ (fun y => G y i) x (coordinateVector 2 i))) 2 (volume.restrict U) := by
      apply memLp_finsetSum
      intro i hi
      have h1 : MemLp (fun x => planarGradient chi x i*F x i) 2 (volume.restrict U) :=
        native_compact_smooth_mul_L2_v468 U hU.measurableSet hUc _ _
          ((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hcg.continuous) (hF.eval_piLp i)
      have h2 := native_compact_smooth_mul_L2_v468 U hU.measurableSet hUc _ _
        (hGs i).continuous (hu.2.2.eval_piLp i)
      have h3 := native_compact_smooth_mul_L2_v468 U hU.measurableSet hUc
        (fun x => fderiv ℝ (fun y => G y i) x (coordinateVector 2 i)) u
        (((hGs i).continuous_fderiv (by simp)).clm_apply continuous_const) hu.2.1
      convert (h1.add h2).add h3 using 1
      funext x
      dsimp only [Pi.add_apply]
      ring
    exact hp.sub hsum
  have hval (x : E2) (hx : x∈U) (i : Fin 2) :
      matrixAction (B.a x) (planarGradient v x) i=chi x*F x i+u x*G x i := by
    have hdu := ((hs x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdchi := hc.differentiable (by simp) x
    have hg (j : Fin 2) : planarGradient v x j=
        chi x*planarGradient u x j+u x*planarGradient chi x j := by
      simp only [QuasilinearLocalization.Helpers.gradient_apply]
      rw [show fderiv ℝ v x=chi x • fderiv ℝ u x+u x • fderiv ℝ chi x by
        dsimp only [v]
        simpa only [add_comm] using fderiv_fun_mul hdchi hdu]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    change (∑ j : Fin 2, B.a x i j*planarGradient v x j)=
      chi x*(∑ j : Fin 2, B.a x i j*planarGradient u x j)+
      u x*(∑ j : Fin 2, B.a x i j*planarGradient chi x j)
    simp_rw [hg]
    simp only [Fin.sum_univ_two]
    ring
  have hder (x : E2) (hx : x∈U) (i : Fin 2) :
      fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient v y) i) x (coordinateVector 2 i)=
        planarGradient chi x i*F x i+
        chi x*fderiv ℝ (fun y => F y i) x (coordinateVector 2 i)+
        planarGradient u x i*G x i+u x*fderiv ℝ (fun y => G y i) x (coordinateVector 2 i) := by
    have he : (fun y => matrixAction (B.a y) (planarGradient v y) i)=ᶠ[𝓝 x]
        (fun y => chi y*F y i+u y*G y i) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hval y hy i
    rw [he.fderiv_eq]
    have hdu := ((hs x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdf := ((hFs i x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdc := hc.differentiable (by simp) x
    have hdg := (hGs i).differentiable (by simp) x
    have hd12 : fderiv ℝ (fun y => chi y*F y i+u y*G y i) x=
        fderiv ℝ (fun y => chi y*F y i) x+fderiv ℝ (fun y => u y*G y i) x := by
      exact fderiv_fun_add (show DifferentiableAt ℝ (fun y => chi y*F y i) x from hdc.mul hdf)
        (show DifferentiableAt ℝ (fun y => u y*G y i) x from hdu.mul hdg)
    have hd1 : fderiv ℝ (fun y => chi y*F y i) x=
        chi x • fderiv ℝ (fun y => F y i) x+F x i • fderiv ℝ chi x := by
      simpa only [Pi.mul_apply] using fderiv_fun_mul hdc hdf
    have hd2 : fderiv ℝ (fun y => u y*G y i) x=
        u x • fderiv ℝ (fun y => G y i) x+G x i • fderiv ℝ u x := by
      simpa only [Pi.mul_apply] using fderiv_fun_mul hdu hdg
    rw [hd12,hd1,hd2]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      QuasilinearLocalization.Helpers.gradient_apply]
    ring
  apply hTLp.ae_eq
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  change T x=-(∑ i : Fin 2, fderiv ℝ
    (fun y => matrixAction (B.a y) (planarGradient v y) i) x (coordinateVector 2 i))
  simp_rw [hder x hx]
  simp only [T,S,Fin.sum_univ_two]
  ring
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_compact_smooth_mul_L2_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_cutoff_source_L2_v468
