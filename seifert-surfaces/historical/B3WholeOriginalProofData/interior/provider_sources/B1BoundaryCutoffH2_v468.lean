import B1BoundaryNativeH2Iteration_v468
import B1BoundaryCutoffSource_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open ChartMetricProvider.Variational.DirectWeak
set_option maxHeartbeats 1000000

/-- Smooth ambient coefficients act on native L2 gradients up to the flat edge. -/
theorem native_compact_principal_flux_L2_v468 (R : ℝ) (B : SmoothEllipticBilinearForm 2 univ)
    (du : E2 → E2) (hd : MemLp du 2 (volume.restrict (halfDisc R))) :
    MemLp (fun x => matrixAction (B.a x) (du x)) 2 (volume.restrict (halfDisc R)) := by
  have hU : MeasurableSet (halfDisc R) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)).measurableSet
  have hUc : IsCompact (closure (halfDisc R)) := (isCompact_closedBall (0:E2) R).of_isClosed_subset
    isClosed_closure (closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1) Metric.isClosed_closedBall)
  apply memLp_piLp_iff.mpr
  intro i
  change MemLp (fun x => ∑ j : Fin 2, B.a x i j*du x j) 2 (volume.restrict (halfDisc R))
  apply memLp_finsetSum
  intro j hj
  exact native_compact_smooth_mul_L2_v468 _ hU hUc _ _ (B.continuous_a i j) (hd.eval_piLp j)

/-- The principal classical divergence supplies the literal smooth-test weak
identity on the open half-disc, without assuming any boundary regularity. -/
theorem native_classical_principal_weak_v468 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (B : SmoothEllipticBilinearForm 2 univ)
    (phi : E2 → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (ht : tsupport phi ⊆ halfDisc R) :
    (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
      (planarGradient phi x)-
      (-(∑ i : Fin 2, fderiv ℝ (fun y => matrixAction (B.a y) (planarGradient u y) i) x
        (coordinateVector 2 i)))*phi x)=0 := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hh := halfdisc_local_classical_form_identity_v468 R (halfDisc R) hU Subset.rfl
    B.a (fun _ => 0) (fun _ => 0) u (fun i j => (B.smooth_a i j).contDiffOn)
    contDiffOn_const contDiffOn_const hs phi hp hc ht
  have hiP : IntegrableOn (fun x => inner ℝ (matrixAction (B.a x) (planarGradient u x))
      (planarGradient phi x)) (halfDisc R) := by
    simpa only [inner_zero_left,zero_mul,zero_add,sub_zero] using hh.1
  have hiL : IntegrableOn (fun x => (∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i))*phi x)
      (halfDisc R) := by
    simpa [classicalL] using hh.2.1
  simp only [neg_mul,sub_neg_eq_add]
  rw [integral_add hiP hiL]
  have he := hh.2.2
  simp only [inner_zero_left,zero_mul,zero_add,sub_zero,classicalL,add_zero] at he
  linarith

/-- One compact tangential localization gains a second native weak derivative
through the genuine boundary H2 argument. -/
theorem native_boundary_cutoff_H2_v468
    (R : ℝ) (hR : 0<R) (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (hu : H1On (halfDisc R) u (planarGradient u))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ)
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-S x*phi x)=0)
    (chi : E2 → ℝ) (hc : ContDiff ℝ ∞ chi)
    (h0 : H10On (halfDisc R) (fun x => chi x*u x) (cutoffGradient chi u (planarGradient u))) :
    ∀ q : ℝ, 0<q → q<R/4 → MemWkp 2 2 (fun x => chi x*u x) (halfDisc q) := by
  have hU : IsOpen (halfDisc R) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hv : ContDiffOn ℝ ∞ (fun x => chi x*u x) (halfDisc R) := hc.contDiffOn.mul hs
  have hgrad := native_smooth_gradient_ae_v468 _ hU _ _ _ h0.1 hv EventuallyEq.rfl
  have h0' := native_h10_congr_ae_v468 _ _ _ _ _ h0 EventuallyEq.rfl hgrad
  have hF := native_compact_principal_flux_L2_v468 R B _ hu.2.2
  have hsource := native_boundary_classical_source_L2_v468 R u hs B S hS hweak
  have hcut := native_boundary_cutoff_source_L2_v468 R u hs hu B hF hsource chi hc
  have hVF := native_compact_principal_flux_L2_v468 R B _ h0'.1.2.2
  have hh := native_boundary_H2_iteration_v468 R hR _ hv h0' B _ hVF hcut
    (fun phi hp hcc ht => native_classical_principal_weak_v468 R _ hv B phi hp hcc ht)
  intro q hq hqR
  exact (hh.2 q hq hqR).1
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_compact_principal_flux_L2_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_classical_principal_weak_v468
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_cutoff_H2_v468
