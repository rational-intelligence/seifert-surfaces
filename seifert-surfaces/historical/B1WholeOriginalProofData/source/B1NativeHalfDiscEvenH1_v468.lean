import B1BoundaryH3Step_v468
import NativeBoundaryEvenContinuous
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak
open BoundaryContinuation BoundarySupport
open BoundaryRegularity
set_option maxHeartbeats 1000000

/-- The paid even native H1 reflection transported into the original collar's
literal convention: coordinate one is normal and coordinate zero tangential. -/
theorem native_halfdisc_even_H1_v468 (R : ℝ) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (hu : DeGiorgi.MemW1p 2 u (halfDisc R)) :
    DeGiorgi.MemW1p 2 (fun x => if 0≤x 1 then u x else u (reflect x)) (Metric.ball 0 R) := by
  classical
  let A : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0:Fin 2) 1)
  let P : E2 ≃L[ℝ] E2 := A.toContinuousLinearEquiv
  have hP0 (x : E2) : P x 0=x 1 := by
    simp [P,A,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  have hP1 (x : E2) : P x 1=x 0 := by
    simp [P,A,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']
  have hPP (x : E2) : P (P x)=x := by
    ext i
    fin_cases i
    · change P (P x) 0=x 0
      rw [hP0,hP1]
    · change P (P x) 1=x 1
      rw [hP1,hP0]
  have hhalf : P ⁻¹' halfDisc R=BoundaryRegularity.openHalfDisc R := by
    ext x
    change (dist (P x) 0<R ∧ 0<(P x) 1) ↔ (dist x 0<R ∧ 0<x 0)
    simp only [dist_zero_right,hP1]
    change (‖A x‖<R ∧ 0<x 0) ↔ (‖x‖<R ∧ 0<x 0)
    rw [A.norm_map]
  have hball : P ⁻¹' Metric.ball (0:E2) R=Metric.ball 0 R := by
    ext x
    simp only [mem_preimage,Metric.mem_ball,dist_zero_right]
    change ‖A x‖<R ↔ ‖x‖<R
    rw [A.norm_map]
  have hn := native_smooth_memW1p_H1_v468 _
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)) u hs hu
  have ht := linear_h1_pullback (halfDisc R) P u (planarGradient u) hn
  rw [hhalf] at ht
  have huP := (native_regular_witness_v468 _ _ _ ht).memW1p
  have he := native_even_extension_memW1p R (fun x => u (P x)) huP
  let hw := he.someWitness
  have hnE := regular_witness_native_H1_v468 _ _ hw
  have hback := linear_h1_pullback (Metric.ball (0:E2) R) P _ _ hnE
  rw [hball] at hback
  have href (x : E2) : P (normalReflection (P x))=reflect x := by
    ext i
    fin_cases i
    · change P (normalReflection (P x)) 0=reflect x 0
      rw [hP0,normalReflection_one,hP1]
      rfl
    · change P (normalReflection (P x)) 1=reflect x 1
      rw [hP1,normalReflection_zero,hP0]
      rfl
  have hv : (fun x => nativeEvenExtension (fun y => u (P y)) (P x))=
      fun x => if 0≤x 1 then u x else u (reflect x) := by
    funext x
    simp only [nativeEvenExtension,hP0,hPP,href]
  simpa only [hv] using (native_regular_witness_v468 _ _ _ hback).memW1p
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_even_H1_v468
