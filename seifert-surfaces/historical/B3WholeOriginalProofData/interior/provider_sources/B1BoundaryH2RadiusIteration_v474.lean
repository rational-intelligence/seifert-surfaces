import B1BoundaryH2Radius_v474
import B1BoundaryClassicalSourceL2_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open SeifertSurfaces.QuasilinearProviderBridge
set_option maxHeartbeats 800000

/-- The genuine boundary H2 step is reusable for a compactly localized native
tangential equation. It also retains the zero extension needed for the next
flat-edge zero-trace localization. -/
theorem native_boundary_H2_radius_v474
    (R q : ℝ) (hq : 0<q) (hqR : q<R) (u : E2 → ℝ) (hs : ContDiffOn ℝ ∞ u (halfDisc R))
    (h0 : H10On (halfDisc R) u (planarGradient u))
    (B : SmoothEllipticBilinearForm 2 univ) (S : E2 → ℝ)
    (hF : MemLp (fun x => matrixAction (B.a x) (planarGradient u x)) 2
      (volume.restrict (halfDisc R)))
    (hS : MemLp S 2 (volume.restrict (halfDisc R)))
    (hweak : ∀ phi : E2 → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ halfDisc R →
      (∫ x in halfDisc R, inner ℝ (matrixAction (B.a x) (planarGradient u x))
        (planarGradient phi x)-S x*phi x)=0) :
    (∃ df : E2 → E2, H1On (Metric.ball 0 q)
      (fun x => (halfDisc R).indicator (planarGradient u) x 0) df) ∧
    MemWkp 2 2 u (halfDisc q) ∧
      ∀ i : Fin 2, DeGiorgi.MemW1p 2 (fun x => planarGradient u x i) (halfDisc q) := by
  have ht := native_boundary_tangential_radius_v474 R q hq hqR u h0 B S hF hS hweak
  obtain ⟨w0,hw0,hd0⟩ := ht 0
  obtain ⟨w1,hw1,hd1⟩ := ht 1
  refine ⟨⟨_,native_zero_extended_tangent_H1_v468 R q hq
    u (planarGradient u) h0 w0 w1 hw0 hw1 hd0 hd1⟩,?_⟩
  have hsource := native_boundary_classical_source_L2_v468 R u hs B S hS hweak
  have hsub : halfDisc q ⊆ halfDisc R :=
    fun x hx => ⟨Metric.ball_subset_ball hqR.le hx.1,hx.2⟩
  have hU : IsOpen (halfDisc q) := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have htan (i : Fin 2) : MemLp (fun x => fderiv ℝ
      (fun y => planarGradient u y i) x (coordinateVector 2 0)) 2 (volume.restrict (halfDisc q)) := by
    obtain ⟨w,hw,hd⟩ := ht i
    exact native_boundary_classical_tangential_L2_v468 R q hqR u hs i w
      hw hd
  have hg := native_boundary_normal_L2_recovery_v468 q u (hs.mono hsub)
    (h0.1.2.2.mono_measure (Measure.restrict_mono_set _ hsub)) B
    (fun x => -(∑ i : Fin 2, fderiv ℝ
      (fun y => matrixAction (B.a y) (planarGradient u y) i) x (coordinateVector 2 i)))
    (hsource.mono_measure (Measure.restrict_mono_set _ hsub))
    (fun x hx => add_neg_cancel _) htan
  refine ⟨?_,hg⟩
  let hu : DeGiorgi.MemW1pWitness 2 u (halfDisc q) :=
    { memLp := h0.1.2.1.mono_measure (Measure.restrict_mono_set _ hsub)
      weakGrad := planarGradient u
      weakGrad_component_memLp := fun i =>
        (h0.1.2.2.eval_piLp i).mono_measure (Measure.restrict_mono_set _ hsub)
      isWeakGrad := Helpers.C1_hasWeakGrad _ hU u ((hs.mono hsub).of_le (by simp)) }
  exact MemWkp.of_weakGrad_memWkp (by norm_num) hU hu
    (fun i => MemWkp.one_iff_memW1p.mpr (hg i))
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_H2_radius_v474
