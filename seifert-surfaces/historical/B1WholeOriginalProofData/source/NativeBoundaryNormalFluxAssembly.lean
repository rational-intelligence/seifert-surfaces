import NativeBoundaryEvenSobolevAssembly
import NativeBoundaryFluxEnergy

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.local_even_reflected_flux_memW1p
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Metric.ball 0 ρ ∧
      ∀ i : Fin 2,
        DeGiorgi.MemW1p 2
          (nativeEvenReflectedSource (2 * r)
            (fun x => Q.flux (firstJetWithin ρ u (x + c)) i))
          (Metric.ball 0 (2 * r)) := by
  obtain ⟨s, hs, hball, hflux⟩ := hsolution.local_native_flux_memW1p hρ c hc
  have hcf : c 0 = 0 := hc.2
  let U := Metric.ball c s ∩ {x : E2 | 0 < x 0}
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  have hpre : (fun x : E2 => x + c) ⁻¹' U = openHalfDisc s := by
    ext x
    change (dist (x + c) c < s ∧ 0 < (x + c) 0) ↔ (dist x 0 < s ∧ 0 < x 0)
    simp only [dist_eq_norm, add_sub_cancel_right, sub_zero, PiLp.add_apply, hcf, add_zero]
  have hshift (i : Fin 2) :
      DeGiorgi.MemW1p 2 (fun x => Q.flux (firstJetWithin ρ u (x + c)) i)
        (openHalfDisc s) := by
    rw [← hpre]
    exact native_memW1p_translation U hU.measurableSet c
      (fun x => Q.flux (firstJetWithin ρ u x) i) (hflux i).2
  have hsrc (i : Fin 2) :
      DeGiorgi.MemW1p 2 (nativeEvenReflectedSource s
        (fun x => Q.flux (firstJetWithin ρ u (x + c)) i)) (Metric.ball 0 s) := by
    exact native_even_reflected_memW1p s _ (hshift i)
  refine ⟨s / 2, by positivity,
    (Metric.closedBall_subset_closedBall (by linarith : s / 2 ≤ s)).trans hball, ?_⟩
  intro i
  simpa only [show 2 * (s / 2) = s by ring] using hsrc i

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
