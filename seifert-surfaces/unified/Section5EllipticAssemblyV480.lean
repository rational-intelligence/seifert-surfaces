import Section5GeometricDefinitions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency

/-- Mean-value graph coefficients use the same native operator in Section 5.7. -/
theorem linear_graph_equation_of_native_operator
    (f : E2 → ℝ) (domain : Set E2) (hopen : IsOpen domain)
    (hf : ContDiffOn ℝ ∞ f domain)
    (a : E2 → Mat2) (b : E2 → E2) (c : E2 → ℝ)
    (hcoeff : SmoothEllipticOn a b c domain)
    (heq : ∀ x ∈ domain, classicalL a b c f x = 0) :
    Nonempty (LinearGraphEquation f domain) := by
  obtain ⟨ha, hb, hc, hsym, ell, C, hell, hC, hbounds⟩ := hcoeff
  have hgradient : ∀ x i, planarGradient f x i = partialDerivative f i x := by
    intro x i
    fin_cases i <;> simp [planarGradient, partialDerivative, coordinateVector]
  have hflux : ∀ x i, matrixAction (a x) (planarGradient f x) i =
      ∑ j : Fin 2, a x i j * partialDerivative f j x := by
    intro x i
    simp [matrixAction, hgradient]
  refine ⟨{
    principal := fun i j x => a x i j
    drift := fun i x => b x i
    zeroth := c
    principal_smooth := ha
    drift_smooth := ?_
    zeroth_smooth := hc
    symmetric := fun i j x hx => hsym x hx i j
    ellipticity := ell
    ellipticity_pos := hell
    elliptic := ?_
    equation := ?_ }⟩
  · intro i
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.comp hb
      (fun _ _ => Set.mem_univ _)
  · intro x hx v
    have h := (hbounds x hx v).1
    convert h using 1
    simp [matrixAction, PiLp.inner_apply]
    ring
  · intro x hx
    have h := heq x hx
    unfold classicalL at h
    simp only [hflux] at h
    have hdiv : (∑ i : Fin 2, fderiv ℝ
        (fun y => ∑ j : Fin 2, a y i j * partialDerivative f j y) x (coordinateVector 2 i)) =
        ∑ i : Fin 2, ∑ j : Fin 2,
          partialDerivative (fun y => a y i j * partialDerivative f j y) i x := by
      apply Finset.sum_congr rfl
      intro i hi
      have hd : ∀ j : Fin 2, DifferentiableAt ℝ
          (fun y => a y i j * partialDerivative f j y) x := by
        intro j
        apply ((ha i j x hx).contDiffAt (hopen.mem_nhds hx)).differentiableAt (by simp) |>.mul
        exact (((hf x hx).contDiffAt (hopen.mem_nhds hx)).fderiv_right (m := 1)
          (by simp) |>.clm_apply contDiffAt_const).differentiableAt (by norm_num)
      have hsum := (HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) =>
        (hd j).hasFDerivAt)).fderiv
      have happ := congrArg (fun L : E2 →L[ℝ] ℝ => L (coordinateVector 2 i)) hsum
      simpa [partialDerivative] using happ
    rw [hdiv] at h
    simpa [PiLp.inner_apply, hgradient, mul_comm] using h

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates

/-- Restriction preserves every clause of the native linear graph equation when
an open ball is contained in its coefficient domain. -/
theorem linear_graph_equation_restrict_ball
    {f : E2 → ℝ} {domain : Set E2}
    (L : LinearGraphEquation f domain) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball (0 : E2) r ⊆ domain) :
    Nonempty (LinearGraphEquation f (Metric.ball 0 r)) := by
  refine ⟨{
    principal := L.principal
    drift := L.drift
    zeroth := L.zeroth
    principal_smooth := fun i j => L.principal_smooth i j |>.mono hball
    drift_smooth := fun i => L.drift_smooth i |>.mono hball
    zeroth_smooth := L.zeroth_smooth.mono hball
    symmetric := fun i j x hx => L.symmetric i j x (hball hx)
    ellipticity := L.ellipticity
    ellipticity_pos := L.ellipticity_pos
    elliptic := fun x hx v => L.elliptic x (hball hx) v
    equation := fun x hx => L.equation x (hball hx)
  }⟩

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
