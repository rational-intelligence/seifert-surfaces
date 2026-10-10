import NativeBoundaryNormalDerivativeHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_holder_of_norm_distance_bound
    {F : Type*} [NormedAddCommGroup F]
    (V : Set E2) (f : E2 → F) (K α : ℝ≥0)
    (hf : ∀ x ∈ V, ∀ y ∈ V, ‖f x - f y‖ ≤ (K : ℝ) * dist x y ^ (α : ℝ)) :
    HolderOnWith K α f V := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa only [dist_eq_norm] using hf x hx y hy)

/-- Both within partial derivatives and the same full native gradient have
a common positive Holder exponent on a smaller closed boundary cap. -/
theorem C1QuasilinearDirichletSolution.local_holder_full_gradient
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      (∀ i : Fin 2, HolderOnWith K α
        (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i))
          (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0})) ∧
      HolderOnWith (2 * K) α (planarGradientWithin u (closedHalfDisc ρ))
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δN, KN, αN, hδN, hαN, hαN1, hballN, hN⟩ :=
    hsolution.local_holder_normal_derivative hρ c hc
  obtain ⟨δT, KT, αT, hδT, hαT, hαT1, hballT, hT⟩ :=
    hsolution.local_holder_tangential_derivative hρ c hc
  let δ := min δN δT
  have hδ : 0 < δ := lt_min hδN hδT
  let α := min αN αT
  have hα : 0 < α := lt_min hαN hαT
  have hα1 : α < 1 := (min_le_left _ _).trans_lt hαN1
  let V := Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}
  let D : ℝ≥0 := ⟨2 * δ, by positivity⟩
  have hdiam : ∀ x ∈ V, ∀ y ∈ V, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * δ
    have hd := dist_triangle_right x y c
    have hx' : dist x c ≤ δ := hx.1
    have hy' : dist y c ≤ δ := hy.1
    linarith
  have hNH := HolderOnWith.of_le hdiam
    (hN.mono (fun x hx => ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hx.1, hx.2⟩))
    (min_le_left αN αT)
  have hTH := HolderOnWith.of_le hdiam
    (hT.mono (fun x hx => ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hx.1, hx.2⟩))
    (min_le_right αN αT)
  let CN := KN * D ^ ((αN : ℝ) - (α : ℝ))
  let CT := KT * D ^ ((αT : ℝ) - (α : ℝ))
  let K := CN + CT
  have hcomponents : ∀ i : Fin 2, HolderOnWith K α
      (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 i)) V := by
    intro i
    fin_cases i
    · intro x hx y hy
      exact (hNH x hx y hy).trans (by
        change (CN : ℝ≥0∞) * edist x y ^ (α : ℝ) ≤ ((CN + CT : ℝ≥0) : ℝ≥0∞) * edist x y ^ (α : ℝ)
        rw [ENNReal.coe_add]
        gcongr <;> exact le_add_of_nonneg_right zero_le)
    · intro x hx y hy
      exact (hTH x hx y hy).trans (by
        change (CT : ℝ≥0∞) * edist x y ^ (α : ℝ) ≤ ((CN + CT : ℝ≥0) : ℝ≥0∞) * edist x y ^ (α : ℝ)
        rw [ENNReal.coe_add]
        gcongr <;> exact le_add_of_nonneg_left zero_le)
  refine ⟨δ, K, α, hδ, hα, hα1,
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hballN, hcomponents, ?_⟩
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have h₀ := (hcomponents 0).dist_le hx hy
  have h₁ := (hcomponents 1).dist_le hx hy
  calc
    _ ≤ |planarGradientWithin u (closedHalfDisc ρ) x 0 - planarGradientWithin u (closedHalfDisc ρ) y 0| +
        |planarGradientWithin u (closedHalfDisc ρ) x 1 - planarGradientWithin u (closedHalfDisc ρ) y 1| := by
      simpa only [PiLp.sub_apply] using native_planar_norm_le_coordinate_sum
        (planarGradientWithin u (closedHalfDisc ρ) x - planarGradientWithin u (closedHalfDisc ρ) y)
    _ ≤ (K : ℝ) * dist x y ^ (α : ℝ) + (K : ℝ) * dist x y ^ (α : ℝ) := by
      simp only [native_within_gradient_component]
      exact add_le_add (by simpa only [Real.dist_eq] using h₀) (by simpa only [Real.dist_eq] using h₁)
    _ = _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; ring

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
