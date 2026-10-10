import NativeBoundaryNormalDerivativeBound

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem native_holder_of_real_distance_bound
    (V : Set E2) (f : E2 → ℝ) (K α : ℝ≥0)
    (hf : ∀ x ∈ V, ∀ y ∈ V, |f x - f y| ≤ (K : ℝ) * dist x y ^ (α : ℝ)) :
    HolderOnWith K α f V := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.dist_eq] using hf x hx y hy)

/-- Normal within derivative Holder regularity is a conclusion under the
original C1 state. It follows from the actual native normal flux and the
actual tangential derivative, using ellipticity along the true jet tube. -/
theorem C1QuasilinearDirichletSolution.local_holder_normal_derivative
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α (fun x => fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0))
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δF, KF, αF, hδF, hballF, hαF, hαF1, hF⟩ := hsolution.local_normal_flux_holder hρ c hc
  obtain ⟨δT, KT, αT, hδT, hαT, hαT1, hballT, hT⟩ :=
    hsolution.local_holder_tangential_derivative hρ c hc
  obtain ⟨r, κ, M, L, hr, hκ, hM, hball, hbound⟩ :=
    hsolution.local_normal_derivative_difference_bound hρ c hc
  let δ := min r (min δF δT)
  have hδ : 0 < δ := lt_min hr (lt_min hδF hδT)
  have hδr : δ ≤ r := min_le_left _ _
  have hδF' : δ ≤ δF := (min_le_right _ _).trans (min_le_left _ _)
  have hδT' : δ ≤ δT := (min_le_right _ _).trans (min_le_right _ _)
  let V := Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}
  let α := min αF αT
  have hα : 0 < α := lt_min hαF hαT
  have hα1 : α < 1 := (min_le_left _ _).trans_lt hαF1
  let D : ℝ≥0 := ⟨2 * δ, by positivity⟩
  have hdiam : ∀ x ∈ V, ∀ y ∈ V, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * δ
    have hd := dist_triangle_right x y c
    have hx' : dist x c ≤ δ := hx.1
    have hy' : dist y c ≤ δ := hy.1
    linarith
  have hFH := HolderOnWith.of_le hdiam
    (hF.mono (fun x hx => ⟨Metric.closedBall_subset_closedBall hδF' hx.1, hx.2⟩))
    (min_le_left αF αT)
  have hTH := HolderOnWith.of_le hdiam
    (hT.mono (fun x hx => ⟨Metric.closedBall_subset_closedBall hδT' hx.1, hx.2⟩))
    (min_le_right αF αT)
  have hIH := HolderOnWith.of_le hdiam (holderWith_id.holderOnWith V) hα1.le
  let CF := KF * D ^ ((αF : ℝ) - (α : ℝ))
  let CT := KT * D ^ ((αT : ℝ) - (α : ℝ))
  let CI := (1 : ℝ≥0) * D ^ (1 - (α : ℝ))
  let C : ℝ := ((CF : ℝ) + M * (((L : ℝ) + 1) * CI + CT)) / κ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let K : ℝ≥0 := ⟨C, hC⟩
  refine ⟨δ, K, α, hδ, hα, hα1,
    (Metric.closedBall_subset_closedBall hδr).trans hball, ?_⟩
  apply native_holder_of_real_distance_bound
  intro x hx y hy
  have hFx := hFH.dist_le hx hy
  have hTx := hTH.dist_le hx hy
  have hIx := hIH.dist_le hx hy
  have hbx := hbound x ⟨Metric.closedBall_subset_closedBall hδr hx.1, hx.2⟩
    y ⟨Metric.closedBall_subset_closedBall hδr hy.1, hy.2⟩
  have hFreal : |Q.flux (firstJetWithin ρ u y) 0 - Q.flux (firstJetWithin ρ u x) 0| ≤
      (CF : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [CF, α, Real.dist_eq, abs_sub_comm] using hFx
  have hTreal : |fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 1) -
      fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 1)| ≤
      (CT : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [CT, α, Real.dist_eq, abs_sub_comm] using hTx
  have hIreal : dist x y ≤ (CI : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [CI, α, id_eq, NNReal.coe_one] using hIx
  have hmajor : κ * |fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0) -
      fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0)| ≤
      ((CF : ℝ) + M * (((L : ℝ) + 1) * CI + CT)) * dist x y ^ (α : ℝ) := by
    calc
      _ ≤ _ := hbx
      _ ≤ (CF : ℝ) * dist x y ^ (α : ℝ) + M *
          (((L : ℝ) + 1) * ((CI : ℝ) * dist x y ^ (α : ℝ)) +
            (CT : ℝ) * dist x y ^ (α : ℝ)) := by gcongr
      _ = _ := by ring
  have hh := (le_div_iff₀ hκ).mpr (by simpa only [mul_comm κ] using hmajor)
  change |fderivWithin ℝ u (closedHalfDisc ρ) x (coordinateVector 2 0) -
    fderivWithin ℝ u (closedHalfDisc ρ) y (coordinateVector 2 0)| ≤ C * dist x y ^ (α : ℝ)
  rw [abs_sub_comm]
  exact hh.trans_eq (by dsimp [C]; ring)

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
