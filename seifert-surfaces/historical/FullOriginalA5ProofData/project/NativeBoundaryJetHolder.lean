import NativeBoundaryFullGradientHolder

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Holder control of the actual first jet, derived from the same original
solution state on a closed native boundary cap. -/
theorem C1QuasilinearDirichletSolution.local_holder_firstJetWithin
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α (firstJetWithin ρ u)
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δ, K, α, hδ, hα, hα1, hball, _, hG⟩ :=
    hsolution.local_holder_full_gradient hρ c hc
  obtain ⟨L, hL⟩ := hsolution.lipschitz_on_closedHalfDisc hρ
  let V := Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}
  have hV : V ⊆ closedHalfDisc ρ := fun x hx => ⟨Metric.ball_subset_closedBall (hball hx.1), hx.2⟩
  let D : ℝ≥0 := ⟨2 * δ, by positivity⟩
  have hdiam : ∀ x ∈ V, ∀ y ∈ V, edist x y ≤ D := by
    intro x hx y hy
    rw [edist_dist, ENNReal.ofReal_le_coe]
    change dist x y ≤ 2 * δ
    have hd := dist_triangle_right x y c
    have hx' : dist x c ≤ δ := hx.1
    have hy' : dist y c ≤ δ := hy.1
    linarith
  have hI := HolderOnWith.of_le hdiam (holderWith_id.holderOnWith V) hα1.le
  have hU := HolderOnWith.of_le hdiam (hL.mono hV).holderOnWith hα1.le
  let CI := (1 : ℝ≥0) * D ^ (1 - (α : ℝ))
  let CU := L * D ^ (1 - (α : ℝ))
  let C := CI + CU + 2 * K
  refine ⟨δ, C, α, hδ, hα, hα1, hball, ?_⟩
  apply native_holder_of_norm_distance_bound
  intro x hx y hy
  have hi : dist x y ≤ (CI : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [CI, id_eq, NNReal.coe_one] using hI.dist_le hx hy
  have hu : |u x - u y| ≤ (CU : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [CU, Real.dist_eq, NNReal.coe_one] using hU.dist_le hx hy
  have hg : ‖planarGradientWithin u (closedHalfDisc ρ) x -
      planarGradientWithin u (closedHalfDisc ρ) y‖ ≤ ((2 * K : ℝ≥0) : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [dist_eq_norm] using hG.dist_le hx hy
  change ‖(x, u x, planarGradientWithin u (closedHalfDisc ρ) x) -
    (y, u y, planarGradientWithin u (closedHalfDisc ρ) y)‖ ≤ _
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  simp only [C, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
  have hrpow : 0 ≤ dist x y ^ (α : ℝ) := Real.rpow_nonneg dist_nonneg _
  apply max_le
  · calc
      ‖x - y‖ ≤ (CI : ℝ) * dist x y ^ (α : ℝ) := by simpa only [dist_eq_norm] using hi
      _ ≤ _ := by nlinarith [CI.coe_nonneg, CU.coe_nonneg, K.coe_nonneg]
  · apply max_le
    · calc
        ‖u x - u y‖ ≤ (CU : ℝ) * dist x y ^ (α : ℝ) := by simpa only [Real.norm_eq_abs] using hu
        _ ≤ _ := by nlinarith [CI.coe_nonneg, CU.coe_nonneg, K.coe_nonneg]
    · calc
        _ ≤ _ := hg
        _ ≤ _ := by simp only [NNReal.coe_mul, NNReal.coe_ofNat]; nlinarith [CI.coe_nonneg, CU.coe_nonneg, K.coe_nonneg]

/-- A smooth coefficient on the original open jet domain is Holder along
the actual within jets, on a smaller closed boundary cap. -/
theorem C1QuasilinearDirichletSolution.local_holder_jet_composition
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) (f : Jet → F) (hf : ContDiffOn ℝ 1 f J) :
    ∃ δ : ℝ, ∃ K α : ℝ≥0, 0 < δ ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c δ ⊆ Metric.ball 0 ρ ∧
      HolderOnWith K α (fun x => f (firstJetWithin ρ u x))
        (Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0}) := by
  obtain ⟨δ, K, α, hδ, hα, hα1, hball, hH⟩ := hsolution.local_holder_firstJetWithin hρ c hc
  have hcD : c ∈ closedHalfDisc ρ := ⟨Metric.ball_subset_closedBall hc.1, hc.2.ge⟩
  obtain ⟨r, κ, M, T, hr, hTopen, hTconvex, hTcompact, hTJ, hjets, _⟩ :=
    hsolution.local_boundary_jet_tube hρ c hcD
  have hlocal : LocallyLipschitzOn J f := by
    intro z hz
    obtain ⟨A, U, hU, hA⟩ := (hf.contDiffAt (hsolution.jet_domain_open.mem_nhds hz)).exists_lipschitzOnWith
    exact ⟨A, U, mem_nhdsWithin_of_mem_nhds hU, hA⟩
  obtain ⟨A, hA⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hTcompact (hlocal.mono hTJ)
  let s := min δ r
  have hs : 0 < s := lt_min hδ hr
  have hsr : s ≤ 4 * r := by dsimp [s]; have := min_le_right δ r; linarith
  have hV : Metric.closedBall c s ∩ {x : E2 | 0 ≤ x 0} ⊆
      Metric.closedBall c δ ∩ {x : E2 | 0 ≤ x 0} := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hx.1, hx.2⟩
  have hmap : MapsTo (firstJetWithin ρ u)
      (Metric.closedBall c s ∩ {x : E2 | 0 ≤ x 0}) (closure T) := by
    intro x hx
    apply subset_closure
    apply hjets x
    exact ⟨Metric.closedBall_subset_closedBall hsr hx.1,
      ⟨Metric.ball_subset_closedBall (hball (hV hx).1), hx.2⟩⟩
  refine ⟨s, A * K, α, hs, hα, hα1,
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hball, ?_⟩
  have hh := hA.holderOnWith.comp (hH.mono hV) hmap
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul, Function.comp_def] using hh

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
