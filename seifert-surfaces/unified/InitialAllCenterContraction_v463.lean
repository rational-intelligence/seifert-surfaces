import InitialAllCenterGeometry_v463

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1500000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent
local macro "paid_interior_step" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialInteriorHoleFilling_v460 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_minimizer_contained_ball_hole_filling_v460)⟩
local macro "paid_boundary_step" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialBoundaryHoleFilling_v463 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_minimizer_boundary_cap_hole_filling_v463)⟩
local macro "paid_center_geometry" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialAllCenterGeometry_v463 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_disc_center_ball_or_boundary_near_v463)⟩

private theorem original_minimizer_all_center_cap_contraction_v463
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x∈closure Ω.domain,M x=inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j,∃ C:ℝ≥0,HolderWith C G.alpha (fun x=>M x i j))
    (identity_at_infinity : ∃ L:ℝ,0 < L ∧ ∀ x:E2,L ≤ ‖x‖ → M x=1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d) :
    ∃ rho q:ℝ,0 < rho ∧ rho ≤ 1/2 ∧ 0 < q ∧ q < 1 ∧
      ∀ x∈closedDisc 1,∀ r:ℝ,0 < r → r ≤ rho →
        (∫ z in planarCap x (r/32),euclideanJetDensity d z) ≤
          q*∫ z in planarCap x r,euclideanJetDensity d z := by
  classical
  obtain ⟨KI,hKI,hI⟩ := paid_interior_step R A G Ω M agreement symmetric elliptic
    holder identity_at_infinity f d minimum
  obtain ⟨KB,rho,hKB,hrho,hrhohalf,hB⟩ := paid_boundary_step R A G Ω M agreement
    symmetric elliptic holder identity_at_infinity f d minimum
  let K:ℝ := max KI KB
  let q:ℝ := (K+1)/(K+2)
  have hK:0 < K := hKI.trans_le (le_max_left _ _)
  have hq:0 < q := by dsimp [q];positivity
  have hq1:q < 1 := by dsimp [q];rw [div_lt_one (by linarith : 0 < K+2)];linarith
  have hqeq:q*(K+2)=K+1 := div_mul_cancel₀ _ (by linarith : K+2 ≠ 0)
  let E:E2→ℝ→ℝ := fun x r=>∫ z in planarCap x r,euclideanJetDensity d z
  have hi:IntegrableOn (euclideanJetDensity d) (disc 1) := by
    apply integrable_finsetSum
    intro i _
    exact (minimum.admissible.1 i).2.2.norm.integrable_sq
  have hn (x:E2) (r:ℝ):0 ≤ E x r := integral_nonneg (fun z=>Finset.sum_nonneg fun i _=>sq_nonneg _)
  have hm (x y:E2) (r s:ℝ) (hs:planarCap x r⊆planarCap y s):E x r ≤ E y s :=
    setIntegral_mono_set (hi.mono_set inter_subset_left)
      (Eventually.of_forall fun z=>Finset.sum_nonneg fun i _=>sq_nonneg _)
      (Eventually.of_forall fun z hz=>hs hz)
  have contract (small big:ℝ) (hs:0 ≤ small) (hb:0 ≤ big) (horder:small ≤ big)
      (k:ℝ) (hk:k ≤ K) (step:small ≤ k*(big-small)):small ≤ q*big := by
    have hd:0 ≤ big-small := sub_nonneg.mpr horder
    have hstep:small ≤ K*(big-small) := step.trans (mul_le_mul_of_nonneg_right hk hd)
    have hmul:q*big*(K+2)=(K+1)*big := by rw [mul_right_comm,hqeq]
    nlinarith [mul_nonneg hK.le hs]
  refine ⟨rho,q,hrho,hrhohalf,hq,hq1,?_⟩
  intro x hx r hr hrr
  change E x (r/32) ≤ q*E x r
  rcases paid_center_geometry x hx r hr (hrr.trans hrhohalf) with hint | hnear
  · have hstep := hI x hx (r/16) (by positivity) (by linarith [hrr.trans hrhohalf]) hint
    change E x ((r/16)/2) ≤ KI*(E x (r/16)-E x ((r/16)/2)) at hstep
    rw [show (r/16)/2=r/32 by ring] at hstep
    have hm1:E x (r/32) ≤ E x (r/16) := hm x x _ _
      (inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith)))
    have hc := contract _ _ (hn _ _) (hn _ _) hm1 KI (le_max_left _ _) hstep
    have hm2:E x (r/16) ≤ E x r := hm x x _ _
      (inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith)))
    exact hc.trans (mul_le_mul_of_nonneg_left hm2 hq.le)
  · obtain ⟨s,hs⟩ := hnear
    let b:E2 := unitCircleParameter s
    have hs':dist x b < r/8 := hs
    have hstep := hB s (r/2) (by positivity) (by linarith)
    change E b ((r/2)/2) ≤ KB*(E b (r/2)-E b ((r/2)/2)) at hstep
    rw [show (r/2)/2=r/4 by ring] at hstep
    have hm1:E b (r/4) ≤ E b (r/2) := hm b b _ _
      (inter_subset_inter_right _ (Metric.ball_subset_ball (by linarith)))
    have hc := contract _ _ (hn _ _) (hn _ _) hm1 KB (le_max_right _ _) hstep
    have hsmall:E x (r/32) ≤ E b (r/4) := by
      apply hm
      intro z hz
      refine ⟨hz.1,?_⟩
      have hzsmall:dist z x < r/32 := hz.2
      have ht := dist_triangle z x b
      change dist z b < r/4
      linarith
    have hbig:E b (r/2) ≤ E x r := by
      apply hm
      intro z hz
      refine ⟨hz.1,?_⟩
      have hzbig:dist z b < r/2 := hz.2
      have ht := dist_triangle z b x
      rw [dist_comm b x] at ht
      change dist z x < r
      linarith
    exact hsmall.trans (hc.trans (mul_le_mul_of_nonneg_left hbig hq.le))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
