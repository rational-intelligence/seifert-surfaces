import NativeBoundaryHolderCLMComposition

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology BigOperators ContDiff NNReal ENNReal

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

theorem C1QuasilinearDirichletSolution.local_C1_holder_jet_composition
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : ℝ} (hρ : 0 < ρ) {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u)
    (c : E2) (hc : c ∈ flatBoundary ρ) (f : Jet → F) (hf : ContDiffOn ℝ ∞ f J) :
    ∃ s : ℝ, ∃ α : ℝ≥0, 0 < s ∧ 0 < α ∧ α < 1 ∧
      Metric.closedBall c s ⊆ Metric.ball 0 ρ ∧
      ContDiffOn ℝ 2 u (nativeClosedBoundaryCap c s) ∧
      ContDiffOn ℝ 1 (fun x => f (firstJetWithin ρ u x)) (nativeClosedBoundaryCap c s) ∧
      ∃ C : ℝ≥0, HolderOnWith C α
        (fderivWithin ℝ (fun x => f (firstJetWithin ρ u x)) (nativeClosedBoundaryCap c s))
        (nativeClosedBoundaryCap c s) := by
  obtain ⟨r, α, hr, hα, hα1, hball, hu, hg, Cg, hCg⟩ :=
    hsolution.local_C1_holder_firstJetWithin hρ c hc
  obtain ⟨t, κ, M, T, ht, hTo, hTc, hTk, hTJ, hmaps, _⟩ :=
    hsolution.local_boundary_jet_tube hρ c ⟨Metric.ball_subset_closedBall hc.1, hc.2.ge⟩
  let s := min r t
  have hs : 0 < s := lt_min hr ht
  let K := nativeClosedBoundaryCap c s
  let g0 := firstJetWithin ρ u
  have hsub : K ⊆ nativeClosedBoundaryCap c r := fun x hx =>
    ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hx.1, hx.2⟩
  have hballs : Metric.closedBall c s ⊆ Metric.ball 0 ρ :=
    (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hball
  have hKD := nativeClosedBoundaryCap_uniqueDiffOn c s hs hc.2
  have hgs : ContDiffOn ℝ 1 g0 K := hg.mono hsub
  have hmap : MapsTo g0 K (closure T) := by
    intro x hx
    apply subset_closure
    apply hmaps x
    refine ⟨Metric.closedBall_subset_closedBall (by dsimp [s]; linarith [min_le_right r t]) hx.1, ?_⟩
    exact ⟨Metric.ball_subset_closedBall (hballs hx.1), hx.2⟩
  have hCgs : HolderOnWith Cg α (fderivWithin ℝ g0 K) K := by
    have hEq (x : E2) (hx : x ∈ K) : fderivWithin ℝ g0 K x =
        fderivWithin ℝ g0 (nativeClosedBoundaryCap c r) x :=
      fderivWithin_subset hsub (hKD x hx) (hg.differentiableOn (by norm_num) x (hsub hx))
    intro x hx y hy
    rw [hEq x hx, hEq y hy]
    exact hCg x (hsub hx) y (hsub hy)
  obtain ⟨G, hG⟩ := native_contDiffOn_cap_holder c s hs g0 α hα1.le hgs
  have hDf : ContDiffOn ℝ 1 (fderiv ℝ f) J :=
    hf.fderiv_of_isOpen hsolution.jet_domain_open (by simp)
  obtain ⟨L, hL⟩ := (hDf.mono hTJ).exists_lipschitzOnWith (by norm_num) hTc.closure hTk
  have hAf : HolderOnWith (L * G) α (fun x => fderiv ℝ f (g0 x)) K := by
    have hh := hL.holderOnWith.comp hG hmap
    simpa only [Function.comp_def, NNReal.coe_one, NNReal.rpow_one, one_mul] using hh
  have hcompact : IsCompact K := (isCompact_closedBall c s).inter_right
    (isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  obtain ⟨C, hC⟩ := native_compact_holder_clm_comp_exists K hcompact _ _ α hα
    ⟨L * G, hAf⟩ ⟨Cg, hCgs⟩
  have hcf : ContDiffOn ℝ 1 (fun x => f (g0 x)) K :=
    (hf.of_le (by simp)).comp hgs (fun x hx => hTJ (hmap hx))
  refine ⟨s, α, hs, hα, hα1, hballs, hu.mono hsub, hcf, C, ?_⟩
  have hformula (x : E2) (hx : x ∈ K) :
      fderivWithin ℝ (fun x => f (g0 x)) K x =
        (fderiv ℝ f (g0 x)).comp (fderivWithin ℝ g0 K x) :=
    fderiv_comp_fderivWithin x
      ((hf.contDiffAt (hsolution.jet_domain_open.mem_nhds (hTJ (hmap hx)))).differentiableAt (by simp))
      (hgs.differentiableOn (by norm_num) x hx) (hKD x hx)
  intro x hx y hy
  change edist (fderivWithin ℝ (fun x => f (g0 x)) K x)
      (fderivWithin ℝ (fun x => f (g0 x)) K y) ≤ _
  rw [hformula x hx, hformula y hy]
  exact hC x hx y hy

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
