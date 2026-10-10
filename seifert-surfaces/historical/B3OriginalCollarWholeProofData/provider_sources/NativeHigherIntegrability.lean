import NativeStopping

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak
open SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.L1Independent
set_option autoImplicit false
set_option maxHeartbeats 0

private theorem native_components_from_density
    {δ : ℝ} (hδ : 0 < δ) (U : Set E2) (d : Fin 2 → E2 → E2)
    (hdm : ∀ i, AEStronglyMeasurable (d i) (volume.restrict U))
    (hdens : MemLp (fun x => (Real.sqrt (euclideanJetDensity d x)) ^ (4 / (3 : ℝ)))
      (ENNReal.ofReal ((3 / (2 : ℝ)) + δ)) (volume.restrict U)) :
    ∀ i : Fin 2, MemLp (d i)
      (ENNReal.ofReal (2 + (4 / (3 : ℝ)) * δ)) (volume.restrict U) := by
  have hp := hdens.norm_rpow_div (ENNReal.ofReal (3 / (4 : ℝ)))
  have hpe : ENNReal.ofReal ((3 / (2 : ℝ)) + δ) / ENNReal.ofReal (3 / (4 : ℝ)) =
      ENNReal.ofReal (2 + (4 / (3 : ℝ)) * δ) := by
    rw [← ENNReal.ofReal_div_of_pos (by norm_num)]
    congr 1
    ring
  rw [hpe] at hp
  have hg : MemLp (fun x => Real.sqrt (euclideanJetDensity d x))
      (ENNReal.ofReal (2 + (4 / 3 : ℝ) * δ)) (volume.restrict U) := by
    apply (memLp_congr_ae ?_).mp hp
    filter_upwards with x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _),
      ← Real.rpow_mul (Real.sqrt_nonneg _)]
    norm_num
  intro i
  apply MemLp.of_le hg (hdm i)
  filter_upwards with x
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖d j x‖) (Finset.mem_univ i)

private theorem native_reverse_holder_from_caccioppoli
    (u : E2 → E2) (e h : E2 → ℝ) (C S : ℝ)
    (hC : 0 ≤ C) (hS : 0 ≤ S)
    (hshape : ∀ x, h x ^ (3 / (2 : ℝ)) = e x)
    (hcacc : ∀ (x : E2) (r : ℝ), 0 < r → Metric.closedBall x (2 * r) ⊆ disc 1 →
      (∫ y in Metric.ball x r, e y) ≤ C / r ^ 2 *
        ∫ y in Metric.ball x (2 * r), ‖u y - ⨍ z in Metric.ball x (2 * r), u z‖ ^ 2)
    (hosc : ∀ (x : E2) (r : ℝ), 0 < r → Metric.closedBall x r ⊆ disc 1 →
      (∫ y in Metric.ball x r, ‖u y - ⨍ z in Metric.ball x r, u z‖ ^ 2) ≤
        S * r * (∫ y in Metric.ball x r, h y) ^ (3 / (2 : ℝ))) :
    ∀ (x : E2) (r : ℝ), 0 < r → Metric.closedBall x (2 * r) ⊆ disc 1 →
      (∫ y in Metric.ball x r, h y ^ (3 / (2 : ℝ))) ≤
        (2 * C * S) / r * (∫ y in Metric.ball x (2 * r), h y) ^ (3 / (2 : ℝ)) := by
  intro x r hr hinside
  have hosc' := hosc x (2 * r) (by positivity) hinside
  have hc := hcacc x r hr hinside
  have hshape' : (∫ y in Metric.ball x r, h y ^ (3 / (2 : ℝ))) =
      ∫ y in Metric.ball x r, e y := by
    apply integral_congr_ae
    filter_upwards with y
    exact hshape y
  rw [hshape']
  calc
    _ ≤ C / r ^ 2 * ∫ y in Metric.ball x (2 * r), ‖u y - ⨍ z in Metric.ball x (2 * r), u z‖ ^ 2 := hc
    _ ≤ C / r ^ 2 * (S * (2 * r) *
        (∫ y in Metric.ball x (2 * r), h y) ^ (3 / (2 : ℝ))) := by
      gcongr
    _ = (2 * C * S) / r * (∫ y in Metric.ball x (2 * r), h y) ^ (3 / (2 : ℝ)) := by
      field_simp

private theorem native_H1_restrict_ball (a : E2) (r : ℝ)
    (hsub : Metric.ball a r ⊆ disc 1) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (disc 1) u du) : H1On (Metric.ball a r) u du := by
  have hup := hu.2.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdup := hu.2.2.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨⟨hu.1.1.mono_set hsub, hu.1.2.1.mono_set hsub, ?_⟩, hup, hdup⟩
  intro phi hp hc hs i
  have he1 : (∫ x in disc 1, u x * fderiv ℝ phi x (coordinateVector 2 i)) =
      ∫ x in Metric.ball a r, u x * fderiv ℝ phi x (coordinateVector 2 i) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
    intro x hx
    have hxn : x ∉ tsupport phi := fun h => hx.2 (hs h)
    rw [fderiv_of_notMem_tsupport ℝ hxn]
    simp
  have he2 : (∫ x in disc 1, du x i * phi x) =
      ∫ x in Metric.ball a r, du x i * phi x := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet hsub
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx.2 (hs h)), mul_zero]
  rw [← he1, ← he2]
  exact hu.1.2.2 phi hp hc (hs.trans hsub) i

private theorem native_density_initial
    (d : Fin 2 → E2 → E2) (hd : ∀ i, MemLp (d i) 2 (volume.restrict (disc 1))) :
    Integrable ((disc 1).indicator (fun x => Real.sqrt (euclideanJetDensity d x) ^ (4 / (3 : ℝ)))) ∧
    Integrable (fun x => ((disc 1).indicator (fun x => Real.sqrt (euclideanJetDensity d x) ^ (4 / (3 : ℝ))) x) ^ (3 / (2 : ℝ))) := by
  have hg : MemLp (fun x => Real.sqrt (euclideanJetDensity d x)) 2 (volume.restrict (disc 1)) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeSubcriticalSobolev 0) ++
        `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.native_jet_density_sqrt_memLp
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn) 0 1 $(Lean.mkIdent `d) $(Lean.mkIdent `hd)))
  letI : IsFiniteMeasure (volume.restrict (disc 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hgq : MemLp (fun x => Real.sqrt (euclideanJetDensity d x))
      (ENNReal.ofReal (4 / (3 : ℝ))) (volume.restrict (disc 1)) := hg.mono_exponent (by norm_num)
  have hqi : IntegrableOn (fun x => Real.sqrt (euclideanJetDensity d x) ^ (4 / (3 : ℝ))) (disc 1) := by
    have hqi' := hgq.integrable_norm_rpow (by norm_num) ENNReal.ofReal_ne_top
    simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3),
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hqi'
    exact hqi' 
  have he : IntegrableOn (euclideanJetDensity d) (disc 1) :=
    integrable_finsetSum _ (fun i _ => (hd i).norm.integrable_sq)
  refine ⟨hqi.integrable_indicator Metric.isOpen_ball.measurableSet, ?_⟩
  convert he.integrable_indicator Metric.isOpen_ball.measurableSet using 1
  ext x
  by_cases hx : x ∈ disc 1
  · simp only [indicator_of_mem hx]
    rw [← Real.rpow_mul (Real.sqrt_nonneg _)]
    norm_num
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖d i x‖))
  · simp only [indicator_of_notMem hx, Real.zero_rpow (by norm_num : (3 / (2 : ℝ)) ≠ 0)]

private theorem native_higher_integrability_from_caccioppoli
    (u : E2 → E2) (d : Fin 2 → E2 → E2)
    (hH1 : ∀ i, H1On (disc 1) (fun x => u x i) (d i))
    (C : ℝ) (hC : 0 ≤ C)
    (hcacc : ∀ (a : E2) (r : ℝ), 0 < r → Metric.closedBall a (2 * r) ⊆ disc 1 →
      ∀ c : E2, (∫ x in Metric.ball a r, euclideanJetDensity d x) ≤
        C / r ^ 2 * ∫ x in Metric.ball a (2 * r), ‖u x - c‖ ^ 2) :
    ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 →
      ∀ i, MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t)) := by
  classical
  let g : E2 → ℝ := fun x => Real.sqrt (euclideanJetDensity d x) ^ (4 / (3 : ℝ))
  let h0 : E2 → ℝ := (disc 1).indicator g
  have hgn (x : E2) : 0 ≤ g x := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have h0n (x : E2) : 0 ≤ h0 x := indicator_nonneg (fun y _ => hgn y) x
  obtain ⟨hi0, hs0⟩ := native_density_initial d (fun i => (hH1 i).2.2)
  change Integrable h0 at hi0
  change Integrable (fun x => h0 x ^ (3 / (2 : ℝ))) at hs0
  let h : E2 → ℝ := fun x => max (hi0.aestronglyMeasurable.mk h0 x) 0
  have hm : Measurable h := hi0.aestronglyMeasurable.measurable_mk.max measurable_const
  have hn (x : E2) : 0 ≤ h x := le_max_right _ _
  have heq : h =ᵐ[volume] h0 := by
    filter_upwards [hi0.aestronglyMeasurable.ae_eq_mk] with x hx
    dsimp only [h]
    rw [← hx, max_eq_left (h0n x)]
  have hi : Integrable h := hi0.congr heq.symm
  have hs : Integrable (fun x => h x ^ (3 / (2 : ℝ))) := by
    apply hs0.congr
    filter_upwards [heq] with x hx
    rw [hx]
  have hball (a : E2) (r : ℝ) (hsub : Metric.ball a r ⊆ disc 1) :
      h =ᵐ[volume.restrict (Metric.ball a r)] g := by
    filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
    exact hx.trans (indicator_of_mem (hsub hxB) g)
  have hshape (x : E2) : g x ^ (3 / (2 : ℝ)) = euclideanJetDensity d x := by
    dsimp only [g]
    rw [← Real.rpow_mul (Real.sqrt_nonneg _)]
    norm_num
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖d i x‖))
  have hSob : ∃ S : ℝ, 0 < S ∧ ∀ (a : E2) (r : ℝ), 0 < r →
      ∀ (u : E2 → E2) (d : Fin 2 → E2 → E2),
      (∀ i, H1On (Metric.ball a r) (fun x => u x i) (d i)) →
      (∫ x in Metric.ball a r, ‖u x - ⨍ y in Metric.ball a r, u y ∂volume‖ ^ 2) ≤
        S * r * (∫ x in Metric.ball a r,
          (Real.sqrt (euclideanJetDensity d x)) ^ (4 / (3 : ℝ))) ^ (3 / (2 : ℝ)) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeSubcriticalSobolev 0) ++
        `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.DirectWeak.native_subcritical_ball_integral
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn)))
  obtain ⟨S, hS, hSob⟩ := hSob
  have hraw := native_reverse_holder_from_caccioppoli u (euclideanJetDensity d) g C S hC hS.le hshape
    (fun a r hr hb => hcacc a r hr hb (⨍ z in Metric.ball a (2 * r), u z))
    (fun a r hr hb => hSob a r hr u d (fun i =>
      native_H1_restrict_ball a r (Metric.ball_subset_closedBall.trans hb)
        (fun x => u x i) (d i) (hH1 i)))
  have hrev : ∀ (a : E2) (r : ℝ), 0 < r → Metric.closedBall a (2 * r) ⊆ disc 1 →
      (∫ x in Metric.ball a r, h x ^ (3 / (2 : ℝ))) ≤
        (2 * C * S) / r * (∫ x in Metric.ball a (2 * r), h x) ^ (3 / (2 : ℝ)) := by
    intro a r hr hb
    have hb2 := Metric.ball_subset_closedBall.trans hb
    have hb1 := (Metric.ball_subset_ball (by linarith : r ≤ 2 * r)).trans hb2
    have hpw : (fun x => h x ^ (3 / (2 : ℝ))) =ᵐ[volume.restrict (Metric.ball a r)]
        (fun x => g x ^ (3 / (2 : ℝ))) := by
      filter_upwards [hball a r hb1] with x hx
      rw [hx]
    rw [integral_congr_ae hpw, integral_congr_ae (hball a (2 * r) hb2)]
    exact hraw a r hr hb
  have hGehring : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ t : ℝ, 0 < t → t < 1 →
      MemLp h (ENNReal.ofReal ((3 / (2 : ℝ)) + δ)) (volume.restrict (disc t)) := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeStopping 0).str "gehring_local_reverse_holder"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn)
        $(Lean.mkIdent `h) $(Lean.mkIdent `hm) $(Lean.mkIdent `hn) $(Lean.mkIdent `hi) $(Lean.mkIdent `hs)
        (2 * $(Lean.mkIdent `C) * $(Lean.mkIdent `S)) (by positivity) $(Lean.mkIdent `hrev)))
  obtain ⟨δ, hδ, _, hGehring⟩ := hGehring
  refine ⟨2 + (4 / (3 : ℝ)) * δ, by linarith, ?_⟩
  intro t ht ht1
  have hsub : disc t ⊆ disc 1 := Metric.ball_subset_ball ht1.le
  have hg : MemLp g (ENNReal.ofReal ((3 / (2 : ℝ)) + δ)) (volume.restrict (disc t)) :=
    (memLp_congr_ae (hball 0 t hsub)).mp (hGehring t ht ht1)
  exact native_components_from_density hδ (disc t) d
    (fun i => (hH1 i).2.2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)) hg

private theorem native_original_higher_integrability
    (R : ℝ) (A : E2 → Mat2) (G : InverseMetricData R A)
    (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
    (f : E2 → E2) (d : Fin 2 → E2 → E2)
    (minimum : SimultaneousMetricMinimum Ω M f d)
    (theta : ℝ → ℝ) (sigma : ℝ) (beta : ℝ≥0)
    (P : SameHolderRepresentative Ω f d theta sigma beta) :
    ∃ p : ℝ, 2 < p ∧ ∀ t : ℝ, 0 < t → t < 1 →
      ∀ i, MemLp (d i) (ENNReal.ofReal p) (volume.restrict (disc t)) := by
  have hcacc : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : E2) (r : ℝ), 0 < r →
      Metric.closedBall a (2 * r) ⊆ disc 1 → ∀ c : E2,
      (∫ z in Metric.ball a r, euclideanJetDensity d z) ≤
        C / r ^ 2 * ∫ z in Metric.ball a (2 * r), ‖P.u z - c‖ ^ 2 := by
    run_tac do
      let pn := (Lean.Name.num `_private.NativeOriginalCaccioppoli 0).str "native_original_Caccioppoli"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $(Lean.mkIdent pn)
        $(Lean.mkIdent `R) $(Lean.mkIdent `A) $(Lean.mkIdent `G) $(Lean.mkIdent `Ω) $(Lean.mkIdent `M) $(Lean.mkIdent `agreement) $(Lean.mkIdent `symmetric) $(Lean.mkIdent `elliptic) $(Lean.mkIdent `holder) $(Lean.mkIdent `identity_at_infinity) $(Lean.mkIdent `f) $(Lean.mkIdent `d) $(Lean.mkIdent `minimum) $(Lean.mkIdent `theta) $(Lean.mkIdent `sigma) $(Lean.mkIdent `beta) $(Lean.mkIdent `P)))
  obtain ⟨C, hC, hcacc⟩ := hcacc
  exact native_higher_integrability_from_caccioppoli P.u d P.same_H1 C hC hcacc
