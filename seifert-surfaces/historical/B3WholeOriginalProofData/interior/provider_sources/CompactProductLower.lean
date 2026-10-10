import InteriorPotentialData

noncomputable section
set_option autoImplicit false
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
open SeifertSurfaces.AppendixACoordinates

/-- F1a: the native compact product is its own zero extension from the unit ball,
with the stated weak gradient. Only the supplied native H¹ witness is assumed.
Source: Morrey, physical p.154, the compact product preceding (5.5.18), specialized
to the native scalar, two-dimensional divergence-form context. -/
theorem compact_product_H1_zero_extension
    (w : E2 → ℝ) (dv : E2 → E2)
    (hw : H1On (Metric.ball (0 : E2) 1) w dv)
    (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hs : tsupport chi ⊆ Metric.ball (0 : E2) 1) :
    let U := localizedScalar chi w
    let dU := localizedGradient chi w dv
    (∀ z ∉ tsupport chi, chi z = 0 ∧ planarGradient chi z = 0) ∧
    U = (Metric.ball (0 : E2) 1).indicator U ∧
    dU = (Metric.ball (0 : E2) 1).indicator dU ∧
    H1On Set.univ U dU ∧
    Integrable U volume ∧ Integrable dU volume ∧
    HasCompactSupport U ∧ HasCompactSupport dU ∧
    tsupport U ⊆ tsupport chi ∧ tsupport dU ⊆ tsupport chi := by
  run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  classical\n  let B := Metric.ball (0 : E2) 1\n  let μ := volume.restrict B\n  let U := localizedScalar chi w\n  let dU := localizedGradient chi w dv\n  have hzero (z : E2) (hz : z ∉ tsupport chi) :\n      chi z = 0 ∧ planarGradient chi z = 0 :=\n    ⟨image_eq_zero_of_notMem_tsupport hz, planarGradient_eq_zero_off_support chi hz⟩\n  have hgsub : tsupport (planarGradient chi) ⊆ tsupport chi := by\n    apply closure_minimal _ (isClosed_tsupport chi)\n    intro z hz\n    by_contra h\n    exact hz ((hzero z h).2)\n  have hgcompact : HasCompactSupport (planarGradient chi) :=\n    hc.of_isClosed_subset (isClosed_tsupport _) hgsub\n  have hgcont : Continuous (planarGradient chi) := continuous_planarGradient hchi\n  have hUs : tsupport U ⊆ tsupport chi := tsupport_mul_subset_left\n  have hdUs : tsupport dU ⊆ tsupport chi := by\n    apply closure_minimal _ (isClosed_tsupport chi)\n    intro z hz\n    by_contra h\n    apply hz\n    change chi z • dv z + w z • planarGradient chi z = 0\n    rw [(hzero z h).1, (hzero z h).2, zero_smul, smul_zero, zero_add]\n  have hUc : HasCompactSupport U := hc.of_isClosed_subset (isClosed_tsupport _) hUs\n  have hdUc : HasCompactSupport dU := hc.of_isClosed_subset (isClosed_tsupport _) hdUs\n  have hUi : U = B.indicator U :=\n    (Set.indicator_eq_self.mpr ((subset_tsupport U).trans (hUs.trans hs))).symm\n  have hdUi : dU = B.indicator dU :=\n    (Set.indicator_eq_self.mpr ((subset_tsupport dU).trans (hdUs.trans hs))).symm\n  have hcLp : MemLp chi ∞ μ :=\n    (hchi.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict B\n  have hgLp : MemLp (planarGradient chi) ∞ μ :=\n    (hgcont.memLp_of_hasCompactSupport (μ := volume) hgcompact).restrict B\n  have hULp : MemLp U 2 μ := hcLp.mul hw.2.1\n  have hdULp : MemLp dU 2 μ := (hcLp.smul hw.2.2).add (hw.2.1.smul hgLp)\n  have hULpall : MemLp U 2 volume := by\n    have hh := (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hULp\n    rw [← hUi] at hh\n    exact hh\n  have hdULpall : MemLp dU 2 volume := by\n    have hh := (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hdULp\n    rw [← hdUi] at hh\n    exact hh\n  let _ : IsFiniteMeasure μ :=\n    isFiniteMeasure_restrict.mpr (measure_ball_lt_top (μ := volume) (x := (0 : E2)) (r := 1)).ne\n  have hUint : Integrable U volume :=\n    IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) (hULp.integrable (by norm_num)) fun z hz =>\n      image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hUs ht)))\n  have hdUint : Integrable dU volume :=\n    IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) (hdULp.integrable (by norm_num)) fun z hz =>\n      image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hdUs ht)))\n  have hcoord (phi : E2 → ℝ) (z : E2) (i : Fin 2) :\n      planarGradient phi z i = fderiv ℝ phi z (coordinateVector 2 i) := by\n    fin_cases i <;> simp only [planarGradient, Fin.sum_univ_two, coordinateVector,\n      PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]\n    all_goals norm_num\n  have hweak : WeakGradientOn Set.univ U dU := by\n    refine ⟨hUint.locallyIntegrable.locallyIntegrableOn _,\n      hdUint.locallyIntegrable.locallyIntegrableOn _, ?_⟩\n    intro phi hp hpc hps i\n    have htest : ContDiff ℝ ∞ (chi * phi) := hchi.mul hp\n    have htestc : HasCompactSupport (chi * phi) := hc.mul_right\n    have htests : tsupport (chi * phi) ⊆ B := tsupport_mul_subset_left.trans hs\n    have hi := hw.1.2.2 (chi * phi) htest htestc htests i\n    have hDphi : MemLp (fun z => fderiv ℝ phi z (coordinateVector 2 i)) 2 μ :=\n      (((hp.continuous_fderiv (by decide)).clm_apply continuous_const).memLp_of_hasCompactSupport\n        (μ := volume) (hpc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))).restrict B\n    have hterm1 : Integrable (fun z => U z * fderiv ℝ phi z (coordinateVector 2 i)) μ :=\n      hULp.integrable_mul hDphi\n    have hDchi : MemLp (fun z => fderiv ℝ chi z (coordinateVector 2 i)) ∞ μ :=\n      (((hchi.continuous_fderiv (by decide)).clm_apply continuous_const).memLp_of_hasCompactSupport\n        (μ := volume) (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i))).restrict B\n    have hphiLp : MemLp phi 2 μ :=\n      (hp.continuous.memLp_of_hasCompactSupport (μ := volume) hpc).restrict B\n    have hwDchi : MemLp (fun z => w z * fderiv ℝ chi z (coordinateVector 2 i)) 2 μ :=\n      hw.2.1.mul hDchi\n    have hterm2 : Integrable (fun z => (w z * fderiv ℝ chi z (coordinateVector 2 i)) * phi z) μ :=\n      hwDchi.integrable_mul hphiLp\n    have hchidv : MemLp (fun z => chi z * dv z i) 2 μ :=\n      hcLp.mul (hw.2.2.eval_piLp i)\n    have hterm3 : Integrable (fun z => (chi z * dv z i) * phi z) μ :=\n      hchidv.integrable_mul hphiLp\n    have htestder (z : E2) :\n        w z * fderiv ℝ (chi * phi) z (coordinateVector 2 i) =\n          U z * fderiv ℝ phi z (coordinateVector 2 i) +\n            (w z * fderiv ℝ chi z (coordinateVector 2 i)) * phi z := by\n      rw [fderiv_mul (hchi.differentiable (by decide) z) (hp.differentiable (by decide) z)]\n      change w z * (chi z * fderiv ℝ phi z (coordinateVector 2 i) +\n        phi z * fderiv ℝ chi z (coordinateVector 2 i)) = _\n      change _ = (chi z * w z) * fderiv ℝ phi z (coordinateVector 2 i) + _\n      ring\n    have htestval (z : E2) : dv z i * (chi * phi) z = (chi z * dv z i) * phi z := by\n      change dv z i * (chi z * phi z) = _\n      ring\n    simp_rw [htestder, htestval] at hi\n    rw [integral_add hterm1 hterm2] at hi\n    have hgradval (z : E2) : dU z i * phi z =\n        (chi z * dv z i) * phi z +\n          (w z * fderiv ℝ chi z (coordinateVector 2 i)) * phi z := by\n      change (chi z • dv z + w z • planarGradient chi z) i * phi z = _\n      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, hcoord]\n      change (chi z * dv z i + w z * fderiv ℝ chi z (coordinateVector 2 i)) * phi z = _\n      ring\n    rw [Measure.restrict_univ]\n    have hleft : (∫ z, U z * fderiv ℝ phi z (coordinateVector 2 i)) =\n        ∫ z in B, U z * fderiv ℝ phi z (coordinateVector 2 i) :=\n      (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by\n        rw [show U z = 0 from image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hUs ht))), zero_mul]).symm\n    have hright : (∫ z, dU z i * phi z) = ∫ z in B, dU z i * phi z :=\n      (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by\n        rw [show dU z = 0 from image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hdUs ht)))]\n        change (0 : ℝ) * phi z = 0\n        exact zero_mul _).symm\n    rw [hleft, hright]\n    simp_rw [hgradval]\n    rw [integral_add hterm3 hterm2]\n    linarith\n  refine ⟨hzero, hUi, hdUi, ?_, hUint, hdUint, hUc, hdUc, hUs, hdUs⟩\n  exact ⟨hweak, by simpa only [Measure.restrict_univ] using hULpall,\n    by simpa only [Measure.restrict_univ] using hdULpall⟩\n)"))

/-- F1a: applying the original weak equation to the compact product gives the
whole-space equation with both native forcing terms and scalar mean cancellation.
The scalar is the original native mean subtraction. The coefficient outside
the compact support is arbitrary; it agrees with the original coefficient on
the support. Source: Morrey (5.5.18), adapted only to the native sign convention
`∫ N·dv·Dpsi = ∫ F·Dpsi`, and the original scalar forcing zero. -/
theorem normalized_compact_forced_equation
    (alpha : ℝ≥0) (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (lam Lambda : ℝ) (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (HN : ℝ≥0) (d : InteriorData alpha lam Lambda HN)
    (chi : E2 → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hc : HasCompactSupport chi) (hs : tsupport chi ⊆ Metric.ball (0 : E2) 1)
    (Ntilde : E2 → Mat2) (hN : ∀ z ∈ tsupport chi, Ntilde z = d.N z) :
    let w := normalizedScalar d
    let U := localizedScalar chi w
    let dU := localizedGradient chi w d.dv
    let E := localizedVectorData d.N d.F chi w
    let f0 := localizedScalarData d.N d.F d.dv chi
    DirectWeak.WeakDivergenceWithData Set.univ Ntilde E f0 U dU ∧
    MemLp E 2 volume ∧ MemLp f0 2 volume ∧
    Integrable E volume ∧ Integrable f0 volume ∧
    HasCompactSupport E ∧ HasCompactSupport f0 ∧
    tsupport E ⊆ tsupport chi ∧ tsupport f0 ⊆ tsupport chi ∧
    (∫ z, f0 z) = 0 := by
  classical
  let B := Metric.ball (0 : E2) 1
  let μ := volume.restrict B
  let c := ⨍ z in B, d.v z
  let w := normalizedScalar d
  let U := localizedScalar chi w
  let dU := localizedGradient chi w d.dv
  let E := localizedVectorData d.N d.F chi w
  let f0 := localizedScalarData d.N d.F d.dv chi
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hw : H1On B (normalizedScalar d) d.dv := by
    refine ⟨⟨d.weak.1.1.1.sub (continuous_const.locallyIntegrable.locallyIntegrableOn B),
      d.weak.1.1.2.1, ?_⟩,
      d.weak.1.2.1.sub (memLp_const c), d.weak.1.2.2⟩
    intro phi hp hk hsphi i
    let e := coordinateVector 2 i
    have hdc : Continuous (fun z => fderiv ℝ phi z e) :=
      (hp.continuous_fderiv (by decide)).clm_apply continuous_const
    have hdk : HasCompactSupport (fun z => fderiv ℝ phi z e) := hk.fderiv_apply ℝ e
    have hdi : Integrable (fun z => fderiv ℝ phi z e) := hdc.integrable_of_hasCompactSupport hdk
    have hpint : Integrable phi := hp.continuous.integrable_of_hasCompactSupport hk
    have hdint : (∫ z in B, fderiv ℝ phi z e) = 0 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
        rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hsphi h)), zero_apply])]
      have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (f := fun _ : E2 => (1 : ℝ)) (g := phi) (v := e)
        (by simpa only [fderiv_const_apply, zero_apply, zero_mul] using
          (integrable_zero E2 ℝ volume : Integrable (fun _ : E2 => (0 : ℝ))))
        (by simpa only [one_mul] using hdi)
        (by simpa only [one_mul] using hpint)
        (fun _ _ => differentiableAt_const _) (fun z _ => hp.differentiable (by decide) z)
      simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero] using hi
    have hvint : IntegrableOn d.v B := d.weak.1.2.1.integrable (by norm_num)
    have hvd : IntegrableOn (fun z => d.v z * fderiv ℝ phi z e) B :=
      hvint.mul_continuousOn_of_subset hdc.continuousOn measurableSet_ball
        (isCompact_closedBall (0 : E2) 1) Metric.ball_subset_closedBall
    have hcd : IntegrableOn (fun z => c * fderiv ℝ phi z e) B := hdi.integrableOn.const_mul c
    change (∫ z in B, (d.v z - c) * fderiv ℝ phi z e) = _
    simp_rw [sub_mul]
    rw [integral_sub hvd hcd, integral_const_mul, hdint, mul_zero, sub_zero]
    exact d.weak.1.1.2.2 phi hp hk hsphi i
  obtain ⟨hzero, hUi, hdUi, hH1, hUint, hdUint, hUc, hdUc, hUs, hdUs⟩ :=
    compact_product_H1_zero_extension w d.dv hw chi hchi hc hs
  have maadd (a : Mat2) (v v' : E2) : matrixAction a (v + v') = matrixAction a v + matrixAction a v' := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    change (∑ j, a i j * (v j + v' j)) = (∑ j, a i j * v j) + ∑ j, a i j * v' j
    simp only [mul_add, Finset.sum_add_distrib]
  have masmul (a : Mat2) (s : ℝ) (v : E2) : matrixAction a (s • v) = s • matrixAction a v := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    ext i
    change (∑ j, a i j * (s * v j)) = s * ∑ j, a i j * v j
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have mazero (a : Mat2) : matrixAction a 0 = 0 := by
    simpa only [zero_smul] using masmul a 0 (0 : E2)
  have hn (i j : Fin 2) : AEStronglyMeasurable (fun z => d.N z i j) μ :=
    ((d.holder_N i j).continuousOn halpha).aestronglyMeasurable measurableSet_ball
  have mapped (g : E2 → E2) (hg : AEStronglyMeasurable g μ) :
      AEStronglyMeasurable (fun z => matrixAction (d.N z) (g z)) μ := by
    have hm (i : Fin 2) : AEStronglyMeasurable (fun z => ∑ j, d.N z i j * g z j) μ :=
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
        (hn i j).mul ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) j).comp_aestronglyMeasurable hg)
    have hp : AEMeasurable (fun z => fun i : Fin 2 => ∑ j, d.N z i j * g z j) μ :=
      AEMeasurable.of_eval fun i => (hm i).aemeasurable
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp_aemeasurable hp).aestronglyMeasurable
  have mapLp (g : E2 → E2) (p : ℝ≥0∞) (hg : MemLp g p μ) :
      MemLp (fun z => matrixAction (d.N z) (g z)) p μ := by
    apply hg.of_le_mul (mapped g hg.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact (d.elliptic_bound z hz (g z)).2
  have hint (g h : E2 → E2) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
      Integrable (fun z => inner ℝ (g z) (h z)) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hg.toLp g) (hh.toLp h)).congr
    filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with z hz hz'
    rw [hz, hz']
  have hgradsub (phi : E2 → ℝ) : tsupport (planarGradient phi) ⊆ tsupport phi := by
    apply closure_minimal _ (isClosed_tsupport phi)
    intro z hz
    by_contra h
    exact hz (planarGradient_eq_zero_off_support phi h)
  have hgcont := continuous_planarGradient hchi
  have hgc : HasCompactSupport (planarGradient chi) := hc.of_isClosed_subset (isClosed_tsupport _) (hgradsub chi)
  have hchiLp : MemLp chi ∞ μ := (hchi.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict B
  have hgradLp : MemLp (planarGradient chi) ∞ μ := (hgcont.memLp_of_hasCompactSupport (μ := volume) hgc).restrict B
  have hgradLp2 : MemLp (planarGradient chi) 2 μ := (hgcont.memLp_of_hasCompactSupport (μ := volume) hgc).restrict B
  have hF : MemLp d.F 2 μ := by
    apply MemLp.of_bound ((d.holder_F.continuousOn halpha).aestronglyMeasurable measurableSet_ball) d.BF
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact d.bounded_F z hz
  have hflux : MemLp (fun z => matrixAction (d.N z) (d.dv z)) 2 μ := mapLp d.dv 2 d.weak.1.2.2
  have hNg : MemLp (fun z => matrixAction (d.N z) (planarGradient chi z)) ∞ μ :=
    mapLp (planarGradient chi) ∞ hgradLp
  have hwLp : MemLp w 2 μ := hw.2.1
  have hELp : MemLp E 2 μ := (hchiLp.smul hF).add (hwLp.smul hNg)
  obtain ⟨Cgrad, hCgrad⟩ := hgcont.bounded_above_of_compact_support hgc
  have hip (g : E2 → E2) (hg : MemLp g 2 μ) :
      MemLp (fun z => inner ℝ (g z) (planarGradient chi z)) 2 μ := by
    apply hg.of_le_mul (hg.aestronglyMeasurable.inner hgcont.aestronglyMeasurable.restrict)
    filter_upwards with z
    calc
      ‖inner ℝ (g z) (planarGradient chi z)‖ ≤ ‖g z‖ * ‖planarGradient chi z‖ := norm_inner_le_norm _ _
      _ ≤ ‖g z‖ * Cgrad := mul_le_mul_of_nonneg_left (hCgrad z) (norm_nonneg _)
      _ = Cgrad * ‖g z‖ := mul_comm _ _
  have hfLp : MemLp f0 2 μ := hip (fun z => d.F z - matrixAction (d.N z) (d.dv z)) (hF.sub hflux)
  have hEzero (z : E2) (hz : z ∉ tsupport chi) : E z = 0 := by
    change chi z • d.F z + w z • matrixAction (d.N z) (planarGradient chi z) = 0
    rw [(hzero z hz).1, (hzero z hz).2, mazero, zero_smul, smul_zero, zero_add]
  have hfzero (z : E2) (hz : z ∉ tsupport chi) : f0 z = 0 := by
    change inner ℝ (d.F z - matrixAction (d.N z) (d.dv z)) (planarGradient chi z) = 0
    rw [(hzero z hz).2, inner_zero_right]
  have hEs : tsupport E ⊆ tsupport chi := by
    apply closure_minimal _ (isClosed_tsupport chi)
    intro z hz
    by_contra h
    exact hz (hEzero z h)
  have hfs : tsupport f0 ⊆ tsupport chi := by
    apply closure_minimal _ (isClosed_tsupport chi)
    intro z hz
    by_contra h
    exact hz (hfzero z h)
  have hEi : B.indicator E = E := Set.indicator_eq_self.mpr ((subset_tsupport E).trans (hEs.trans hs))
  have hfi : B.indicator f0 = f0 := Set.indicator_eq_self.mpr ((subset_tsupport f0).trans (hfs.trans hs))
  have hEall : MemLp E 2 volume := by
    have h := (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hELp
    rw [hEi] at h
    exact h
  have hfall : MemLp f0 2 volume := by
    have h := (memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet).mpr hfLp
    rw [hfi] at h
    exact h
  have hEint : Integrable E volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) (hELp.integrable (by norm_num))
      fun z hz => hEzero z (fun ht => hz (hs ht))
  have hfint : Integrable f0 volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) (hfLp.integrable (by norm_num))
      fun z hz => hfzero z (fun ht => hz (hs ht))
  have hNt (z : E2) : matrixAction (Ntilde z) (dU z) = matrixAction (d.N z) (dU z) := by
    by_cases hz : z ∈ tsupport chi
    · rw [hN z hz]
    · have hu0 : dU z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hdUs ht))
      rw [hu0, mazero, mazero]
  have hDUall : MemLp dU 2 volume := by simpa only [Measure.restrict_univ] using hH1.2.2
  have hDUflux : MemLp (fun z => matrixAction (Ntilde z) (dU z)) 2 μ := by
    apply (mapLp dU 2 (hDUall.restrict B)).ae_eq
    exact Filter.Eventually.of_forall fun z => (hNt z).symm
  have hcoord (phi : E2 → ℝ) (z : E2) (i : Fin 2) :
      planarGradient phi z i = fderiv ℝ phi z (coordinateVector 2 i) := by
    fin_cases i <;> simp only [planarGradient, Fin.sum_univ_two, coordinateVector,
      PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply]
    all_goals norm_num
  have hprod (psi : E2 → ℝ) (hp : ContDiff ℝ ∞ psi) (z : E2) :
      planarGradient (chi * psi) z = chi z • planarGradient psi z + psi z • planarGradient chi z := by
    ext i
    rw [hcoord, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, hcoord, hcoord]
    rw [fderiv_mul (hchi.differentiable (by decide) z) (hp.differentiable (by decide) z)]
    rfl
  have hweak : DirectWeak.WeakDivergenceWithData Set.univ Ntilde E f0 U dU := by
    refine ⟨hH1, ?_⟩
    intro psi hp hpc hps
    have hpsiLp : MemLp psi 2 μ := (hp.continuous.memLp_of_hasCompactSupport (μ := volume) hpc).restrict B
    have hpsiTop : MemLp psi ∞ μ := (hp.continuous.memLp_of_hasCompactSupport (μ := volume) hpc).restrict B
    have hgpsi : MemLp (planarGradient psi) 2 μ :=
      ((continuous_planarGradient hp).memLp_of_hasCompactSupport (μ := volume)
        (hpc.of_isClosed_subset (isClosed_tsupport _) (hgradsub psi))).restrict B
    have hli : Integrable (fun z => inner ℝ (matrixAction (Ntilde z) (dU z)) (planarGradient psi z)) μ :=
      hint _ _ hDUflux hgpsi
    have hri : Integrable (fun z => inner ℝ (E z) (planarGradient psi z) + f0 z * psi z) μ :=
      (hint _ _ hELp hgpsi).add (hfLp.integrable_mul hpsiLp)
    have hlzero (z : E2) (hz : z ∉ B) : inner ℝ (matrixAction (Ntilde z) (dU z)) (planarGradient psi z) = 0 := by
      have hu0 : dU z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hz (hs (hdUs ht)))
      rw [hu0, mazero, inner_zero_left]
    have hrzero (z : E2) (hz : z ∉ B) : inner ℝ (E z) (planarGradient psi z) + f0 z * psi z = 0 := by
      rw [hEzero z (fun ht => hz (hs ht)), hfzero z (fun ht => hz (hs ht)), inner_zero_left, zero_mul, zero_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [IntegrableOn, Measure.restrict_univ]
      exact IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) hli hlzero
    · rw [IntegrableOn, Measure.restrict_univ]
      exact IntegrableOn.integrable_of_forall_notMem_eq_zero (s := B) hri hrzero
    · rw [Measure.restrict_univ,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero hlzero,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero hrzero]
      have hweight (s : E2 → ℝ) (g h : E2 → E2) (hsLp : MemLp s ∞ μ)
          (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
          Integrable (fun z => s z * inner ℝ (g z) (h z)) μ := by
        apply (hint (fun z => s z • g z) h (hsLp.smul hg) hh).congr
        exact Filter.Eventually.of_forall fun z => by
          dsimp only
          rw [inner_smul_left]
          rfl
      have hA := hweight chi _ _ hchiLp hflux hgpsi
      have hB := hweight psi _ _ hpsiTop hflux hgradLp2
      have hC := hweight chi _ _ hchiLp hF hgpsi
      have hD := hweight psi _ _ hpsiTop hF hgradLp2
      have hwNg : MemLp (fun z => w z • matrixAction (d.N z) (planarGradient chi z)) 2 μ := hwLp.smul hNg
      have hT : Integrable (fun z => w z * inner ℝ (matrixAction (d.N z) (planarGradient chi z)) (planarGradient psi z)) μ := by
        apply (hint _ _ hwNg hgpsi).congr
        exact Filter.Eventually.of_forall fun z => by
          dsimp only
          rw [inner_smul_left]
          rfl
      have heq := (d.weak.2 (chi * psi) (hchi.mul hp) hc.mul_right (tsupport_mul_subset_left.trans hs)).2.2
      simp_rw [hprod psi hp, inner_add_right, inner_smul_right, zero_mul, add_zero] at heq
      rw [integral_add hA hB, integral_add hC hD] at heq
      have heL (z : E2) : inner ℝ (matrixAction (Ntilde z) (dU z)) (planarGradient psi z) =
          chi z * inner ℝ (matrixAction (d.N z) (d.dv z)) (planarGradient psi z) +
          w z * inner ℝ (matrixAction (d.N z) (planarGradient chi z)) (planarGradient psi z) := by
        rw [hNt]
        change inner ℝ (matrixAction (d.N z) (chi z • d.dv z + w z • planarGradient chi z)) _ = _
        rw [maadd, masmul, masmul, inner_add_left, inner_smul_left, inner_smul_left]
        rfl
      have heR (z : E2) : inner ℝ (E z) (planarGradient psi z) + f0 z * psi z =
          (chi z * inner ℝ (d.F z) (planarGradient psi z) +
            w z * inner ℝ (matrixAction (d.N z) (planarGradient chi z)) (planarGradient psi z)) +
          (psi z * inner ℝ (d.F z) (planarGradient chi z) -
            psi z * inner ℝ (matrixAction (d.N z) (d.dv z)) (planarGradient chi z)) := by
        change inner ℝ (chi z • d.F z + w z • matrixAction (d.N z) (planarGradient chi z)) _ +
          inner ℝ (d.F z - matrixAction (d.N z) (d.dv z)) (planarGradient chi z) * psi z = _
        rw [inner_add_left, inner_smul_left, inner_smul_left, inner_sub_left]
        change (chi z * _ + w z * _) + (_ - _) * psi z = _
        ring
      change (∫ z, inner ℝ (matrixAction (Ntilde z) (dU z)) (planarGradient psi z) ∂μ) =
        ∫ z, inner ℝ (E z) (planarGradient psi z) + f0 z * psi z ∂μ
      simp_rw [heL, heR]
      have hsplit := integral_add (hC.add hT) (hD.sub hB)
      simp only [Pi.add_apply, Pi.sub_apply] at hsplit
      rw [integral_add hA hT, hsplit, integral_add hC hT, integral_sub hD hB]
      linarith
  refine ⟨hweak, hEall, hfall, hEint, hfint,
    hc.of_isClosed_subset (isClosed_tsupport _) hEs,
    hc.of_isClosed_subset (isClosed_tsupport _) hfs, hEs, hfs, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hfzero z (fun ht => hz (hs ht)))]
  have hFchi := hint d.F (planarGradient chi) hF hgradLp2
  have hNchi := hint (fun z => matrixAction (d.N z) (d.dv z)) (planarGradient chi) hflux hgradLp2
  have heq := (d.weak.2 chi hchi hc hs).2.2
  simp only [zero_mul, add_zero] at heq
  change (∫ z in B, inner ℝ (d.F z - matrixAction (d.N z) (d.dv z)) (planarGradient chi z)) = 0
  simp_rw [inner_sub_left]
  rw [integral_sub hFchi hNchi]
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential
