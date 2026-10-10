import InitialClosedDiscTestJets_v457

noncomputable section
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 800000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "original_clamp" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_disc_clamp_v457)⟩

local macro "paid_clamp_cont" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.continuous_original_disc_clamp_v457)⟩

local macro "paid_clamp_eq" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_disc_clamp_eq_v457)⟩

local macro "paid_circle_closed" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_circle_in_closed_disc_v457)⟩

local macro "original_test_jet" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialClosedDiscTestJets_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_closed_disc_test_jet_v457)⟩

local macro "paid_weighted_cont" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialSeparableTestAE_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.weighted_continuous_map_integral_v457)⟩

local macro "paid_weighted_int" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialSeparableTestAE_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.weighted_continuous_map_integrable_v457)⟩

local macro "paid_disc_weight" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialNormalGreen_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.disc_integrable_continuous_weight_v457)⟩

private def original_cap_test_jet_residual_v458
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (p : E2) (q : ℝ) (i j : Fin 2)
    (u : C(closedDisc 1,ℝ) × (Fin 2 → C(closedDisc 1,ℝ))) : ℝ :=
    (∫ x in planarCap p q,f x i*u.2 j (original_clamp x))+
    (∫ x in planarCap p q,d i x j*u.1 (original_clamp x))-
      q*(∫ t in Ioo (-Real.pi) Real.pi,
        ((disc 1).indicator f (p+q•unitCircleParameter t)) i*unitCircleParameter t j*
          u.1 (original_clamp (p+q•unitCircleParameter t)))-
      ∫ t in circlePatch p q,b t i*unitCircleParameter t j*u.1 (original_clamp (unitCircleParameter t))

private theorem original_cap_test_jet_residual_continuous_v458
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun x=>f x i) (d i)) (hb : Continuous b)
    (p : E2) (q : ℝ)
    (hFs : MemLp (fun t=>(disc 1).indicator f (p+q•unitCircleParameter t)) 2
      (volume.restrict (Ioo (-Real.pi) Real.pi)))
    (i j : Fin 2) : Continuous (original_cap_test_jet_residual_v458 f d b p q i j) := by
  let : CompactSpace (closedDisc 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E2) 1)
  let : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    isFiniteMeasure_restrict.mpr ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hfi0 : IntegrableOn (fun x=>f x i) (disc 1) := (H1 i).2.1.integrable (by norm_num)
  have hdi0 : IntegrableOn (fun x=>d i x j) (disc 1) :=
    ((H1 i).2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) j)).integrable (by norm_num)
  have hfi := hfi0.mono_set (inter_subset_left : planarCap p q⊆disc 1)
  have hdi := hdi0.mono_set (inter_subset_left : planarCap p q⊆disc 1)
  have hc : Continuous unitCircleParameter := by
    change Continuous (fun t:ℝ=>WithLp.toLp 2 ![Real.cos t,Real.sin t])
    fun_prop
  have hci : Continuous (fun t=>unitCircleParameter t j) := (EuclideanSpace.proj (𝕜:=ℝ) j).continuous.comp hc
  have hn (t:ℝ) : ‖unitCircleParameter t j‖≤1 := by
    fin_cases j
    · simpa [unitCircleParameter,Real.norm_eq_abs] using Real.abs_cos_le_one t
    · simpa [unitCircleParameter,Real.norm_eq_abs] using Real.abs_sin_le_one t
  have hAi : IntegrableOn (fun t=>((disc 1).indicator f (p+q•unitCircleParameter t)) i*unitCircleParameter t j)
      (Ioo (-Real.pi) Real.pi) :=
    (hFs.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) i)).integrable (by norm_num) |>.mul_bdd
      hci.aestronglyMeasurable.restrict (Eventually.of_forall hn)
  have hTi : IntegrableOn (fun t=>b t i*unitCircleParameter t j) (circlePatch p q) :=
    (((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp hb).mul hci).integrableOn_Icc.mono_set inter_subset_left
  let J := C(closedDisc 1,ℝ) × (Fin 2 → C(closedDisc 1,ℝ))
  have hjcont : Continuous (fun u:J=>u.2 j) := (continuous_apply j).comp continuous_snd
  have h0cont : Continuous (fun u:J=>u.1) := continuous_fst
  have hB1 : Continuous (fun u:J=>∫ x in planarCap p q,f x i*u.2 j (original_clamp x)) := (paid_weighted_cont (volume.restrict (planarCap p q)) original_clamp
    (paid_clamp_cont).measurable (fun x=>f x i) hfi).comp hjcont
  have hB2 : Continuous (fun u:J=>∫ x in planarCap p q,d i x j*u.1 (original_clamp x)) := (paid_weighted_cont (volume.restrict (planarCap p q)) original_clamp
    (paid_clamp_cont).measurable (fun x=>d i x j) hdi).comp h0cont
  have hslice : Continuous (fun t:ℝ=>p+q•unitCircleParameter t) :=
    continuous_const.add (hc.const_smul q)
  have hclampslice : Measurable (fun t:ℝ=>original_clamp (p+q•unitCircleParameter t)) :=
    ((paid_clamp_cont).comp hslice).measurable
  have hA : Continuous (fun u:J=>∫ t in Ioo (-Real.pi) Real.pi,
      ((disc 1).indicator f (p+q•unitCircleParameter t)) i*unitCircleParameter t j*
        u.1 (original_clamp (p+q•unitCircleParameter t))) := (paid_weighted_cont (volume.restrict (Ioo (-Real.pi) Real.pi))
    (fun t=>original_clamp (p+q•unitCircleParameter t))
    hclampslice
    (fun t=>((disc 1).indicator f (p+q•unitCircleParameter t)) i*unitCircleParameter t j) hAi).comp h0cont
  have hT : Continuous (fun u:J=>∫ t in circlePatch p q,
      b t i*unitCircleParameter t j*u.1 (original_clamp (unitCircleParameter t))) := (paid_weighted_cont (volume.restrict (circlePatch p q))
    (fun t=>original_clamp (unitCircleParameter t)) ((paid_clamp_cont).comp hc).measurable
    (fun t=>b t i*unitCircleParameter t j) hTi).comp h0cont
  change Continuous (fun u:J=>_+_-q*_-_)
  exact ((hB1.add hB2).sub (continuous_const.mul hA)).sub hT

private theorem original_cap_test_jet_residual_native_v458
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun x=>f x i) (d i))
    (p : E2) (q : ℝ) (i j : Fin 2) (psi:E2→ℝ) (hpsi:ContDiff ℝ ∞ psi) :
    original_cap_test_jet_residual_v458 f d b p q i j (original_test_jet psi hpsi)=
      (∫ x in planarCap p q,f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)-
        (q*∫ t in Ioo (-Real.pi) Real.pi,
          (disc 1).indicator (fun x=>f x i*psi x) (p+q•unitCircleParameter t)*unitCircleParameter t j)-
        ∫ t in circlePatch p q,b t i*psi (unitCircleParameter t)*unitCircleParameter t j := by
  classical
  let : IsFiniteMeasure (volume.restrict (disc 1)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let u := original_test_jet psi hpsi
  have hU0 (x:E2) (hx:x∈closedDisc 1) : u.1 (original_clamp x)=psi x := by
    change psi (original_clamp x)=psi x
    rw [paid_clamp_eq x hx]
  have hUj (x:E2) (hx:x∈closedDisc 1) : u.2 j (original_clamp x)=fderiv ℝ psi x (coordinateVector 2 j) := by
    change fderiv ℝ psi (original_clamp x) (coordinateVector 2 j)=_
    rw [paid_clamp_eq x hx]
  have hB1 : (∫ x in planarCap p q,f x i*u.2 j (original_clamp x))=
      ∫ x in planarCap p q,f x i*fderiv ℝ psi x (coordinateVector 2 j) := by
    apply setIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball)
    intro x hx
    dsimp only
    rw [hUj x (Metric.ball_subset_closedBall hx.1)]
  have hB2 : (∫ x in planarCap p q,d i x j*u.1 (original_clamp x))=
      ∫ x in planarCap p q,d i x j*psi x := by
    apply setIntegral_congr_fun (measurableSet_ball.inter measurableSet_ball)
    intro x hx
    dsimp only
    rw [hU0 x (Metric.ball_subset_closedBall hx.1)]
  have hA : (∫ t in Ioo (-Real.pi) Real.pi,
      ((disc 1).indicator f (p+q•unitCircleParameter t)) i*unitCircleParameter t j*
        u.1 (original_clamp (p+q•unitCircleParameter t)))=
      ∫ t in Ioo (-Real.pi) Real.pi,
        (disc 1).indicator (fun x=>f x i*psi x) (p+q•unitCircleParameter t)*unitCircleParameter t j := by
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hx:p+q•unitCircleParameter t∈disc 1
    · rw [indicator_of_mem hx,indicator_of_mem hx,hU0 _ (Metric.ball_subset_closedBall hx)]
      ring
    · simp only [indicator_of_notMem hx,PiLp.zero_apply,zero_mul]
  have hT : (∫ t in circlePatch p q,b t i*unitCircleParameter t j*u.1 (original_clamp (unitCircleParameter t)))=
      ∫ t in circlePatch p q,b t i*psi (unitCircleParameter t)*unitCircleParameter t j := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [hU0 _ (paid_circle_closed t)]
    ring
  have hfi := (H1 i).2.1.integrable (by norm_num)
  have hdi := ((H1 i).2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜:=ℝ) j)).integrable (by norm_num)
  have hI1 := (paid_disc_weight (fun x=>f x i) hfi
    (fun x=>fderiv ℝ psi x (coordinateVector 2 j))
    ((hpsi.continuous_fderiv (by simp)).clm_apply continuous_const)).mono_set
    (inter_subset_left : planarCap p q⊆disc 1)
  have hI2 := (paid_disc_weight (fun x=>d i x j) hdi psi hpsi.continuous).mono_set
    (inter_subset_left : planarCap p q⊆disc 1)
  change _+_-_-_=_-_-_
  change IntegrableOn (fun x=>f x i*fderiv ℝ psi x (coordinateVector 2 j)) (planarCap p q) at hI1
  change IntegrableOn (fun x=>d i x j*psi x) (planarCap p q) at hI2
  rw [hB1,hB2,hA,hT,integral_add hI1 hI2]

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
