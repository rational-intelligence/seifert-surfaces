import B1HalfDiscDirichletSolve_v468
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The supplied representatives of a native completed pair have native H10. -/
theorem halfdisc_pair_native_h10_v468 (R : ℝ) (p : X (halfDisc R)) :
    H10On (halfDisc R) (val (halfDisc R) p) (grad (halfDisc R) p) := by
  let U := halfDisc R
  have hv : MemLp (val U p) 2 (volume.restrict U) := Lp.memLp (valLp U p)
  have hg : MemLp (grad U p) 2 (volume.restrict U) := Lp.memLp (gradLp U p)
  apply (halfdisc_nativeH10_iff_pair_mem_export_v468 R _ _ hv hg).mpr
  have heq : pack U (val U p) (grad U p) hv hg = p.val := by
    have hvEq : hv.toLp (val U p) = valLp U p := Lp.toLp_coeFn (valLp U p) hv
    have hgEq : hg.toLp (grad U p) = gradLp U p := Lp.toLp_coeFn (gradLp U p) hg
    unfold pack
    rw [hvEq,hgEq]
    rfl
  rw [heq]
  exact p.property

/-- Smooth scalar functions have their literal supplied planar weak gradient. -/
theorem smooth_native_weak_gradient_v468 (U : Set E2) (u : E2 → ℝ)
    (hu : ContDiff ℝ ∞ u) : WeakGradientOn U u (planarGradient u) := by
  have hg : Continuous (planarGradient u) := continuous_planarGradient hu
  refine ⟨hu.continuous.locallyIntegrable.locallyIntegrableOn _,
    hg.locallyIntegrable.locallyIntegrableOn _,?_⟩
  intro φ hs hc ht i
  have hcoord (x : E2) : planarGradient u x i = fderiv ℝ u x (coordinateVector 2 i) := by
    fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector]
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector 2 i)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdu : Continuous (fun x => fderiv ℝ u x (coordinateVector 2 i)) :=
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((hdu.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hu.continuous.mul hdφ).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 i)).mul_left)
    ((hu.continuous.mul hs.continuous).integrable_of_hasCompactSupport hc.mul_left)
    (fun x _ => hu.differentiable (by simp) x)
    (fun x _ => hs.differentiable (by simp) x)
  simp_rw [hcoord]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hi
  · intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun h => hx (ht h)),mul_zero]
  · intro x hx
    have hdsub : tsupport (fun x => fderiv ℝ φ x (coordinateVector 2 i)) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ (coordinateVector 2 i)).trans ht
    rw [show fderiv ℝ φ x (coordinateVector 2 i) = 0 from
      image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x (coordinateVector 2 i))
        (fun h => hx (hdsub h)),mul_zero]

/-- Addition by the constant boundary datum preserves the exact native weak gradient. -/
theorem native_weak_gradient_add_one_v468 (U : Set E2)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H1On U u du) :
    WeakGradientOn U (fun x => u x + 1) du := by
  have hconstant : WeakGradientOn U (fun _ : E2 => (1 : ℝ)) (fun _ => 0) := by
    have hz : planarGradient (fun _ : E2 => (1 : ℝ)) = (fun _ => 0) := by
      funext x
      simp [planarGradient]
    rw [← hz]
    exact smooth_native_weak_gradient_v468 U (fun _ : E2 => (1 : ℝ)) contDiff_const
  refine ⟨hu.1.1.add hconstant.1,hu.1.2.1,?_⟩
  intro φ hs hc ht i
  have hdφ : Continuous (fun x => fderiv ℝ φ x (coordinateVector 2 i)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hiu : IntegrableOn (fun x => u x * fderiv ℝ φ x (coordinateVector 2 i)) U := by
    change Integrable (fun x => u x * fderiv ℝ φ x (coordinateVector 2 i)) (volume.restrict U)
    simpa only [smul_eq_mul] using ((hu.2.1.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
      hdφ (hc.fderiv_apply ℝ (coordinateVector 2 i)))
  have hi1 : IntegrableOn (fun x => fderiv ℝ φ x (coordinateVector 2 i)) U :=
    (hdφ.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (coordinateVector 2 i))).restrict
  have hz := hconstant.2.2 φ hs hc ht i
  simp only [one_mul,PiLp.zero_apply,zero_mul,integral_zero,neg_zero] at hz
  simp_rw [add_mul,one_mul]
  rw [integral_add hiu hi1]
  have hzero : (∫ x in U, fderiv ℝ φ x (coordinateVector 2 i)) = 0 := by
    simpa only [one_mul, PiLp.zero_apply, zero_mul, integral_zero, neg_zero] using hz
  rw [hzero,add_zero]
  exact hu.1.2.2 φ hs hc ht i

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The original collar coefficients admit a native weak solution with datum 1 in H10. -/
theorem actual_halfdisc_native_dirichlet_weak_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ, ∃ dh : E2 → E2,
      H1On (halfDisc R) h dh ∧
      H10On (halfDisc R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh := by
  obtain ⟨R,hR,hRW,p,hsolve⟩ := actual_halfdisc_native_variational_solution_v468 D s W
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : MeasurableSet U := by
    change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (lt_of_le_of_lt (measure_mono (show U ⊆ Metric.ball (0 : E2) R from fun x hx => hx.1))
      measure_ball_lt_top).ne
  have hv : MemLp (val U p) 2 μ := Lp.memLp (valLp U p)
  have hg : MemLp (grad U p) 2 μ := Lp.memLp (gradLp U p)
  have hone : MemLp (fun _ : E2 => (1 : ℝ)) 2 μ := memLp_const 1
  let h := fun x => val U p x + 1
  let dh := grad U p
  have hp := halfdisc_pair_native_h10_v468 R p
  have hweak : WeakGradientOn U h dh := native_weak_gradient_add_one_v468 U _ _ hp.1
  refine ⟨R,hR,hRW,h,dh,⟨hweak,hv.add hone,hg⟩,?_,hweak,?_⟩
  · simpa only [h,add_sub_cancel_right] using hp
  · intro φ hs hc ht
    have htH10 := halfdisc_native_smooth_h10_export_v468 R φ hs hc ht
    have hφ := htH10.1.2.1
    have hdφ := htH10.1.2.2
    let q : X U := ⟨pack U φ (planarGradient φ) hφ hdφ,
      (halfdisc_nativeH10_iff_pair_mem_export_v468 R φ (planarGradient φ) hφ hdφ).mp htH10⟩
    have hqval : val U q =ᵐ[μ] φ := hφ.coeFn_toLp
    have hqgrad : grad U q =ᵐ[μ] planarGradient φ := hdφ.coeFn_toLp
    obtain ⟨ha,hb,hc',A,B,C,hA,hB,hC,haBound,hbBound,hcBound⟩ :=
      actual_halfdisc_full_form_bounds_v468 D s W R hRW
    obtain ⟨F,hFeq,hint⟩ := halfdisc_full_form_data_v468 R W.a W.b W.c
      ha hb hc' A B C hA hB hC haBound hbBound hcBound
    have hcLp : MemLp W.c 2 μ := by
      apply MemLp.of_bound hc' C
      filter_upwards [ae_restrict_mem hU] with x hx
      exact hcBound x hx
    have hiload : IntegrableOn (fun x => W.c x * φ x) U := by
      apply (L2.integrable_inner (𝕜 := ℝ) (hcLp.toLp W.c) (hφ.toLp φ)).congr
      filter_upwards [hcLp.coeFn_toLp,hφ.coeFn_toLp] with x hx hφx
      rw [hx,hφx,Real.inner_apply]
    have he := hsolve q
    have hraw : (∫ x in U,
        inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
        (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) =
        ∫ x in U, W.c x * φ x := by
      convert he using 1
      · apply integral_congr_ae
        filter_upwards [hqval,hqgrad] with x hx hdx
        rw [hx,hdx]
      · apply integral_congr_ae
        filter_upwards [hqval] with x hx
        rw [hx]
    have hi := hint (val U p) dh φ (planarGradient φ) hv hg hφ hdφ
    have hih := hint h dh φ (planarGradient φ) (hv.add hone) hg hφ hdφ
    refine ⟨hih,?_⟩
    have hfun : (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
        (inner ℝ (W.b x) (dh x) + W.c x * h x) * φ x) =
        (fun x => inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
          (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) -
        (fun x => W.c x * φ x) := by
      funext x
      dsimp [h]
      ring
    rw [hfun]
    change (∫ x in U, (inner ℝ (matrixAction (W.a x) (dh x)) (planarGradient φ x) -
      (inner ℝ (W.b x) (dh x) + W.c x * val U p x) * φ x) - W.c x * φ x) = 0
    rw [integral_sub hi hiload,hraw,sub_self]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
