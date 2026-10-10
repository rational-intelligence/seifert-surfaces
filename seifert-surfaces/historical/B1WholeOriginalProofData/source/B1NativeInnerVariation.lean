import B1MetricVariationalInterfaces
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation.InnerCourant
open SeifertSurfaces.AppendixACoordinates
theorem native_inner_variation (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)
    (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)
    (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)
    (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))
    (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)
 :
  ∀ f d, MetricAdmissible Ω f d → ∀ η : E2 → E2,
      ContDiff ℝ ∞ η → (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) →
      ∃ fs : ℝ → E2 → E2, ∃ ds : ℝ → Fin 2 → E2 → E2,
        fs 0 = f ∧ ds 0 = d ∧
        (∀ᶠ s in 𝓝 (0 : ℝ), MetricAdmissible Ω (fs s) (ds s)) ∧
        HasDerivAt (fun s => metricArea M (fs s) (ds s)) 0 0 ∧
        HasDerivAt (fun s => metricDirichlet M (fs s) (ds s))
          ((1/2 : ℝ)*(∫ x in disc 1, (metricE M f d x-metricH M f d x) *
          ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +
          (2*metricF M f d x) * ((fderiv ℝ η x (coordinateVector 2 0)) 1 +
            (fderiv ℝ η x (coordinateVector 2 1)) 0))) 0 := by
  set_option maxHeartbeats 0 in
  set_option maxRecDepth 100000 in
  set_option cleanup.letToHave false in
  exact (by
      have nativeH1 :
      ∀ (f : E2 → E2) (d : Fin 2 → E2 → E2),
          (∀ i, H1On (disc 1) (fun x => f x i) (d i)) →
          ∀ η : E2 → E2, ContDiff ℝ ∞ η →
          (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) →
        let τ := fun (s : ℝ) (x : E2) => (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
        let fs := fun s x => f (τ s x)
        let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
        ∀ᶠ s in 𝓝 (0:ℝ), ∀ i, H1On (disc 1) (fun x => fs s x i) (ds s i) :=
        by
          set_option maxHeartbeats 0 in
            exact (by
              classical
              have hLp (f : E2 → E2) (d : Fin 2 → E2 → E2)
                  (hH1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i))
                  (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
                  (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
                  let τ := fun (s : ℝ) (x : E2) =>
                    (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                  let fs := fun s x => f (τ s x)
                  let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
                  ∀ᶠ s in 𝓝 (0:ℝ), ∀ i,
                    MemLp (fun x => fs s x i) 2 (volume.restrict (disc 1)) ∧
                    MemLp (ds s i) 2 (volume.restrict (disc 1)) ∧
                    LocallyIntegrableOn (fun x => fs s x i) (disc 1) ∧
                    LocallyIntegrableOn (ds s i) (disc 1) := by
                have hL2 (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ)
                    (hb : BijOn τ (disc 1) (disc 1))
                    (hn : ∀ x ∈ closedDisc 1, (fderiv ℝ τ x).det ≠ 0)
                    (f : E2 → E2) (d : Fin 2 → E2 → E2)
                    (hH1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i)) :
                    let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                      (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))
                    ∀ i, MemLp (fun x => f (τ x) i) 2 (volume.restrict (disc 1)) ∧
                      MemLp (dt i) 2 (volume.restrict (disc 1)) ∧
                      LocallyIntegrableOn (fun x => f (τ x) i) (disc 1) ∧
                      LocallyIntegrableOn (dt i) (disc 1) := by
                  dsimp only
                  let μ := volume.restrict (disc 1)
                  let w := fun x => ENNReal.ofReal |(fderiv ℝ τ x).det|
                  have hdet : Continuous (fun x => |(fderiv ℝ τ x).det|) :=
                    (ContinuousLinearMap.continuous_det.comp (hc.continuous_fderiv (by simp))).abs
                  obtain ⟨δ,hδ,hbound⟩ := (isCompact_closedBall (0 : E2) 1).exists_forall_le'
                    hdet.continuousOn (fun x hx => abs_pos.mpr (hn x hx))
                  let c := ENNReal.ofReal δ
                  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
                  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
                  have hμ : μ ≤ c⁻¹ • μ.withDensity w := by
                    have hw : Measurable w := ENNReal.measurable_ofReal.comp hdet.measurable
                    rw [← withDensity_smul c⁻¹ hw]
                    calc
                      μ = μ.withDensity (fun _ => (1 : ℝ≥0∞)) := (withDensity_one).symm
                      _ ≤ μ.withDensity (c⁻¹ • w) := by
                        apply withDensity_mono
                        filter_upwards [ae_restrict_mem (s := disc 1) Metric.isOpen_ball.measurableSet] with x hx
                        change 1 ≤ c⁻¹ * w x
                        calc
                          1 = c⁻¹ * c := (ENNReal.inv_mul_cancel hc0 hctop).symm
                          _ ≤ c⁻¹ * w x := by
                            gcongr
                            exact ENNReal.ofReal_le_ofReal (hbound x (Metric.ball_subset_closedBall hx))
                  have hmap : Measure.map τ (μ.withDensity w) = μ := by
                    have hh := map_withDensity_abs_det_fderiv_eq_addHaar (μ := volume)
                      Metric.isOpen_ball.measurableSet.nullMeasurableSet
                      (fun x (_ : x ∈ disc 1) => (hc.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
                      hb.injOn
                    change Measure.map τ (μ.withDensity w) = volume.restrict (τ '' disc 1) at hh
                    rw [hb.image_eq] at hh
                    exact hh
                  have hcomp {F : Type} [NormedAddCommGroup F] (v : E2 → F) (hv : MemLp v 2 μ) :
                      MemLp (v ∘ τ) 2 μ := by
                    have hi : MemLp v 2 (Measure.map τ (μ.withDensity w)) := by rwa [hmap]
                    have hj := hi.comp_of_map hc.continuous.measurable.aemeasurable
                    exact MemLp.of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hμ hj
                  intro i
                  have hf := hcomp (fun x => f x i) (hH1 i).2.1
                  have hd := hcomp (d i) (hH1 i).2.2
                  have hcoef (j k : Fin 2) : MemLp (fun x => (fderiv ℝ τ x (coordinateVector 2 j)) k) ∞ μ := by
                    have hcont : Continuous (fun x => (fderiv ℝ τ x (coordinateVector 2 j)) k) :=
                      (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.comp
                        ((hc.continuous_fderiv (by simp)).clm_apply continuous_const)
                    obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E2) 1).exists_bound_of_continuousOn hcont.continuousOn
                    apply memLp_top_of_bound hcont.aestronglyMeasurable C
                    filter_upwards [ae_restrict_mem (s := disc 1) Metric.isOpen_ball.measurableSet] with x hx
                    exact hC x (Metric.ball_subset_closedBall hx)
                  have hdt : MemLp (fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                      (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))) 2 μ := by
                    apply MemLp.of_eval_piLp
                    intro j
                    have h0 := (hd.eval_piLp 0).mul (r := 2) (hcoef j 0)
                    have h1 := (hd.eval_piLp 1).mul (r := 2) (hcoef j 1)
                    have hsum : MemLp (fun x => d i (τ x) 0 * (fderiv ℝ τ x (coordinateVector 2 j)) 0 +
                        d i (τ x) 1 * (fderiv ℝ τ x (coordinateVector 2 j)) 1) 2 μ := h0.add h1
                    apply MemLp.ae_eq (hf_Lp := hsum)
                    exact Filter.Eventually.of_forall fun x => by
                      change _ = inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j))
                      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                      ring
                  exact ⟨hf,hdt,locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable (by norm_num)),
                    locallyIntegrableOn_of_locallyIntegrable_restrict (hdt.locallyIntegrable (by norm_num))⟩
                have hgeometry (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
                    (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
                    let τ := fun (s : ℝ) (x : E2) =>
                      (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                    let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                      (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                    let α := fun s t => t+Real.arctan (s*k t)
                    (∀ x, τ 0 x = x) ∧
                    (∀ x, HasDerivAt (fun s => τ s x) (η x) 0) ∧
                    ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) ∧
                    (∀ᶠ s in 𝓝 (0:ℝ),
                      BijOn (τ s) (disc 1) (disc 1) ∧
                      BijOn (τ s) (closedDisc 1) (closedDisc 1) ∧
                      StrictMono (α s) ∧ Continuous (α s) ∧
                      (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi) ∧
                      (∀ t, τ s (unitCircleParameter t) = unitCircleParameter (α s t)) ∧
                      (∀ x ∈ closedDisc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                        (e : E2 → E2) = τ s ∧ x ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (τ s x))) := by
                  have hnormalized (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
                      (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
                      let tau : ℝ → E2 → E2 := fun s x =>
                        (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x)
                      (∀ x, tau 0 x = x) ∧
                      (∀ x, HasDerivAt (fun s => tau s x) (η x) 0) ∧
                      ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2) ∧
                      (∀ s x, ‖x‖ = 1 → ‖tau s x‖ = 1) := by
                    dsimp only
                    have hpos (s : ℝ) (x : E2) : 0 < 1 + s^2 * ‖η x‖^2 := by positivity
                    refine ⟨fun x => by simp, ?_, ?_, ?_⟩
                    · intro x
                      have ha : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s^2 * ‖η x‖^2)) 0 0 := by
                        convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖η x‖^2)).const_add 1 |>.sqrt (by simp) using 1 <;> norm_num
                      have hb : HasDerivAt (fun s : ℝ => x + s • η x) (η x) 0 := by
                        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add x
                      convert (ha.inv (by simp)).smul hb using 1 <;> norm_num
                    · have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖η p.2‖^2) :=
                        (hη.comp contDiff_snd).norm_sq (𝕜 := ℝ)
                      have hd : ContDiff ℝ ∞ (fun p : ℝ × E2 => Real.sqrt (1 + p.1^2 * ‖η p.2‖^2)) :=
                        (contDiff_const.add ((contDiff_fst.pow 2).mul hi)).sqrt (fun p => (hpos p.1 p.2).ne')
                      exact (hd.inv (fun p => (Real.sqrt_pos.mpr (hpos p.1 p.2)).ne')).smul
                        (contDiff_snd.add (contDiff_fst.smul (hη.comp contDiff_snd)))
                    · intro s x hx
                      have ht : inner ℝ x (η x) = 0 := by
                        rw [real_inner_comm]
                        exact htan x hx
                      have hn : ‖x + s • η x‖^2 = 1 + s^2 * ‖η x‖^2 := by
                        rw [norm_add_sq_real, real_inner_smul_right, ht,hx,norm_smul]
                        simp [mul_pow,sq_abs]
                      have he : ‖x + s • η x‖ = Real.sqrt (1 + s^2 * ‖η x‖^2) := by
                        rw [← hn,Real.sqrt_sq (norm_nonneg _)]
                      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.sqrt_pos.mpr (hpos s x)),he]
                      exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos s x)).ne'
                  have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)
                      (f : E2 → E2) (d : Fin 2 → E2 → E2) :
                      (fun x => f (tau 0 x)) = f ∧
                      (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                        (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by
                    have hz : tau 0 = id := funext hzero
                    refine ⟨by simp [hz],?_⟩
                    funext i x
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                    funext j
                    simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
                      Fin.sum_univ_two,EuclideanSpace.single]
                  have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
                      (hz : ∀ x, tau 0 x = x) :
                      ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,
                        ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by
                    have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                        (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
                      have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                        convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                          ext z <;> simp [ContinuousLinearMap.inr]
                      exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
                    have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
                      simp_rw [he]
                      exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
                    have hnorm : Continuous (fun p : ℝ × E2 =>
                        ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=
                      (hf.sub continuous_const).norm
                    apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually
                    intro x hx
                    apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const
                    have hz' : tau 0 = id := funext hz
                    simp [hz']
                  have hinjective (tau : E2 → E2) (hc : ContDiff ℝ ∞ tau)
                      (hd : ∀ x ∈ closedDisc 1,
                        ‖fderiv ℝ tau x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ)) :
                      InjOn tau (closedDisc 1) := by
                    have hf := hc.differentiable (by simp)
                    have hl : LipschitzOnWith (1/2 : ℝ≥0) (fun x => tau x - x) (closedDisc 1) := by
                      apply (convex_closedBall (0 : E2) 1).lipschitzOnWith_of_nnnorm_fderiv_le
                        (fun x _ => (hf x).sub differentiableAt_id)
                      intro x hx
                      rw [fderiv_sub (hf x) differentiableAt_id, fderiv_id]
                      exact_mod_cast (hd x hx).le
                    intro x hx y hy hxy
                    have hb := hl.dist_le_mul x hx y hy
                    have he : (tau x - x) - (tau y - y) = y-x := by rw [hxy, sub_sub_sub_cancel_left]
                    rw [dist_eq_norm,he,norm_sub_rev] at hb
                    change ‖x-y‖ ≤ (1/2 : ℝ) * dist x y at hb
                    rw [← dist_eq_norm] at hb
                    exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])
                  have hangle (η : E2 → E2)
                      (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) (s t : ℝ) :
                      let x := unitCircleParameter t
                      let k := x 0 * η x 1 - x 1 * η x 0
                      (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x) =
                        unitCircleParameter (t + Real.arctan (s*k)) := by
                    dsimp only
                    let x := unitCircleParameter t
                    let k := x 0 * η x 1 - x 1 * η x 0
                    have hc : (x 0)^2 + (x 1)^2 = 1 := by
                      change (Real.cos t)^2 + (Real.sin t)^2 = 1
                      exact Real.cos_sq_add_sin_sq t
                    have hnorm : ‖x‖ = 1 := by
                      have hn : ‖x‖^2 = 1 := by
                        calc
                          ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
                          _ = 1 := by
                            simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two] using hc
                      nlinarith [norm_nonneg x]
                    have ht : η x 0 * x 0 + η x 1 * x 1 = 0 := by
                      simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm] using htan x hnorm
                    have h0 : η x 0 = -k * x 1 := by
                      dsimp only [k]
                      linear_combination -(η x 0)*hc + x 0*ht
                    have h1 : η x 1 = k * x 0 := by
                      dsimp only [k]
                      linear_combination -(η x 1)*hc + x 1*ht
                    have hn : ‖η x‖^2 = k^2 := by
                      rw [← real_inner_self_eq_norm_sq]
                      simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                      rw [h0,h1]
                      nlinarith [sq_nonneg k]
                    change (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x) = _
                    rw [hn]
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                    funext j
                    fin_cases j
                    · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 0 + s*η x 0) =
                        Real.cos (t+Real.arctan (s*k))
                      rw [h0,Real.cos_add,Real.cos_arctan,Real.sin_arctan]
                      change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.cos t + s*(-k*Real.sin t)) = _
                      simp only [mul_pow,div_eq_mul_inv]
                      ring
                    · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 1 + s*η x 1) =
                        Real.sin (t+Real.arctan (s*k))
                      rw [h1,Real.sin_add,Real.cos_arctan,Real.sin_arctan]
                      change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.sin t + s*(k*Real.cos t)) = _
                      simp only [mul_pow,div_eq_mul_inv]
                      ring
                  have hlift (k : ℝ → ℝ) (hk : Continuous k) (hp : Function.Periodic k (2*Real.pi)) (s : ℝ) :
                      Continuous (fun t => t + Real.arctan (s*k t)) ∧
                      (∀ t, (t+2*Real.pi) + Real.arctan (s*k (t+2*Real.pi)) =
                        (t + Real.arctan (s*k t)) + 2*Real.pi) ∧
                      Surjective (fun t => t+Real.arctan (s*k t)) := by
                    have hc : Continuous (fun t => t+Real.arctan (s*k t)) :=
                      continuous_id.add (Real.continuous_arctan.comp (continuous_const.mul hk))
                    refine ⟨hc,fun t => by rw [hp t]; ring,?_⟩
                    intro y
                    have hleft : (y-Real.pi)+Real.arctan (s*k (y-Real.pi)) ≤ y := by
                      linarith [Real.arctan_lt_pi_div_two (s*k (y-Real.pi)),Real.pi_pos]
                    have hright : y ≤ (y+Real.pi)+Real.arctan (s*k (y+Real.pi)) := by
                      linarith [Real.neg_pi_div_two_lt_arctan (s*k (y+Real.pi)),Real.pi_pos]
                    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : y-Real.pi ≤ y+Real.pi)
                      hc.continuousOn ⟨hleft,hright⟩
                    exact ⟨t,he⟩
                  have hlocal (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (x : E2)
                      (hd : ‖fderiv ℝ τ x - ContinuousLinearMap.id ℝ E2‖ < 1) :
                      ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ ∧ x ∈ e.source ∧
                        ContDiffAt ℝ ∞ e.symm (τ x) := by
                    let D := fderiv ℝ τ x
                    have hinj : Injective D := by
                      apply (LinearMap.ker_eq_bot).mp
                      apply LinearMap.ker_eq_bot'.mpr
                      intro v hv
                      change D v = 0 at hv
                      have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]
                      have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v
                      rw [he,norm_neg] at hn
                      have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := hd
                      have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
                      exact norm_eq_zero.mp hz
                    have hsurj : Surjective D := LinearMap.injective_iff_surjective.mp hinj
                    let d : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective D
                      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
                    have heq : (d : E2 →L[ℝ] E2) = D := ContinuousLinearEquiv.coe_ofBijective _ _ _
                    have hf : HasFDerivAt τ (d : E2 →L[ℝ] E2) x := by
                      rw [heq]
                      exact (hc.differentiable (by simp) x).hasFDerivAt
                    let e := hc.contDiffAt.toOpenPartialHomeomorph τ hf (by simp)
                    refine ⟨e,rfl,hc.contDiffAt.mem_toOpenPartialHomeomorph_source hf (by simp),?_⟩
                    exact hc.contDiffAt.to_localInverse hf (by simp)
                  have hcircle (x : E2) (hx : ‖x‖ = 1) : ∃ t : ℝ, unitCircleParameter t = x := by
                    let z : ℂ := ⟨x 0,x 1⟩
                    have hs : (x 0)^2+(x 1)^2=1 := by
                      have h := real_inner_self_eq_norm_sq x
                      rw [hx] at h
                      simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two,one_mul] using h
                    have hz : ‖z‖ = 1 := by
                      have hsq : ‖z‖^2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; simpa [z,Complex.normSq_apply,pow_two] using hs
                      nlinarith [norm_nonneg z]
                    have hne : z ≠ 0 := by intro h; simp [h] at hz
                    refine ⟨Complex.arg z,?_⟩
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                    funext j
                    fin_cases j
                    · change Real.cos (Complex.arg z) = x 0
                      rw [Complex.cos_arg hne,hz]
                      simp [z]
                    · change Real.sin (Complex.arg z) = x 1
                      rw [Complex.sin_arg,hz]
                      simp [z]
                  have hpreserve (τ : E2 → E2) (hc : Continuous τ)
                      (hinj : InjOn τ (closedDisc 1))
                      (hsphere : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ x = y)
                      (hzero : ‖τ 0‖ < 1) : MapsTo τ (disc 1) (disc 1) := by
                    intro x hx
                    change dist (τ x) 0 < 1
                    rw [dist_zero_right]
                    by_contra hn
                    have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
                    have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
                    obtain ⟨z,hz,hze⟩ := (convex_ball (0:E2) 1).isPreconnected.intermediate_value h0 hx
                      hc.norm.continuousOn ⟨hzero.le,not_lt.mp hn⟩
                    obtain ⟨w,hw,he⟩ := hsphere (τ z) hze
                    have hz' : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz
                    have hw' : w ∈ closedDisc 1 := mem_closedBall_zero_iff.mpr hw.le
                    have hzw : z = w := hinj hz' hw' he.symm
                    have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
                    rw [hzw,hw] at hzlt
                    exact lt_irrefl _ hzlt
                  have hsurjective (τ : E2 → E2) (hc : Continuous τ)
                      (hmaps : MapsTo τ (disc 1) (disc 1))
                      (hsphere : ∀ x : E2, ‖x‖ = 1 → ‖τ x‖ = 1)
                      (hlocal : ∀ x ∈ disc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                        (e : E2 → E2) = τ ∧ x ∈ e.source) :
                      SurjOn τ (disc 1) (disc 1) := by
                    have hopen : IsOpen (τ '' disc 1) := by
                      rw [isOpen_iff_mem_nhds]
                      rintro y ⟨x,hx,rfl⟩
                      obtain ⟨e,he,hxe⟩ := hlocal x hx
                      have ho := e.isOpen_image_source_inter (s := disc 1) Metric.isOpen_ball
                      have hm : τ x ∈ e '' (e.source ∩ disc 1) := ⟨x,⟨hxe,hx⟩,by rw [he]⟩
                      exact Filter.mem_of_superset (ho.mem_nhds hm) (by
                        rintro z ⟨w,hw,rfl⟩
                        exact ⟨w,hw.2,by rw [he]⟩)
                    have hcompact : IsClosed (τ '' closedDisc 1) :=
                      ((isCompact_closedBall (0:E2) 1).image hc).isClosed
                    have hclosure : closure (τ '' disc 1) ⊆ τ '' closedDisc 1 :=
                      closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact
                    have hboundary : closure (τ '' disc 1) ∩ disc 1 ⊆ τ '' disc 1 := by
                      intro y hy
                      obtain ⟨x,hx,hxy⟩ := hclosure hy.1
                      refine ⟨x,?_,hxy⟩
                      have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
                      have hylt : ‖y‖ < 1 := mem_ball_zero_iff.mp hy.2
                      have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by
                        intro hxe
                        have := hsphere x hxe
                        rw [hxy] at this
                        linarith)
                      exact mem_ball_zero_iff.mpr hxlt
                    have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
                    exact (convex_ball (0:E2) 1).isPreconnected.subset_of_closure_inter_subset hopen
                      ⟨τ 0,hmaps h0,⟨0,h0,rfl⟩⟩ hboundary
                  have hmonotone (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
                      (hp : Periodic k (2*Real.pi)) :
                      ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (fun t => t+Real.arctan (s*k t)) := by
                    have hpd : Periodic (deriv k) (2*Real.pi) := by
                      intro t
                      have he : (fun t => k (t+2*Real.pi)) = k := funext hp
                      rw [← deriv_comp_add_const k (2*Real.pi) t,he]
                    obtain ⟨C,hC,hbound⟩ := (hpd.isBounded_of_continuous (by positivity)
                      (hk.continuous_deriv (by simp))).exists_pos_norm_le
                    have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), |s| * C < (1/2:ℝ) := by
                      exact (continuousAt_id.abs.mul_const C).eventually_lt_const (by norm_num)
                    filter_upwards [hsmall] with s hs
                    apply strictMono_of_hasDerivAt_pos
                      (f' := fun t => 1 + (s*deriv k t)/(1+(s*k t)^2))
                    · intro t
                      convert (hasDerivAt_id t).add (((hk.differentiable (by simp) t).hasDerivAt.const_mul s).arctan) using 1 <;> first | rfl | ring
                    · intro t
                      have hb : |s*deriv k t| < (1/2:ℝ) := by
                        rw [abs_mul]
                        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
                          (by simpa using hbound (deriv k t) ⟨t,rfl⟩) (abs_nonneg s)) hs
                      have hd : 0 < 1+(s*k t)^2 := by positivity
                      have hl : -1 < (s*deriv k t)/(1+(s*k t)^2) := by
                        rw [lt_div_iff₀ hd]
                        have hlow := (abs_lt.mp hb).1
                        nlinarith [sq_nonneg (s*k t)]
                      linarith
                  have hcoefficient (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :
                      let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                        (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                      ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by
                    dsimp only
                    have hc : ContDiff ℝ ∞ unitCircleParameter := by
                      apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
                      apply contDiff_pi.mpr
                      intro i
                      fin_cases i
                      · simpa using Real.contDiff_cos
                      · simpa using Real.contDiff_sin
                    have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=
                      (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i
                    refine ⟨?_,?_⟩
                    · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))
                    · intro t
                      have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by
                        apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                        funext i
                        fin_cases i
                        · change Real.cos (t+2*Real.pi) = Real.cos t
                          exact Real.cos_add_two_pi t
                        · change Real.sin (t+2*Real.pi) = Real.sin t
                          exact Real.sin_add_two_pi t
                      dsimp only
                      rw [hp]
                  dsimp only
                  let τ := fun (s : ℝ) (x : E2) =>
                    (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                  let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                    (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                  let α := fun s t => t+Real.arctan (s*k t)
                  obtain ⟨hz,hvel,hc,hsp⟩ := hnormalized η hη htan
                  have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc
                  have hcs (s : ℝ) : ContDiff ℝ ∞ (τ s) :=
                    hc'.comp (contDiff_const.prodMk contDiff_id)
                  have hu := huniform τ hc' hz
                  obtain ⟨hk,hkp⟩ := hcoefficient η hη
                  have hm := hmonotone k hk hkp
                  have hcenter : ∀ᶠ s in 𝓝 (0:ℝ), ‖τ s 0‖ < 1 := by
                    exact (((hc'.continuous.comp (continuous_id.prodMk continuous_const)).norm).continuousAt).eventually_lt_const (by simp [τ])
                  refine ⟨hz,hvel,hc',?_⟩
                  filter_upwards [hu,hm,hcenter] with s hs hms hzs
                  have hi := hinjective (τ s) (hcs s) hs
                  obtain ⟨hac,hap,has⟩ := hlift k hk.continuous hkp s
                  have hformula (t : ℝ) : τ s (unitCircleParameter t) = unitCircleParameter (α s t) :=
                    hangle η htan s t
                  have honto : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ s x = y := by
                    intro y hy
                    obtain ⟨t,ht⟩ := hcircle y hy
                    obtain ⟨u,hu⟩ := has t
                    refine ⟨unitCircleParameter u,?_,?_⟩
                    · have hh := real_inner_self_eq_norm_sq (unitCircleParameter u)
                      have hsq : ‖unitCircleParameter u‖^2 = 1 := by
                        calc
                          _ = inner ℝ (unitCircleParameter u) (unitCircleParameter u) := hh.symm
                          _ = 1 := by
                            simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                            change Real.cos u * Real.cos u + Real.sin u * Real.sin u = 1
                            nlinarith [Real.cos_sq_add_sin_sq u]
                      nlinarith [norm_nonneg (unitCircleParameter u)]
                    · rw [hformula]
                      change unitCircleParameter (u+Real.arctan (s*k u)) = y
                      dsimp only at hu
                      rw [hu,ht]
                  have hmap := hpreserve (τ s) (hcs s).continuous hi honto hzs
                  have hl (x : E2) (hx : x ∈ closedDisc 1) :
                      ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ s ∧ x ∈ e.source ∧
                        ContDiffAt ℝ ∞ e.symm (τ s x) :=
                    hlocal (τ s) (hcs s) x (lt_trans (hs x hx) (by norm_num))
                  have hsurj := hsurjective (τ s) (hcs s).continuous hmap (hsp s) (fun x hx => by
                    obtain ⟨e,he,hx,hd⟩ := hl x (Metric.ball_subset_closedBall hx)
                    exact ⟨e,he,hx⟩)
                  have hmapclosed : MapsTo (τ s) (closedDisc 1) (closedDisc 1) := by
                    intro x hx
                    have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
                    rcases lt_or_eq_of_le hxle with hxlt | hxe
                    · exact Metric.ball_subset_closedBall (hmap (mem_ball_zero_iff.mpr hxlt))
                    · have hh : ‖τ s x‖ = 1 := hsp s x hxe
                      exact mem_closedBall_zero_iff.mpr hh.le
                  have hsurjclosed : SurjOn (τ s) (closedDisc 1) (closedDisc 1) := by
                    intro y hy
                    have hyle : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
                    rcases lt_or_eq_of_le hyle with hylt | hye
                    · obtain ⟨x,hx,hxy⟩ := hsurj (mem_ball_zero_iff.mpr hylt)
                      exact ⟨x,Metric.ball_subset_closedBall hx,hxy⟩
                    · obtain ⟨x,hx,hxy⟩ := honto y hye
                      exact ⟨x,mem_closedBall_zero_iff.mpr hx.le,hxy⟩
                  exact ⟨⟨hmap,hi.mono Metric.ball_subset_closedBall,hsurj⟩,
                    ⟨hmapclosed,hi,hsurjclosed⟩,hms,hac,hap,hformula,hl⟩
                have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
                    (hz : ∀ x, tau 0 x = x) :
                    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,
                      ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by
                  have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                      (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
                    have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                      convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                        ext z <;> simp [ContinuousLinearMap.inr]
                    exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
                  have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
                    simp_rw [he]
                    exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
                  have hnorm : Continuous (fun p : ℝ × E2 =>
                      ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=
                    (hf.sub continuous_const).norm
                  apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually
                  intro x hx
                  apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const
                  have hz' : tau 0 = id := funext hz
                  simp [hz']
              
                dsimp only
                let τ : ℝ → E2 → E2 := fun s x =>
                  (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                have hg := hgeometry η hη htan
                have hz : ∀ x, τ 0 x = x := hg.1
                have hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hg.2.2.1
                have hclose := huniform τ hc hz
                filter_upwards [hg.2.2.2,hclose] with s hs hd
                refine hL2 (τ s) (hc.comp (contDiff_const.prodMk contDiff_id)) hs.1 ?_ f d hH1
                intro x hx
                let D := fderiv ℝ (τ s) x
                have hinj : Injective D := by
                  apply (LinearMap.ker_eq_bot).mp
                  apply LinearMap.ker_eq_bot'.mpr
                  intro v hv
                  change D v = 0 at hv
                  have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]
                  have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v
                  rw [he,norm_neg] at hn
                  have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := (hd x hx).trans (by norm_num)
                  have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
                  exact norm_eq_zero.mp hz
                exact fun he => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp he) (LinearMap.ker_eq_bot.mpr hinj)
              have hgeometry (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
                  (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
                  let τ := fun (s : ℝ) (x : E2) =>
                    (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                  let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                    (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                  let α := fun s t => t+Real.arctan (s*k t)
                  (∀ x, τ 0 x = x) ∧
                  (∀ x, HasDerivAt (fun s => τ s x) (η x) 0) ∧
                  ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) ∧
                  (∀ᶠ s in 𝓝 (0:ℝ),
                    BijOn (τ s) (disc 1) (disc 1) ∧
                    BijOn (τ s) (closedDisc 1) (closedDisc 1) ∧
                    StrictMono (α s) ∧ Continuous (α s) ∧
                    (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi) ∧
                    (∀ t, τ s (unitCircleParameter t) = unitCircleParameter (α s t)) ∧
                    (∀ x ∈ closedDisc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                      (e : E2 → E2) = τ s ∧ x ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (τ s x))) := by
                have hnormalized (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
                    (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
                    let tau : ℝ → E2 → E2 := fun s x =>
                      (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x)
                    (∀ x, tau 0 x = x) ∧
                    (∀ x, HasDerivAt (fun s => tau s x) (η x) 0) ∧
                    ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2) ∧
                    (∀ s x, ‖x‖ = 1 → ‖tau s x‖ = 1) := by
                  dsimp only
                  have hpos (s : ℝ) (x : E2) : 0 < 1 + s^2 * ‖η x‖^2 := by positivity
                  refine ⟨fun x => by simp, ?_, ?_, ?_⟩
                  · intro x
                    have ha : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s^2 * ‖η x‖^2)) 0 0 := by
                      convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖η x‖^2)).const_add 1 |>.sqrt (by simp) using 1 <;> norm_num
                    have hb : HasDerivAt (fun s : ℝ => x + s • η x) (η x) 0 := by
                      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add x
                    convert (ha.inv (by simp)).smul hb using 1 <;> norm_num
                  · have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖η p.2‖^2) :=
                      (hη.comp contDiff_snd).norm_sq (𝕜 := ℝ)
                    have hd : ContDiff ℝ ∞ (fun p : ℝ × E2 => Real.sqrt (1 + p.1^2 * ‖η p.2‖^2)) :=
                      (contDiff_const.add ((contDiff_fst.pow 2).mul hi)).sqrt (fun p => (hpos p.1 p.2).ne')
                    exact (hd.inv (fun p => (Real.sqrt_pos.mpr (hpos p.1 p.2)).ne')).smul
                      (contDiff_snd.add (contDiff_fst.smul (hη.comp contDiff_snd)))
                  · intro s x hx
                    have ht : inner ℝ x (η x) = 0 := by
                      rw [real_inner_comm]
                      exact htan x hx
                    have hn : ‖x + s • η x‖^2 = 1 + s^2 * ‖η x‖^2 := by
                      rw [norm_add_sq_real, real_inner_smul_right, ht,hx,norm_smul]
                      simp [mul_pow,sq_abs]
                    have he : ‖x + s • η x‖ = Real.sqrt (1 + s^2 * ‖η x‖^2) := by
                      rw [← hn,Real.sqrt_sq (norm_nonneg _)]
                    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.sqrt_pos.mpr (hpos s x)),he]
                    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos s x)).ne'
                have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)
                    (f : E2 → E2) (d : Fin 2 → E2 → E2) :
                    (fun x => f (tau 0 x)) = f ∧
                    (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                      (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by
                  have hz : tau 0 = id := funext hzero
                  refine ⟨by simp [hz],?_⟩
                  funext i x
                  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                  funext j
                  simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
                    Fin.sum_univ_two,EuclideanSpace.single]
                have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
                    (hz : ∀ x, tau 0 x = x) :
                    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,
                      ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by
                  have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                      (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
                    have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                      convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                        ext z <;> simp [ContinuousLinearMap.inr]
                    exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
                  have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
                    simp_rw [he]
                    exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
                  have hnorm : Continuous (fun p : ℝ × E2 =>
                      ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=
                    (hf.sub continuous_const).norm
                  apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually
                  intro x hx
                  apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const
                  have hz' : tau 0 = id := funext hz
                  simp [hz']
                have hinjective (tau : E2 → E2) (hc : ContDiff ℝ ∞ tau)
                    (hd : ∀ x ∈ closedDisc 1,
                      ‖fderiv ℝ tau x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ)) :
                    InjOn tau (closedDisc 1) := by
                  have hf := hc.differentiable (by simp)
                  have hl : LipschitzOnWith (1/2 : ℝ≥0) (fun x => tau x - x) (closedDisc 1) := by
                    apply (convex_closedBall (0 : E2) 1).lipschitzOnWith_of_nnnorm_fderiv_le
                      (fun x _ => (hf x).sub differentiableAt_id)
                    intro x hx
                    rw [fderiv_sub (hf x) differentiableAt_id, fderiv_id]
                    exact_mod_cast (hd x hx).le
                  intro x hx y hy hxy
                  have hb := hl.dist_le_mul x hx y hy
                  have he : (tau x - x) - (tau y - y) = y-x := by rw [hxy, sub_sub_sub_cancel_left]
                  rw [dist_eq_norm,he,norm_sub_rev] at hb
                  change ‖x-y‖ ≤ (1/2 : ℝ) * dist x y at hb
                  rw [← dist_eq_norm] at hb
                  exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])
                have hangle (η : E2 → E2)
                    (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) (s t : ℝ) :
                    let x := unitCircleParameter t
                    let k := x 0 * η x 1 - x 1 * η x 0
                    (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x) =
                      unitCircleParameter (t + Real.arctan (s*k)) := by
                  dsimp only
                  let x := unitCircleParameter t
                  let k := x 0 * η x 1 - x 1 * η x 0
                  have hc : (x 0)^2 + (x 1)^2 = 1 := by
                    change (Real.cos t)^2 + (Real.sin t)^2 = 1
                    exact Real.cos_sq_add_sin_sq t
                  have hnorm : ‖x‖ = 1 := by
                    have hn : ‖x‖^2 = 1 := by
                      calc
                        ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
                        _ = 1 := by
                          simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two] using hc
                    nlinarith [norm_nonneg x]
                  have ht : η x 0 * x 0 + η x 1 * x 1 = 0 := by
                    simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm] using htan x hnorm
                  have h0 : η x 0 = -k * x 1 := by
                    dsimp only [k]
                    linear_combination -(η x 0)*hc + x 0*ht
                  have h1 : η x 1 = k * x 0 := by
                    dsimp only [k]
                    linear_combination -(η x 1)*hc + x 1*ht
                  have hn : ‖η x‖^2 = k^2 := by
                    rw [← real_inner_self_eq_norm_sq]
                    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                    rw [h0,h1]
                    nlinarith [sq_nonneg k]
                  change (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x) = _
                  rw [hn]
                  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                  funext j
                  fin_cases j
                  · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 0 + s*η x 0) =
                      Real.cos (t+Real.arctan (s*k))
                    rw [h0,Real.cos_add,Real.cos_arctan,Real.sin_arctan]
                    change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.cos t + s*(-k*Real.sin t)) = _
                    simp only [mul_pow,div_eq_mul_inv]
                    ring
                  · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 1 + s*η x 1) =
                      Real.sin (t+Real.arctan (s*k))
                    rw [h1,Real.sin_add,Real.cos_arctan,Real.sin_arctan]
                    change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.sin t + s*(k*Real.cos t)) = _
                    simp only [mul_pow,div_eq_mul_inv]
                    ring
                have hlift (k : ℝ → ℝ) (hk : Continuous k) (hp : Function.Periodic k (2*Real.pi)) (s : ℝ) :
                    Continuous (fun t => t + Real.arctan (s*k t)) ∧
                    (∀ t, (t+2*Real.pi) + Real.arctan (s*k (t+2*Real.pi)) =
                      (t + Real.arctan (s*k t)) + 2*Real.pi) ∧
                    Surjective (fun t => t+Real.arctan (s*k t)) := by
                  have hc : Continuous (fun t => t+Real.arctan (s*k t)) :=
                    continuous_id.add (Real.continuous_arctan.comp (continuous_const.mul hk))
                  refine ⟨hc,fun t => by rw [hp t]; ring,?_⟩
                  intro y
                  have hleft : (y-Real.pi)+Real.arctan (s*k (y-Real.pi)) ≤ y := by
                    linarith [Real.arctan_lt_pi_div_two (s*k (y-Real.pi)),Real.pi_pos]
                  have hright : y ≤ (y+Real.pi)+Real.arctan (s*k (y+Real.pi)) := by
                    linarith [Real.neg_pi_div_two_lt_arctan (s*k (y+Real.pi)),Real.pi_pos]
                  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : y-Real.pi ≤ y+Real.pi)
                    hc.continuousOn ⟨hleft,hright⟩
                  exact ⟨t,he⟩
                have hlocal (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (x : E2)
                    (hd : ‖fderiv ℝ τ x - ContinuousLinearMap.id ℝ E2‖ < 1) :
                    ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ ∧ x ∈ e.source ∧
                      ContDiffAt ℝ ∞ e.symm (τ x) := by
                  let D := fderiv ℝ τ x
                  have hinj : Injective D := by
                    apply (LinearMap.ker_eq_bot).mp
                    apply LinearMap.ker_eq_bot'.mpr
                    intro v hv
                    change D v = 0 at hv
                    have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]
                    have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v
                    rw [he,norm_neg] at hn
                    have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := hd
                    have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
                    exact norm_eq_zero.mp hz
                  have hsurj : Surjective D := LinearMap.injective_iff_surjective.mp hinj
                  let d : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective D
                    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
                  have heq : (d : E2 →L[ℝ] E2) = D := ContinuousLinearEquiv.coe_ofBijective _ _ _
                  have hf : HasFDerivAt τ (d : E2 →L[ℝ] E2) x := by
                    rw [heq]
                    exact (hc.differentiable (by simp) x).hasFDerivAt
                  let e := hc.contDiffAt.toOpenPartialHomeomorph τ hf (by simp)
                  refine ⟨e,rfl,hc.contDiffAt.mem_toOpenPartialHomeomorph_source hf (by simp),?_⟩
                  exact hc.contDiffAt.to_localInverse hf (by simp)
                have hcircle (x : E2) (hx : ‖x‖ = 1) : ∃ t : ℝ, unitCircleParameter t = x := by
                  let z : ℂ := ⟨x 0,x 1⟩
                  have hs : (x 0)^2+(x 1)^2=1 := by
                    have h := real_inner_self_eq_norm_sq x
                    rw [hx] at h
                    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two,one_mul] using h
                  have hz : ‖z‖ = 1 := by
                    have hsq : ‖z‖^2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; simpa [z,Complex.normSq_apply,pow_two] using hs
                    nlinarith [norm_nonneg z]
                  have hne : z ≠ 0 := by intro h; simp [h] at hz
                  refine ⟨Complex.arg z,?_⟩
                  apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                  funext j
                  fin_cases j
                  · change Real.cos (Complex.arg z) = x 0
                    rw [Complex.cos_arg hne,hz]
                    simp [z]
                  · change Real.sin (Complex.arg z) = x 1
                    rw [Complex.sin_arg,hz]
                    simp [z]
                have hpreserve (τ : E2 → E2) (hc : Continuous τ)
                    (hinj : InjOn τ (closedDisc 1))
                    (hsphere : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ x = y)
                    (hzero : ‖τ 0‖ < 1) : MapsTo τ (disc 1) (disc 1) := by
                  intro x hx
                  change dist (τ x) 0 < 1
                  rw [dist_zero_right]
                  by_contra hn
                  have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
                  have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
                  obtain ⟨z,hz,hze⟩ := (convex_ball (0:E2) 1).isPreconnected.intermediate_value h0 hx
                    hc.norm.continuousOn ⟨hzero.le,not_lt.mp hn⟩
                  obtain ⟨w,hw,he⟩ := hsphere (τ z) hze
                  have hz' : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz
                  have hw' : w ∈ closedDisc 1 := mem_closedBall_zero_iff.mpr hw.le
                  have hzw : z = w := hinj hz' hw' he.symm
                  have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
                  rw [hzw,hw] at hzlt
                  exact lt_irrefl _ hzlt
                have hsurjective (τ : E2 → E2) (hc : Continuous τ)
                    (hmaps : MapsTo τ (disc 1) (disc 1))
                    (hsphere : ∀ x : E2, ‖x‖ = 1 → ‖τ x‖ = 1)
                    (hlocal : ∀ x ∈ disc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                      (e : E2 → E2) = τ ∧ x ∈ e.source) :
                    SurjOn τ (disc 1) (disc 1) := by
                  have hopen : IsOpen (τ '' disc 1) := by
                    rw [isOpen_iff_mem_nhds]
                    rintro y ⟨x,hx,rfl⟩
                    obtain ⟨e,he,hxe⟩ := hlocal x hx
                    have ho := e.isOpen_image_source_inter (s := disc 1) Metric.isOpen_ball
                    have hm : τ x ∈ e '' (e.source ∩ disc 1) := ⟨x,⟨hxe,hx⟩,by rw [he]⟩
                    exact Filter.mem_of_superset (ho.mem_nhds hm) (by
                      rintro z ⟨w,hw,rfl⟩
                      exact ⟨w,hw.2,by rw [he]⟩)
                  have hcompact : IsClosed (τ '' closedDisc 1) :=
                    ((isCompact_closedBall (0:E2) 1).image hc).isClosed
                  have hclosure : closure (τ '' disc 1) ⊆ τ '' closedDisc 1 :=
                    closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact
                  have hboundary : closure (τ '' disc 1) ∩ disc 1 ⊆ τ '' disc 1 := by
                    intro y hy
                    obtain ⟨x,hx,hxy⟩ := hclosure hy.1
                    refine ⟨x,?_,hxy⟩
                    have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
                    have hylt : ‖y‖ < 1 := mem_ball_zero_iff.mp hy.2
                    have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by
                      intro hxe
                      have := hsphere x hxe
                      rw [hxy] at this
                      linarith)
                    exact mem_ball_zero_iff.mpr hxlt
                  have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
                  exact (convex_ball (0:E2) 1).isPreconnected.subset_of_closure_inter_subset hopen
                    ⟨τ 0,hmaps h0,⟨0,h0,rfl⟩⟩ hboundary
                have hmonotone (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
                    (hp : Periodic k (2*Real.pi)) :
                    ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (fun t => t+Real.arctan (s*k t)) := by
                  have hpd : Periodic (deriv k) (2*Real.pi) := by
                    intro t
                    have he : (fun t => k (t+2*Real.pi)) = k := funext hp
                    rw [← deriv_comp_add_const k (2*Real.pi) t,he]
                  obtain ⟨C,hC,hbound⟩ := (hpd.isBounded_of_continuous (by positivity)
                    (hk.continuous_deriv (by simp))).exists_pos_norm_le
                  have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), |s| * C < (1/2:ℝ) := by
                    exact (continuousAt_id.abs.mul_const C).eventually_lt_const (by norm_num)
                  filter_upwards [hsmall] with s hs
                  apply strictMono_of_hasDerivAt_pos
                    (f' := fun t => 1 + (s*deriv k t)/(1+(s*k t)^2))
                  · intro t
                    convert (hasDerivAt_id t).add (((hk.differentiable (by simp) t).hasDerivAt.const_mul s).arctan) using 1 <;> first | rfl | ring
                  · intro t
                    have hb : |s*deriv k t| < (1/2:ℝ) := by
                      rw [abs_mul]
                      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
                        (by simpa using hbound (deriv k t) ⟨t,rfl⟩) (abs_nonneg s)) hs
                    have hd : 0 < 1+(s*k t)^2 := by positivity
                    have hl : -1 < (s*deriv k t)/(1+(s*k t)^2) := by
                      rw [lt_div_iff₀ hd]
                      have hlow := (abs_lt.mp hb).1
                      nlinarith [sq_nonneg (s*k t)]
                    linarith
                have hcoefficient (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :
                    let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                      (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                    ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by
                  dsimp only
                  have hc : ContDiff ℝ ∞ unitCircleParameter := by
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
                    apply contDiff_pi.mpr
                    intro i
                    fin_cases i
                    · simpa using Real.contDiff_cos
                    · simpa using Real.contDiff_sin
                  have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=
                    (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i
                  refine ⟨?_,?_⟩
                  · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))
                  · intro t
                    have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by
                      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                      funext i
                      fin_cases i
                      · change Real.cos (t+2*Real.pi) = Real.cos t
                        exact Real.cos_add_two_pi t
                      · change Real.sin (t+2*Real.pi) = Real.sin t
                        exact Real.sin_add_two_pi t
                    dsimp only
                    rw [hp]
                dsimp only
                let τ := fun (s : ℝ) (x : E2) =>
                  (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
                let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                  (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
                let α := fun s t => t+Real.arctan (s*k t)
                obtain ⟨hz,hvel,hc,hsp⟩ := hnormalized η hη htan
                have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc
                have hcs (s : ℝ) : ContDiff ℝ ∞ (τ s) :=
                  hc'.comp (contDiff_const.prodMk contDiff_id)
                have hu := huniform τ hc' hz
                obtain ⟨hk,hkp⟩ := hcoefficient η hη
                have hm := hmonotone k hk hkp
                have hcenter : ∀ᶠ s in 𝓝 (0:ℝ), ‖τ s 0‖ < 1 := by
                  exact (((hc'.continuous.comp (continuous_id.prodMk continuous_const)).norm).continuousAt).eventually_lt_const (by simp [τ])
                refine ⟨hz,hvel,hc',?_⟩
                filter_upwards [hu,hm,hcenter] with s hs hms hzs
                have hi := hinjective (τ s) (hcs s) hs
                obtain ⟨hac,hap,has⟩ := hlift k hk.continuous hkp s
                have hformula (t : ℝ) : τ s (unitCircleParameter t) = unitCircleParameter (α s t) :=
                  hangle η htan s t
                have honto : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ s x = y := by
                  intro y hy
                  obtain ⟨t,ht⟩ := hcircle y hy
                  obtain ⟨u,hu⟩ := has t
                  refine ⟨unitCircleParameter u,?_,?_⟩
                  · have hh := real_inner_self_eq_norm_sq (unitCircleParameter u)
                    have hsq : ‖unitCircleParameter u‖^2 = 1 := by
                      calc
                        _ = inner ℝ (unitCircleParameter u) (unitCircleParameter u) := hh.symm
                        _ = 1 := by
                          simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                          change Real.cos u * Real.cos u + Real.sin u * Real.sin u = 1
                          nlinarith [Real.cos_sq_add_sin_sq u]
                    nlinarith [norm_nonneg (unitCircleParameter u)]
                  · rw [hformula]
                    change unitCircleParameter (u+Real.arctan (s*k u)) = y
                    dsimp only at hu
                    rw [hu,ht]
                have hmap := hpreserve (τ s) (hcs s).continuous hi honto hzs
                have hl (x : E2) (hx : x ∈ closedDisc 1) :
                    ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ s ∧ x ∈ e.source ∧
                      ContDiffAt ℝ ∞ e.symm (τ s x) :=
                  hlocal (τ s) (hcs s) x (lt_trans (hs x hx) (by norm_num))
                have hsurj := hsurjective (τ s) (hcs s).continuous hmap (hsp s) (fun x hx => by
                  obtain ⟨e,he,hx,hd⟩ := hl x (Metric.ball_subset_closedBall hx)
                  exact ⟨e,he,hx⟩)
                have hmapclosed : MapsTo (τ s) (closedDisc 1) (closedDisc 1) := by
                  intro x hx
                  have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
                  rcases lt_or_eq_of_le hxle with hxlt | hxe
                  · exact Metric.ball_subset_closedBall (hmap (mem_ball_zero_iff.mpr hxlt))
                  · have hh : ‖τ s x‖ = 1 := hsp s x hxe
                    exact mem_closedBall_zero_iff.mpr hh.le
                have hsurjclosed : SurjOn (τ s) (closedDisc 1) (closedDisc 1) := by
                  intro y hy
                  have hyle : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
                  rcases lt_or_eq_of_le hyle with hylt | hye
                  · obtain ⟨x,hx,hxy⟩ := hsurj (mem_ball_zero_iff.mpr hylt)
                    exact ⟨x,Metric.ball_subset_closedBall hx,hxy⟩
                  · obtain ⟨x,hx,hxy⟩ := honto y hye
                    exact ⟨x,mem_closedBall_zero_iff.mpr hx.le,hxy⟩
                exact ⟨⟨hmap,hi.mono Metric.ball_subset_closedBall,hsurj⟩,
                  ⟨hmapclosed,hi,hsurjclosed⟩,hms,hac,hap,hformula,hl⟩
              have hpositive (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
                  (hz : ∀ x, tau 0 x = x) :
                  ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,
                    0 < (fderiv ℝ (tau s) x).det := by
                have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                    (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
                  have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                    convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                      ext z <;> simp [ContinuousLinearMap.inr]
                  exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
                have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
                  simp_rw [he]
                  exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
                have hdet : Continuous (fun p : ℝ × E2 => (fderiv ℝ (tau p.1) p.2).det) :=
                  ContinuousLinearMap.continuous_det.comp hf
                apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually
                intro x hx
                apply (hdet.continuousAt (x := (0,x))).eventually_const_lt
                have hz' : tau 0 = id := funext hz
                simp only [hz',fderiv_id]
                change (0:ℝ) < LinearMap.det (LinearMap.id : E2 →ₗ[ℝ] E2)
                simp
              have hinverse (τ : ℝ → E2 → E2) (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))
                  (hzero : ∀ x, τ 0 x = x) :
                  ∀ᶠ s in 𝓝 (0:ℝ), ∃ ρ : E2 → E2, ContDiff ℝ ∞ ρ ∧
                    ∀ x ∈ Metric.ball (0:E2) 2, ρ (τ s x) = x := by
                have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
                    (hz : ∀ x, tau 0 x = x) :
                    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ Metric.closedBall (0:E2) 3,
                      ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by
                  have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                      (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
                    have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                      convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                        ext z <;> simp [ContinuousLinearMap.inr]
                    exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
                  have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
                    simp_rw [he]
                    exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
                  have hnorm : Continuous (fun p : ℝ × E2 =>
                      ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=
                    (hf.sub continuous_const).norm
                  apply (isCompact_closedBall (0 : E2) 3).eventually_forall_of_forall_eventually
                  intro x hx
                  apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const
                  have hz' : tau 0 = id := funext hz
                  simp [hz']
            
                let φ : ContDiffBump (0:E2) := ⟨2,3,by norm_num,by norm_num⟩
                let F : ℝ → E2 → E2 := fun s x => x + φ x • (τ s x - x)
                have hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) :=
                  contDiff_snd.add ((φ.contDiff.comp contDiff_snd).smul (hτ.sub contDiff_snd))
                have hFzero (x : E2) : F 0 x = x := by simp [F,hzero]
                filter_upwards [huniform F hF hFzero] with s hs
                have hFs : ContDiff ℝ ∞ (F s) := hF.comp (contDiff_const.prodMk contDiff_id)
                have hbound (x : E2) : ‖fderiv ℝ (F s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2:ℝ) := by
                  by_cases hx : x ∈ Metric.closedBall (0:E2) 3
                  · exact hs x hx
                  · have he : F s =ᶠ[𝓝 x] id := by
                      have hn : {y : E2 | y ∉ Metric.closedBall (0:E2) 3} ∈ 𝓝 x :=
                        Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx
                      filter_upwards [hn] with y hy
                      have hφ : φ y = 0 := by
                        apply φ.zero_of_le_dist
                        change 3 ≤ dist y 0
                        exact le_of_lt (lt_of_not_ge hy)
                      simp [F,hφ]
                    rw [he.fderiv_eq, fderiv_id]
                    norm_num
                have hdiff : Differentiable ℝ (fun x => F s x - x) := hFs.differentiable (by simp) |>.sub differentiable_id
                have hLip : LipschitzOnWith (1/2:ℝ≥0) (fun x => F s x - x) univ := by
                  apply convex_univ.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hdiff x)
                  intro x hx
                  have hi : DifferentiableAt ℝ (fun y : E2 => y) x := differentiableAt_id
                  rw [fderiv_fun_sub (hFs.differentiable (by simp) x) hi, fderiv_fun_id]
                  exact_mod_cast (hbound x).le
                have happ : ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℝ E2) univ (1/2:ℝ≥0) :=
                  hLip.approximatesLinearOn (f := F s) (f' := ContinuousLinearMap.id ℝ E2)
                let e : E2 ≃ₜ E2 := ApproximatesLinearOn.toHomeomorph (F s) (f' := ContinuousLinearEquiv.refl ℝ E2) happ
                  (Or.inr (by norm_num))
                have he : (e : E2 → E2) = F s := rfl
                have hD (x : E2) : ∃ D : E2 ≃L[ℝ] E2, (D : E2 →L[ℝ] E2) = fderiv ℝ (F s) x := by
                  let A := fderiv ℝ (F s) x
                  have hinj : Injective A := by
                    apply LinearMap.ker_eq_bot.mp
                    apply LinearMap.ker_eq_bot'.mpr
                    intro v hv
                    change A v = 0 at hv
                    have hz : (A - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]
                    have hn := (A - ContinuousLinearMap.id ℝ E2).le_opNorm v
                    rw [hz,norm_neg] at hn
                    have hb : ‖A - ContinuousLinearMap.id ℝ E2‖ < 1 := lt_trans (hbound x) (by norm_num)
                    have hnv : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
                    exact norm_eq_zero.mp hnv
                  have hsurj : Surjective A := LinearMap.injective_iff_surjective.mp hinj
                  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)
                    (LinearMap.range_eq_top.mpr hsurj),ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
                choose D hDeq using hD
                have hsmooth : ContDiff ℝ ∞ (e.symm : E2 → E2) := by
                  apply e.contDiff_symm (f₀' := D)
                  · intro x
                    rw [he,hDeq x]
                    exact (hFs.differentiable (by simp) x).hasFDerivAt
                  · rw [he]; exact hFs
                refine ⟨e.symm,hsmooth,?_⟩
                intro x hx
                have hφ : φ x = 1 := φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)
                have hxF : F s x = τ s x := by simp [F,hφ]
                rw [← hxF,← he]
                exact e.symm_apply_apply x
              have hpiola (τ ρ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (hρ : ContDiff ℝ ∞ ρ)
                  (hleft : ∀ x ∈ Metric.ball (0:E2) 2, ρ (τ x) = x)
                  (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (j : Fin 2) :
                    ∃ χ : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
                      (∀ x ∈ disc 1, (fderiv ℝ τ x).det *
                        (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                         fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) =
                        fderiv ℝ ψ x (coordinateVector 2 j)) ∧
                      (∀ x ∈ closedDisc 1, ∀ k : Fin 2, (fderiv ℝ τ x).det * χ k (τ x) =
                        (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x) := by
                have hproduct (u q : E2 → ℝ) (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q) (y : E2) :
                    fderiv ℝ (fun z => fderiv ℝ u z (coordinateVector 2 1) * q z) y (coordinateVector 2 0) +
                    fderiv ℝ (fun z => -fderiv ℝ u z (coordinateVector 2 0) * q z) y (coordinateVector 2 1) =
                    fderiv ℝ u y (coordinateVector 2 1) * fderiv ℝ q y (coordinateVector 2 0) -
                    fderiv ℝ u y (coordinateVector 2 0) * fderiv ℝ q y (coordinateVector 2 1) := by
                  have hdC : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
                  have hd : Differentiable ℝ (fderiv ℝ u) := hdC.differentiable (by simp)
                  have hp (i : Fin 2) : Differentiable ℝ (fun z => fderiv ℝ u z (coordinateVector 2 i)) :=
                    hd.clm_apply (differentiable_const _)
                  have hn : DifferentiableAt ℝ (fun z => -fderiv ℝ u z (coordinateVector 2 0)) y := (hp 0 y).neg
                  rw [fderiv_fun_mul (hp 1 y) (hq.differentiable (by simp) y),
                    fderiv_fun_mul hn (hq.differentiable (by simp) y),
                    fderiv_fun_neg]
                  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
                    ContinuousLinearMap.neg_apply,smul_eq_mul]
                  rw [fderiv_clm_apply (hd y) (differentiableAt_const _),
                    fderiv_clm_apply (hd y) (differentiableAt_const _)]
                  simp only [fderiv_fun_const,ContinuousLinearMap.zero_apply,ContinuousLinearMap.add_apply,
                    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,map_zero,add_zero,zero_add]
                  have hs := ((hu.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)).eq
                    (coordinateVector 2 0) (coordinateVector 2 1)
                  simp only [Pi.zero_apply,zero_apply,map_zero,zero_add,add_zero]
                  rw [hs]
                  ring
                have halgebra (A B : E2 →L[ℝ] E2) (hBA : B.comp A = ContinuousLinearMap.id ℝ E2) :
                    A.det * (B (coordinateVector 2 1)) 1 = (A (coordinateVector 2 0)) 0 ∧
                    A.det * (-(B (coordinateVector 2 0)) 1) = (A (coordinateVector 2 0)) 1 ∧
                    A.det * (-(B (coordinateVector 2 1)) 0) = (A (coordinateVector 2 1)) 0 ∧
                    A.det * (B (coordinateVector 2 0)) 0 = (A (coordinateVector 2 1)) 1 ∧
                    A.det * ((B (coordinateVector 2 0)) 0 * (B (coordinateVector 2 1)) 1 -
                      (B (coordinateVector 2 1)) 0 * (B (coordinateVector 2 0)) 1) = 1 := by
                  have hv (v : E2) : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                    funext k
                    fin_cases k <;> simp [coordinateVector]
                  have he (j k : Fin 2) :
                      (A (coordinateVector 2 j)) 0 * (B (coordinateVector 2 0)) k +
                      (A (coordinateVector 2 j)) 1 * (B (coordinateVector 2 1)) k =
                      (coordinateVector 2 j) k := by
                    have h := congrArg (fun L : E2 →L[ℝ] E2 => L (coordinateVector 2 j) k) hBA
                    change B (A (coordinateVector 2 j)) k = (coordinateVector 2 j) k at h
                    rw [hv (A (coordinateVector 2 j))] at h
                    simpa [map_add,map_smul] using h
                  have h00 := he 0 0
                  have h01 := he 1 0
                  have h10 := he 0 1
                  have h11 := he 1 1
                  simp [coordinateVector] at h00 h01 h10 h11
                  have hdet (L : E2 →L[ℝ] E2) : L.det =
                      (L (coordinateVector 2 0)) 0 * (L (coordinateVector 2 1)) 1 -
                      (L (coordinateVector 2 1)) 0 * (L (coordinateVector 2 0)) 1 := by
                    change LinearMap.det L.toLinearMap = _
                    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,Matrix.det_fin_two]
                    rfl
                  have hd : A.det * B.det = 1 := by
                    have he : B.toLinearMap.comp A.toLinearMap = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap hBA
                    have h := congrArg LinearMap.det he
                    rw [LinearMap.det_comp,LinearMap.det_id] at h
                    simpa [mul_comm] using h
                  refine ⟨?_,?_,?_,?_,?_⟩
                  · rw [hdet A]
                    simp only [coordinateVector]
                    linear_combination (A (EuclideanSpace.single 0 1)) 0 * h11 - (A (EuclideanSpace.single 1 1)) 0 * h10
                  · rw [hdet A]
                    simp only [coordinateVector]
                    linear_combination (A (EuclideanSpace.single 0 1)) 1 * h11 - (A (EuclideanSpace.single 1 1)) 1 * h10
                  · rw [hdet A]
                    simp only [coordinateVector]
                    linear_combination (A (EuclideanSpace.single 1 1)) 0 * h00 - (A (EuclideanSpace.single 0 1)) 0 * h01
                  · rw [hdet A]
                    simp only [coordinateVector]
                    linear_combination (A (EuclideanSpace.single 1 1)) 1 * h00 - (A (EuclideanSpace.single 0 1)) 1 * h01
                  · rw [← hdet B]
                    exact hd
            
                have hin (x : E2) (hx : x ∈ closedDisc 1) : x ∈ Metric.ball (0:E2) 2 :=
                  lt_of_le_of_lt (show dist x 0 ≤ 1 from hx) (by norm_num)
                have hBA (x : E2) (hx : x ∈ closedDisc 1) :
                    (fderiv ℝ ρ (τ x)).comp (fderiv ℝ τ x) = ContinuousLinearMap.id ℝ E2 := by
                  have he : (ρ ∘ τ) =ᶠ[𝓝 x] id := by
                    filter_upwards [Metric.isOpen_ball.mem_nhds (hin x hx)] with z hz
                    exact hleft z hz
                  have hd := ((hρ.differentiable (by simp) (τ x)).hasFDerivAt.comp x
                    (hτ.differentiable (by simp) x).hasFDerivAt).fderiv
                  rw [he.fderiv_eq,fderiv_id] at hd
                  exact hd.symm
                have hu (k : Fin 2) : ContDiff ℝ ∞ (fun y => ρ y k) :=
                  (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hρ)) k
                have hc (k : Fin 2) (y : E2) :
                    fderiv ℝ (fun z => ρ z k) y = (EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ ρ y) := by
                  exact ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp y
                    (hρ.differentiable (by simp) y).hasFDerivAt).fderiv
                have hud (k l : Fin 2) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => ρ z k) y (coordinateVector 2 l)) := by
                  have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z => ρ z k)) := (hu k).fderiv_right (by simp)
                  exact hd.clm_apply contDiff_const
                have hq : ContDiff ℝ ∞ (ψ ∘ ρ) := hψ.comp hρ
                have hqjet (y : E2) (l : Fin 2) : fderiv ℝ (ψ ∘ ρ) y (coordinateVector 2 l) =
                    fderiv ℝ ψ (ρ y) (coordinateVector 2 0) * (fderiv ℝ ρ y (coordinateVector 2 l)) 0 +
                    fderiv ℝ ψ (ρ y) (coordinateVector 2 1) * (fderiv ℝ ρ y (coordinateVector 2 l)) 1 := by
                  rw [fderiv_comp y (hψ.differentiable (by simp) (ρ y)) (hρ.differentiable (by simp) y)]
                  have hv (v : E2) : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
                    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                    funext k
                    fin_cases k <;> simp [coordinateVector]
                  change fderiv ℝ ψ (ρ y) (fderiv ℝ ρ y (coordinateVector 2 l)) = _
                  rw [hv (fderiv ℝ ρ y (coordinateVector 2 l)),map_add,map_smul,map_smul]
                  simp [coordinateVector,mul_comm]
                have hcomp (k l : Fin 2) (y : E2) :
                    fderiv ℝ (fun z => ρ z k) y (coordinateVector 2 l) = (fderiv ℝ ρ y (coordinateVector 2 l)) k := by
                  rw [hc]; rfl
                fin_cases j
                · let χ : Fin 2 → E2 → ℝ := ![
                    fun y => fderiv ℝ (fun z => ρ z 1) y (coordinateVector 2 1) * (ψ ∘ ρ) y,
                    fun y => -fderiv ℝ (fun z => ρ z 1) y (coordinateVector 2 0) * (ψ ∘ ρ) y]
                  refine ⟨χ,?_,?_,?_⟩
                  · intro k
                    fin_cases k
                    · exact (hud 1 1).mul hq
                    · exact (hud 1 0).neg.mul hq
                  · intro x hx
                    change (fderiv ℝ τ x).det * (_ + _) = fderiv ℝ ψ x (coordinateVector 2 0)
                    have hp := hproduct (fun z => ρ z 1) (ψ ∘ ρ) (hu 1) hq (τ x)
                    change fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                      fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1) = _ at hp
                    rw [hp,hcomp,hcomp,hqjet,hqjet,hleft x (hin x (Metric.ball_subset_closedBall hx))]
                    have hd := (halgebra _ _ (hBA x (Metric.ball_subset_closedBall hx))).2.2.2.2
                    calc
                      _ = fderiv ℝ ψ x (coordinateVector 2 0) *
                          ((fderiv ℝ τ x).det * ((fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 0 *
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 1 -
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 0 *
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 1)) := by ring
                      _ = _ := by rw [hd,mul_one]
                  · intro x hx k
                    obtain ⟨h00,h10,h01,h11,hd⟩ := halgebra _ _ (hBA x hx)
                    fin_cases k
                    · change (fderiv ℝ τ x).det * (fderiv ℝ (fun z => ρ z 1) (τ x) (coordinateVector 2 1) * ψ (ρ (τ x))) = _
                      rw [hcomp,hleft x (hin x hx),← mul_assoc,h00]
                      rfl
                    · change (fderiv ℝ τ x).det * (-fderiv ℝ (fun z => ρ z 1) (τ x) (coordinateVector 2 0) * ψ (ρ (τ x))) = _
                      rw [hcomp,hleft x (hin x hx),← mul_assoc,h10]
                      rfl
                · let χ : Fin 2 → E2 → ℝ := ![
                    fun y => -fderiv ℝ (fun z => ρ z 0) y (coordinateVector 2 1) * (ψ ∘ ρ) y,
                    fun y => fderiv ℝ (fun z => ρ z 0) y (coordinateVector 2 0) * (ψ ∘ ρ) y]
                  refine ⟨χ,?_,?_,?_⟩
                  · intro k
                    fin_cases k
                    · exact (hud 0 1).neg.mul hq
                    · exact (hud 0 0).mul hq
                  · intro x hx
                    change (fderiv ℝ τ x).det * (_ + _) = fderiv ℝ ψ x (coordinateVector 2 1)
                    have hp := hproduct (fun z => ρ z 0) (ψ ∘ ρ) (hu 0) hq (τ x)
                    have hn (a q : E2 → ℝ) (y v : E2) :
                        fderiv ℝ (fun z => -a z * q z) y v = -fderiv ℝ (fun z => a z * q z) y v := by
                      simp_rw [neg_mul]
                      rw [fderiv_fun_neg]
                      rfl
                    have hdiv : fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                        fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1) =
                        -(fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 1) *
                            fderiv ℝ (ψ ∘ ρ) (τ x) (coordinateVector 2 0) -
                          fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 0) *
                            fderiv ℝ (ψ ∘ ρ) (τ x) (coordinateVector 2 1)) := by
                      dsimp only [χ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
                      rw [hn] at hp ⊢
                      linarith
                    rw [hdiv,hcomp,hcomp,hqjet,hqjet,hleft x (hin x (Metric.ball_subset_closedBall hx))]
                    have hd := (halgebra _ _ (hBA x (Metric.ball_subset_closedBall hx))).2.2.2.2
                    calc
                      _ = fderiv ℝ ψ x (coordinateVector 2 1) *
                          ((fderiv ℝ τ x).det * ((fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 0 *
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 1 -
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 0 *
                            (fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 1)) := by ring
                      _ = _ := by rw [hd,mul_one]
                  · intro x hx k
                    obtain ⟨h00,h10,h01,h11,hd⟩ := halgebra _ _ (hBA x hx)
                    fin_cases k
                    · change (fderiv ℝ τ x).det * (-fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 1) * ψ (ρ (τ x))) = _
                      rw [hcomp,hleft x (hin x hx),← mul_assoc,h01]
                      rfl
                    · change (fderiv ℝ τ x).det * (fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 0) * ψ (ρ (τ x))) = _
                      rw [hcomp,hleft x (hin x hx),← mul_assoc,h11]
                      rfl
              have hassemble (f : E2 → E2) (d : Fin 2 → E2 → E2)
                  (hH1 : ∀ i, H1On (disc 1) (fun x => f x i) (d i))
                  (τ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (hbij : BijOn τ (disc 1) (disc 1))
                  (hpos : ∀ x ∈ closedDisc 1, 0 < (fderiv ℝ τ x).det)
                  (htests : ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → ∀ j : Fin 2,
                    ∃ χ : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧
                      (∀ x ∈ disc 1, (fderiv ℝ τ x).det *
                        (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                         fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) = fderiv ℝ ψ x (coordinateVector 2 j)) ∧
                      (∀ x ∈ closedDisc 1, ∀ k : Fin 2, (fderiv ℝ τ x).det * χ k (τ x) =
                        (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x)) :
                  let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                    (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))
                  (∀ i, MemLp (fun x => f (τ x) i) 2 (volume.restrict (disc 1)) ∧
                    MemLp (dt i) 2 (volume.restrict (disc 1))) →
                  ∀ i, H1On (disc 1) (fun x => f (τ x) i) (dt i) := by
                have hcut (τ : E2 → E2) (hτ : Continuous τ) (hb : BijOn τ (disc 1) (disc 1))
                    (hd : ∀ x ∈ disc 1, (fderiv ℝ τ x).det ≠ 0)
                    (ψ : E2 → ℝ) (hψ : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ disc 1)
                    (j : Fin 2) (χ : Fin 2 → E2 → ℝ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k))
                    (hjet : ∀ x ∈ disc 1, ∀ k : Fin 2, (fderiv ℝ τ x).det * χ k (τ x) =
                      (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x) :
                    ∃ χc : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χc k)) ∧
                      (∀ k, HasCompactSupport (χc k)) ∧ (∀ k, tsupport (χc k) ⊆ disc 1) ∧
                      (∀ k, EqOn (χc k) (χ k) (disc 1)) := by
                  let K := τ '' tsupport ψ
                  have hK : IsCompact K := hψ.isCompact.image hτ
                  have hsub : K ⊆ disc 1 := Set.image_subset_iff.mpr (fun x hx => hb.mapsTo (hsupp hx))
                  obtain ⟨r,hr,hrK⟩ := exists_pos_lt_subset_ball (by norm_num : (0:ℝ) < 1) hK.isClosed hsub
                  let κ : ContDiffBump (0:E2) := ⟨r,(r+1)/2,hr.1,by linarith [hr.2]⟩
                  have hsκ : tsupport (κ : E2 → ℝ) ⊆ disc 1 := by
                    rw [κ.tsupport_eq]
                    intro x hx
                    exact lt_of_le_of_lt (show dist x 0 ≤ (r+1)/2 from hx) (by linarith [hr.2])
                  refine ⟨fun k x => κ x * χ k x,fun k => κ.contDiff.mul (hχ k),?_,?_,?_⟩
                  · intro k
                    exact κ.hasCompactSupport.mul_right
                  · intro k
                    exact tsupport_mul_subset_left.trans hsκ
                  · intro k y hy
                    by_cases hyK : y ∈ K
                    · dsimp only
                      rw [κ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hrK hyK)),one_mul]
                    · obtain ⟨x,hx,hxy⟩ := hb.surjOn hy
                      have hxK : x ∉ tsupport ψ := fun h => hyK ⟨x,h,hxy⟩
                      have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxK
                      have he := hjet x hx k
                      rw [hz,mul_zero,hxy] at he
                      have hc : χ k y = 0 := (mul_eq_zero.mp he).resolve_left (hd x hx)
                      dsimp only
                      rw [hc,mul_zero]
                dsimp only
                intro hLp i
                have hprod (v q : E2 → ℝ) (hv : MemLp v 2 (volume.restrict (disc 1)))
                    (hq : Continuous q) (hcompact : HasCompactSupport q) :
                    IntegrableOn (fun x => v x * q x) (disc 1) := by
                  exact (hv.locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport hq hcompact
                refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict ((hLp i).1.locallyIntegrable (by norm_num)),
                  locallyIntegrableOn_of_locallyIntegrable_restrict ((hLp i).2.locallyIntegrable (by norm_num)),?_⟩,
                  (hLp i).1,(hLp i).2⟩
                intro ψ hψ hcompact hsupp j
                obtain ⟨χ,hχ,hdiv,hjet⟩ := htests ψ hψ j
                obtain ⟨χc,hχc,hcompactχ,hsuppχ,heqχ⟩ := hcut τ hτ.continuous hbij
                  (fun x hx => (hpos x (Metric.ball_subset_closedBall hx)).ne') ψ hcompact hsupp j χ hχ
                  (fun x hx k => hjet x (Metric.ball_subset_closedBall hx) k)
                have hDχ (x : E2) (hx : x ∈ disc 1) (k : Fin 2) :
                    fderiv ℝ (χc k) x = fderiv ℝ (χ k) x := by
                  apply Filter.EventuallyEq.fderiv_eq
                  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
                  exact heqχ k hy
                have h0 := (hH1 i).1.2.2 (χc 0) (hχc 0) (hcompactχ 0) (hsuppχ 0) 0
                have h1 := (hH1 i).1.2.2 (χc 1) (hχc 1) (hcompactχ 1) (hsuppχ 1) 1
                have hfa (k : Fin 2) : IntegrableOn
                    (fun x => f x i * fderiv ℝ (χc k) x (coordinateVector 2 k)) (disc 1) :=
                  hprod _ _ (hH1 i).2.1 ((hχc k).continuous_fderiv (by simp) |>.clm_apply continuous_const)
                    ((hcompactχ k).fderiv_apply (𝕜 := ℝ) (coordinateVector 2 k))
                have hdb (k : Fin 2) : IntegrableOn (fun x => d i x k * χc k x) (disc 1) :=
                  hprod _ _ ((hH1 i).2.2.eval_piLp k) (hχc k).continuous (hcompactχ k)
                let L := fun x => f x i * (fderiv ℝ (χc 0) x (coordinateVector 2 0) +
                  fderiv ℝ (χc 1) x (coordinateVector 2 1)) + d i x 0 * χc 0 x + d i x 1 * χc 1 x
                have hLeq : L = fun x =>
                    (f x i * fderiv ℝ (χc 0) x (coordinateVector 2 0) + d i x 0 * χc 0 x) +
                    (f x i * fderiv ℝ (χc 1) x (coordinateVector 2 1) + d i x 1 * χc 1 x) := by
                  funext x; dsimp only [L]; ring
                have hL : IntegrableOn L (disc 1) := by
                  rw [hLeq]; exact ((hfa 0).add (hdb 0)).add ((hfa 1).add (hdb 1))
                have hc0 : IntegrableOn (fun x => f x i * fderiv ℝ (χc 0) x (coordinateVector 2 0) + d i x 0 * χc 0 x) (disc 1) := (hfa 0).add (hdb 0)
                have hc1 : IntegrableOn (fun x => f x i * fderiv ℝ (χc 1) x (coordinateVector 2 1) + d i x 1 * χc 1 x) (disc 1) := (hfa 1).add (hdb 1)
                dsimp only at h0 h1
                have hLzero : (∫ x in disc 1, L x) = 0 := by
                  rw [hLeq]
                  change (∫ x in disc 1, ((f x i * fderiv ℝ (χc 0) x (coordinateVector 2 0) + d i x 0 * χc 0 x) + (f x i * fderiv ℝ (χc 1) x (coordinateVector 2 1) + d i x 1 * χc 1 x))) = 0
                  rw [integral_add hc0 hc1,
                    integral_add (hfa 0) (hdb 0),integral_add (hfa 1) (hdb 1),h0,h1]
                  ring
                let G := fun x => f (τ x) i * fderiv ℝ ψ x (coordinateVector 2 j) +
                  inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)) * ψ x
                have hidentity (x : E2) (hx : x ∈ disc 1) :
                    |(fderiv ℝ τ x).det| * L (τ x) = G x := by
                  dsimp only [L,G]
                  rw [hDχ (τ x) (hbij.mapsTo hx) 0,hDχ (τ x) (hbij.mapsTo hx) 1,
                    heqχ 0 (hbij.mapsTo hx),heqχ 1 (hbij.mapsTo hx),abs_of_pos (hpos x (Metric.ball_subset_closedBall hx))]
                  rw [show (fderiv ℝ τ x).det *
                      (f (τ x) i * (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                        fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) +
                        d i (τ x) 0 * χ 0 (τ x) + d i (τ x) 1 * χ 1 (τ x)) =
                      f (τ x) i * ((fderiv ℝ τ x).det *
                        (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +
                         fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1))) +
                        d i (τ x) 0 * ((fderiv ℝ τ x).det * χ 0 (τ x)) +
                        d i (τ x) 1 * ((fderiv ℝ τ x).det * χ 1 (τ x)) by ring]
                  rw [hdiv x hx,hjet x (Metric.ball_subset_closedBall hx) 0,hjet x (Metric.ball_subset_closedBall hx) 1]
                  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                  ring
                have hd : ∀ x ∈ disc 1, HasFDerivWithinAt τ (fderiv ℝ τ x) (disc 1) x :=
                  fun x _ => (hτ.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt
                have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
                  (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet) hd hbij.injOn L
                rw [hbij.image_eq] at hchange
                have hLG : (∫ x in disc 1, L x) = ∫ x in disc 1, G x :=
                  hchange.trans (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hidentity)
                have hGa := hprod _ _ (hLp i).1
                  (hψ.continuous_fderiv (by simp) |>.clm_apply continuous_const)
                  (hcompact.fderiv_apply (𝕜 := ℝ) (coordinateVector 2 j))
                have hGb := hprod _ _ ((hLp i).2.eval_piLp j) hψ.continuous hcompact
                change IntegrableOn (fun x => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)) * ψ x) (disc 1) at hGb
                have hGzero : (∫ x in disc 1, G x) = 0 := hLG.symm.trans hLzero
                dsimp only [G] at hGzero
                change (∫ x in disc 1, f (τ x) i * fderiv ℝ ψ x (coordinateVector 2 j) + inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)) * ψ x) = 0 at hGzero
                rw [integral_add hGa hGb] at hGzero
                exact eq_neg_of_add_eq_zero_left hGzero
              intro f d hH1 η hη htan
              dsimp only
              let τ : ℝ → E2 → E2 := fun s x =>
                (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
              obtain ⟨hz,hvel,hjoint,hgeom⟩ := hgeometry η hη htan
              have hLpall := hLp f d hH1 η hη htan
              filter_upwards [hgeom,hpositive τ hjoint hz,hinverse τ hjoint hz,hLpall] with s hg hp hi hL
              obtain ⟨ρ,hρ,hleft⟩ := hi
              have hτ : ContDiff ℝ ∞ (τ s) := hjoint.comp (contDiff_const.prodMk contDiff_id)
              exact hassemble f d hH1 (τ s) hτ hg.1 hp
                (fun ψ hψ j => hpiola (τ s) ρ hτ hρ hleft ψ hψ j)
                (fun i => ⟨(hL i).1,(hL i).2.1⟩))
      have nativeGreen :
      ∀ (f : E2 → E2) (d : Fin 2 → E2 → E2)
          (theta : ℝ → ℝ) (orientation : ℝ),
          (∀ i, H1On (disc 1) (fun x => f x i) (d i)) →
          WeakMonotoneBoundaryLift Ω theta orientation →
          HasGreenBoundaryTrace f d (liftedBoundaryValue Ω theta) →
          ∀ η : E2 → E2, ContDiff ℝ ∞ η →
          (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) →
        let τ := fun (s : ℝ) (x : E2) => (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
        let fs := fun s x => f (τ s x)
        let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
        let α := fun (s : ℝ) (t : ℝ) => t + Real.arctan (s *
          ((unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
           (unitCircleParameter t) 1 * η (unitCircleParameter t) 0))
        ∀ᶠ s in 𝓝 (0:ℝ), HasGreenBoundaryTrace (fs s) (ds s)
          (liftedBoundaryValue Ω (theta ∘ α s)) :=
        by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  set_option maxHeartbeats 0 in\n    exact (by\n      classical\n      have circle_def (t : ℝ) : unitCircleParameter t = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos t,Real.sin t] := rfl\n      have disc_def (r : ℝ) : disc r = Metric.ball (0:E2) r := rfl\n      have closed_def (r : ℝ) : closedDisc r = Metric.closedBall (0:E2) r := rfl\n      have ball_mem_def (x y : E2) (r : ℝ) : (y ∈ Metric.ball x r) = (dist y x < r) := propext Metric.mem_ball\n      have closed_mem_def (x y : E2) (r : ℝ) : (y ∈ Metric.closedBall x r) = (dist y x ≤ r) := propext Metric.mem_closedBall\n      have hgeometry (η : E2 → E2) (hη : ContDiff ℝ ∞ η)\n          (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :\n          let τ := fun (s : ℝ) (x : E2) =>\n            (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)\n          let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n            (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n          let α := fun s t => t+Real.arctan (s*k t)\n          (∀ x, τ 0 x = x) ∧\n          (∀ x, HasDerivAt (fun s => τ s x) (η x) 0) ∧\n          ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) ∧\n          (∀ᶠ s in 𝓝 (0:ℝ),\n            BijOn (τ s) (disc 1) (disc 1) ∧\n            BijOn (τ s) (closedDisc 1) (closedDisc 1) ∧\n            StrictMono (α s) ∧ Continuous (α s) ∧\n            (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi) ∧\n            (∀ t, τ s (unitCircleParameter t) = unitCircleParameter (α s t)) ∧\n            (∀ x ∈ closedDisc 1, ∃ e : OpenPartialHomeomorph E2 E2,\n              (e : E2 → E2) = τ s ∧ x ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (τ s x))) := by\n        have hnormalized (η : E2 → E2) (hη : ContDiff ℝ ∞ η)\n            (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :\n            let tau : ℝ → E2 → E2 := fun s x =>\n              (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x)\n            (∀ x, tau 0 x = x) ∧\n            (∀ x, HasDerivAt (fun s => tau s x) (η x) 0) ∧\n            ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2) ∧\n            (∀ s x, ‖x‖ = 1 → ‖tau s x‖ = 1) := by\n          dsimp only\n          have hpos (s : ℝ) (x : E2) : 0 < 1 + s^2 * ‖η x‖^2 := by positivity\n          refine ⟨fun x => by simp, ?_, ?_, ?_⟩\n          · intro x\n            have ha : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s^2 * ‖η x‖^2)) 0 0 := by\n              convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖η x‖^2)).const_add 1 |>.sqrt (by simp) using 1 <;> norm_num\n            have hb : HasDerivAt (fun s : ℝ => x + s • η x) (η x) 0 := by\n              simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add x\n            convert (ha.inv (by simp)).smul hb using 1 <;> norm_num\n          · have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖η p.2‖^2) :=\n              (hη.comp contDiff_snd).norm_sq (𝕜 := ℝ)\n            have hd : ContDiff ℝ ∞ (fun p : ℝ × E2 => Real.sqrt (1 + p.1^2 * ‖η p.2‖^2)) :=\n              (contDiff_const.add ((contDiff_fst.pow 2).mul hi)).sqrt (fun p => (hpos p.1 p.2).ne')\n            exact (hd.inv (fun p => (Real.sqrt_pos.mpr (hpos p.1 p.2)).ne')).smul\n              (contDiff_snd.add (contDiff_fst.smul (hη.comp contDiff_snd)))\n          · intro s x hx\n            have ht : inner ℝ x (η x) = 0 := by\n              rw [real_inner_comm]\n              exact htan x hx\n            have hn : ‖x + s • η x‖^2 = 1 + s^2 * ‖η x‖^2 := by\n              rw [norm_add_sq_real, real_inner_smul_right, ht,hx,norm_smul]\n              simp [mul_pow,sq_abs]\n            have he : ‖x + s • η x‖ = Real.sqrt (1 + s^2 * ‖η x‖^2) := by\n              rw [← hn,Real.sqrt_sq (norm_nonneg _)]\n            rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.sqrt_pos.mpr (hpos s x)),he]\n            exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos s x)).ne'\n        have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)\n            (f : E2 → E2) (d : Fin 2 → E2 → E2) :\n            (fun x => f (tau 0 x)) = f ∧\n            (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n              (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by\n          have hz : tau 0 = id := funext hzero\n          refine ⟨by simp [hz],?_⟩\n          funext i x\n          apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n          funext j\n          simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,\n            Fin.sum_univ_two,EuclideanSpace.single]\n        have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n            (hz : ∀ x, tau 0 x = x) :\n            ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,\n              ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by\n          have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n              (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n            have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n              convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n                ext z <;> simp [ContinuousLinearMap.inr]\n            exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n          have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n            simp_rw [he]\n            exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n          have hnorm : Continuous (fun p : ℝ × E2 =>\n              ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=\n            (hf.sub continuous_const).norm\n          apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually\n          intro x hx\n          apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const\n          have hz' : tau 0 = id := funext hz\n          simp [hz']\n        have hinjective (tau : E2 → E2) (hc : ContDiff ℝ ∞ tau)\n            (hd : ∀ x ∈ closedDisc 1,\n              ‖fderiv ℝ tau x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ)) :\n            InjOn tau (closedDisc 1) := by\n          have hf := hc.differentiable (by simp)\n          have hl : LipschitzOnWith (1/2 : ℝ≥0) (fun x => tau x - x) (closedDisc 1) := by\n            apply (convex_closedBall (0 : E2) 1).lipschitzOnWith_of_nnnorm_fderiv_le\n              (fun x _ => (hf x).sub differentiableAt_id)\n            intro x hx\n            rw [fderiv_sub (hf x) differentiableAt_id, fderiv_id]\n            exact_mod_cast (hd x hx).le\n          intro x hx y hy hxy\n          have hb := hl.dist_le_mul x hx y hy\n          have he : (tau x - x) - (tau y - y) = y-x := by rw [hxy,sub_sub_sub_cancel_left]\n          rw [dist_eq_norm,he,norm_sub_rev] at hb\n          change ‖x-y‖ ≤ (1/2 : ℝ) * dist x y at hb\n          rw [← dist_eq_norm] at hb\n          exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])\n        have hangle (η : E2 → E2)\n            (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) (s t : ℝ) :\n            let x := unitCircleParameter t\n            let k := x 0 * η x 1 - x 1 * η x 0\n            (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x) =\n              unitCircleParameter (t + Real.arctan (s*k)) := by\n          dsimp only\n          let x := unitCircleParameter t\n          let k := x 0 * η x 1 - x 1 * η x 0\n          have hc : (x 0)^2 + (x 1)^2 = 1 := by\n            simpa [x,circle_def] using Real.cos_sq_add_sin_sq t\n          have hnorm : ‖x‖ = 1 := by\n            have hn : ‖x‖^2 = 1 := by\n              calc\n                ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm\n                _ = 1 := by\n                  simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two] using hc\n            nlinarith [norm_nonneg x]\n          have ht : η x 0 * x 0 + η x 1 * x 1 = 0 := by\n            simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm] using htan x hnorm\n          have h0 : η x 0 = -k * x 1 := by\n            dsimp only [k]\n            linear_combination -(η x 0)*hc + x 0*ht\n          have h1 : η x 1 = k * x 0 := by\n            dsimp only [k]\n            linear_combination -(η x 1)*hc + x 1*ht\n          have hn : ‖η x‖^2 = k^2 := by\n            rw [← real_inner_self_eq_norm_sq]\n            simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]\n            rw [h0,h1]\n            nlinarith [sq_nonneg k]\n          change (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x) = _\n          rw [hn]\n          apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n          funext j\n          fin_cases j\n          · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 0 + s*η x 0) =\n              Real.cos (t+Real.arctan (s*k))\n            rw [h0,Real.cos_add,Real.cos_arctan,Real.sin_arctan]\n            change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.cos t + s*(-k*Real.sin t)) = _\n            simp only [mul_pow,div_eq_mul_inv]\n            ring\n          · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 1 + s*η x 1) =\n              Real.sin (t+Real.arctan (s*k))\n            rw [h1,Real.sin_add,Real.cos_arctan,Real.sin_arctan]\n            change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.sin t + s*(k*Real.cos t)) = _\n            simp only [mul_pow,div_eq_mul_inv]\n            ring\n        have hlift (k : ℝ → ℝ) (hk : Continuous k) (hp : Function.Periodic k (2*Real.pi)) (s : ℝ) :\n            Continuous (fun t => t + Real.arctan (s*k t)) ∧\n            (∀ t, (t+2*Real.pi) + Real.arctan (s*k (t+2*Real.pi)) =\n              (t + Real.arctan (s*k t)) + 2*Real.pi) ∧\n            Surjective (fun t => t+Real.arctan (s*k t)) := by\n          have hc : Continuous (fun t => t+Real.arctan (s*k t)) :=\n            continuous_id.add (Real.continuous_arctan.comp (continuous_const.mul hk))\n          refine ⟨hc,fun t => by rw [hp t]; ring,?_⟩\n          intro y\n          have hleft : (y-Real.pi)+Real.arctan (s*k (y-Real.pi)) ≤ y := by\n            linarith [Real.arctan_lt_pi_div_two (s*k (y-Real.pi)),Real.pi_pos]\n          have hright : y ≤ (y+Real.pi)+Real.arctan (s*k (y+Real.pi)) := by\n            linarith [Real.neg_pi_div_two_lt_arctan (s*k (y+Real.pi)),Real.pi_pos]\n          obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : y-Real.pi ≤ y+Real.pi)\n            hc.continuousOn ⟨hleft,hright⟩\n          exact ⟨t,he⟩\n        have hlocal (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (x : E2)\n            (hd : ‖fderiv ℝ τ x - ContinuousLinearMap.id ℝ E2‖ < 1) :\n            ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ ∧ x ∈ e.source ∧\n              ContDiffAt ℝ ∞ e.symm (τ x) := by\n          let D := fderiv ℝ τ x\n          have hinj : Injective D := by\n            apply (LinearMap.ker_eq_bot).mp\n            apply LinearMap.ker_eq_bot'.mpr\n            intro v hv\n            change D v = 0 at hv\n            have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]\n            have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v\n            rw [he,norm_neg] at hn\n            have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := hd\n            have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]\n            exact norm_eq_zero.mp hz\n          have hsurj : Surjective D := LinearMap.injective_iff_surjective.mp hinj\n          let d : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective D\n            (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)\n          have heq : (d : E2 →L[ℝ] E2) = D := ContinuousLinearEquiv.coe_ofBijective _ _ _\n          have hf : HasFDerivAt τ (d : E2 →L[ℝ] E2) x := by\n            rw [heq]\n            exact (hc.differentiable (by simp) x).hasFDerivAt\n          let e := hc.contDiffAt.toOpenPartialHomeomorph τ hf (by simp)\n          refine ⟨e,rfl,hc.contDiffAt.mem_toOpenPartialHomeomorph_source hf (by simp),?_⟩\n          exact hc.contDiffAt.to_localInverse hf (by simp)\n        have hcircle (x : E2) (hx : ‖x‖ = 1) : ∃ t : ℝ, unitCircleParameter t = x := by\n          let z : ℂ := ⟨x 0,x 1⟩\n          have hs : (x 0)^2+(x 1)^2=1 := by\n            have h := real_inner_self_eq_norm_sq x\n            rw [hx] at h\n            simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two,one_mul] using h\n          have hz : ‖z‖ = 1 := by\n            have hsq : ‖z‖^2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; simpa [z,Complex.normSq_apply,pow_two] using hs\n            nlinarith [norm_nonneg z]\n          have hne : z ≠ 0 := by intro h; simp [h] at hz\n          refine ⟨Complex.arg z,?_⟩\n          apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n          funext j\n          fin_cases j\n          · change Real.cos (Complex.arg z) = x 0\n            rw [Complex.cos_arg hne,hz]\n            simp [z]\n          · change Real.sin (Complex.arg z) = x 1\n            rw [Complex.sin_arg,hz]\n            simp [z]\n        have hpreserve (τ : E2 → E2) (hc : Continuous τ)\n            (hinj : InjOn τ (closedDisc 1))\n            (hsphere : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ x = y)\n            (hzero : ‖τ 0‖ < 1) : MapsTo τ (disc 1) (disc 1) := by\n          intro x hx\n          change dist (τ x) 0 < 1\n          rw [dist_zero_right]\n          by_contra hn\n          have hx' : ‖x‖ < 1 := by simpa [disc_def,ball_mem_def] using hx\n          have h0 : (0:E2) ∈ disc 1 := by simp [disc_def]\n          obtain ⟨z,hz,hze⟩ := (convex_ball (0:E2) 1).isPreconnected.intermediate_value h0 hx\n            hc.norm.continuousOn ⟨hzero.le,not_lt.mp hn⟩\n          obtain ⟨w,hw,he⟩ := hsphere (τ z) hze\n          have hz' : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz\n          have hw' : w ∈ closedDisc 1 := by simpa [closed_def,closed_mem_def,hw]\n          have hzw : z = w := hinj hz' hw' he.symm\n          have hzlt : ‖z‖ < 1 := by simpa [disc_def,ball_mem_def] using hz\n          rw [hzw,hw] at hzlt\n          exact lt_irrefl _ hzlt\n        have hsurjective (τ : E2 → E2) (hc : Continuous τ)\n            (hmaps : MapsTo τ (disc 1) (disc 1))\n            (hsphere : ∀ x : E2, ‖x‖ = 1 → ‖τ x‖ = 1)\n            (hlocal : ∀ x ∈ disc 1, ∃ e : OpenPartialHomeomorph E2 E2,\n              (e : E2 → E2) = τ ∧ x ∈ e.source) :\n            SurjOn τ (disc 1) (disc 1) := by\n          have hopen : IsOpen (τ '' disc 1) := by\n            rw [isOpen_iff_mem_nhds]\n            rintro y ⟨x,hx,rfl⟩\n            obtain ⟨e,he,hxe⟩ := hlocal x hx\n            have ho := e.isOpen_image_source_inter (s := disc 1) Metric.isOpen_ball\n            have hm : τ x ∈ e '' (e.source ∩ disc 1) := ⟨x,⟨hxe,hx⟩,by rw [he]⟩\n            exact Filter.mem_of_superset (ho.mem_nhds hm) (by\n              rintro z ⟨w,hw,rfl⟩\n              exact ⟨w,hw.2,by rw [he]⟩)\n          have hcompact : IsClosed (τ '' closedDisc 1) :=\n            ((isCompact_closedBall (0:E2) 1).image hc).isClosed\n          have hclosure : closure (τ '' disc 1) ⊆ τ '' closedDisc 1 :=\n            closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact\n          have hboundary : closure (τ '' disc 1) ∩ disc 1 ⊆ τ '' disc 1 := by\n            intro y hy\n            obtain ⟨x,hx,hxy⟩ := hclosure hy.1\n            refine ⟨x,?_,hxy⟩\n            have hxle : ‖x‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hx\n            have hylt : ‖y‖ < 1 := by simpa [disc_def,ball_mem_def] using hy.2\n            have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by\n              intro hxe\n              have := hsphere x hxe\n              rw [hxy] at this\n              linarith)\n            simpa [disc_def,ball_mem_def] using hxlt\n          have h0 : (0:E2) ∈ disc 1 := by simp [disc_def]\n          exact (convex_ball (0:E2) 1).isPreconnected.subset_of_closure_inter_subset hopen\n            ⟨τ 0,hmaps h0,⟨0,h0,rfl⟩⟩ hboundary\n        have hmonotone (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)\n            (hp : Periodic k (2*Real.pi)) :\n            ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (fun t => t+Real.arctan (s*k t)) := by\n          have hpd : Periodic (deriv k) (2*Real.pi) := by\n            intro t\n            have he : (fun t => k (t+2*Real.pi)) = k := funext hp\n            rw [← deriv_comp_add_const k (2*Real.pi) t,he]\n          obtain ⟨C,hC,hbound⟩ := (hpd.isBounded_of_continuous (by positivity)\n            (hk.continuous_deriv (by simp))).exists_pos_norm_le\n          have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), |s| * C < (1/2:ℝ) := by\n            exact (continuousAt_id.abs.mul_const C).eventually_lt_const (by norm_num)\n          filter_upwards [hsmall] with s hs\n          apply strictMono_of_hasDerivAt_pos\n            (f' := fun t => 1 + (s*deriv k t)/(1+(s*k t)^2))\n          · intro t\n            convert (hasDerivAt_id t).add (((hk.differentiable (by simp) t).hasDerivAt.const_mul s).arctan) using 1 <;> first | rfl | ring\n          · intro t\n            have hb : |s*deriv k t| < (1/2:ℝ) := by\n              rw [abs_mul]\n              exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left\n                (by simpa using hbound (deriv k t) ⟨t,rfl⟩) (abs_nonneg s)) hs\n            have hd : 0 < 1+(s*k t)^2 := by positivity\n            have hl : -1 < (s*deriv k t)/(1+(s*k t)^2) := by\n              rw [lt_div_iff₀ hd]\n              have hlow := (abs_lt.mp hb).1\n              nlinarith [sq_nonneg (s*k t)]\n            linarith\n        have hcoefficient (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :\n            let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n              (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n            ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by\n          dsimp only\n          have hc : ContDiff ℝ ∞ unitCircleParameter := by\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp\n            apply contDiff_pi.mpr\n            intro i\n            fin_cases i\n            · simpa using Real.contDiff_cos\n            · simpa using Real.contDiff_sin\n          have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=\n            (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i\n          refine ⟨?_,?_⟩\n          · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))\n          · intro t\n            have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by\n              apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n              funext i\n              fin_cases i <;> simp [circle_def,Real.cos_add_two_pi,Real.sin_add_two_pi]\n            dsimp only\n            rw [hp]\n        dsimp only\n        let τ := fun (s : ℝ) (x : E2) =>\n          (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)\n        let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n          (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n        let α := fun s t => t+Real.arctan (s*k t)\n        obtain ⟨hz,hvel,hc,hsp⟩ := hnormalized η hη htan\n        have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc\n        have hcs (s : ℝ) : ContDiff ℝ ∞ (τ s) :=\n          hc'.comp (contDiff_const.prodMk contDiff_id)\n        have hu := huniform τ hc' hz\n        obtain ⟨hk,hkp⟩ := hcoefficient η hη\n        have hm := hmonotone k hk hkp\n        have hcenter : ∀ᶠ s in 𝓝 (0:ℝ), ‖τ s 0‖ < 1 := by\n          exact (((hc'.continuous.comp (continuous_id.prodMk continuous_const)).norm).continuousAt).eventually_lt_const (by simp [τ])\n        refine ⟨hz,hvel,hc',?_⟩\n        filter_upwards [hu,hm,hcenter] with s hs hms hzs\n        have hi := hinjective (τ s) (hcs s) hs\n        obtain ⟨hac,hap,has⟩ := hlift k hk.continuous hkp s\n        have hformula (t : ℝ) : τ s (unitCircleParameter t) = unitCircleParameter (α s t) :=\n          hangle η htan s t\n        have honto : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ s x = y := by\n          intro y hy\n          obtain ⟨t,ht⟩ := hcircle y hy\n          obtain ⟨u,hu⟩ := has t\n          refine ⟨unitCircleParameter u,?_,?_⟩\n          · have hh := real_inner_self_eq_norm_sq (unitCircleParameter u)\n            have hsq : ‖unitCircleParameter u‖^2 = 1 := by\n              calc\n                _ = inner ℝ (unitCircleParameter u) (unitCircleParameter u) := hh.symm\n                _ = 1 := by\n                  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]\n                  change Real.cos u * Real.cos u + Real.sin u * Real.sin u = 1\n                  nlinarith [Real.cos_sq_add_sin_sq u]\n            nlinarith [norm_nonneg (unitCircleParameter u)]\n          · rw [hformula]\n            change unitCircleParameter (u+Real.arctan (s*k u)) = y\n            dsimp only at hu\n            rw [hu,ht]\n        have hmap := hpreserve (τ s) (hcs s).continuous hi honto hzs\n        have hl (x : E2) (hx : x ∈ closedDisc 1) :\n            ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ s ∧ x ∈ e.source ∧\n              ContDiffAt ℝ ∞ e.symm (τ s x) :=\n          hlocal (τ s) (hcs s) x (lt_trans (hs x hx) (by norm_num))\n        have hsurj := hsurjective (τ s) (hcs s).continuous hmap (hsp s) (fun x hx => by\n          obtain ⟨e,he,hx,hd⟩ := hl x (Metric.ball_subset_closedBall hx)\n          exact ⟨e,he,hx⟩)\n        have hmapclosed : MapsTo (τ s) (closedDisc 1) (closedDisc 1) := by\n          intro x hx\n          have hxle : ‖x‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hx\n          rcases lt_or_eq_of_le hxle with hxlt | hxe\n          · exact Metric.ball_subset_closedBall (hmap (by simpa [disc_def,ball_mem_def] using hxlt))\n          · have hh : ‖τ s x‖ = 1 := hsp s x hxe\n            simpa [closed_def,closed_mem_def,hh]\n        have hsurjclosed : SurjOn (τ s) (closedDisc 1) (closedDisc 1) := by\n          intro y hy\n          have hyle : ‖y‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hy\n          rcases lt_or_eq_of_le hyle with hylt | hye\n          · obtain ⟨x,hx,hxy⟩ := hsurj (by simpa [disc_def,ball_mem_def] using hylt)\n            exact ⟨x,Metric.ball_subset_closedBall hx,hxy⟩\n          · obtain ⟨x,hx,hxy⟩ := honto y hye\n            exact ⟨x,by simpa [closed_def,closed_mem_def,hx],hxy⟩\n        exact ⟨⟨hmap,hi.mono Metric.ball_subset_closedBall,hsurj⟩,\n          ⟨hmapclosed,hi,hsurjclosed⟩,hms,hac,hap,hformula,hl⟩\n      have hpositive (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n          (hz : ∀ x, tau 0 x = x) :\n          ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,\n            0 < (fderiv ℝ (tau s) x).det := by\n        have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n            (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n          have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n            convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n              ext z <;> simp [ContinuousLinearMap.inr]\n          exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n        have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n          simp_rw [he]\n          exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n        have hdet : Continuous (fun p : ℝ × E2 => (fderiv ℝ (tau p.1) p.2).det) :=\n          ContinuousLinearMap.continuous_det.comp hf\n        apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually\n        intro x hx\n        apply (hdet.continuousAt (x := (0,x))).eventually_const_lt\n        have hz' : tau 0 = id := funext hz\n        simp only [hz',fderiv_id]\n        change (0:ℝ) < LinearMap.det (LinearMap.id : E2 →ₗ[ℝ] E2)\n        simp\n      have hinverse (τ : ℝ → E2 → E2) (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))\n          (hzero : ∀ x, τ 0 x = x) :\n          ∀ᶠ s in 𝓝 (0:ℝ), ∃ ρ : E2 → E2, ContDiff ℝ ∞ ρ ∧\n            ∀ x ∈ Metric.ball (0:E2) 2, ρ (τ s x) = x := by\n        have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n            (hz : ∀ x, tau 0 x = x) :\n            ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ Metric.closedBall (0:E2) 3,\n              ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by\n          have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n              (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n            have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n              convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n                ext z <;> simp [ContinuousLinearMap.inr]\n            exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n          have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n            simp_rw [he]\n            exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n          have hnorm : Continuous (fun p : ℝ × E2 =>\n              ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=\n            (hf.sub continuous_const).norm\n          apply (isCompact_closedBall (0 : E2) 3).eventually_forall_of_forall_eventually\n          intro x hx\n          apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const\n          have hz' : tau 0 = id := funext hz\n          simp [hz']\n      \n        let φ : ContDiffBump (0:E2) := ⟨2,3,by norm_num,by norm_num⟩\n        let F : ℝ → E2 → E2 := fun s x => x + φ x • (τ s x - x)\n        have hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) :=\n          contDiff_snd.add ((φ.contDiff.comp contDiff_snd).smul (hτ.sub contDiff_snd))\n        have hFzero (x : E2) : F 0 x = x := by simp [F,hzero]\n        filter_upwards [huniform F hF hFzero] with s hs\n        have hFs : ContDiff ℝ ∞ (F s) := hF.comp (contDiff_const.prodMk contDiff_id)\n        have hbound (x : E2) : ‖fderiv ℝ (F s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2:ℝ) := by\n          by_cases hx : x ∈ Metric.closedBall (0:E2) 3\n          · exact hs x hx\n          · have he : F s =ᶠ[𝓝 x] id := by\n              have hn : {y : E2 | y ∉ Metric.closedBall (0:E2) 3} ∈ 𝓝 x :=\n                Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx\n              filter_upwards [hn] with y hy\n              have hφ : φ y = 0 := by\n                apply φ.zero_of_le_dist\n                change 3 ≤ dist y 0\n                exact le_of_lt (lt_of_not_ge hy)\n              simp [F,hφ]\n            rw [he.fderiv_eq, fderiv_id]\n            norm_num\n        have hdiff : Differentiable ℝ (fun x => F s x - x) := hFs.differentiable (by simp) |>.sub differentiable_id\n        have hLip : LipschitzOnWith (1/2:ℝ≥0) (fun x => F s x - x) univ := by\n          apply convex_univ.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hdiff x)\n          intro x hx\n          have hi : DifferentiableAt ℝ (fun y : E2 => y) x := differentiableAt_id\n          rw [fderiv_fun_sub (hFs.differentiable (by simp) x) hi, fderiv_fun_id]\n          exact_mod_cast (hbound x).le\n        have happ : ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℝ E2) univ (1/2:ℝ≥0) :=\n          hLip.approximatesLinearOn (f := F s) (f' := ContinuousLinearMap.id ℝ E2)\n        let e : E2 ≃ₜ E2 := ApproximatesLinearOn.toHomeomorph (F s) (f' := ContinuousLinearEquiv.refl ℝ E2) happ\n          (Or.inr (by norm_num))\n        have he : (e : E2 → E2) = F s := rfl\n        have hD (x : E2) : ∃ D : E2 ≃L[ℝ] E2, (D : E2 →L[ℝ] E2) = fderiv ℝ (F s) x := by\n          let A := fderiv ℝ (F s) x\n          have hinj : Injective A := by\n            apply LinearMap.ker_eq_bot.mp\n            apply LinearMap.ker_eq_bot'.mpr\n            intro v hv\n            change A v = 0 at hv\n            have hz : (A - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]\n            have hn := (A - ContinuousLinearMap.id ℝ E2).le_opNorm v\n            rw [hz,norm_neg] at hn\n            have hb : ‖A - ContinuousLinearMap.id ℝ E2‖ < 1 := lt_trans (hbound x) (by norm_num)\n            have hnv : ‖v‖ = 0 := by nlinarith [norm_nonneg v]\n            exact norm_eq_zero.mp hnv\n          have hsurj : Surjective A := LinearMap.injective_iff_surjective.mp hinj\n          exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)\n            (LinearMap.range_eq_top.mpr hsurj),ContinuousLinearEquiv.coe_ofBijective _ _ _⟩\n        choose D hDeq using hD\n        have hsmooth : ContDiff ℝ ∞ (e.symm : E2 → E2) := by\n          apply e.contDiff_symm (f₀' := D)\n          · intro x\n            rw [he,hDeq x]\n            exact (hFs.differentiable (by simp) x).hasFDerivAt\n          · rw [he]; exact hFs\n        refine ⟨e.symm,hsmooth,?_⟩\n        intro x hx\n        have hφ : φ x = 1 := φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)\n        have hxF : F s x = τ s x := by simp [F,hφ]\n        rw [← hxF,← he]\n        exact e.symm_apply_apply x\n      have hpiola (τ ρ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (hρ : ContDiff ℝ ∞ ρ)\n          (hleft : ∀ x ∈ Metric.ball (0:E2) 2, ρ (τ x) = x)\n          (ψ : E2 → ℝ) (hψ : ContDiff ℝ ∞ ψ) (j : Fin 2) :\n            ∃ χ : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧\n              (∀ x ∈ disc 1, (fderiv ℝ τ x).det *\n                (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                 fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) =\n                fderiv ℝ ψ x (coordinateVector 2 j)) ∧\n              (∀ x ∈ closedDisc 1, ∀ k : Fin 2, (fderiv ℝ τ x).det * χ k (τ x) =\n                (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x) := by\n        have hproduct (u q : E2 → ℝ) (hu : ContDiff ℝ ∞ u) (hq : ContDiff ℝ ∞ q) (y : E2) :\n            fderiv ℝ (fun z => fderiv ℝ u z (coordinateVector 2 1) * q z) y (coordinateVector 2 0) +\n            fderiv ℝ (fun z => -fderiv ℝ u z (coordinateVector 2 0) * q z) y (coordinateVector 2 1) =\n            fderiv ℝ u y (coordinateVector 2 1) * fderiv ℝ q y (coordinateVector 2 0) -\n            fderiv ℝ u y (coordinateVector 2 0) * fderiv ℝ q y (coordinateVector 2 1) := by\n          have hdC : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)\n          have hd : Differentiable ℝ (fderiv ℝ u) := hdC.differentiable (by simp)\n          have hp (i : Fin 2) : Differentiable ℝ (fun z => fderiv ℝ u z (coordinateVector 2 i)) :=\n            hd.clm_apply (differentiable_const _)\n          have hn : DifferentiableAt ℝ (fun z => -fderiv ℝ u z (coordinateVector 2 0)) y := (hp 0 y).neg\n          rw [fderiv_fun_mul (hp 1 y) (hq.differentiable (by simp) y),\n            fderiv_fun_mul hn (hq.differentiable (by simp) y),\n            fderiv_fun_neg]\n          simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,\n            ContinuousLinearMap.neg_apply,smul_eq_mul]\n          rw [fderiv_clm_apply (hd y) (differentiableAt_const _),\n            fderiv_clm_apply (hd y) (differentiableAt_const _)]\n          simp only [fderiv_fun_const,ContinuousLinearMap.zero_apply,ContinuousLinearMap.add_apply,\n            ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,map_zero,add_zero,zero_add]\n          have hs := ((hu.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)).eq\n            (coordinateVector 2 0) (coordinateVector 2 1)\n          simp only [Pi.zero_apply,zero_apply,map_zero,zero_add,add_zero]\n          rw [hs]\n          ring\n        have halgebra (A B : E2 →L[ℝ] E2) (hBA : B.comp A = ContinuousLinearMap.id ℝ E2) :\n            A.det * (B (coordinateVector 2 1)) 1 = (A (coordinateVector 2 0)) 0 ∧\n            A.det * (-(B (coordinateVector 2 0)) 1) = (A (coordinateVector 2 0)) 1 ∧\n            A.det * (-(B (coordinateVector 2 1)) 0) = (A (coordinateVector 2 1)) 0 ∧\n            A.det * (B (coordinateVector 2 0)) 0 = (A (coordinateVector 2 1)) 1 ∧\n            A.det * ((B (coordinateVector 2 0)) 0 * (B (coordinateVector 2 1)) 1 -\n              (B (coordinateVector 2 1)) 0 * (B (coordinateVector 2 0)) 1) = 1 := by\n          have hv (v : E2) : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n            funext k\n            fin_cases k <;> simp [coordinateVector]\n          have he (j k : Fin 2) :\n              (A (coordinateVector 2 j)) 0 * (B (coordinateVector 2 0)) k +\n              (A (coordinateVector 2 j)) 1 * (B (coordinateVector 2 1)) k =\n              (coordinateVector 2 j) k := by\n            have h := congrArg (fun L : E2 →L[ℝ] E2 => L (coordinateVector 2 j) k) hBA\n            change B (A (coordinateVector 2 j)) k = (coordinateVector 2 j) k at h\n            rw [hv (A (coordinateVector 2 j))] at h\n            simpa [map_add,map_smul] using h\n          have h00 := he 0 0\n          have h01 := he 1 0\n          have h10 := he 0 1\n          have h11 := he 1 1\n          simp [coordinateVector] at h00 h01 h10 h11\n          have hdet (L : E2 →L[ℝ] E2) : L.det =\n              (L (coordinateVector 2 0)) 0 * (L (coordinateVector 2 1)) 1 -\n              (L (coordinateVector 2 1)) 0 * (L (coordinateVector 2 0)) 1 := by\n            change LinearMap.det L.toLinearMap = _\n            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis,Matrix.det_fin_two]\n            rfl\n          have hd : A.det * B.det = 1 := by\n            have he : B.toLinearMap.comp A.toLinearMap = LinearMap.id := congrArg ContinuousLinearMap.toLinearMap hBA\n            have h := congrArg LinearMap.det he\n            rw [LinearMap.det_comp,LinearMap.det_id] at h\n            simpa [mul_comm] using h\n          refine ⟨?_,?_,?_,?_,?_⟩\n          · rw [hdet A]\n            simp only [coordinateVector]\n            linear_combination (A (EuclideanSpace.single 0 1)) 0 * h11 - (A (EuclideanSpace.single 1 1)) 0 * h10\n          · rw [hdet A]\n            simp only [coordinateVector]\n            linear_combination (A (EuclideanSpace.single 0 1)) 1 * h11 - (A (EuclideanSpace.single 1 1)) 1 * h10\n          · rw [hdet A]\n            simp only [coordinateVector]\n            linear_combination (A (EuclideanSpace.single 1 1)) 0 * h00 - (A (EuclideanSpace.single 0 1)) 0 * h01\n          · rw [hdet A]\n            simp only [coordinateVector]\n            linear_combination (A (EuclideanSpace.single 1 1)) 1 * h00 - (A (EuclideanSpace.single 0 1)) 1 * h01\n          · rw [← hdet B]\n            exact hd\n      \n        have hin (x : E2) (hx : x ∈ closedDisc 1) : x ∈ Metric.ball (0:E2) 2 :=\n          lt_of_le_of_lt (show dist x 0 ≤ 1 from hx) (by norm_num)\n        have hBA (x : E2) (hx : x ∈ closedDisc 1) :\n            (fderiv ℝ ρ (τ x)).comp (fderiv ℝ τ x) = ContinuousLinearMap.id ℝ E2 := by\n          have he : (ρ ∘ τ) =ᶠ[𝓝 x] id := by\n            filter_upwards [Metric.isOpen_ball.mem_nhds (hin x hx)] with z hz\n            exact hleft z hz\n          have hd := ((hρ.differentiable (by simp) (τ x)).hasFDerivAt.comp x\n            (hτ.differentiable (by simp) x).hasFDerivAt).fderiv\n          rw [he.fderiv_eq,fderiv_id] at hd\n          exact hd.symm\n        have hu (k : Fin 2) : ContDiff ℝ ∞ (fun y => ρ y k) :=\n          (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hρ)) k\n        have hc (k : Fin 2) (y : E2) :\n            fderiv ℝ (fun z => ρ z k) y = (EuclideanSpace.proj (𝕜 := ℝ) k).comp (fderiv ℝ ρ y) := by\n          exact ((EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp y\n            (hρ.differentiable (by simp) y).hasFDerivAt).fderiv\n        have hud (k l : Fin 2) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => ρ z k) y (coordinateVector 2 l)) := by\n          have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z => ρ z k)) := (hu k).fderiv_right (by simp)\n          exact hd.clm_apply contDiff_const\n        have hq : ContDiff ℝ ∞ (ψ ∘ ρ) := hψ.comp hρ\n        have hqjet (y : E2) (l : Fin 2) : fderiv ℝ (ψ ∘ ρ) y (coordinateVector 2 l) =\n            fderiv ℝ ψ (ρ y) (coordinateVector 2 0) * (fderiv ℝ ρ y (coordinateVector 2 l)) 0 +\n            fderiv ℝ ψ (ρ y) (coordinateVector 2 1) * (fderiv ℝ ρ y (coordinateVector 2 l)) 1 := by\n          rw [fderiv_comp y (hψ.differentiable (by simp) (ρ y)) (hρ.differentiable (by simp) y)]\n          have hv (v : E2) : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n            funext k\n            fin_cases k <;> simp [coordinateVector]\n          change fderiv ℝ ψ (ρ y) (fderiv ℝ ρ y (coordinateVector 2 l)) = _\n          rw [hv (fderiv ℝ ρ y (coordinateVector 2 l)),map_add,map_smul,map_smul]\n          simp [coordinateVector,mul_comm]\n        have hcomp (k l : Fin 2) (y : E2) :\n            fderiv ℝ (fun z => ρ z k) y (coordinateVector 2 l) = (fderiv ℝ ρ y (coordinateVector 2 l)) k := by\n          rw [hc]; rfl\n        fin_cases j\n        · let χ : Fin 2 → E2 → ℝ := ![\n            fun y => fderiv ℝ (fun z => ρ z 1) y (coordinateVector 2 1) * (ψ ∘ ρ) y,\n            fun y => -fderiv ℝ (fun z => ρ z 1) y (coordinateVector 2 0) * (ψ ∘ ρ) y]\n          refine ⟨χ,?_,?_,?_⟩\n          · intro k\n            fin_cases k\n            · exact (hud 1 1).mul hq\n            · exact (hud 1 0).neg.mul hq\n          · intro x hx\n            change (fderiv ℝ τ x).det * (_ + _) = fderiv ℝ ψ x (coordinateVector 2 0)\n            have hp := hproduct (fun z => ρ z 1) (ψ ∘ ρ) (hu 1) hq (τ x)\n            change fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n              fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1) = _ at hp\n            rw [hp,hcomp,hcomp,hqjet,hqjet,hleft x (hin x (Metric.ball_subset_closedBall hx))]\n            have hd := (halgebra _ _ (hBA x (Metric.ball_subset_closedBall hx))).2.2.2.2\n            calc\n              _ = fderiv ℝ ψ x (coordinateVector 2 0) *\n                  ((fderiv ℝ τ x).det * ((fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 0 *\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 1 -\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 0 *\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 1)) := by ring\n              _ = _ := by rw [hd,mul_one]\n          · intro x hx k\n            obtain ⟨h00,h10,h01,h11,hd⟩ := halgebra _ _ (hBA x hx)\n            fin_cases k\n            · change (fderiv ℝ τ x).det * (fderiv ℝ (fun z => ρ z 1) (τ x) (coordinateVector 2 1) * ψ (ρ (τ x))) = _\n              rw [hcomp,hleft x (hin x hx),← mul_assoc,h00]\n              rfl\n            · change (fderiv ℝ τ x).det * (-fderiv ℝ (fun z => ρ z 1) (τ x) (coordinateVector 2 0) * ψ (ρ (τ x))) = _\n              rw [hcomp,hleft x (hin x hx),← mul_assoc,h10]\n              rfl\n        · let χ : Fin 2 → E2 → ℝ := ![\n            fun y => -fderiv ℝ (fun z => ρ z 0) y (coordinateVector 2 1) * (ψ ∘ ρ) y,\n            fun y => fderiv ℝ (fun z => ρ z 0) y (coordinateVector 2 0) * (ψ ∘ ρ) y]\n          refine ⟨χ,?_,?_,?_⟩\n          · intro k\n            fin_cases k\n            · exact (hud 0 1).neg.mul hq\n            · exact (hud 0 0).mul hq\n          · intro x hx\n            change (fderiv ℝ τ x).det * (_ + _) = fderiv ℝ ψ x (coordinateVector 2 1)\n            have hp := hproduct (fun z => ρ z 0) (ψ ∘ ρ) (hu 0) hq (τ x)\n            have hn (a q : E2 → ℝ) (y v : E2) :\n                fderiv ℝ (fun z => -a z * q z) y v = -fderiv ℝ (fun z => a z * q z) y v := by\n              simp_rw [neg_mul]\n              rw [fderiv_fun_neg]\n              rfl\n            have hdiv : fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1) =\n                -(fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 1) *\n                    fderiv ℝ (ψ ∘ ρ) (τ x) (coordinateVector 2 0) -\n                  fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 0) *\n                    fderiv ℝ (ψ ∘ ρ) (τ x) (coordinateVector 2 1)) := by\n              dsimp only [χ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]\n              rw [hn] at hp ⊢\n              linarith\n            rw [hdiv,hcomp,hcomp,hqjet,hqjet,hleft x (hin x (Metric.ball_subset_closedBall hx))]\n            have hd := (halgebra _ _ (hBA x (Metric.ball_subset_closedBall hx))).2.2.2.2\n            calc\n              _ = fderiv ℝ ψ x (coordinateVector 2 1) *\n                  ((fderiv ℝ τ x).det * ((fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 0 *\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 1 -\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 1)) 0 *\n                    (fderiv ℝ ρ (τ x) (coordinateVector 2 0)) 1)) := by ring\n              _ = _ := by rw [hd,mul_one]\n          · intro x hx k\n            obtain ⟨h00,h10,h01,h11,hd⟩ := halgebra _ _ (hBA x hx)\n            fin_cases k\n            · change (fderiv ℝ τ x).det * (-fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 1) * ψ (ρ (τ x))) = _\n              rw [hcomp,hleft x (hin x hx),← mul_assoc,h01]\n              rfl\n            · change (fderiv ℝ τ x).det * (fderiv ℝ (fun z => ρ z 0) (τ x) (coordinateVector 2 0) * ψ (ρ (τ x))) = _\n              rw [hcomp,hleft x (hin x hx),← mul_assoc,h11]\n              rfl\n      have hassemble (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)\n          (hgreen : HasGreenBoundaryTrace f d b) (hb : Continuous b) (hbp : Periodic b (2*Real.pi))\n          (τ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (hbij : BijOn τ (disc 1) (disc 1))\n          (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hαp : ∀ t, α (t+2*Real.pi)=α t+2*Real.pi)\n          (hboundary : ∀ t, τ (unitCircleParameter t)=unitCircleParameter (α t))\n          (hpositive : ∀ x ∈ closedDisc 1, 0 < (fderiv ℝ τ x).det)\n          (htests : ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → ∀ j : Fin 2,\n            ∃ χ : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧\n              (∀ x ∈ disc 1, (fderiv ℝ τ x).det *\n                (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                 fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) =\n                fderiv ℝ ψ x (coordinateVector 2 j)) ∧\n              (∀ x ∈ closedDisc 1, ∀ k : Fin 2, (fderiv ℝ τ x).det * χ k (τ x) =\n                (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x)) :\n          HasGreenBoundaryTrace (f ∘ τ)\n            (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n              (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j))))\n            (b ∘ α) := by\n        have hassemble (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)\n            (hgreen : HasGreenBoundaryTrace f d b) (hb : Continuous b) (hbp : Periodic b (2*Real.pi))\n            (τ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (hbij : BijOn τ (disc 1) (disc 1))\n            (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hαp : ∀ t, α (t+2*Real.pi)=α t+2*Real.pi)\n            (hboundary : ∀ t, τ (unitCircleParameter t)=unitCircleParameter (α t))\n            (htests : ∀ ψ : E2 → ℝ, ContDiff ℝ ∞ ψ → ∀ j : Fin 2,\n              ∃ χ : Fin 2 → E2 → ℝ, (∀ k, ContDiff ℝ ∞ (χ k)) ∧\n                (∀ x ∈ disc 1, |(fderiv ℝ τ x).det| *\n                  (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                   fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) =\n                  fderiv ℝ ψ x (coordinateVector 2 j)) ∧\n                (∀ x ∈ disc 1, ∀ k : Fin 2, |(fderiv ℝ τ x).det| * χ k (τ x) =\n                  (fderiv ℝ τ x (coordinateVector 2 j)) k * ψ x) ∧\n                (∀ t, (χ 0 (unitCircleParameter (α t)) * (unitCircleParameter (α t)) 0 +\n                  χ 1 (unitCircleParameter (α t)) * (unitCircleParameter (α t)) 1) * deriv α t =\n                  ψ (unitCircleParameter t) * (unitCircleParameter t) j)) :\n            HasGreenBoundaryTrace (f ∘ τ)\n              (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n                (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j))))\n              (b ∘ α) := by\n          have hvector (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)\n              (hgreen : HasGreenBoundaryTrace f d b)\n              (χ : Fin 2 → E2 → ℝ) (hχ : ∀ k, ContDiff ℝ ∞ (χ k)) (i : Fin 2) :\n              let L := fun x => f x i * (fderiv ℝ (χ 0) x (coordinateVector 2 0) +\n                fderiv ℝ (χ 1) x (coordinateVector 2 1)) + d i x 0 * χ 0 x + d i x 1 * χ 1 x\n              let B := fun t => b t i * (χ 0 (unitCircleParameter t) * (unitCircleParameter t) 0 +\n                χ 1 (unitCircleParameter t) * (unitCircleParameter t) 1)\n              IntegrableOn L (disc 1) ∧ IntegrableOn B (Icc 0 (2*Real.pi)) ∧\n                (∫ x in disc 1, L x) = ∫ t in Icc 0 (2*Real.pi), B t := by\n            dsimp only\n            obtain ⟨hi0,hb0,he0⟩ := hgreen (χ 0) (hχ 0) i 0\n            obtain ⟨hi1,hb1,he1⟩ := hgreen (χ 1) (hχ 1) i 1\n            have hL : (fun x => f x i * (fderiv ℝ (χ 0) x (coordinateVector 2 0) +\n                fderiv ℝ (χ 1) x (coordinateVector 2 1)) + d i x 0 * χ 0 x + d i x 1 * χ 1 x) =\n                (fun x => (f x i * fderiv ℝ (χ 0) x (coordinateVector 2 0) + d i x 0 * χ 0 x) +\n                  (f x i * fderiv ℝ (χ 1) x (coordinateVector 2 1) + d i x 1 * χ 1 x)) := by\n              funext x; ring\n            have hB : (fun t => b t i * (χ 0 (unitCircleParameter t) * (unitCircleParameter t) 0 +\n                χ 1 (unitCircleParameter t) * (unitCircleParameter t) 1)) =\n                (fun t => b t i * χ 0 (unitCircleParameter t) * (unitCircleParameter t) 0 +\n                  b t i * χ 1 (unitCircleParameter t) * (unitCircleParameter t) 1) := by\n              funext t; ring\n            rw [hL,hB]\n            refine ⟨hi0.add hi1,hb0.add hb1,?_⟩\n            rw [integral_add hi0 hi1, integral_add hb0 hb1,he0,he1]\n          have hperiodic (g α : ℝ → ℝ) (hg : Continuous g) (hp : Periodic g (2*Real.pi))\n              (ha : ContDiff ℝ ∞ α) (hs : ∀ t, α (t+2*Real.pi)=α t+2*Real.pi) :\n              IntegrableOn (fun t => g (α t) * deriv α t) (Icc 0 (2*Real.pi)) ∧\n              (∫ t in Icc 0 (2*Real.pi), g (α t) * deriv α t) =\n                ∫ t in Icc 0 (2*Real.pi), g t := by\n            have hT : (0:ℝ) ≤ 2*Real.pi := by positivity\n            have hi : Continuous (fun t => g (α t) * deriv α t) :=\n              (hg.comp ha.continuous).mul (ha.continuous_deriv (by simp))\n            refine ⟨hi.continuousOn.integrableOn_Icc, ?_⟩\n            have he := intervalIntegral.integral_comp_mul_deriv\n              (fun x (_ : x ∈ uIcc 0 (2*Real.pi)) => (ha.differentiable (by simp) x).hasDerivAt)\n              (ha.continuous_deriv (by simp)).continuousOn hg\n            have hz := hs 0\n            simp only [zero_add] at hz\n            rw [hz] at he\n            rw [hp.intervalIntegral_add_eq (α 0) 0] at he\n            simpa only [zero_add, intervalIntegral.integral_of_le hT,\n              integral_Icc_eq_integral_Ioc, Function.comp_apply] using he\n        \n          have hc : Continuous unitCircleParameter := by\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp\n            apply continuous_pi\n            intro i\n            fin_cases i\n            · simpa using Real.continuous_cos\n            · simpa using Real.continuous_sin\n          have hcp : Periodic unitCircleParameter (2*Real.pi) := by\n            intro t\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n            funext i\n            fin_cases i <;> simp [circle_def,Real.cos_add_two_pi,Real.sin_add_two_pi]\n          intro ψ hψ i j\n          obtain ⟨χ,hχ,hdiv,hjet,hflux⟩ := htests ψ hψ j\n          obtain ⟨hL,hB,he⟩ := hvector f d b hgreen χ hχ i\n          let L := fun x => f x i * (fderiv ℝ (χ 0) x (coordinateVector 2 0) +\n            fderiv ℝ (χ 1) x (coordinateVector 2 1)) + d i x 0 * χ 0 x + d i x 1 * χ 1 x\n          let B := fun t => b t i * (χ 0 (unitCircleParameter t) * (unitCircleParameter t) 0 +\n            χ 1 (unitCircleParameter t) * (unitCircleParameter t) 1)\n          let G := fun x => f (τ x) i * fderiv ℝ ψ x (coordinateVector 2 j) +\n            inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)) * ψ x\n          have hidentity (x : E2) (hx : x ∈ disc 1) : |(fderiv ℝ τ x).det| * L (τ x) = G x := by\n            dsimp only [L,G]\n            rw [show |(fderiv ℝ τ x).det| *\n                (f (τ x) i * (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                  fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1)) +\n                  d i (τ x) 0 * χ 0 (τ x) + d i (τ x) 1 * χ 1 (τ x)) =\n                f (τ x) i * (|(fderiv ℝ τ x).det| *\n                  (fderiv ℝ (χ 0) (τ x) (coordinateVector 2 0) +\n                   fderiv ℝ (χ 1) (τ x) (coordinateVector 2 1))) +\n                  d i (τ x) 0 * (|(fderiv ℝ τ x).det| * χ 0 (τ x)) +\n                  d i (τ x) 1 * (|(fderiv ℝ τ x).det| * χ 1 (τ x)) by ring]\n            rw [hdiv x hx,hjet x hx 0,hjet x hx 1]\n            simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]\n            ring\n          have hd : ∀ x ∈ disc 1, HasFDerivWithinAt τ (fderiv ℝ τ x) (disc 1) x := fun x _ =>\n            (hτ.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt\n          have hi := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)\n            (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet) hd hbij.injOn L\n          rw [hbij.image_eq] at hi\n          have hG : IntegrableOn G (disc 1) := (hi.mp hL).congr_fun hidentity Metric.isOpen_ball.measurableSet\n          have hchange := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)\n            (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet) hd hbij.injOn L\n          rw [hbij.image_eq] at hchange\n          have hLG : (∫ x in disc 1, L x) = ∫ x in disc 1, G x :=\n            hchange.trans (setIntegral_congr_fun Metric.isOpen_ball.measurableSet hidentity)\n          have hBi : Continuous (fun t => b t i) :=\n            (continuous_apply i).comp ((EuclideanSpace.equiv (Fin 2) ℝ).continuous.comp hb)\n          have hci (k : Fin 2) : Continuous (fun t => unitCircleParameter t k) :=\n            (continuous_apply k).comp ((EuclideanSpace.equiv (Fin 2) ℝ).continuous.comp hc)\n          have hBc : Continuous B := hBi.mul\n            (((hχ 0).continuous.comp hc).mul (hci 0) |>.add\n              (((hχ 1).continuous.comp hc).mul (hci 1)))\n          have hBp : Periodic B (2*Real.pi) := by\n            intro t\n            dsimp only [B]\n            rw [hbp t,hcp t]\n          obtain ⟨hBP,hsub⟩ := hperiodic B α hBc hBp hα hαp\n          have hfluxB (t : ℝ) : B (α t) * deriv α t =\n              b (α t) i * ψ (unitCircleParameter t) * (unitCircleParameter t) j := by\n            dsimp only [B]\n            rw [mul_assoc,hflux t]\n            ring\n          have htargetB := hBP.congr_fun (fun t _ => hfluxB t) measurableSet_Icc\n          refine ⟨hG,htargetB,?_⟩\n          change (∫ x in disc 1, G x) = _\n          rw [← hLG,he,← hsub]\n          exact integral_congr_ae (Filter.Eventually.of_forall hfluxB)\n        have hcofactor (τ : E2 → E2) (hτ : ContDiff ℝ ∞ τ) (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α)\n            (hb : ∀ t, τ (unitCircleParameter t)=unitCircleParameter (α t))\n            (t : ℝ) (j : Fin 2) :\n            ((fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 j)) 0 * (unitCircleParameter (α t)) 0 +\n             (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 j)) 1 * (unitCircleParameter (α t)) 1) * deriv α t =\n              (fderiv ℝ τ (unitCircleParameter t)).det * (unitCircleParameter t) j := by\n          let T := fun t => (-Real.sin t) • coordinateVector 2 0 + Real.cos t • coordinateVector 2 1\n          have hc (t : ℝ) : HasDerivAt unitCircleParameter (T t) t := by\n            have he : unitCircleParameter = fun t => Real.cos t • coordinateVector 2 0 + Real.sin t • coordinateVector 2 1 := by\n              funext t\n              apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n              funext i\n              fin_cases i <;> simp [circle_def,coordinateVector,PiLp.single_apply]\n            rw [he]\n            exact ((Real.hasDerivAt_cos t).smul_const _).add ((Real.hasDerivAt_sin t).smul_const _)\n          have hleft := (hτ.differentiable (by simp) (unitCircleParameter t)).hasFDerivAt.comp_hasDerivAt t (hc t)\n          have hright := (hc (α t)).scomp t (hα.differentiable (by simp) t).hasDerivAt\n          have he : (fun z => τ (unitCircleParameter z)) = fun z => unitCircleParameter (α z) := funext hb\n          have htan : fderiv ℝ τ (unitCircleParameter t) (T t) = deriv α t • T (α t) := by\n            apply hleft.unique\n            simpa only [Function.comp_def, ← he] using hright\n          have h0 := congrArg (fun v : E2 => v 0) htan\n          have h1 := congrArg (fun v : E2 => v 1) htan\n          simp [T,map_add,map_smul,coordinateVector,PiLp.single_apply] at h0 h1\n          have hdet : (fderiv ℝ τ (unitCircleParameter t)).det =\n              (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 0)) 0 *\n              (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 1)) 1 -\n              (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 1)) 0 *\n              (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 0)) 1 := by\n            change LinearMap.det (fderiv ℝ τ (unitCircleParameter t)).toLinearMap = _\n            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]\n            rfl\n          rw [hdet]\n          simp only [coordinateVector] at *\n          fin_cases j\n          · change (((fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single (0 : Fin 2) 1)) 0 * Real.cos (α t) + (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single (0 : Fin 2) 1)) 1 * Real.sin (α t)) * deriv α t = _ * Real.cos t)\n            linear_combination\n              (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single 0 1)) 1 * h0 -\n              (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single 0 1)) 0 * h1\n          · change (((fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single (1 : Fin 2) 1)) 0 * Real.cos (α t) + (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single (1 : Fin 2) 1)) 1 * Real.sin (α t)) * deriv α t = _ * Real.sin t)\n            linear_combination\n              (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single 1 1)) 1 * h0 -\n              (fderiv ℝ τ (unitCircleParameter t) (EuclideanSpace.single 1 1)) 0 * h1\n      \n        apply hassemble f d b hgreen hb hbp τ hτ hbij α hα hαp hboundary\n        intro ψ hψ j\n        obtain ⟨χ,hχ,hdiv,hjet⟩ := htests ψ hψ j\n        refine ⟨χ,hχ,?_,?_,?_⟩\n        · intro x hx\n          rw [abs_of_pos (hpositive x (Metric.ball_subset_closedBall hx))]\n          exact hdiv x hx\n        · intro x hx k\n          rw [abs_of_pos (hpositive x (Metric.ball_subset_closedBall hx))]\n          exact hjet x (Metric.ball_subset_closedBall hx) k\n        · intro t\n          have hc : unitCircleParameter t ∈ closedDisc 1 := by\n            change ‖unitCircleParameter t - (0:E2)‖ ≤ 1\n            rw [sub_zero]\n            have hn : ‖unitCircleParameter t‖^2 = 1 := by\n              simp [EuclideanSpace.real_norm_sq_eq,circle_def,Fin.sum_univ_two,\n                Real.cos_sq_add_sin_sq]\n            nlinarith [norm_nonneg (unitCircleParameter t)]\n          have hd := (hpositive _ hc).ne'\n          apply (mul_left_cancel₀ hd)\n          have h0 := hjet _ hc 0\n          have h1 := hjet _ hc 1\n          rw [hboundary t] at h0 h1\n          calc\n            (fderiv ℝ τ (unitCircleParameter t)).det *\n                ((χ 0 (unitCircleParameter (α t)) * (unitCircleParameter (α t)) 0 +\n                  χ 1 (unitCircleParameter (α t)) * (unitCircleParameter (α t)) 1) * deriv α t) =\n                ((fderiv ℝ τ (unitCircleParameter t)).det * χ 0 (unitCircleParameter (α t)) *\n                  (unitCircleParameter (α t)) 0 +\n                 (fderiv ℝ τ (unitCircleParameter t)).det * χ 1 (unitCircleParameter (α t)) *\n                  (unitCircleParameter (α t)) 1) * deriv α t := by ring\n            _ = ψ (unitCircleParameter t) *\n                (((fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 j)) 0 * (unitCircleParameter (α t)) 0 +\n                 (fderiv ℝ τ (unitCircleParameter t) (coordinateVector 2 j)) 1 * (unitCircleParameter (α t)) 1) * deriv α t) := by\n              rw [h0,h1]; ring\n            _ = _ := by rw [hcofactor τ hτ α hα hboundary t j]; ring\n      have hlift (R : ℝ) (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (orientation : ℝ)\n          (ht : WeakMonotoneBoundaryLift Ω theta orientation) :\n          Continuous (liftedBoundaryValue Ω theta) ∧\n          Periodic (liftedBoundaryValue Ω theta) (2*Real.pi) := by\n        refine ⟨Ω.boundary.smooth.continuous.comp ht.2.1, ?_⟩\n        intro t\n        change Ω.boundary.gamma (theta (t+2*Real.pi)) = Ω.boundary.gamma (theta t)\n        rw [ht.2.2.2]\n        rcases ht.1 with ho | ho\n        · simpa [ho] using Ω.boundary.periodic (theta t)\n        · simpa [ho, sub_eq_add_neg] using Ω.boundary.periodic.sub_eq (theta t)\n      have hangular (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :\n          let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n            (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n          ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by\n        dsimp only\n        have hc : ContDiff ℝ ∞ unitCircleParameter := by\n          apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp\n          apply contDiff_pi.mpr\n          intro i\n          fin_cases i\n          · simpa using Real.contDiff_cos\n          · simpa using Real.contDiff_sin\n        have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=\n          (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i\n        refine ⟨?_,?_⟩\n        · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))\n        · intro t\n          have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by\n            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n            funext i\n            fin_cases i <;> simp [circle_def,Real.cos_add_two_pi,Real.sin_add_two_pi]\n          dsimp only\n          rw [hp]\n      intro f d theta orientation hh1 ht hg η hη htan\n      dsimp only\n      let τ := fun (s : ℝ) (x : E2) => (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)\n      let α := fun (s : ℝ) (t : ℝ) => t + Real.arctan (s *\n        ((unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n         (unitCircleParameter t) 1 * η (unitCircleParameter t) 0))\n      obtain ⟨hz,hder,hjoint,hevent⟩ := hgeometry η hη htan\n      obtain ⟨hb,hbp⟩ := hlift R Ω theta orientation ht\n      have hα (s : ℝ) : ContDiff ℝ ∞ (α s) :=\n        contDiff_id.add (Real.contDiff_arctan.comp (contDiff_const.mul (hangular η hη).1))\n      filter_upwards [hevent,hpositive τ hjoint hz,hinverse τ hjoint hz] with s hs hpos hinv\n      obtain ⟨hbij,hclosed,hmono,hcont,hperiod,hboundary,hlocal⟩ := hs\n      obtain ⟨ρ,hρ,hleft⟩ := hinv\n      exact hassemble f d (liftedBoundaryValue Ω theta) hg hb hbp (τ s)\n        (hjoint.comp (contDiff_const.prodMk contDiff_id)) hbij (α s) (hα s) hperiod hboundary\n        hpos (fun ψ hψ j => hpiola (τ s) ρ (hjoint.comp (contDiff_const.prodMk contDiff_id)) hρ hleft ψ hψ j)\n    ))"))
      have nativeDirichlet :
      ∀ f d, MetricAdmissible Ω f d →
          ∀ η : E2 → E2, ContDiff ℝ ∞ η →
          (∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) →
        let τ := fun (s : ℝ) (x : E2) => (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
        let fs := fun s x => f (τ s x)
        let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
        HasDerivAt (fun s => metricDirichlet M (fs s) (ds s))
          ((1/2 : ℝ)*(∫ x in disc 1, (metricE M f d x-metricH M f d x) *
          ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +
          (2*metricF M f d x) * ((fderiv ℝ η x (coordinateVector 2 0)) 1 +
            (fderiv ℝ η x (coordinateVector 2 1)) 0))) 0 :=
        by run_tac do Lean.Elab.Tactic.evalTactic (← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "exact (by\n  classical\n  have circle_def (t : ℝ) : unitCircleParameter t = (EuclideanSpace.equiv (Fin 2) ℝ).symm ![Real.cos t,Real.sin t] := rfl\n  have disc_def (r : ℝ) : disc r = Metric.ball (0:E2) r := rfl\n  have closed_def (r : ℝ) : closedDisc r = Metric.closedBall (0:E2) r := rfl\n  have ball_mem_def (x y : E2) (r : ℝ) : (y ∈ Metric.ball x r) = (dist y x < r) := propext Metric.mem_ball\n  have closed_mem_def (x y : E2) (r : ℝ) : (y ∈ Metric.closedBall x r) = (dist y x ≤ r) := propext Metric.mem_closedBall\n  have hgeneral (τ : ℝ → E2 → E2) (η : E2 → E2)\n      (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))\n      (hzero : ∀ x, τ 0 x = x)\n      (hvelocity : ∀ x, HasDerivAt (fun s => τ s x) (η x) 0)\n      (hbij : ∀ᶠ s in 𝓝 (0:ℝ), BijOn (τ s) (disc 1) (disc 1))\n      (M : E2 → Mat2) (hsym : SymmetricOn M univ)\n      (f : E2 → E2) (d : Fin 2 → E2 → E2)\n      (hE : IntegrableOn (metricE M f d) (disc 1))\n      (hF : IntegrableOn (metricF M f d) (disc 1))\n      (hH : IntegrableOn (metricH M f d) (disc 1)) :\n      let fs := fun s x => f (τ s x)\n      let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n        (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))\n      HasDerivAt (fun s => metricDirichlet M (fs s) (ds s))\n        ((1/2 : ℝ)*(∫ x in disc 1, (metricE M f d x-metricH M f d x) *\n        ((fderiv ℝ η x (coordinateVector 2 0)) 0 - (fderiv ℝ η x (coordinateVector 2 1)) 1) +\n        (2*metricF M f d x) * ((fderiv ℝ η x (coordinateVector 2 0)) 1 +\n          (fderiv ℝ η x (coordinateVector 2 1)) 0))) 0 := by\n    have hinverse (τ : ℝ → E2 → E2) (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))\n        (hzero : ∀ x, τ 0 x = x) :\n        ∀ᶠ s in 𝓝 (0:ℝ), ∃ ρ : E2 → E2, ContDiff ℝ ∞ ρ ∧\n          ∀ x ∈ Metric.ball (0:E2) 2, ρ (τ s x) = x := by\n      have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n          (hz : ∀ x, tau 0 x = x) :\n          ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ Metric.closedBall (0:E2) 3,\n            ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by\n        have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n            (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n          have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n            convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n              ext z <;> simp [ContinuousLinearMap.inr]\n          exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n        have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n          simp_rw [he]\n          exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n        have hnorm : Continuous (fun p : ℝ × E2 =>\n            ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=\n          (hf.sub continuous_const).norm\n        apply (isCompact_closedBall (0 : E2) 3).eventually_forall_of_forall_eventually\n        intro x hx\n        apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const\n        have hz' : tau 0 = id := funext hz\n        simp [hz']\n    \n      let φ : ContDiffBump (0:E2) := ⟨2,3,by norm_num,by norm_num⟩\n      let F : ℝ → E2 → E2 := fun s x => x + φ x • (τ s x - x)\n      have hF : ContDiff ℝ ∞ (fun p : ℝ × E2 => F p.1 p.2) :=\n        contDiff_snd.add ((φ.contDiff.comp contDiff_snd).smul (hτ.sub contDiff_snd))\n      have hFzero (x : E2) : F 0 x = x := by simp [F,hzero]\n      filter_upwards [huniform F hF hFzero] with s hs\n      have hFs : ContDiff ℝ ∞ (F s) := hF.comp (contDiff_const.prodMk contDiff_id)\n      have hbound (x : E2) : ‖fderiv ℝ (F s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2:ℝ) := by\n        by_cases hx : x ∈ Metric.closedBall (0:E2) 3\n        · exact hs x hx\n        · have he : F s =ᶠ[𝓝 x] id := by\n            have hn : {y : E2 | y ∉ Metric.closedBall (0:E2) 3} ∈ 𝓝 x :=\n              Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx\n            filter_upwards [hn] with y hy\n            have hφ : φ y = 0 := by\n              apply φ.zero_of_le_dist\n              change 3 ≤ dist y 0\n              exact le_of_lt (lt_of_not_ge hy)\n            simp [F,hφ]\n          rw [he.fderiv_eq, fderiv_id]\n          norm_num\n      have hdiff : Differentiable ℝ (fun x => F s x - x) := hFs.differentiable (by simp) |>.sub differentiable_id\n      have hLip : LipschitzOnWith (1/2:ℝ≥0) (fun x => F s x - x) univ := by\n        apply convex_univ.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hdiff x)\n        intro x hx\n        have hi : DifferentiableAt ℝ (fun y : E2 => y) x := differentiableAt_id\n        rw [fderiv_fun_sub (hFs.differentiable (by simp) x) hi, fderiv_fun_id]\n        exact_mod_cast (hbound x).le\n      have happ : ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℝ E2) univ (1/2:ℝ≥0) :=\n        hLip.approximatesLinearOn (f := F s) (f' := ContinuousLinearMap.id ℝ E2)\n      let e : E2 ≃ₜ E2 := ApproximatesLinearOn.toHomeomorph (F s) (f' := ContinuousLinearEquiv.refl ℝ E2) happ\n        (Or.inr (by norm_num))\n      have he : (e : E2 → E2) = F s := rfl\n      have hD (x : E2) : ∃ D : E2 ≃L[ℝ] E2, (D : E2 →L[ℝ] E2) = fderiv ℝ (F s) x := by\n        let A := fderiv ℝ (F s) x\n        have hinj : Injective A := by\n          apply LinearMap.ker_eq_bot.mp\n          apply LinearMap.ker_eq_bot'.mpr\n          intro v hv\n          change A v = 0 at hv\n          have hz : (A - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]\n          have hn := (A - ContinuousLinearMap.id ℝ E2).le_opNorm v\n          rw [hz,norm_neg] at hn\n          have hb : ‖A - ContinuousLinearMap.id ℝ E2‖ < 1 := lt_trans (hbound x) (by norm_num)\n          have hnv : ‖v‖ = 0 := by nlinarith [norm_nonneg v]\n          exact norm_eq_zero.mp hnv\n        have hsurj : Surjective A := LinearMap.injective_iff_surjective.mp hinj\n        exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)\n          (LinearMap.range_eq_top.mpr hsurj),ContinuousLinearEquiv.coe_ofBijective _ _ _⟩\n      choose D hDeq using hD\n      have hsmooth : ContDiff ℝ ∞ (e.symm : E2 → E2) := by\n        apply e.contDiff_symm (f₀' := D)\n        · intro x\n          rw [he,hDeq x]\n          exact (hFs.differentiable (by simp) x).hasFDerivAt\n        · rw [he]; exact hFs\n      refine ⟨e.symm,hsmooth,?_⟩\n      intro x hx\n      have hφ : φ x = 1 := φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)\n      have hxF : F s x = τ s x := by simp [F,hφ]\n      rw [← hxF,← he]\n      exact e.symm_apply_apply x\n    have hjoint (τ ρ : ℝ → E2 → E2)\n        (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))\n        (hzero : ∀ x, τ 0 x = x)\n        (hinv : ∀ᶠ s in 𝓝 (0:ℝ), ∀ x ∈ Metric.ball (0:E2) 2, ρ s (τ s x) = x) :\n        ∀ x ∈ Metric.closedBall (0:E2) 1,\n          ρ 0 x = x ∧ ContDiffAt ℝ ∞ (fun p : ℝ × E2 => ρ p.1 p.2) (0,x) := by\n      intro x hx\n      have hx2 : x ∈ Metric.ball (0:E2) 2 := by\n        exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by norm_num))\n      have hρ0 : ρ 0 x = x := by simpa only [hzero] using hinv.self_of_nhds x hx2\n      refine ⟨hρ0,?_⟩\n      let T : ℝ × E2 → ℝ × E2 := fun p => (p.1,τ p.1 p.2)\n      let U : ℝ × E2 → ℝ × E2 := fun p => (p.1,ρ p.1 p.2)\n      have hT : ContDiff ℝ ∞ T := contDiff_fst.prodMk hτ\n      have hT0 : T (0,x) = (0,x) := by simp [T,hzero]\n      let D := fderiv ℝ T (0,x)\n      have hfst (v : ℝ × E2) : (D v).1 = v.1 := by\n        have hh := (hasFDerivAt_fst (p := T (0,x))).comp (0,x)\n          (hT.differentiable (by simp) (0,x)).hasFDerivAt\n        have hh' : HasFDerivAt (fun p : ℝ × E2 => p.1)\n            ((ContinuousLinearMap.fst ℝ ℝ E2).comp D) (0,x) := hh\n        have he := hh'.unique (hasFDerivAt_fst (p := (0,x)))\n        exact congrArg (fun L : (ℝ × E2) →L[ℝ] ℝ => L v) he\n      have hinr (v : E2) : D (0,v) = (0,v) := by\n        have hi : HasFDerivAt (fun y : E2 => ((0:ℝ),y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n          convert (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) x).prodMk (hasFDerivAt_id x) using 1 <;>\n            ext y <;> simp [ContinuousLinearMap.inr]\n        have hh := (hT.differentiable (by simp) (0,x)).hasFDerivAt.comp x hi\n        have hh' : HasFDerivAt (fun y : E2 => ((0:ℝ),y))\n            (D.comp (ContinuousLinearMap.inr ℝ ℝ E2)) x := by\n          change HasFDerivAt (fun y : E2 => ((0:ℝ),τ 0 y)) (D.comp (ContinuousLinearMap.inr ℝ ℝ E2)) x at hh\n          simpa only [hzero] using hh\n        have he := hh'.unique hi\n        exact congrArg (fun L : E2 →L[ℝ] (ℝ × E2) => L v) he\n      have hDinj : Injective D := by\n        apply LinearMap.ker_eq_bot.mp\n        apply LinearMap.ker_eq_bot'.mpr\n        intro v hv\n        change D v = 0 at hv\n        have hv1 : v.1 = 0 := by rw [← hfst v,hv]; rfl\n        have hv' : v = (0,v.2) := Prod.ext hv1 rfl\n        rw [hv',hinr] at hv\n        exact hv'.trans hv\n      let e : (ℝ × E2) ≃L[ℝ] (ℝ × E2) := ContinuousLinearEquiv.ofBijective D\n        (LinearMap.ker_eq_bot.mpr hDinj)\n        (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp hDinj))\n      have he : (e : (ℝ × E2) →L[ℝ] (ℝ × E2)) = D :=\n        ContinuousLinearEquiv.coe_ofBijective _ _ _\n      have hTd : HasFDerivAt T (e : (ℝ × E2) →L[ℝ] (ℝ × E2)) (0,x) := by\n        rw [he]\n        exact (hT.differentiable (by simp) (0,x)).hasFDerivAt\n      have hleft : ∀ᶠ p in 𝓝 ((0:ℝ),x), U (T p) = p := by\n        have hp := (continuous_fst.tendsto ((0:ℝ),x)).eventually hinv\n        have hxevent : ∀ᶠ p in 𝓝 ((0:ℝ),x), p.2 ∈ Metric.ball (0:E2) 2 :=\n          (continuous_snd.tendsto ((0:ℝ),x)).eventually (Metric.isOpen_ball.mem_nhds hx2)\n        filter_upwards [hp,hxevent] with p hp hx\n        exact Prod.ext rfl (hp p.2 hx)\n      have hsame := (hT.contDiffAt.hasStrictFDerivAt' hTd (by simp)).localInverse_unique hleft\n      have hsmooth := hT.contDiffAt.to_localInverse hTd (by simp)\n      have hU : ContDiffAt ℝ ∞ U (T (0,x)) := hsmooth.congr_of_eventuallyEq hsame\n      rw [hT0] at hU\n      exact contDiffAt_snd.comp (0,x) hU\n    have hjetderiv (τ ρ : ℝ → E2 → E2) (η : E2 → E2)\n        (hτ : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2))\n        (hzero : ∀ x, τ 0 x = x)\n        (hvelocity : ∀ x, HasDerivAt (fun s => τ s x) (η x) 0)\n        (x : E2) (hρ0 : ρ 0 x = x)\n        (hρ : ContDiffAt ℝ ∞ (fun p : ℝ × E2 => ρ p.1 p.2) (0,x))\n        (v : E2) :\n        HasDerivAt (fun s => fderiv ℝ (τ s) (ρ s x) v) (fderiv ℝ η x v) 0 := by\n      let T : ℝ × E2 → E2 := fun p => τ p.1 p.2\n      have hDT : ContDiff ℝ ∞ (fderiv ℝ T) := hτ.fderiv_right (by simp)\n      have hdiff : Differentiable ℝ (fderiv ℝ T) := hDT.differentiable (by simp)\n      let K : ℝ × E2 → E2 := fun p => fderiv ℝ T p (0,v)\n      let L : ℝ × E2 → E2 := fun p => fderiv ℝ T p (1,0)\n      have hK : ContDiff ℝ ∞ K := hDT.clm_apply contDiff_const\n      have hL : ContDiff ℝ ∞ L := hDT.clm_apply contDiff_const\n      have he (s : ℝ) (y : E2) : K (s,y) = fderiv ℝ (τ s) y v := by\n        have hi : HasFDerivAt (fun z : E2 => (s,z)) (ContinuousLinearMap.inr ℝ ℝ E2) y := by\n          convert (hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id y) using 1 <;>\n            ext z <;> simp [ContinuousLinearMap.inr]\n        have hh := ((hτ.differentiable (by simp) (s,y)).hasFDerivAt.comp y hi).fderiv\n        exact (congrArg (fun A : E2 →L[ℝ] E2 => A v) hh).symm\n      have hK0 : (fun y => K (0,y)) = fun _ => v := by\n        funext y\n        rw [he]\n        have hz : τ 0 = id := funext hzero\n        simp [hz]\n      have hL0 : (fun y => L (0,y)) = η := by\n        funext y\n        have hi : HasDerivAt (fun s : ℝ => (s,y)) ((1:ℝ),(0:E2)) 0 :=\n          (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 y)\n        have hh := (hτ.differentiable (by simp) (0,y)).hasFDerivAt.comp_hasDerivAt 0 hi\n        change HasDerivAt (fun s => τ s y) (L (0,y)) 0 at hh\n        exact hh.unique (hvelocity y)\n      have hinr : HasFDerivAt (fun y : E2 => ((0:ℝ),y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n        convert (hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) x).prodMk (hasFDerivAt_id x) using 1 <;>\n          ext z <;> simp [ContinuousLinearMap.inr]\n      have hKsp (w : E2) : fderiv ℝ K (0,x) (0,w) = 0 := by\n        have hh := ((hK.differentiable (by simp) (0,x)).hasFDerivAt.comp x hinr).fderiv\n        change fderiv ℝ (fun y => K (0,y)) x = _ at hh\n        rw [hK0,fderiv_fun_const] at hh\n        exact (congrArg (fun A : E2 →L[ℝ] E2 => A w) hh).symm\n      have hLsp : fderiv ℝ L (0,x) (0,v) = fderiv ℝ η x v := by\n        have hh := ((hL.differentiable (by simp) (0,x)).hasFDerivAt.comp x hinr).fderiv\n        change fderiv ℝ (fun y => L (0,y)) x = _ at hh\n        rw [hL0] at hh\n        exact (congrArg (fun A : E2 →L[ℝ] E2 => A v) hh).symm\n      have hKt : fderiv ℝ K (0,x) (1,0) = fderiv ℝ η x v := by\n        rw [← hLsp]\n        dsimp only [K,L]\n        rw [fderiv_clm_apply (hdiff (0,x)) (differentiableAt_const _),\n          fderiv_clm_apply (hdiff (0,x)) (differentiableAt_const _)]\n        simp only [fderiv_fun_const,ContinuousLinearMap.zero_apply,ContinuousLinearMap.add_apply,\n          ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,map_zero,Pi.zero_apply,\n          zero_add,add_zero]\n        exact ((hτ.contDiffAt (x := (0,x))).isSymmSndFDerivAt (by simp)).eq (1,0) (0,v)\n      have hKd (w : E2) : fderiv ℝ K (0,x) (1,w) = fderiv ℝ η x v := by\n        have he' : ((1:ℝ),w) = (1,0) + (0,w) := by ext <;> simp\n        rw [he',map_add,hKt,hKsp,add_zero]\n      have hρline : DifferentiableAt ℝ (fun s => ρ s x) 0 :=\n        by\n          have hh := hρ.differentiableAt (by simp)\n          have hc : DifferentiableAt ℝ (fun s : ℝ => ((s:ℝ),x)) 0 := differentiableAt_id.prodMk (differentiableAt_const x)\n          have hcomp := hh.comp 0 hc\n          change DifferentiableAt ℝ (fun s : ℝ => ρ s x) 0 at hcomp\n          exact hcomp\n      have hcurve := (hasDerivAt_id (0:ℝ)).prodMk hρline.hasDerivAt\n      have hh := (hK.differentiable (by simp) (0,ρ 0 x)).hasFDerivAt.comp_hasDerivAt 0 hcurve\n      rw [hρ0,hKd] at hh\n      change HasDerivAt (fun s => K (s,ρ s x)) (fderiv ℝ η x v) 0 at hh\n      simpa only [he] using hh\n    have hpositive (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n        (hz : ∀ x, tau 0 x = x) :\n        ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,\n          0 < (fderiv ℝ (tau s) x).det := by\n      have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n          (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n        have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n          convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n            ext z <;> simp [ContinuousLinearMap.inr]\n        exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n      have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n        simp_rw [he]\n        exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n      have hdet : Continuous (fun p : ℝ × E2 => (fderiv ℝ (tau p.1) p.2).det) :=\n        ContinuousLinearMap.continuous_det.comp hf\n      apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually\n      intro x hx\n      apply (hdet.continuousAt (x := (0,x))).eventually_const_lt\n      have hz' : tau 0 = id := funext hz\n      simp only [hz',fderiv_id]\n      change (0:ℝ) < LinearMap.det (LinearMap.id : E2 →ₗ[ℝ] E2)\n      simp\n    have htransport (τ ρ : E2 → E2) (hc : ContDiff ℝ ∞ τ)\n        (hb : BijOn τ (disc 1) (disc 1))\n        (hinv : ∀ x ∈ disc 1, ρ (τ x) = x)\n        (hdet : ∀ x ∈ disc 1, 0 < (fderiv ℝ τ x).det)\n        (M : E2 → Mat2) (hsym : SymmetricOn M univ)\n        (f : E2 → E2) (d : Fin 2 → E2 → E2) :\n        let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n          (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))\n        let a := fun x => (fderiv ℝ τ (ρ x) (coordinateVector 2 0)) 0\n        let b := fun x => (fderiv ℝ τ (ρ x) (coordinateVector 2 1)) 0\n        let c := fun x => (fderiv ℝ τ (ρ x) (coordinateVector 2 0)) 1\n        let e := fun x => (fderiv ℝ τ (ρ x) (coordinateVector 2 1)) 1\n        metricDirichlet M (f ∘ τ) dt = (1/2:ℝ) * ∫ x in disc 1,\n          (metricE M f d x * (a x^2 + b x^2) +\n            2*metricF M f d x * (a x*c x + b x*e x) +\n            metricH M f d x * (c x^2 + e x^2)) / (a x*e x-b x*c x) := by\n      dsimp only\n      let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n        (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))\n      let J : E2 → Mat2 := fun x i j => (fderiv ℝ τ x (coordinateVector 2 j)) i\n      have hdetJ (x : E2) : (fderiv ℝ τ x).det = J x 0 0 * J x 1 1 - J x 0 1 * J x 1 0 := by\n        change LinearMap.det (fderiv ℝ τ x).toLinearMap = _\n        rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]\n        change Matrix.det (J x) = _\n        exact Matrix.det_fin_two _\n      have hdensity (x : E2) : metricDirichletDensity M (f ∘ τ) dt x =\n          metricE M f d (τ x) * (J x 0 0 ^ 2 + J x 0 1 ^ 2) +\n          2 * metricF M f d (τ x) * (J x 0 0 * J x 1 0 + J x 0 1 * J x 1 1) +\n          metricH M f d (τ x) * (J x 1 0 ^ 2 + J x 1 1 ^ 2) := by\n        have hm : M (f (τ x)) 1 0 = M (f (τ x)) 0 1 := by\n          exact hsym (f (τ x)) (mem_univ _) 1 0\n        unfold metricDirichletDensity metricE metricF metricH weakColumn matrixAction\n        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,\n          Pi.star_apply, star_trivial, Function.comp_apply]\n        change _ = _\n        dsimp only [dt]\n        simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,\n          Pi.star_apply, star_trivial]\n        have heval (v : Fin 2 → ℝ) (i : Fin 2) : ((EuclideanSpace.equiv (Fin 2) ℝ).symm v) i = v i := rfl\n        simp only [heval]\n        change _ = _\n        dsimp only [J]\n        rw [hm]\n        ring\n      let L : E2 → ℝ := fun x =>\n        (metricE M f d x * (J (ρ x) 0 0 ^ 2 + J (ρ x) 0 1 ^ 2) +\n          2 * metricF M f d x * (J (ρ x) 0 0 * J (ρ x) 1 0 + J (ρ x) 0 1 * J (ρ x) 1 1) +\n          metricH M f d x * (J (ρ x) 1 0 ^ 2 + J (ρ x) 1 1 ^ 2)) /\n            (J (ρ x) 0 0 * J (ρ x) 1 1 - J (ρ x) 0 1 * J (ρ x) 1 0)\n      change (1/2:ℝ) * (∫ x in disc 1, metricDirichletDensity M (f ∘ τ) dt x) =\n        (1/2:ℝ) * ∫ x in disc 1, L x\n      congr 1\n      have hd : ∀ x ∈ disc 1, HasFDerivWithinAt τ (fderiv ℝ τ x) (disc 1) x :=\n        fun x _ => (hc.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt\n      have hv := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)\n        (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet) hd hb.injOn L\n      rw [hb.image_eq] at hv\n      rw [hv]\n      apply setIntegral_congr_fun (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)\n      intro x hx\n      rw [hdensity]\n      dsimp only [L]\n      rw [hinv x hx,abs_of_pos (hdet x hx)]\n      rw [hdetJ]\n      change _ = _ * (_ / _)\n      exact (mul_div_cancel₀ _ (by simpa only [hdetJ] using (hdet x hx).ne')).symm\n    have henergy (a b c e : ℝ → E2 → ℝ) (da db dc de : E2 → ℝ)\n        (ha : ∀ x ∈ Metric.closedBall (0:E2) 1, ContDiffAt ℝ 2 (fun p : ℝ × E2 => a p.1 p.2) (0,x))\n        (hb : ∀ x ∈ Metric.closedBall (0:E2) 1, ContDiffAt ℝ 2 (fun p : ℝ × E2 => b p.1 p.2) (0,x))\n        (hc : ∀ x ∈ Metric.closedBall (0:E2) 1, ContDiffAt ℝ 2 (fun p : ℝ × E2 => c p.1 p.2) (0,x))\n        (he : ∀ x ∈ Metric.closedBall (0:E2) 1, ContDiffAt ℝ 2 (fun p : ℝ × E2 => e p.1 p.2) (0,x))\n        (hinit : ∀ x ∈ Metric.closedBall (0:E2) 1, a 0 x = 1 ∧ b 0 x = 0 ∧ c 0 x = 0 ∧ e 0 x = 1)\n        (hd : ∀ x ∈ Metric.closedBall (0:E2) 1,\n          HasDerivAt (fun s => a s x) (da x) 0 ∧ HasDerivAt (fun s => b s x) (db x) 0 ∧\n          HasDerivAt (fun s => c s x) (dc x) 0 ∧ HasDerivAt (fun s => e s x) (de x) 0)\n        (E F H : E2 → ℝ) (hE : IntegrableOn E (disc 1))\n        (hF : IntegrableOn F (disc 1)) (hH : IntegrableOn H (disc 1)) :\n        HasDerivAt (fun s => (1/2:ℝ) * ∫ x in disc 1,\n          (E x * (a s x^2 + b s x^2) + 2*F x * (a s x*c s x + b s x*e s x) +\n            H x * (c s x^2 + e s x^2)) / (a s x*e s x-b s x*c s x))\n          ((1/2:ℝ) * ∫ x in disc 1,\n            (E x-H x)*(da x-de x) + (2*F x)*(dc x+db x)) 0 := by\n      have hweighted (q : ℝ → E2 → ℝ)\n          (hq : ∀ x ∈ Metric.closedBall (0:E2) 1,\n            ContDiffAt ℝ 2 (fun p : ℝ × E2 => q p.1 p.2) (0,x))\n          (w : E2 → ℝ) (hw : IntegrableOn w (disc 1)) :\n          (∀ᶠ s in 𝓝 (0:ℝ), IntegrableOn (fun x => w x * q s x) (disc 1)) ∧\n          IntegrableOn (fun x => w x * fderiv ℝ (fun p : ℝ × E2 => q p.1 p.2) (0,x) (1,0)) (disc 1) ∧\n          HasDerivAt (fun s => ∫ x in disc 1, w x * q s x)\n            (∫ x in disc 1, w x * fderiv ℝ (fun p : ℝ × E2 => q p.1 p.2) (0,x) (1,0)) 0 := by\n        let Q : ℝ × E2 → ℝ := fun p => q p.1 p.2\n        let D : ℝ → E2 → ℝ := fun s x => fderiv ℝ Q (s,x) (1,0)\n        have hinit : ContinuousOn (q 0) (Metric.closedBall (0:E2) 1) := by\n          intro x hx\n          exact ((hq x hx).continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt\n        have hDc : ∀ x ∈ Metric.closedBall (0:E2) 1, ContinuousAt (fun p : ℝ × E2 => D p.1 p.2) (0,x) := by\n          intro x hx\n          exact ((hq x hx).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const\n        have hD0 : ContinuousOn (D 0) (Metric.closedBall (0:E2) 1) := by\n          intro x hx\n          exact ((hDc x hx).comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt\n        obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hD0\n        have hev : ∀ᶠ s in 𝓝 (0:ℝ), ∀ x ∈ Metric.closedBall (0:E2) 1,\n            ContDiffAt ℝ 2 Q (s,x) ∧ ‖D s x‖ < C+1 := by\n          apply (isCompact_closedBall (0:E2) 1).eventually_forall_of_forall_eventually\n          intro x hx\n          exact ((hq x hx).eventually (by norm_num)).and\n            ((hDc x hx).norm.eventually_lt_const (lt_of_le_of_lt (hC x hx) (by linarith)))\n        obtain ⟨S,hS,hprops⟩ := Filter.eventually_iff_exists_mem.mp hev\n        have hqS (s : ℝ) (hs : s ∈ S) : ContinuousOn (q s) (disc 1) := by\n          intro x hx\n          exact (((hprops s hs x (Metric.ball_subset_closedBall hx)).1.continuousAt).comp\n            (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt\n        have hDmeas : AEStronglyMeasurable (D 0) (volume.restrict (disc 1)) :=\n          (hD0.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet\n        have hinitint : IntegrableOn (fun x => w x * q 0 x) (disc 1) := by\n          obtain ⟨B,hB⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hinit\n          apply hw.mul_bdd ((hinit.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet)\n          filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx\n          exact hB x (Metric.ball_subset_closedBall hx)\n        have hderiv (s : ℝ) (hs : s ∈ S) (x : E2) (hx : x ∈ disc 1) :\n            HasDerivAt (fun t => w x * q t x) (w x * D s x) s := by\n          have hline : HasDerivAt (fun t : ℝ => (t,x)) ((1:ℝ),(0:E2)) s :=\n            (hasDerivAt_id s).prodMk (hasDerivAt_const s x)\n          exact (((hprops s hs x (Metric.ball_subset_closedBall hx)).1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s hline).const_mul (w x)\n        have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (disc 1))\n          (F := fun s x => w x * q s x) (F' := fun s x => w x * D s x)\n          (bound := fun x => ‖w x‖ * |C+1|) hS\n          (Filter.eventually_of_mem hS (fun s hs => hw.aestronglyMeasurable.mul\n            ((hqS s hs).aestronglyMeasurable Metric.isOpen_ball.measurableSet)))\n          hinitint (hw.aestronglyMeasurable.mul hDmeas)\n          (by\n            filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx\n            intro s hs\n            rw [norm_mul]\n            exact mul_le_mul_of_nonneg_left\n              ((hprops s hs x (Metric.ball_subset_closedBall hx)).2.le.trans (le_abs_self _)) (norm_nonneg _))\n          (hw.norm.mul_const |C+1|)\n          (by\n            filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx\n            exact fun s hs => hderiv s hs x hx)\n        refine ⟨?_,h.1,h.2⟩\n        filter_upwards [hS] with s hs\n        have hc : ContinuousOn (q s) (Metric.closedBall (0:E2) 1) := by\n          intro x hx\n          exact (((hprops s hs x hx).1.continuousAt).comp\n            (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt\n        obtain ⟨B,hB⟩ := (isCompact_closedBall (0:E2) 1).exists_bound_of_continuousOn hc\n        apply hw.mul_bdd ((hc.mono Metric.ball_subset_closedBall).aestronglyMeasurable Metric.isOpen_ball.measurableSet)\n        filter_upwards [ae_restrict_mem (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)] with x hx\n        exact hB x (Metric.ball_subset_closedBall hx)\n      let qE := fun s x => (a s x^2+b s x^2)/(a s x*e s x-b s x*c s x)\n      let qF := fun s x => 2*(a s x*c s x+b s x*e s x)/(a s x*e s x-b s x*c s x)\n      let qH := fun s x => (c s x^2+e s x^2)/(a s x*e s x-b s x*c s x)\n      have hden (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n          a 0 x*e 0 x-b 0 x*c 0 x ≠ 0 := by\n        obtain ⟨h1,h2,h3,h4⟩ := hinit x hx\n        simp only [h1,h2,h3,h4]; norm_num\n      have hqE (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n          ContDiffAt ℝ 2 (fun p : ℝ × E2 => qE p.1 p.2) (0,x) :=\n        (((ha x hx).pow 2).add ((hb x hx).pow 2)).div\n          (((ha x hx).mul (he x hx)).sub ((hb x hx).mul (hc x hx))) (hden x hx)\n      have hqF (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n          ContDiffAt ℝ 2 (fun p : ℝ × E2 => qF p.1 p.2) (0,x) :=\n        (contDiffAt_const.mul (((ha x hx).mul (hc x hx)).add ((hb x hx).mul (he x hx)))).div\n          (((ha x hx).mul (he x hx)).sub ((hb x hx).mul (hc x hx))) (hden x hx)\n      have hqH (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n          ContDiffAt ℝ 2 (fun p : ℝ × E2 => qH p.1 p.2) (0,x) :=\n        (((hc x hx).pow 2).add ((he x hx).pow 2)).div\n          (((ha x hx).mul (he x hx)).sub ((hb x hx).mul (hc x hx))) (hden x hx)\n      let D := fun (q : ℝ → E2 → ℝ) x => fderiv ℝ (fun p : ℝ × E2 => q p.1 p.2) (0,x) (1,0)\n      have hqderiv (q : ℝ → E2 → ℝ) (x : E2)\n          (hq : ContDiffAt ℝ 2 (fun p : ℝ × E2 => q p.1 p.2) (0,x)) :\n          HasDerivAt (fun s => q s x) (D q x) 0 := by\n        have hi : HasDerivAt (fun s : ℝ => (s,x)) ((1:ℝ),(0:E2)) 0 :=\n          (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const 0 x)\n        have hh := (hq.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hi\n        exact hh\n      have hDs (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n          D qE x = da x-de x ∧ D qF x = 2*(dc x+db x) ∧ D qH x = de x-da x := by\n        obtain ⟨ha0,hb0,hc0,he0⟩ := hinit x hx\n        obtain ⟨ha',hb',hc',he'⟩ := hd x hx\n        have hden' := (ha'.mul he').sub (hb'.mul hc')\n        have hqe : HasDerivAt (fun s => qE s x) (da x-de x) 0 := by\n          convert ((ha'.pow 2).add (hb'.pow 2)).div hden' (hden x hx) using 1 <;>\n            simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,ha0,hb0,hc0,he0] <;> norm_num <;> ring\n        have hqf : HasDerivAt (fun s => qF s x) (2*(dc x+db x)) 0 := by\n          convert (((ha'.mul hc').add (hb'.mul he')).const_mul 2).div hden' (hden x hx) using 1 <;>\n            simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,ha0,hb0,hc0,he0] <;> norm_num <;> ring\n        have hqh : HasDerivAt (fun s => qH s x) (de x-da x) 0 := by\n          convert ((hc'.pow 2).add (he'.pow 2)).div hden' (hden x hx) using 1 <;>\n            simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,ha0,hb0,hc0,he0] <;> norm_num <;> ring\n        exact ⟨(hqderiv qE x (hqE x hx)).unique hqe,\n          (hqderiv qF x (hqF x hx)).unique hqf,(hqderiv qH x (hqH x hx)).unique hqh⟩\n      obtain ⟨hEi,hED,hEd⟩ := hweighted qE hqE E hE\n      obtain ⟨hFi,hFD,hFd⟩ := hweighted qF hqF F hF\n      obtain ⟨hHi,hHD,hHd⟩ := hweighted qH hqH H hH\n      have hevent : (fun s => (1/2:ℝ) * ∫ x in disc 1,\n          (E x * (a s x^2 + b s x^2) + 2*F x * (a s x*c s x + b s x*e s x) +\n            H x * (c s x^2 + e s x^2)) / (a s x*e s x-b s x*c s x)) =ᶠ[𝓝 0]\n          (fun s => (1/2:ℝ) * ((∫ x in disc 1,E x*qE s x) + (∫ x in disc 1,F x*qF s x) +\n            (∫ x in disc 1,H x*qH s x))) := by\n        filter_upwards [hEi,hFi,hHi] with s hEi hFi hHi\n        have hsum : IntegrableOn (fun x => E x*qE s x+F x*qF s x) (disc 1) := hEi.add hFi\n        rw [← integral_add hEi hFi,← integral_add hsum hHi]\n        congr 1\n        apply integral_congr_ae\n        exact Filter.Eventually.of_forall fun x => by dsimp only [qE,qF,qH]; ring\n      have hval : (∫ x in disc 1,E x*D qE x) + (∫ x in disc 1,F x*D qF x) +\n          (∫ x in disc 1,H x*D qH x) = ∫ x in disc 1,\n            (E x-H x)*(da x-de x) + (2*F x)*(dc x+db x) := by\n        have hsum : IntegrableOn (fun x => E x*D qE x+F x*D qF x) (disc 1) := hED.add hFD\n        change IntegrableOn (fun x => E x*D qE x) (disc 1) at hED\n        change IntegrableOn (fun x => F x*D qF x) (disc 1) at hFD\n        change IntegrableOn (fun x => H x*D qH x) (disc 1) at hHD\n        rw [← integral_add hED hFD,← integral_add hsum hHD]\n        apply setIntegral_congr_fun (show MeasurableSet (disc 1) from Metric.isOpen_ball.measurableSet)\n        intro x hx\n        obtain ⟨h1,h2,h3⟩ := hDs x (Metric.ball_subset_closedBall hx)\n        change E x*D qE x+F x*D qF x+H x*D qH x = _\n        rw [h1,h2,h3]\n        ring\n      have hh := ((hEd.add hFd).add hHd).const_mul (1/2:ℝ)\n      change HasDerivAt _ ((1/2:ℝ)*((∫ x in disc 1,E x*D qE x) + (∫ x in disc 1,F x*D qF x) +\n          (∫ x in disc 1,H x*D qH x))) 0 at hh\n      rw [hval] at hh\n      exact hh.congr_of_eventuallyEq hevent\n    classical\n    let P : ℝ → (E2 → E2) → Prop := fun s r => ContDiff ℝ ∞ r ∧\n      ∀ x ∈ Metric.ball (0:E2) 2, r (τ s x) = x\n    let ρ : ℝ → E2 → E2 := fun s => if h : ∃ r, P s r then h.choose else id\n    have hρevent : ∀ᶠ s in 𝓝 (0:ℝ), P s (ρ s) := by\n      filter_upwards [hinverse τ hτ hzero] with s hs\n      change ∃ r, P s r at hs\n      dsimp only [ρ]\n      rw [dif_pos hs]\n      exact hs.choose_spec\n    have hleft : ∀ᶠ s in 𝓝 (0:ℝ), ∀ x ∈ Metric.ball (0:E2) 2, ρ s (τ s x) = x :=\n      hρevent.mono fun s hs => hs.2\n    have hρjoint := hjoint τ ρ hτ hzero hleft\n    let J := fun s x i j => (fderiv ℝ (τ s) (ρ s x) (coordinateVector 2 j)) i\n    let V := fun x i j => (fderiv ℝ η x (coordinateVector 2 j)) i\n    have hJjoint (i j : Fin 2) (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n        ContDiffAt ℝ 2 (fun p : ℝ × E2 => J p.1 p.2 i j) (0,x) := by\n      have hpartial (s : ℝ) (y : E2) : fderiv ℝ (τ s) y =\n          (fderiv ℝ (fun p : ℝ × E2 => τ p.1 p.2) (s,y)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n        have hi : HasFDerivAt (fun z : E2 => (s,z)) (ContinuousLinearMap.inr ℝ ℝ E2) y := by\n          convert (hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id y) using 1 <;>\n            ext z <;> simp [ContinuousLinearMap.inr]\n        exact ((hτ.differentiable (by simp) (s,y)).hasFDerivAt.comp y hi).fderiv\n      have hD : ContDiff ℝ ∞ (fun p : ℝ × E2 => fderiv ℝ (τ p.1) p.2) := by\n        simp_rw [hpartial]\n        exact (hτ.fderiv_right (by simp)).clm_comp contDiff_const\n      have hentry : ContDiff ℝ ∞ (fun p : ℝ × E2 => (fderiv ℝ (τ p.1) p.2 (coordinateVector 2 j)) i) :=\n        (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (hD.clm_apply contDiff_const)\n      have hh := hentry.contDiffAt.comp (0,x) (contDiffAt_fst.prodMk (hρjoint x hx).2)\n      exact hh.of_le (by simp)\n    have hJ0 (x : E2) : J 0 x 0 0 = 1 ∧ J 0 x 0 1 = 0 ∧ J 0 x 1 0 = 0 ∧ J 0 x 1 1 = 1 := by\n      have hz : τ 0 = id := funext hzero\n      simp [J,hz,coordinateVector,EuclideanSpace.single]\n    have hJderiv (i j : Fin 2) (x : E2) (hx : x ∈ Metric.closedBall (0:E2) 1) :\n        HasDerivAt (fun s => J s x i j) (V x i j) 0 := by\n      have hh := hjetderiv τ ρ η hτ hzero hvelocity x (hρjoint x hx).1 (hρjoint x hx).2 (coordinateVector 2 j)\n      exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt 0 hh\n    have hmain := henergy (fun s x => J s x 0 0) (fun s x => J s x 0 1)\n      (fun s x => J s x 1 0) (fun s x => J s x 1 1)\n      (fun x => V x 0 0) (fun x => V x 0 1) (fun x => V x 1 0) (fun x => V x 1 1)\n      (hJjoint 0 0) (hJjoint 0 1) (hJjoint 1 0) (hJjoint 1 1)\n      (fun x _ => hJ0 x) (fun x hx => ⟨hJderiv 0 0 x hx,hJderiv 0 1 x hx,hJderiv 1 0 x hx,hJderiv 1 1 x hx⟩)\n      (metricE M f d) (metricF M f d) (metricH M f d) hE hF hH\n    dsimp only\n    apply hmain.congr_of_eventuallyEq\n    filter_upwards [hbij,hleft,hpositive τ hτ hzero] with s hs hl hp\n    have hc : ContDiff ℝ ∞ (τ s) := hτ.comp (contDiff_const.prodMk contDiff_id)\n    have hl' : ∀ x ∈ disc 1, ρ s (τ s x) = x := by\n      intro x hx\n      exact hl x (Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hx) (by norm_num)))\n    exact htransport (τ s) (ρ s) hc hs hl' (fun x hx => hp x (Metric.ball_subset_closedBall hx)) M hsym f d\n  have hgeometry (η : E2 → E2) (hη : ContDiff ℝ ∞ η)\n      (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :\n      let τ := fun (s : ℝ) (x : E2) =>\n        (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)\n      let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n        (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n      let α := fun s t => t+Real.arctan (s*k t)\n      (∀ x, τ 0 x = x) ∧\n      (∀ x, HasDerivAt (fun s => τ s x) (η x) 0) ∧\n      ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) ∧\n      (∀ᶠ s in 𝓝 (0:ℝ),\n        BijOn (τ s) (disc 1) (disc 1) ∧\n        BijOn (τ s) (closedDisc 1) (closedDisc 1) ∧\n        StrictMono (α s) ∧ Continuous (α s) ∧\n        (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi) ∧\n        (∀ t, τ s (unitCircleParameter t) = unitCircleParameter (α s t)) ∧\n        (∀ x ∈ closedDisc 1, ∃ e : OpenPartialHomeomorph E2 E2,\n          (e : E2 → E2) = τ s ∧ x ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (τ s x))) := by\n    have hnormalized (η : E2 → E2) (hη : ContDiff ℝ ∞ η)\n        (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :\n        let tau : ℝ → E2 → E2 := fun s x =>\n          (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x)\n        (∀ x, tau 0 x = x) ∧\n        (∀ x, HasDerivAt (fun s => tau s x) (η x) 0) ∧\n        ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2) ∧\n        (∀ s x, ‖x‖ = 1 → ‖tau s x‖ = 1) := by\n      dsimp only\n      have hpos (s : ℝ) (x : E2) : 0 < 1 + s^2 * ‖η x‖^2 := by positivity\n      refine ⟨fun x => by simp, ?_, ?_, ?_⟩\n      · intro x\n        have ha : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s^2 * ‖η x‖^2)) 0 0 := by\n          convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖η x‖^2)).const_add 1 |>.sqrt (by simp) using 1 <;> norm_num\n        have hb : HasDerivAt (fun s : ℝ => x + s • η x) (η x) 0 := by\n          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add x\n        convert (ha.inv (by simp)).smul hb using 1 <;> norm_num\n      · have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖η p.2‖^2) :=\n          (hη.comp contDiff_snd).norm_sq (𝕜 := ℝ)\n        have hd : ContDiff ℝ ∞ (fun p : ℝ × E2 => Real.sqrt (1 + p.1^2 * ‖η p.2‖^2)) :=\n          (contDiff_const.add ((contDiff_fst.pow 2).mul hi)).sqrt (fun p => (hpos p.1 p.2).ne')\n        exact (hd.inv (fun p => (Real.sqrt_pos.mpr (hpos p.1 p.2)).ne')).smul\n          (contDiff_snd.add (contDiff_fst.smul (hη.comp contDiff_snd)))\n      · intro s x hx\n        have ht : inner ℝ x (η x) = 0 := by\n          rw [real_inner_comm]\n          exact htan x hx\n        have hn : ‖x + s • η x‖^2 = 1 + s^2 * ‖η x‖^2 := by\n          rw [norm_add_sq_real, real_inner_smul_right, ht,hx,norm_smul]\n          simp [mul_pow,sq_abs]\n        have he : ‖x + s • η x‖ = Real.sqrt (1 + s^2 * ‖η x‖^2) := by\n          rw [← hn,Real.sqrt_sq (norm_nonneg _)]\n        rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.sqrt_pos.mpr (hpos s x)),he]\n        exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos s x)).ne'\n    have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)\n        (f : E2 → E2) (d : Fin 2 → E2 → E2) :\n        (fun x => f (tau 0 x)) = f ∧\n        (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm\n          (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by\n      have hz : tau 0 = id := funext hzero\n      refine ⟨by simp [hz],?_⟩\n      funext i x\n      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n      funext j\n      simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,\n        Fin.sum_univ_two,EuclideanSpace.single]\n    have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))\n        (hz : ∀ x, tau 0 x = x) :\n        ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,\n          ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by\n      have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =\n          (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by\n        have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by\n          convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>\n            ext z <;> simp [ContinuousLinearMap.inr]\n        exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv\n      have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by\n        simp_rw [he]\n        exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const\n      have hnorm : Continuous (fun p : ℝ × E2 =>\n          ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=\n        (hf.sub continuous_const).norm\n      apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually\n      intro x hx\n      apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const\n      have hz' : tau 0 = id := funext hz\n      simp [hz']\n    have hinjective (tau : E2 → E2) (hc : ContDiff ℝ ∞ tau)\n        (hd : ∀ x ∈ closedDisc 1,\n          ‖fderiv ℝ tau x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ)) :\n        InjOn tau (closedDisc 1) := by\n      have hf := hc.differentiable (by simp)\n      have hl : LipschitzOnWith (1/2 : ℝ≥0) (fun x => tau x - x) (closedDisc 1) := by\n        apply (convex_closedBall (0 : E2) 1).lipschitzOnWith_of_nnnorm_fderiv_le\n          (fun x _ => (hf x).sub differentiableAt_id)\n        intro x hx\n        rw [fderiv_sub (hf x) differentiableAt_id, fderiv_id]\n        exact_mod_cast (hd x hx).le\n      intro x hx y hy hxy\n      have hb := hl.dist_le_mul x hx y hy\n      have he : (tau x - x) - (tau y - y) = y-x := by rw [hxy,sub_sub_sub_cancel_left]\n      rw [dist_eq_norm,he,norm_sub_rev] at hb\n      change ‖x-y‖ ≤ (1/2 : ℝ) * dist x y at hb\n      rw [← dist_eq_norm] at hb\n      exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])\n    have hangle (η : E2 → E2)\n        (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) (s t : ℝ) :\n        let x := unitCircleParameter t\n        let k := x 0 * η x 1 - x 1 * η x 0\n        (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x) =\n          unitCircleParameter (t + Real.arctan (s*k)) := by\n      dsimp only\n      let x := unitCircleParameter t\n      let k := x 0 * η x 1 - x 1 * η x 0\n      have hc : (x 0)^2 + (x 1)^2 = 1 := by\n        simpa [x,circle_def] using Real.cos_sq_add_sin_sq t\n      have hnorm : ‖x‖ = 1 := by\n        have hn : ‖x‖^2 = 1 := by\n          calc\n            ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm\n            _ = 1 := by\n              simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two] using hc\n        nlinarith [norm_nonneg x]\n      have ht : η x 0 * x 0 + η x 1 * x 1 = 0 := by\n        simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm] using htan x hnorm\n      have h0 : η x 0 = -k * x 1 := by\n        dsimp only [k]\n        linear_combination -(η x 0)*hc + x 0*ht\n      have h1 : η x 1 = k * x 0 := by\n        dsimp only [k]\n        linear_combination -(η x 1)*hc + x 1*ht\n      have hn : ‖η x‖^2 = k^2 := by\n        rw [← real_inner_self_eq_norm_sq]\n        simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]\n        rw [h0,h1]\n        nlinarith [sq_nonneg k]\n      change (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x) = _\n      rw [hn]\n      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n      funext j\n      fin_cases j\n      · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 0 + s*η x 0) =\n          Real.cos (t+Real.arctan (s*k))\n        rw [h0,Real.cos_add,Real.cos_arctan,Real.sin_arctan]\n        change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.cos t + s*(-k*Real.sin t)) = _\n        simp only [mul_pow,div_eq_mul_inv]\n        ring\n      · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 1 + s*η x 1) =\n          Real.sin (t+Real.arctan (s*k))\n        rw [h1,Real.sin_add,Real.cos_arctan,Real.sin_arctan]\n        change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.sin t + s*(k*Real.cos t)) = _\n        simp only [mul_pow,div_eq_mul_inv]\n        ring\n    have hlift (k : ℝ → ℝ) (hk : Continuous k) (hp : Function.Periodic k (2*Real.pi)) (s : ℝ) :\n        Continuous (fun t => t + Real.arctan (s*k t)) ∧\n        (∀ t, (t+2*Real.pi) + Real.arctan (s*k (t+2*Real.pi)) =\n          (t + Real.arctan (s*k t)) + 2*Real.pi) ∧\n        Surjective (fun t => t+Real.arctan (s*k t)) := by\n      have hc : Continuous (fun t => t+Real.arctan (s*k t)) :=\n        continuous_id.add (Real.continuous_arctan.comp (continuous_const.mul hk))\n      refine ⟨hc,fun t => by rw [hp t]; ring,?_⟩\n      intro y\n      have hleft : (y-Real.pi)+Real.arctan (s*k (y-Real.pi)) ≤ y := by\n        linarith [Real.arctan_lt_pi_div_two (s*k (y-Real.pi)),Real.pi_pos]\n      have hright : y ≤ (y+Real.pi)+Real.arctan (s*k (y+Real.pi)) := by\n        linarith [Real.neg_pi_div_two_lt_arctan (s*k (y+Real.pi)),Real.pi_pos]\n      obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : y-Real.pi ≤ y+Real.pi)\n        hc.continuousOn ⟨hleft,hright⟩\n      exact ⟨t,he⟩\n    have hlocal (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (x : E2)\n        (hd : ‖fderiv ℝ τ x - ContinuousLinearMap.id ℝ E2‖ < 1) :\n        ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ ∧ x ∈ e.source ∧\n          ContDiffAt ℝ ∞ e.symm (τ x) := by\n      let D := fderiv ℝ τ x\n      have hinj : Injective D := by\n        apply (LinearMap.ker_eq_bot).mp\n        apply LinearMap.ker_eq_bot'.mpr\n        intro v hv\n        change D v = 0 at hv\n        have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]\n        have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v\n        rw [he,norm_neg] at hn\n        have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := hd\n        have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]\n        exact norm_eq_zero.mp hz\n      have hsurj : Surjective D := LinearMap.injective_iff_surjective.mp hinj\n      let d : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective D\n        (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)\n      have heq : (d : E2 →L[ℝ] E2) = D := ContinuousLinearEquiv.coe_ofBijective _ _ _\n      have hf : HasFDerivAt τ (d : E2 →L[ℝ] E2) x := by\n        rw [heq]\n        exact (hc.differentiable (by simp) x).hasFDerivAt\n      let e := hc.contDiffAt.toOpenPartialHomeomorph τ hf (by simp)\n      refine ⟨e,rfl,hc.contDiffAt.mem_toOpenPartialHomeomorph_source hf (by simp),?_⟩\n      exact hc.contDiffAt.to_localInverse hf (by simp)\n    have hcircle (x : E2) (hx : ‖x‖ = 1) : ∃ t : ℝ, unitCircleParameter t = x := by\n      let z : ℂ := ⟨x 0,x 1⟩\n      have hs : (x 0)^2+(x 1)^2=1 := by\n        have h := real_inner_self_eq_norm_sq x\n        rw [hx] at h\n        simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two,one_mul] using h\n      have hz : ‖z‖ = 1 := by\n        have hsq : ‖z‖^2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; simpa [z,Complex.normSq_apply,pow_two] using hs\n        nlinarith [norm_nonneg z]\n      have hne : z ≠ 0 := by intro h; simp [h] at hz\n      refine ⟨Complex.arg z,?_⟩\n      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n      funext j\n      fin_cases j\n      · change Real.cos (Complex.arg z) = x 0\n        rw [Complex.cos_arg hne,hz]\n        simp [z]\n      · change Real.sin (Complex.arg z) = x 1\n        rw [Complex.sin_arg,hz]\n        simp [z]\n    have hpreserve (τ : E2 → E2) (hc : Continuous τ)\n        (hinj : InjOn τ (closedDisc 1))\n        (hsphere : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ x = y)\n        (hzero : ‖τ 0‖ < 1) : MapsTo τ (disc 1) (disc 1) := by\n      intro x hx\n      change dist (τ x) 0 < 1\n      rw [dist_zero_right]\n      by_contra hn\n      have hx' : ‖x‖ < 1 := by simpa [disc_def,ball_mem_def] using hx\n      have h0 : (0:E2) ∈ disc 1 := by simp [disc_def]\n      obtain ⟨z,hz,hze⟩ := (convex_ball (0:E2) 1).isPreconnected.intermediate_value h0 hx\n        hc.norm.continuousOn ⟨hzero.le,not_lt.mp hn⟩\n      obtain ⟨w,hw,he⟩ := hsphere (τ z) hze\n      have hz' : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz\n      have hw' : w ∈ closedDisc 1 := by simpa [closed_def,closed_mem_def,hw]\n      have hzw : z = w := hinj hz' hw' he.symm\n      have hzlt : ‖z‖ < 1 := by simpa [disc_def,ball_mem_def] using hz\n      rw [hzw,hw] at hzlt\n      exact lt_irrefl _ hzlt\n    have hsurjective (τ : E2 → E2) (hc : Continuous τ)\n        (hmaps : MapsTo τ (disc 1) (disc 1))\n        (hsphere : ∀ x : E2, ‖x‖ = 1 → ‖τ x‖ = 1)\n        (hlocal : ∀ x ∈ disc 1, ∃ e : OpenPartialHomeomorph E2 E2,\n          (e : E2 → E2) = τ ∧ x ∈ e.source) :\n        SurjOn τ (disc 1) (disc 1) := by\n      have hopen : IsOpen (τ '' disc 1) := by\n        rw [isOpen_iff_mem_nhds]\n        rintro y ⟨x,hx,rfl⟩\n        obtain ⟨e,he,hxe⟩ := hlocal x hx\n        have ho := e.isOpen_image_source_inter (s := disc 1) Metric.isOpen_ball\n        have hm : τ x ∈ e '' (e.source ∩ disc 1) := ⟨x,⟨hxe,hx⟩,by rw [he]⟩\n        exact Filter.mem_of_superset (ho.mem_nhds hm) (by\n          rintro z ⟨w,hw,rfl⟩\n          exact ⟨w,hw.2,by rw [he]⟩)\n      have hcompact : IsClosed (τ '' closedDisc 1) :=\n        ((isCompact_closedBall (0:E2) 1).image hc).isClosed\n      have hclosure : closure (τ '' disc 1) ⊆ τ '' closedDisc 1 :=\n        closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact\n      have hboundary : closure (τ '' disc 1) ∩ disc 1 ⊆ τ '' disc 1 := by\n        intro y hy\n        obtain ⟨x,hx,hxy⟩ := hclosure hy.1\n        refine ⟨x,?_,hxy⟩\n        have hxle : ‖x‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hx\n        have hylt : ‖y‖ < 1 := by simpa [disc_def,ball_mem_def] using hy.2\n        have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by\n          intro hxe\n          have := hsphere x hxe\n          rw [hxy] at this\n          linarith)\n        simpa [disc_def,ball_mem_def] using hxlt\n      have h0 : (0:E2) ∈ disc 1 := by simp [disc_def]\n      exact (convex_ball (0:E2) 1).isPreconnected.subset_of_closure_inter_subset hopen\n        ⟨τ 0,hmaps h0,⟨0,h0,rfl⟩⟩ hboundary\n    have hmonotone (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)\n        (hp : Periodic k (2*Real.pi)) :\n        ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (fun t => t+Real.arctan (s*k t)) := by\n      have hpd : Periodic (deriv k) (2*Real.pi) := by\n        intro t\n        have he : (fun t => k (t+2*Real.pi)) = k := funext hp\n        rw [← deriv_comp_add_const k (2*Real.pi) t,he]\n      obtain ⟨C,hC,hbound⟩ := (hpd.isBounded_of_continuous (by positivity)\n        (hk.continuous_deriv (by simp))).exists_pos_norm_le\n      have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), |s| * C < (1/2:ℝ) := by\n        exact (continuousAt_id.abs.mul_const C).eventually_lt_const (by norm_num)\n      filter_upwards [hsmall] with s hs\n      apply strictMono_of_hasDerivAt_pos\n        (f' := fun t => 1 + (s*deriv k t)/(1+(s*k t)^2))\n      · intro t\n        convert (hasDerivAt_id t).add (((hk.differentiable (by simp) t).hasDerivAt.const_mul s).arctan) using 1 <;> first | rfl | ring\n      · intro t\n        have hb : |s*deriv k t| < (1/2:ℝ) := by\n          rw [abs_mul]\n          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left\n            (by simpa using hbound (deriv k t) ⟨t,rfl⟩) (abs_nonneg s)) hs\n        have hd : 0 < 1+(s*k t)^2 := by positivity\n        have hl : -1 < (s*deriv k t)/(1+(s*k t)^2) := by\n          rw [lt_div_iff₀ hd]\n          have hlow := (abs_lt.mp hb).1\n          nlinarith [sq_nonneg (s*k t)]\n        linarith\n    have hcoefficient (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :\n        let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n          (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n        ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by\n      dsimp only\n      have hc : ContDiff ℝ ∞ unitCircleParameter := by\n        apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp\n        apply contDiff_pi.mpr\n        intro i\n        fin_cases i\n        · simpa using Real.contDiff_cos\n        · simpa using Real.contDiff_sin\n      have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=\n        (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i\n      refine ⟨?_,?_⟩\n      · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))\n      · intro t\n        have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by\n          apply (EuclideanSpace.equiv (Fin 2) ℝ).injective\n          funext i\n          fin_cases i <;> simp [circle_def,Real.cos_add_two_pi,Real.sin_add_two_pi]\n        dsimp only\n        rw [hp]\n    dsimp only\n    let τ := fun (s : ℝ) (x : E2) =>\n      (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)\n    let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -\n      (unitCircleParameter t) 1 * η (unitCircleParameter t) 0\n    let α := fun s t => t+Real.arctan (s*k t)\n    obtain ⟨hz,hvel,hc,hsp⟩ := hnormalized η hη htan\n    have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc\n    have hcs (s : ℝ) : ContDiff ℝ ∞ (τ s) :=\n      hc'.comp (contDiff_const.prodMk contDiff_id)\n    have hu := huniform τ hc' hz\n    obtain ⟨hk,hkp⟩ := hcoefficient η hη\n    have hm := hmonotone k hk hkp\n    have hcenter : ∀ᶠ s in 𝓝 (0:ℝ), ‖τ s 0‖ < 1 := by\n      exact (((hc'.continuous.comp (continuous_id.prodMk continuous_const)).norm).continuousAt).eventually_lt_const (by simp [τ])\n    refine ⟨hz,hvel,hc',?_⟩\n    filter_upwards [hu,hm,hcenter] with s hs hms hzs\n    have hi := hinjective (τ s) (hcs s) hs\n    obtain ⟨hac,hap,has⟩ := hlift k hk.continuous hkp s\n    have hformula (t : ℝ) : τ s (unitCircleParameter t) = unitCircleParameter (α s t) :=\n      hangle η htan s t\n    have honto : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ s x = y := by\n      intro y hy\n      obtain ⟨t,ht⟩ := hcircle y hy\n      obtain ⟨u,hu⟩ := has t\n      refine ⟨unitCircleParameter u,?_,?_⟩\n      · have hh := real_inner_self_eq_norm_sq (unitCircleParameter u)\n        have hsq : ‖unitCircleParameter u‖^2 = 1 := by\n          calc\n            _ = inner ℝ (unitCircleParameter u) (unitCircleParameter u) := hh.symm\n            _ = 1 := by\n              simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]\n              change Real.cos u * Real.cos u + Real.sin u * Real.sin u = 1\n              nlinarith [Real.cos_sq_add_sin_sq u]\n        nlinarith [norm_nonneg (unitCircleParameter u)]\n      · rw [hformula]\n        change unitCircleParameter (u+Real.arctan (s*k u)) = y\n        dsimp only at hu\n        rw [hu,ht]\n    have hmap := hpreserve (τ s) (hcs s).continuous hi honto hzs\n    have hl (x : E2) (hx : x ∈ closedDisc 1) :\n        ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ s ∧ x ∈ e.source ∧\n          ContDiffAt ℝ ∞ e.symm (τ s x) :=\n      hlocal (τ s) (hcs s) x (lt_trans (hs x hx) (by norm_num))\n    have hsurj := hsurjective (τ s) (hcs s).continuous hmap (hsp s) (fun x hx => by\n      obtain ⟨e,he,hx,hd⟩ := hl x (Metric.ball_subset_closedBall hx)\n      exact ⟨e,he,hx⟩)\n    have hmapclosed : MapsTo (τ s) (closedDisc 1) (closedDisc 1) := by\n      intro x hx\n      have hxle : ‖x‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hx\n      rcases lt_or_eq_of_le hxle with hxlt | hxe\n      · exact Metric.ball_subset_closedBall (hmap (by simpa [disc_def,ball_mem_def] using hxlt))\n      · have hh : ‖τ s x‖ = 1 := hsp s x hxe\n        simpa [closed_def,closed_mem_def,hh]\n    have hsurjclosed : SurjOn (τ s) (closedDisc 1) (closedDisc 1) := by\n      intro y hy\n      have hyle : ‖y‖ ≤ 1 := by simpa [closed_def,closed_mem_def] using hy\n      rcases lt_or_eq_of_le hyle with hylt | hye\n      · obtain ⟨x,hx,hxy⟩ := hsurj (by simpa [disc_def,ball_mem_def] using hylt)\n        exact ⟨x,Metric.ball_subset_closedBall hx,hxy⟩\n      · obtain ⟨x,hx,hxy⟩ := honto y hye\n        exact ⟨x,by simpa [closed_def,closed_mem_def,hx],hxy⟩\n    exact ⟨⟨hmap,hi.mono Metric.ball_subset_closedBall,hsurj⟩,\n      ⟨hmapclosed,hi,hsurjclosed⟩,hms,hac,hap,hformula,hl⟩\n  have hstress (R : ℝ) (A : E2 → Mat2)\n      (G : InverseMetricData R A) (Ω : SmoothFlatJordanDomain R) (M : E2 → Mat2)\n      (agreement : ∀ x ∈ closure Ω.domain, M x = inverseMetric A x)\n      (symmetric : SymmetricOn M univ) (elliptic : UniformEllipticOn M univ)\n      (holder : ∀ i j, ∃ C : ℝ≥0, HolderWith C G.alpha (fun x => M x i j))\n      (identity_at_infinity : ∃ L : ℝ, 0 < L ∧ ∀ x : E2, L ≤ ‖x‖ → M x = 1)\n      (f : E2 → E2) (d : Fin 2 → E2 → E2) (had : MetricAdmissible Ω f d) :\n      IntegrableOn (metricE M f d) (disc 1) ∧\n      IntegrableOn (metricF M f d) (disc 1) ∧\n      IntegrableOn (metricH M f d) (disc 1) ∧\n      IntegrableOn (fun x => metricE M f d x - metricH M f d x) (disc 1) ∧\n      IntegrableOn (fun x => 2 * metricF M f d x) (disc 1) := by\n    let μ := volume.restrict (disc 1)\n    have hM (i j : Fin 2) : Continuous (fun x => M x i j) := by\n      obtain ⟨C,hC⟩ := holder i j\n      exact hC.continuous G.alpha_pos\n    have hfs : AEStronglyMeasurable f μ := by\n      have hp : AEMeasurable (fun x => fun i : Fin 2 => f x i) μ :=\n        aemeasurable_pi_iff.mpr (fun i => (had.1 i).2.1.aestronglyMeasurable.aemeasurable)\n      exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp_aestronglyMeasurable\n        hp.aestronglyMeasurable\n    obtain ⟨L,hL,hfar⟩ := identity_at_infinity\n    have hb (i j : Fin 2) : ∃ C, ∀ x : E2, ‖M x i j‖ ≤ C := by\n      obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : E2) L).exists_bound_of_continuousOn\n        (hM i j).continuousOn\n      refine ⟨max C ‖(1 : Mat2) i j‖,fun x => ?_⟩\n      by_cases hx : ‖x‖ ≤ L\n      · exact (hC x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _)\n      · rw [hfar x (le_of_lt (lt_of_not_ge hx))]\n        exact le_max_right _ _\n    have hdc (i j : Fin 2) : MemLp (fun x => d i x j) 2 μ :=\n      (had.1 i).2.2.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)\n    have hprod (i j k l : Fin 2) : Integrable (fun x => d i x j * d k x l) μ :=\n      (hdc i j).integrable_mul (hdc k l)\n    have hx (r s : Fin 2) : Integrable (fun x =>\n        inner ℝ (weakColumn d r x) (matrixAction (M (f x)) (weakColumn d s x))) μ := by\n      have hi (i k : Fin 2) : Integrable (fun x => M (f x) i k * (d i x r * d k x s)) μ := by\n        obtain ⟨C,hC⟩ := hb i k\n        exact (hprod i r k s).bdd_mul ((hM i k).comp_aestronglyMeasurable hfs)\n          (Filter.Eventually.of_forall fun x => hC (f x))\n      have hs : Integrable (fun x => ∑ i : Fin 2, ∑ k : Fin 2,\n          M (f x) i k * (d i x r * d k x s)) μ := by\n        apply integrable_finsetSum\n        intro i _\n        exact integrable_finsetSum _ (fun k _ => hi i k)\n      apply hs.congr\n      apply Filter.Eventually.of_forall\n      intro x\n      dsimp only\n      delta weakColumn matrixAction\n      rw [EuclideanSpace.inner_eq_star_dotProduct]\n      simp only [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]\n      change _ = ((M (f x) 0 0 * d 0 x s + M (f x) 0 1 * d 1 x s) * d 0 x r +\n        (M (f x) 1 0 * d 0 x s + M (f x) 1 1 * d 1 x s) * d 1 x r)\n      ring\n    exact ⟨hx 0 0,hx 0 1,hx 1 1,(hx 0 0).sub (hx 1 1),(hx 0 1).const_mul 2⟩\n  intro f d had η hη htan\n  obtain ⟨hE,hF,hH,-⟩ := hstress R A G Ω M agreement symmetric elliptic holder identity_at_infinity f d had\n  obtain ⟨hz,hvel,hsmooth,hgeom⟩ := hgeometry η hη htan\n  exact hgeneral _ η hsmooth hz hvel (hgeom.mono fun s hs => hs.1) M symmetric f d hE hF hH)"))
      have hfamily (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
          (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0)
          (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2) :
          let τ := fun (s : ℝ) (x : E2) =>
            (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
          let fs := fun s x => f (τ s x)
          let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
            (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
          let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
            (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
          let α := fun s t => t+Real.arctan (s*k t)
          fs 0 = f ∧ ds 0 = d ∧
          HasDerivAt (fun s => metricArea M (fs s) (ds s)) 0 0 ∧
          (∀ᶠ s in 𝓝 (0:ℝ), StrictMono (α s) ∧ Continuous (α s) ∧
            (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi)) := by
        have hgeometry (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
            (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
            let τ := fun (s : ℝ) (x : E2) =>
              (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
            let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
              (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
            let α := fun s t => t+Real.arctan (s*k t)
            (∀ x, τ 0 x = x) ∧
            (∀ x, HasDerivAt (fun s => τ s x) (η x) 0) ∧
            ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) ∧
            (∀ᶠ s in 𝓝 (0:ℝ),
              BijOn (τ s) (disc 1) (disc 1) ∧
              BijOn (τ s) (closedDisc 1) (closedDisc 1) ∧
              StrictMono (α s) ∧ Continuous (α s) ∧
              (∀ t, α s (t+2*Real.pi) = α s t+2*Real.pi) ∧
              (∀ t, τ s (unitCircleParameter t) = unitCircleParameter (α s t)) ∧
              (∀ x ∈ closedDisc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                (e : E2 → E2) = τ s ∧ x ∈ e.source ∧ ContDiffAt ℝ ∞ e.symm (τ s x))) := by
          have hnormalized (η : E2 → E2) (hη : ContDiff ℝ ∞ η)
              (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) :
              let tau : ℝ → E2 → E2 := fun s x =>
                (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x)
              (∀ x, tau 0 x = x) ∧
              (∀ x, HasDerivAt (fun s => tau s x) (η x) 0) ∧
              ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2) ∧
              (∀ s x, ‖x‖ = 1 → ‖tau s x‖ = 1) := by
            dsimp only
            have hpos (s : ℝ) (x : E2) : 0 < 1 + s^2 * ‖η x‖^2 := by positivity
            refine ⟨fun x => by simp, ?_, ?_, ?_⟩
            · intro x
              have ha : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s^2 * ‖η x‖^2)) 0 0 := by
                convert (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖η x‖^2)).const_add 1 |>.sqrt (by simp) using 1 <;> norm_num
              have hb : HasDerivAt (fun s : ℝ => x + s • η x) (η x) 0 := by
                simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (η x)).const_add x
              convert (ha.inv (by simp)).smul hb using 1 <;> norm_num
            · have hi : ContDiff ℝ ∞ (fun p : ℝ × E2 => ‖η p.2‖^2) :=
                (hη.comp contDiff_snd).norm_sq (𝕜 := ℝ)
              have hd : ContDiff ℝ ∞ (fun p : ℝ × E2 => Real.sqrt (1 + p.1^2 * ‖η p.2‖^2)) :=
                (contDiff_const.add ((contDiff_fst.pow 2).mul hi)).sqrt (fun p => (hpos p.1 p.2).ne')
              exact (hd.inv (fun p => (Real.sqrt_pos.mpr (hpos p.1 p.2)).ne')).smul
                (contDiff_snd.add (contDiff_fst.smul (hη.comp contDiff_snd)))
            · intro s x hx
              have ht : inner ℝ x (η x) = 0 := by
                rw [real_inner_comm]
                exact htan x hx
              have hn : ‖x + s • η x‖^2 = 1 + s^2 * ‖η x‖^2 := by
                rw [norm_add_sq_real, real_inner_smul_right, ht,hx,norm_smul]
                simp [mul_pow,sq_abs]
              have he : ‖x + s • η x‖ = Real.sqrt (1 + s^2 * ‖η x‖^2) := by
                rw [← hn,Real.sqrt_sq (norm_nonneg _)]
              rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos (Real.sqrt_pos.mpr (hpos s x)),he]
              exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hpos s x)).ne'
          have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)
              (f : E2 → E2) (d : Fin 2 → E2 → E2) :
              (fun x => f (tau 0 x)) = f ∧
              (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
                (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by
            have hz : tau 0 = id := funext hzero
            refine ⟨by simp [hz],?_⟩
            funext i x
            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
            funext j
            simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
              Fin.sum_univ_two,EuclideanSpace.single]
          have huniform (tau : ℝ → E2 → E2) (hc : ContDiff ℝ ∞ (fun p : ℝ × E2 => tau p.1 p.2))
              (hz : ∀ x, tau 0 x = x) :
              ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedDisc 1,
                ‖fderiv ℝ (tau s) x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ) := by
            have he (s : ℝ) (x : E2) : fderiv ℝ (tau s) x =
                (fderiv ℝ (fun p : ℝ × E2 => tau p.1 p.2) (s,x)).comp (ContinuousLinearMap.inr ℝ ℝ E2) := by
              have hi : HasFDerivAt (fun y : E2 => (s,y)) (ContinuousLinearMap.inr ℝ ℝ E2) x := by
                convert (hasFDerivAt_const (𝕜 := ℝ) s x).prodMk (hasFDerivAt_id x) using 1 <;>
                  ext z <;> simp [ContinuousLinearMap.inr]
              exact ((hc.differentiable (by simp) (s,x)).hasFDerivAt.comp x hi).fderiv
            have hf : Continuous (fun p : ℝ × E2 => fderiv ℝ (tau p.1) p.2) := by
              simp_rw [he]
              exact (hc.continuous_fderiv (by simp)).clm_comp continuous_const
            have hnorm : Continuous (fun p : ℝ × E2 =>
                ‖fderiv ℝ (tau p.1) p.2 - ContinuousLinearMap.id ℝ E2‖) :=
              (hf.sub continuous_const).norm
            apply (isCompact_closedBall (0 : E2) 1).eventually_forall_of_forall_eventually
            intro x hx
            apply (hnorm.continuousAt (x := (0,x))).eventually_lt_const
            have hz' : tau 0 = id := funext hz
            simp [hz']
          have hinjective (tau : E2 → E2) (hc : ContDiff ℝ ∞ tau)
              (hd : ∀ x ∈ closedDisc 1,
                ‖fderiv ℝ tau x - ContinuousLinearMap.id ℝ E2‖ < (1/2 : ℝ)) :
              InjOn tau (closedDisc 1) := by
            have hf := hc.differentiable (by simp)
            have hl : LipschitzOnWith (1/2 : ℝ≥0) (fun x => tau x - x) (closedDisc 1) := by
              apply (convex_closedBall (0 : E2) 1).lipschitzOnWith_of_nnnorm_fderiv_le
                (fun x _ => (hf x).sub differentiableAt_id)
              intro x hx
              rw [fderiv_sub (hf x) differentiableAt_id, fderiv_id]
              exact_mod_cast (hd x hx).le
            intro x hx y hy hxy
            have hb := hl.dist_le_mul x hx y hy
            have he : (tau x - x) - (tau y - y) = y-x := by rw [hxy, sub_sub_sub_cancel_left]
            rw [dist_eq_norm,he,norm_sub_rev] at hb
            change ‖x-y‖ ≤ (1/2 : ℝ) * dist x y at hb
            rw [← dist_eq_norm] at hb
            exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := x) (y := y)])
          have hangle (η : E2 → E2)
              (htan : ∀ x : E2, ‖x‖ = 1 → inner ℝ (η x) x = 0) (s t : ℝ) :
              let x := unitCircleParameter t
              let k := x 0 * η x 1 - x 1 * η x 0
              (Real.sqrt (1 + s^2 * ‖η x‖^2))⁻¹ • (x + s • η x) =
                unitCircleParameter (t + Real.arctan (s*k)) := by
            dsimp only
            let x := unitCircleParameter t
            let k := x 0 * η x 1 - x 1 * η x 0
            have hc : (x 0)^2 + (x 1)^2 = 1 := by
              change (Real.cos t)^2 + (Real.sin t)^2 = 1
              exact Real.cos_sq_add_sin_sq t
            have hnorm : ‖x‖ = 1 := by
              have hn : ‖x‖^2 = 1 := by
                calc
                  ‖x‖^2 = inner ℝ x x := (real_inner_self_eq_norm_sq x).symm
                  _ = 1 := by
                    simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two] using hc
              nlinarith [norm_nonneg x]
            have ht : η x 0 * x 0 + η x 1 * x 1 = 0 := by
              simpa [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm] using htan x hnorm
            have h0 : η x 0 = -k * x 1 := by
              dsimp only [k]
              linear_combination -(η x 0)*hc + x 0*ht
            have h1 : η x 1 = k * x 0 := by
              dsimp only [k]
              linear_combination -(η x 1)*hc + x 1*ht
            have hn : ‖η x‖^2 = k^2 := by
              rw [← real_inner_self_eq_norm_sq]
              simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
              rw [h0,h1]
              nlinarith [sq_nonneg k]
            change (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x) = _
            rw [hn]
            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
            funext j
            fin_cases j
            · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 0 + s*η x 0) =
                Real.cos (t+Real.arctan (s*k))
              rw [h0,Real.cos_add,Real.cos_arctan,Real.sin_arctan]
              change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.cos t + s*(-k*Real.sin t)) = _
              simp only [mul_pow,div_eq_mul_inv]
              ring
            · change (Real.sqrt (1+s^2*k^2))⁻¹ * (x 1 + s*η x 1) =
                Real.sin (t+Real.arctan (s*k))
              rw [h1,Real.sin_add,Real.cos_arctan,Real.sin_arctan]
              change (Real.sqrt (1+s^2*k^2))⁻¹ * (Real.sin t + s*(k*Real.cos t)) = _
              simp only [mul_pow,div_eq_mul_inv]
              ring
          have hlift (k : ℝ → ℝ) (hk : Continuous k) (hp : Function.Periodic k (2*Real.pi)) (s : ℝ) :
              Continuous (fun t => t + Real.arctan (s*k t)) ∧
              (∀ t, (t+2*Real.pi) + Real.arctan (s*k (t+2*Real.pi)) =
                (t + Real.arctan (s*k t)) + 2*Real.pi) ∧
              Surjective (fun t => t+Real.arctan (s*k t)) := by
            have hc : Continuous (fun t => t+Real.arctan (s*k t)) :=
              continuous_id.add (Real.continuous_arctan.comp (continuous_const.mul hk))
            refine ⟨hc,fun t => by rw [hp t]; ring,?_⟩
            intro y
            have hleft : (y-Real.pi)+Real.arctan (s*k (y-Real.pi)) ≤ y := by
              linarith [Real.arctan_lt_pi_div_two (s*k (y-Real.pi)),Real.pi_pos]
            have hright : y ≤ (y+Real.pi)+Real.arctan (s*k (y+Real.pi)) := by
              linarith [Real.neg_pi_div_two_lt_arctan (s*k (y+Real.pi)),Real.pi_pos]
            obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith [Real.pi_pos] : y-Real.pi ≤ y+Real.pi)
              hc.continuousOn ⟨hleft,hright⟩
            exact ⟨t,he⟩
          have hlocal (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (x : E2)
              (hd : ‖fderiv ℝ τ x - ContinuousLinearMap.id ℝ E2‖ < 1) :
              ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ ∧ x ∈ e.source ∧
                ContDiffAt ℝ ∞ e.symm (τ x) := by
            let D := fderiv ℝ τ x
            have hinj : Injective D := by
              apply (LinearMap.ker_eq_bot).mp
              apply LinearMap.ker_eq_bot'.mpr
              intro v hv
              change D v = 0 at hv
              have he : (D - ContinuousLinearMap.id ℝ E2) v = -v := by simp [hv]
              have hn := (D - ContinuousLinearMap.id ℝ E2).le_opNorm v
              rw [he,norm_neg] at hn
              have hb : ‖D - ContinuousLinearMap.id ℝ E2‖ < 1 := hd
              have hz : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
              exact norm_eq_zero.mp hz
            have hsurj : Surjective D := LinearMap.injective_iff_surjective.mp hinj
            let d : E2 ≃L[ℝ] E2 := ContinuousLinearEquiv.ofBijective D
              (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
            have heq : (d : E2 →L[ℝ] E2) = D := ContinuousLinearEquiv.coe_ofBijective _ _ _
            have hf : HasFDerivAt τ (d : E2 →L[ℝ] E2) x := by
              rw [heq]
              exact (hc.differentiable (by simp) x).hasFDerivAt
            let e := hc.contDiffAt.toOpenPartialHomeomorph τ hf (by simp)
            refine ⟨e,rfl,hc.contDiffAt.mem_toOpenPartialHomeomorph_source hf (by simp),?_⟩
            exact hc.contDiffAt.to_localInverse hf (by simp)
          have hcircle (x : E2) (hx : ‖x‖ = 1) : ∃ t : ℝ, unitCircleParameter t = x := by
            let z : ℂ := ⟨x 0,x 1⟩
            have hs : (x 0)^2+(x 1)^2=1 := by
              have h := real_inner_self_eq_norm_sq x
              rw [hx] at h
              simpa only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial,pow_two,one_mul] using h
            have hz : ‖z‖ = 1 := by
              have hsq : ‖z‖^2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; simpa [z,Complex.normSq_apply,pow_two] using hs
              nlinarith [norm_nonneg z]
            have hne : z ≠ 0 := by intro h; simp [h] at hz
            refine ⟨Complex.arg z,?_⟩
            apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
            funext j
            fin_cases j
            · change Real.cos (Complex.arg z) = x 0
              rw [Complex.cos_arg hne,hz]
              simp [z]
            · change Real.sin (Complex.arg z) = x 1
              rw [Complex.sin_arg,hz]
              simp [z]
          have hpreserve (τ : E2 → E2) (hc : Continuous τ)
              (hinj : InjOn τ (closedDisc 1))
              (hsphere : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ x = y)
              (hzero : ‖τ 0‖ < 1) : MapsTo τ (disc 1) (disc 1) := by
            intro x hx
            change dist (τ x) 0 < 1
            rw [dist_zero_right]
            by_contra hn
            have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
            have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
            obtain ⟨z,hz,hze⟩ := (convex_ball (0:E2) 1).isPreconnected.intermediate_value h0 hx
              hc.norm.continuousOn ⟨hzero.le,not_lt.mp hn⟩
            obtain ⟨w,hw,he⟩ := hsphere (τ z) hze
            have hz' : z ∈ closedDisc 1 := Metric.ball_subset_closedBall hz
            have hw' : w ∈ closedDisc 1 := mem_closedBall_zero_iff.mpr hw.le
            have hzw : z = w := hinj hz' hw' he.symm
            have hzlt : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
            rw [hzw,hw] at hzlt
            exact lt_irrefl _ hzlt
          have hsurjective (τ : E2 → E2) (hc : Continuous τ)
              (hmaps : MapsTo τ (disc 1) (disc 1))
              (hsphere : ∀ x : E2, ‖x‖ = 1 → ‖τ x‖ = 1)
              (hlocal : ∀ x ∈ disc 1, ∃ e : OpenPartialHomeomorph E2 E2,
                (e : E2 → E2) = τ ∧ x ∈ e.source) :
              SurjOn τ (disc 1) (disc 1) := by
            have hopen : IsOpen (τ '' disc 1) := by
              rw [isOpen_iff_mem_nhds]
              rintro y ⟨x,hx,rfl⟩
              obtain ⟨e,he,hxe⟩ := hlocal x hx
              have ho := e.isOpen_image_source_inter (s := disc 1) Metric.isOpen_ball
              have hm : τ x ∈ e '' (e.source ∩ disc 1) := ⟨x,⟨hxe,hx⟩,by rw [he]⟩
              exact Filter.mem_of_superset (ho.mem_nhds hm) (by
                rintro z ⟨w,hw,rfl⟩
                exact ⟨w,hw.2,by rw [he]⟩)
            have hcompact : IsClosed (τ '' closedDisc 1) :=
              ((isCompact_closedBall (0:E2) 1).image hc).isClosed
            have hclosure : closure (τ '' disc 1) ⊆ τ '' closedDisc 1 :=
              closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hcompact
            have hboundary : closure (τ '' disc 1) ∩ disc 1 ⊆ τ '' disc 1 := by
              intro y hy
              obtain ⟨x,hx,hxy⟩ := hclosure hy.1
              refine ⟨x,?_,hxy⟩
              have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
              have hylt : ‖y‖ < 1 := mem_ball_zero_iff.mp hy.2
              have hxlt : ‖x‖ < 1 := lt_of_le_of_ne hxle (by
                intro hxe
                have := hsphere x hxe
                rw [hxy] at this
                linarith)
              exact mem_ball_zero_iff.mpr hxlt
            have h0 : (0:E2) ∈ disc 1 := by change (0 : E2) ∈ Metric.ball (0 : E2) 1; simp
            exact (convex_ball (0:E2) 1).isPreconnected.subset_of_closure_inter_subset hopen
              ⟨τ 0,hmaps h0,⟨0,h0,rfl⟩⟩ hboundary
          have hmonotone (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k)
              (hp : Periodic k (2*Real.pi)) :
              ∀ᶠ s in 𝓝 (0:ℝ), StrictMono (fun t => t+Real.arctan (s*k t)) := by
            have hpd : Periodic (deriv k) (2*Real.pi) := by
              intro t
              have he : (fun t => k (t+2*Real.pi)) = k := funext hp
              rw [← deriv_comp_add_const k (2*Real.pi) t,he]
            obtain ⟨C,hC,hbound⟩ := (hpd.isBounded_of_continuous (by positivity)
              (hk.continuous_deriv (by simp))).exists_pos_norm_le
            have hsmall : ∀ᶠ s in 𝓝 (0:ℝ), |s| * C < (1/2:ℝ) := by
              exact (continuousAt_id.abs.mul_const C).eventually_lt_const (by norm_num)
            filter_upwards [hsmall] with s hs
            apply strictMono_of_hasDerivAt_pos
              (f' := fun t => 1 + (s*deriv k t)/(1+(s*k t)^2))
            · intro t
              convert (hasDerivAt_id t).add (((hk.differentiable (by simp) t).hasDerivAt.const_mul s).arctan) using 1 <;> first | rfl | ring
            · intro t
              have hb : |s*deriv k t| < (1/2:ℝ) := by
                rw [abs_mul]
                exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
                  (by simpa using hbound (deriv k t) ⟨t,rfl⟩) (abs_nonneg s)) hs
              have hd : 0 < 1+(s*k t)^2 := by positivity
              have hl : -1 < (s*deriv k t)/(1+(s*k t)^2) := by
                rw [lt_div_iff₀ hd]
                have hlow := (abs_lt.mp hb).1
                nlinarith [sq_nonneg (s*k t)]
              linarith
          have hcoefficient (η : E2 → E2) (hη : ContDiff ℝ ∞ η) :
              let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
                (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
              ContDiff ℝ ∞ k ∧ Periodic k (2*Real.pi) := by
            dsimp only
            have hc : ContDiff ℝ ∞ unitCircleParameter := by
              apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.comp
              apply contDiff_pi.mpr
              intro i
              fin_cases i
              · simpa using Real.contDiff_cos
              · simpa using Real.contDiff_sin
            have he (i : Fin 2) : ContDiff ℝ ∞ (fun t => η (unitCircleParameter t) i) :=
              (contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp (hη.comp hc))) i
            refine ⟨?_,?_⟩
            · exact ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 0).mul (he 1)).sub ((contDiff_pi.mp ((EuclideanSpace.equiv (Fin 2) ℝ).contDiff.comp hc) 1).mul (he 0))
            · intro t
              have hp : unitCircleParameter (t+2*Real.pi) = unitCircleParameter t := by
                apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
                funext i
                fin_cases i
                · change Real.cos (t+2*Real.pi) = Real.cos t
                  exact Real.cos_add_two_pi t
                · change Real.sin (t+2*Real.pi) = Real.sin t
                  exact Real.sin_add_two_pi t
              dsimp only
              rw [hp]
          dsimp only
          let τ := fun (s : ℝ) (x : E2) =>
            (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
          let k := fun t => (unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
            (unitCircleParameter t) 1 * η (unitCircleParameter t) 0
          let α := fun s t => t+Real.arctan (s*k t)
          obtain ⟨hz,hvel,hc,hsp⟩ := hnormalized η hη htan
          have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc
          have hcs (s : ℝ) : ContDiff ℝ ∞ (τ s) :=
            hc'.comp (contDiff_const.prodMk contDiff_id)
          have hu := huniform τ hc' hz
          obtain ⟨hk,hkp⟩ := hcoefficient η hη
          have hm := hmonotone k hk hkp
          have hcenter : ∀ᶠ s in 𝓝 (0:ℝ), ‖τ s 0‖ < 1 := by
            exact (((hc'.continuous.comp (continuous_id.prodMk continuous_const)).norm).continuousAt).eventually_lt_const (by simp [τ])
          refine ⟨hz,hvel,hc',?_⟩
          filter_upwards [hu,hm,hcenter] with s hs hms hzs
          have hi := hinjective (τ s) (hcs s) hs
          obtain ⟨hac,hap,has⟩ := hlift k hk.continuous hkp s
          have hformula (t : ℝ) : τ s (unitCircleParameter t) = unitCircleParameter (α s t) :=
            hangle η htan s t
          have honto : ∀ y : E2, ‖y‖ = 1 → ∃ x : E2, ‖x‖ = 1 ∧ τ s x = y := by
            intro y hy
            obtain ⟨t,ht⟩ := hcircle y hy
            obtain ⟨u,hu⟩ := has t
            refine ⟨unitCircleParameter u,?_,?_⟩
            · have hh := real_inner_self_eq_norm_sq (unitCircleParameter u)
              have hsq : ‖unitCircleParameter u‖^2 = 1 := by
                calc
                  _ = inner ℝ (unitCircleParameter u) (unitCircleParameter u) := hh.symm
                  _ = 1 := by
                    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
                    change Real.cos u * Real.cos u + Real.sin u * Real.sin u = 1
                    nlinarith [Real.cos_sq_add_sin_sq u]
              nlinarith [norm_nonneg (unitCircleParameter u)]
            · rw [hformula]
              change unitCircleParameter (u+Real.arctan (s*k u)) = y
              dsimp only at hu
              rw [hu,ht]
          have hmap := hpreserve (τ s) (hcs s).continuous hi honto hzs
          have hl (x : E2) (hx : x ∈ closedDisc 1) :
              ∃ e : OpenPartialHomeomorph E2 E2, (e : E2 → E2) = τ s ∧ x ∈ e.source ∧
                ContDiffAt ℝ ∞ e.symm (τ s x) :=
            hlocal (τ s) (hcs s) x (lt_trans (hs x hx) (by norm_num))
          have hsurj := hsurjective (τ s) (hcs s).continuous hmap (hsp s) (fun x hx => by
            obtain ⟨e,he,hx,hd⟩ := hl x (Metric.ball_subset_closedBall hx)
            exact ⟨e,he,hx⟩)
          have hmapclosed : MapsTo (τ s) (closedDisc 1) (closedDisc 1) := by
            intro x hx
            have hxle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
            rcases lt_or_eq_of_le hxle with hxlt | hxe
            · exact Metric.ball_subset_closedBall (hmap (mem_ball_zero_iff.mpr hxlt))
            · have hh : ‖τ s x‖ = 1 := hsp s x hxe
              exact mem_closedBall_zero_iff.mpr hh.le
          have hsurjclosed : SurjOn (τ s) (closedDisc 1) (closedDisc 1) := by
            intro y hy
            have hyle : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
            rcases lt_or_eq_of_le hyle with hylt | hye
            · obtain ⟨x,hx,hxy⟩ := hsurj (mem_ball_zero_iff.mpr hylt)
              exact ⟨x,Metric.ball_subset_closedBall hx,hxy⟩
            · obtain ⟨x,hx,hxy⟩ := honto y hye
              exact ⟨x,mem_closedBall_zero_iff.mpr hx.le,hxy⟩
          exact ⟨⟨hmap,hi.mono Metric.ball_subset_closedBall,hsurj⟩,
            ⟨hmapclosed,hi,hsurjclosed⟩,hms,hac,hap,hformula,hl⟩
        have hinitial (tau : ℝ → E2 → E2) (hzero : ∀ x, tau 0 x = x)
            (f : E2 → E2) (d : Fin 2 → E2 → E2) :
            (fun x => f (tau 0 x)) = f ∧
            (fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
              (fun j => inner ℝ (d i (tau 0 x)) (fderiv ℝ (tau 0) x (coordinateVector 2 j)))) = d := by
          have hz : tau 0 = id := funext hzero
          refine ⟨by simp [hz],?_⟩
          funext i x
          apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
          funext j
          simp [hz,coordinateVector,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,
            Fin.sum_univ_two,EuclideanSpace.single]
        have harea (τ : E2 → E2) (hc : ContDiff ℝ ∞ τ) (hb : BijOn τ (disc 1) (disc 1))
            (M : E2 → Mat2) (f : E2 → E2) (d : Fin 2 → E2 → E2) :
            let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
              (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))
            metricArea M (f ∘ τ) dt = metricArea M f d := by
          dsimp only
          let dt := fun i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
            (fun j => inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)))
          let J : E2 → Mat2 := fun x i j => (fderiv ℝ τ x (coordinateVector 2 j)) i
          have hjet (x : E2) : weakJacobian dt x = weakJacobian d (τ x) * J x := by
            ext i j
            change inner ℝ (d i (τ x)) (fderiv ℝ τ x (coordinateVector 2 j)) =
              ∑ k : Fin 2, d i (τ x) k * (fderiv ℝ τ x (coordinateVector 2 j)) k
            simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,star_trivial]
            ring
          have hdet (x : E2) : Matrix.det (J x) = (fderiv ℝ τ x).det := by
            change Matrix.det (J x) = LinearMap.det (fderiv ℝ τ x).toLinearMap
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
            congr 1
          have hdensity (x : E2) : metricAreaDensity M (f ∘ τ) dt x =
              |(fderiv ℝ τ x).det| * metricAreaDensity M f d (τ x) := by
            unfold metricAreaDensity
            rw [hjet,Matrix.det_mul,abs_mul,hdet]
            simp only [Function.comp_apply]
            ring
          change (∫ x in disc 1, metricAreaDensity M (f ∘ τ) dt x) = _
          simp_rw [hdensity]
          symm
          change (∫ x in disc 1, metricAreaDensity M f d x) = _
          have hv := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
            Metric.isOpen_ball.measurableSet
            (fun x (_ : x ∈ disc 1) => (hc.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
            hb.injOn (metricAreaDensity M f d)
          change (∫ x in τ '' disc 1, metricAreaDensity M f d x) = _ at hv
          rw [hb.image_eq] at hv
          exact hv
        dsimp only
        let τ := fun (s : ℝ) (x : E2) =>
          (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
        let fs := fun s x => f (τ s x)
        let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
          (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
        obtain ⟨hz,hvel,hc,hgeom⟩ := hgeometry η hη htan
        have hc' : ContDiff ℝ ∞ (fun p : ℝ × E2 => τ p.1 p.2) := hc
        obtain ⟨hf0,hd0⟩ := hinitial τ hz f d
        have ha : (fun s => metricArea M (fs s) (ds s)) =ᶠ[𝓝 (0:ℝ)]
            (fun _ => metricArea M f d) := by
          filter_upwards [hgeom] with s hs
          exact harea (τ s) (hc'.comp (contDiff_const.prodMk contDiff_id)) hs.1 M f d
        refine ⟨hf0,hd0,?_,?_⟩
        · exact (hasDerivAt_const (0:ℝ) (metricArea M f d)).congr_of_eventuallyEq ha
        · filter_upwards [hgeom] with s hs
          exact ⟨hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1⟩
      have hlift {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (orientation : ℝ)
          (h : WeakMonotoneBoundaryLift Ω theta orientation)
          (alpha : ℝ → ℝ) (hc : Continuous alpha) (hm : Monotone alpha)
          (hp : ∀ t, alpha (t + 2*Real.pi) = alpha t + 2*Real.pi) :
          WeakMonotoneBoundaryLift Ω (theta ∘ alpha) orientation := by
        refine ⟨h.1,h.2.1.comp hc,?_,?_⟩
        · exact h.2.2.1.comp hm
        · intro t
          change theta (alpha (t + 2*Real.pi)) = theta (alpha t) + orientation*(2*Real.pi)
          rw [hp, h.2.2.2]
      intro f d had η hη htan
      let τ := fun (s : ℝ) (x : E2) => (Real.sqrt (1+s^2*‖η x‖^2))⁻¹ • (x+s•η x)
      let fs := fun s x => f (τ s x)
      let ds := fun s i x => (EuclideanSpace.equiv (Fin 2) ℝ).symm
        (fun j => inner ℝ (d i (τ s x)) (fderiv ℝ (τ s) x (coordinateVector 2 j)))
      let α := fun (s : ℝ) (t : ℝ) => t + Real.arctan (s *
        ((unitCircleParameter t) 0 * η (unitCircleParameter t) 1 -
         (unitCircleParameter t) 1 * η (unitCircleParameter t) 0))
      obtain ⟨hf0,hd0,ha,hboundary⟩ := hfamily η hη htan M f d
      refine ⟨fs,ds,hf0,hd0,?_,ha,nativeDirichlet f d had η hη htan⟩
      obtain ⟨theta,orientation,htheta,htrace⟩ := had.2
      have hH := nativeH1 f d had.1 η hη htan
      have hG := nativeGreen f d theta orientation had.1 htheta htrace η hη htan
      filter_upwards [hH,hG,hboundary] with s hsH hsG hsB
      exact ⟨hsH,theta ∘ α s,orientation,
        hlift Ω theta orientation htheta (α s) hsB.2.1 hsB.1.monotone hsB.2.2,hsG⟩
  )
end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.EpsilonMinimizerVariation.InnerCourant
