import B1HalfDiscNativeTruncation_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem scalar_indicator_derivative_convergence_v468
    (U : Set E2) (u g : E2 → ℝ) (ψ dψ : ℕ → E2 → ℝ)
    (hu : MemLp u 2 (volume.restrict U)) (hg : MemLp g 2 (volume.restrict U))
    (hψ : ∀ n, MemLp (ψ n) 2 (volume.restrict U)) (hdψ : ∀ n, MemLp (dψ n) 2 (volume.restrict U))
    (hzero : ∀ᵐ x ∂(volume.restrict U), u x = 0 → g x = 0)
    (hv : Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 (volume.restrict U)) atTop (𝓝 0))
    (hd : Tendsto (fun n => eLpNorm (fun x => dψ n x - g x) 2 (volume.restrict U)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < ψ n x then dψ n x else 0) - (if 0 < u x then g x else 0)) 2 (volume.restrict U)) atTop (𝓝 0) := by
  let first := fun n x => if 0 < ψ n x then dψ n x - g x else 0
  let second := fun n x => (if 0 < ψ n x then g x else 0) - (if 0 < u x then g x else 0)
  have hf (n : ℕ) : eLpNorm (first n) 2 (volume.restrict U) ≤ eLpNorm (fun x => dψ n x - g x) 2 (volume.restrict U) := by
    apply eLpNorm_mono_ae
      (DeGiorgi.indicator_component_memLp (hψ n).aemeasurable ((hdψ n).sub hg)).aestronglyMeasurable
    filter_upwards [] with x
    by_cases hx : 0 < ψ n x <;> simp [first,hx]
  have htf : Tendsto (fun n => eLpNorm (first n) 2 (volume.restrict U)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
      (fun _ => bot_le) hf
  have hts : Tendsto (fun n => eLpNorm (second n) 2 (volume.restrict U)) atTop (𝓝 0) :=
    DeGiorgi.tendsto_eLpNorm_indicator_diff_mul_of_tendsto_eLpNorm
      (fun n => (hψ n).aestronglyMeasurable) hu.aestronglyMeasurable hg hzero hv
  have hb (n : ℕ) : eLpNorm (fun x =>
      (if 0 < ψ n x then dψ n x else 0) - (if 0 < u x then g x else 0)) 2 (volume.restrict U) ≤
      eLpNorm (first n) 2 (volume.restrict U) + eLpNorm (second n) 2 (volume.restrict U) := by
    have he : (fun x => (if 0 < ψ n x then dψ n x else 0) - (if 0 < u x then g x else 0)) =
        first n + second n := by
      funext x
      by_cases hx : 0 < ψ n x <;> by_cases hu : 0 < u x <;> simp [first,second,hx,hu]
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using htf.add hts) (fun _ => bot_le) hb

theorem vector_component_eLp_convergence_v468
    (μ : Measure E2) (f : ℕ → E2 → E2) (hf : ∀ n, MemLp (f n) 2 μ)
    (ht : ∀ i : Fin 2, Tendsto (fun n => eLpNorm (fun x => f n x i) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : eLpNorm (f n) 2 μ ≤
      eLpNorm (fun x => f n x 0) 2 μ + eLpNorm (fun x => f n x 1) 2 μ := by
    calc
      _ ≤ eLpNorm (fun x => ‖f n x 0‖ + ‖f n x 1‖) 2 μ := by
        apply eLpNorm_mono_ae (hf n).aestronglyMeasurable
        filter_upwards [] with x
        have hn : ‖f n x‖ ^ 2 = ‖f n x 0‖ ^ 2 + ‖f n x 1‖ ^ 2 := by
          simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs]
        rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        nlinarith [norm_nonneg (f n x),norm_nonneg (f n x 0),norm_nonneg (f n x 1),
          mul_nonneg (norm_nonneg (f n x 0)) (norm_nonneg (f n x 1))]
      _ ≤ eLpNorm (fun x => ‖f n x 0‖) 2 μ + eLpNorm (fun x => ‖f n x 1‖) 2 μ :=
        eLpNorm_add_le (by norm_num)
      _ = _ := by rw [eLpNorm_norm _ ((hf n).eval_piLp 0).aestronglyMeasurable,
        eLpNorm_norm _ ((hf n).eval_piLp 1).aestronglyMeasurable]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (ht 0).add (ht 1)) (fun _ => bot_le) hb

theorem native_toLp_tendsto_of_eLp_v468 {F : Type} [NormedAddCommGroup F]
    (μ : Measure E2) (f : ℕ → E2 → F) (u : E2 → F)
    (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp ht
  simpa only [ENNReal.toReal_zero] using hh.congr (fun n => by
    rw [← MemLp.toLp_sub,Lp.norm_toLp]
    rfl)

/-- Positive-part truncation preserves the literal native H10 completion on a half-disc. -/
theorem halfdisc_native_positive_h10_v468 (R : ℝ) (p : X (halfDisc R)) :
    H10On (halfDisc R) (fun x => max (val (halfDisc R) p x) 0)
      (fun x => if 0 < val (halfDisc R) p x then grad (halfDisc R) p x else 0) := by
  classical
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hn := halfdisc_pair_native_h10_v468 R p
  let u := val U p
  let du := grad U p
  have humem : MemLp u 2 μ := hn.1.2.1
  have hdmem : MemLp du 2 μ := hn.1.2.2
  let hw : DeGiorgi.MemW1pWitness 2 u U :=
    { memLp := hn.1.2.1
      weakGrad := du
      weakGrad_component_memLp := fun i => hn.1.2.2.eval_piLp i
      isWeakGrad := by
        intro i φ hs hc ht
        exact hn.1.1.2.2 φ hs hc ht i }
  obtain ⟨φ,hs,hc,ht,hv,hd⟩ := halfdisc_native_smooth_approx_v468 R p
  have hφ (n : ℕ) : H10On U (φ n) (planarGradient (φ n)) :=
    halfdisc_native_smooth_h10_export_v468 R (φ n) (hs n) (hc n) (ht n)
  let uplus := fun x => max (u x) 0
  let duplus := fun x => if 0 < u x then du x else 0
  have hup : MemLp uplus 2 μ := hn.1.2.1.pos_part
  have hdup : MemLp duplus 2 μ := by
    apply memLp_piLp_iff.mpr
    intro i
    convert DeGiorgi.indicator_component_memLp humem.aemeasurable (hdmem.eval_piLp i) using 1
    funext x
    by_cases hx : 0 < u x <;> simp [duplus,hx]
  have hplus (n : ℕ) : H10On U (fun x => max (φ n x) 0)
      (fun x => if 0 < φ n x then planarGradient (φ n) x else 0) :=
    native_smooth_positive_h10_v468 U hU (φ n) (hs n) (hc n) (ht n)
  have hvplus := native_positivepart_convergence_provider_v468 u φ μ
    hn.1.2.1.aestronglyMeasurable (fun n => (hφ n).1.2.1.aestronglyMeasurable) hv
  have hdcoord (i : Fin 2) : Tendsto (fun n => eLpNorm
      (fun x => planarGradient (φ n) x i - du x i) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
      (fun _ => bot_le)
    intro n
    apply eLpNorm_mono_ae ((hφ n).1.2.2.eval_piLp i |>.sub (hn.1.2.2.eval_piLp i)).aestronglyMeasurable
    filter_upwards [] with x
    exact PiLp.norm_apply_le (planarGradient (φ n) x - du x) i
  have hdpluscoord (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < φ n x then planarGradient (φ n) x else 0) i - duplus x i) 2 μ) atTop (𝓝 0) := by
    have he := scalar_indicator_derivative_convergence_v468 U u (fun x => du x i) φ
      (fun n x => planarGradient (φ n) x i) hn.1.2.1 (hn.1.2.2.eval_piLp i)
      (fun n => (hφ n).1.2.1) (fun n => (hφ n).1.2.2.eval_piLp i)
      (hw.weakGrad_ae_eq_zero_on_zeroSet hU i) hv (hdcoord i)
    convert he using 1
    congr 1
    funext n
    congr 1
    funext x
    by_cases hx : 0 < φ n x <;> by_cases hy : 0 < u x <;> simp [duplus,hx,hy]
  have hdplus : Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < φ n x then planarGradient (φ n) x else 0) - duplus x) 2 μ) atTop (𝓝 0) :=
    vector_component_eLp_convergence_v468 μ _ (fun n => (hplus n).1.2.2.sub hdup)
      (fun i => by simpa only [PiLp.sub_apply] using hdpluscoord i)
  let seq := fun n => pack U (fun x => max (φ n x) 0)
    (fun x => if 0 < φ n x then planarGradient (φ n) x else 0)
    (hplus n).1.2.1 (hplus n).1.2.2
  let target := pack U uplus duplus hup hdup
  have hvLp := native_toLp_tendsto_of_eLp_v468 μ _ uplus (fun n => (hplus n).1.2.1) hup hvplus
  have hdLp := native_toLp_tendsto_of_eLp_v468 μ _ duplus (fun n => (hplus n).1.2.2) hdup hdplus
  have hseq : Tendsto seq atTop (𝓝 target) :=
    (WithLp.prod_continuous_toLp 2 (Lp ℝ 2 μ) (Lp E2 2 μ)).tendsto _ |>.comp (hvLp.prodMk_nhds hdLp)
  apply (halfdisc_nativeH10_iff_pair_mem_export_v468 R _ _ hup hdup).mpr
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hseq
    (Filter.Eventually.of_forall fun n =>
      (halfdisc_nativeH10_iff_pair_mem_export_v468 R _ _ (hplus n).1.2.1 (hplus n).1.2.2).mp (hplus n))

end SeifertSurfaces.OriginalEndpoints.B1Tangency
