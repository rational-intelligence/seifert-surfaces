import B1NativeSmoothAddition_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A nonpositive smooth offset preserves native H10 after positive-part truncation. -/
theorem halfdisc_native_offset_positive_h10_v468 (R : ℝ) (p : X (halfDisc R))
    (w : E2 → ℝ) (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ halfDisc R, w x ≤ 0)
    (hwLp : MemLp w 2 (volume.restrict (halfDisc R)))
    (hdwLp : MemLp (planarGradient w) 2 (volume.restrict (halfDisc R))) :
    H10On (halfDisc R) (fun x => max (val (halfDisc R) p x + w x) 0)
      (fun x => if 0 < val (halfDisc R) p x + w x then
        grad (halfDisc R) p x + planarGradient w x else 0) := by
  classical
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  have hn := halfdisc_pair_native_h10_v468 R p
  let u := fun x => val U p x + w x
  let du := fun x => grad U p x + planarGradient w x
  have hsum := native_h1_add_smooth_v468 U (val U p) (grad U p) hn.1 w hw hwLp hdwLp
  have humem : MemLp u 2 μ := hsum.2.1
  have hdmem : MemLp du 2 μ := hsum.2.2
  let hwt : DeGiorgi.MemW1pWitness 2 u U :=
    { memLp := hsum.2.1
      weakGrad := du
      weakGrad_component_memLp := fun i => hsum.2.2.eval_piLp i
      isWeakGrad := by
        intro i φ hs hc ht
        exact hsum.1.2.2 φ hs hc ht i }
  obtain ⟨φ,hs,hc,ht,hv0,hd0⟩ := halfdisc_native_smooth_approx_v468 R p
  let ψ := fun n x => φ n x + w x
  let dψ := fun n x => planarGradient (φ n) x + planarGradient w x
  have hφ0 (n : ℕ) : H10On U (φ n) (planarGradient (φ n)) :=
    halfdisc_native_smooth_h10_export_v468 R (φ n) (hs n) (hc n) (ht n)
  have hφ (n : ℕ) : H1On U (ψ n) (dψ n) :=
    native_h1_add_smooth_v468 U (φ n) (planarGradient (φ n)) (hφ0 n).1 w hw hwLp hdwLp
  have hv : Tendsto (fun n => eLpNorm (fun x => ψ n x - u x) 2 μ) atTop (𝓝 0) := by
    apply hv0.congr
    intro n
    congr 1
    funext x
    dsimp [ψ,u]
    ring
  have hd : Tendsto (fun n => eLpNorm (fun x => dψ n x - du x) 2 μ) atTop (𝓝 0) := by
    apply hd0.congr
    intro n
    congr 1
    funext x
    dsimp [dψ,du]
    abel
  let uplus := fun x => max (u x) 0
  let duplus := fun x => if 0 < u x then du x else 0
  have hup : MemLp uplus 2 μ := hsum.2.1.pos_part
  have hdup : MemLp duplus 2 μ := by
    apply memLp_piLp_iff.mpr
    intro i
    convert DeGiorgi.indicator_component_memLp humem.aemeasurable (hdmem.eval_piLp i) using 1
    funext x
    by_cases hx : 0 < u x <;> simp [duplus,hx]
  have hplus (n : ℕ) : H10On U (fun x => max (ψ n x) 0)
      (fun x => if 0 < ψ n x then dψ n x else 0) :=
    native_smooth_offset_positive_h10_v468 U hU (φ n) w (hs n) (hc n) (ht n) hw hwn
  have hvplus := native_positivepart_convergence_provider_v468 u ψ μ
    hsum.2.1.aestronglyMeasurable (fun n => (hφ n).2.1.aestronglyMeasurable) hv
  have hdcoord (i : Fin 2) : Tendsto (fun n => eLpNorm
      (fun x => dψ n x i - du x i) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd
      (fun _ => bot_le)
    intro n
    apply eLpNorm_mono_ae ((hφ n).2.2.eval_piLp i |>.sub (hsum.2.2.eval_piLp i)).aestronglyMeasurable
    filter_upwards [] with x
    exact PiLp.norm_apply_le (dψ n x - du x) i
  have hdpluscoord (i : Fin 2) : Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < ψ n x then dψ n x else 0) i - duplus x i) 2 μ) atTop (𝓝 0) := by
    have he := scalar_indicator_derivative_convergence_v468 U u (fun x => du x i) ψ
      (fun n x => dψ n x i) hsum.2.1 (hsum.2.2.eval_piLp i)
      (fun n => (hφ n).2.1) (fun n => (hφ n).2.2.eval_piLp i)
      (hwt.weakGrad_ae_eq_zero_on_zeroSet hU i) hv (hdcoord i)
    convert he using 1
    congr 1
    funext n
    congr 1
    funext x
    by_cases hx : 0 < ψ n x <;> by_cases hy : 0 < u x <;> simp [duplus,hx,hy]
  have hdplus : Tendsto (fun n => eLpNorm (fun x =>
      (if 0 < ψ n x then dψ n x else 0) - duplus x) 2 μ) atTop (𝓝 0) :=
    vector_component_eLp_convergence_v468 μ _ (fun n => (hplus n).1.2.2.sub hdup)
      (fun i => by simpa only [PiLp.sub_apply] using hdpluscoord i)
  let seq := fun n => pack U (fun x => max (ψ n x) 0)
    (fun x => if 0 < ψ n x then dψ n x else 0)
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
