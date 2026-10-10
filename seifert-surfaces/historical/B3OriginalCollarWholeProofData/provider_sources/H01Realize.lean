import H01PairBridge

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder

set_option maxHeartbeats 3000000

theorem H01Space_realize (Ω : Set V) (hΩ : IsOpen Ω)
    (p : H01Space Ω) :
    ∃ (v : V → ℝ) (hv : H1Witness v Ω),
      DeGiorgi.MemH01 v Ω ∧ witnessPair hv = p.val := by
  classical
  have hp : p.val ∈ closure (smoothPairs Ω) := by
    rw [← H01Space_eq_closure_smoothPairs Ω hΩ]
    exact p.property
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  choose v hv hs hc ht heq using hq
  let μ := volume.restrict Ω
  let f : V → ℝ := p.val.ofLp.1
  let G : V → V := p.val.ofLp.2
  have hf : MemLp f 2 μ := Lp.memLp _
  have hG : MemLp G 2 μ := Lp.memLp _
  have hflim : Tendsto (fun n => (hv n).memLp.toLp (v n)) atTop (𝓝 p.val.ofLp.1) := by
    have := (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) (Lp V 2 μ)).continuous.tendsto p.val |>.comp hlim
    simpa [Function.comp_def, heq, witnessPair] using this
  have hGlim : Tendsto (fun n => (weak_gradient_memLp Ω (v n) (hv n)).toLp (hv n).weakGrad)
      atTop (𝓝 p.val.ofLp.2) := by
    have := (WithLp.sndL 2 ℝ (Lp ℝ 2 μ) (Lp V 2 μ)).continuous.tendsto p.val |>.comp hlim
    simpa [Function.comp_def, heq, witnessPair] using this
  have hflim' : Tendsto (fun n => eLpNorm (fun x => v n x - f x) 2 μ) atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v (fun n => (hv n).memLp) f hf).mp
    simpa only [f, Lp.toLp_coeFn] using hflim
  have hGlim' : Tendsto (fun n => eLpNorm (fun x => (hv n).weakGrad x - G x) 2 μ)
      atTop (𝓝 0) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (hv n).weakGrad)
      (fun n => weak_gradient_memLp Ω (v n) (hv n)) G hG).mp
    simpa only [G, Lp.toLp_coeFn] using hGlim
  have hclim (i : Fin 3) : Tendsto
      (fun n => eLpNorm (fun x => (hv n).weakGrad x i - G x i) 2 μ) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim'
    · intro n
      exact bot_le
    · intro n
      exact eLpNorm_mono (((hv n).weakGrad_component_memLp i).sub (hG.eval_piLp i)).aestronglyMeasurable
        (fun x => PiLp.norm_apply_le ((hv n).weakGrad x - G x) i)
  let hw : H1Witness f Ω :=
    { memLp := hf
      weakGrad := G
      weakGrad_component_memLp := hG.eval_piLp
      isWeakGrad := by
        intro i
        apply DeGiorgi.HasWeakPartialDeriv.of_eLpNormApprox_p hΩ (by norm_num : (1 : ℝ) < 2)
          (by simpa using hf) (by simpa using hG.eval_piLp i)
          (fun n => (hv n).isWeakGrad i)
          (fun n => by convert (hv n).memLp.sub hf using 1 <;> norm_num)
          (by simpa using hflim')
          (fun n => by convert ((hv n).weakGrad_component_memLp i).sub (hG.eval_piLp i) using 1 <;> norm_num)
          (by simpa using hclim i) }
  refine ⟨f, hw, ?_, ?_⟩
  · refine ⟨hw.memW1p, hw, v, hs, hc, ht, hflim', ?_⟩
    intro i
    apply (tendsto_congr (fun n => ?_)).mp (hclim i)
    apply eLpNorm_congr_ae
    filter_upwards [witnessPair_smooth_grad hΩ (hv n) (hs n) (hc n)] with x hx
    change (hv n).weakGrad x i - G x i = (fderiv ℝ (v n) x) (EuclideanSpace.single i 1) - G x i
    rw [hx]
    rfl
  · apply WithLp.ofLp_injective
    apply Prod.ext
    · exact Lp.toLp_coeFn p.val.ofLp.1 hf
    · exact Lp.toLp_coeFn p.val.ofLp.2 hG

end SeifertSurfaces.WeakSchauder
