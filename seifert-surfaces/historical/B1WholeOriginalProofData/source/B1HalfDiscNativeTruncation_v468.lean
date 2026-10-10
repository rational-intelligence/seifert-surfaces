import B1NativeTruncationProviders_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Smooth positive parts are admissible native H10 tests, via the paid supported bridge. -/
theorem native_smooth_positive_h10_v468 (U : Set E2) (hU : IsOpen U)
    (φ : E2 → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ U) :
    H10On U (fun x => max (φ x) 0)
      (fun x => if 0 < φ x then planarGradient φ x else 0) := by
  classical
  have hgc : HasCompactSupport (planarGradient φ) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra h
    exact hx (planarGradient_eq_zero_off_support φ h)
  have hp : MemLp φ 2 (volume.restrict U) :=
    (hs.continuous.memLp_of_hasCompactSupport (μ := volume) hc).restrict _
  have hg : MemLp (planarGradient φ) 2 (volume.restrict U) :=
    ((continuous_planarGradient hs).memLp_of_hasCompactSupport (μ := volume) hgc).restrict _
  have hpos : MemLp (fun x => max (φ x) 0) 2 (volume.restrict U) := hp.pos_part
  have hposg : MemLp (fun x => if 0 < φ x then planarGradient φ x else 0) 2 (volume.restrict U) := by
    apply memLp_piLp_iff.mpr
    intro i
    convert DeGiorgi.indicator_component_memLp hp.aemeasurable (hg.eval_piLp i) using 1
    funext x
    by_cases hx : 0 < φ x <;> simp [hx]
  have h1 : H1On U (fun x => max (φ x) 0)
      (fun x => if 0 < φ x then planarGradient φ x else 0) := by
    refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hpos.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict (hposg.locallyIntegrable (by norm_num)),?_⟩,hpos,hposg⟩
    intro ψ hψ hcψ htψ i
    have he := smooth_positivepart_partial_provider_v468 U i φ (hs.of_le (by simp)) hc ψ hψ hcψ htψ
    have hcoord (x : E2) : planarGradient φ x i = fderiv ℝ φ x (coordinateVector 2 i) := by
      fin_cases i <;> simp [planarGradient,Fin.sum_univ_two,coordinateVector]
    have heq : (fun x => (if 0 < φ x then planarGradient φ x else 0) i) =
        (fun x => if 0 < φ x then (fderiv ℝ φ x) (coordinateVector 2 i) else 0) := by
      funext x
      by_cases hx : 0 < φ x <;> simp [hx,hcoord]
    change (∫ x in U, max (φ x) 0 * (fderiv ℝ ψ x) (coordinateVector 2 i)) =
      -∫ x in U, (fun x => (if 0 < φ x then planarGradient φ x else 0) i) x * ψ x
    rw [heq]
    exact he
  apply native_supported_h10_provider_v468 U (tsupport φ) hU hc ht _ _ h1
  · apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport (f := φ) hn
    exact hx (by simp [hz])
  · intro i
    apply closure_minimal _ (isClosed_tsupport φ)
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport (f := φ) hn
    exact hx (by simp [hz])

/-- The completed native pair has smooth compact tests converging in the exact L2 scalar and vector classes. -/
theorem halfdisc_native_smooth_approx_v468 (R : ℝ) (p : X (halfDisc R)) :
    ∃ φ : ℕ → E2 → ℝ,
      (∀ n, ContDiff ℝ ∞ (φ n)) ∧
      (∀ n, HasCompactSupport (φ n)) ∧
      (∀ n, tsupport (φ n) ⊆ halfDisc R) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - val (halfDisc R) p x)
        2 (volume.restrict (halfDisc R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun x => planarGradient (φ n) x - grad (halfDisc R) p x)
        2 (volume.restrict (halfDisc R))) atTop (𝓝 0) := by
  classical
  let U := halfDisc R
  let μ := volume.restrict U
  have hspace : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe,halfdisc_smoothGraph_span_export_v468 R]
  have hmem : p.val ∈ closure (SmoothGraph U) := by rw [← hspace]; exact p.property
  obtain ⟨q,hq,hqt⟩ := mem_closure_iff_seq_limit.mp hmem
  choose φ hφ hg hs hc ht he using hq
  have hvLp (n : ℕ) : (hφ n).toLp (φ n) = (q n).fst := by rw [he n]; rfl
  have hgLp (n : ℕ) : (hg n).toLp (planarGradient (φ n)) = (q n).snd := by rw [he n]; rfl
  have hvs : Tendsto (fun n => (q n).fst) atTop (𝓝 p.val.fst) :=
    (WithLp.continuous_fst 2 (Lp ℝ 2 μ) (Lp E2 2 μ)).tendsto p.val |>.comp hqt
  have hgs : Tendsto (fun n => (q n).snd) atTop (𝓝 p.val.snd) :=
    (WithLp.continuous_snd 2 (Lp ℝ 2 μ) (Lp E2 2 μ)).tendsto p.val |>.comp hqt
  have hv : MemLp (val U p) 2 μ := Lp.memLp (valLp U p)
  have hd : MemLp (grad U p) 2 μ := Lp.memLp (gradLp U p)
  have hconv {F : Type} [NormedAddCommGroup F]
      (f : ℕ → E2 → F) (u : E2 → F) (hf : ∀ n, MemLp (f n) 2 μ) (hu : MemLp u 2 μ)
      (hn : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u))) :
      Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) atTop (𝓝 0) := by
    have hh := ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.mp hn)
    simpa only [ENNReal.ofReal_zero] using hh.congr (fun n => by
      rw [← MemLp.toLp_sub,Lp.norm_toLp,ENNReal.ofReal_toReal (hf n |>.sub hu |>.eLpNorm_ne_top)]
      rfl)
  have hpval : hv.toLp (val U p) = p.val.fst := by
    change hv.toLp (valLp U p) = valLp U p
    exact Lp.toLp_coeFn (valLp U p) hv
  have hdval : hd.toLp (grad U p) = p.val.snd := by
    change hd.toLp (gradLp U p) = gradLp U p
    exact Lp.toLp_coeFn (gradLp U p) hd
  refine ⟨φ,hs,hc,ht,?_,?_⟩
  · apply hconv φ (val U p) hφ hv
    rw [hpval]
    exact hvs.congr (fun n => (hvLp n).symm)
  · apply hconv (fun n => planarGradient (φ n)) (grad U p) hg hd
    rw [hdval]
    exact hgs.congr (fun n => (hgLp n).symm)

end SeifertSurfaces.OriginalEndpoints.B1Tangency
