import ReplacementEnergy

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000

theorem harmonic_replacement_exists (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)) :
    ∃ (h : V → ℝ) (hh : H1Witness h (Metric.ball center R)),
      IsHarmonicReplacement A hv hh ∧
      energy hh.weakGrad center R ≤ (Λ / κ) ^ 2 * energy hv.weakGrad center R ∧
      ∀ (h' : V → ℝ) (hh' : H1Witness h' (Metric.ball center R)),
        IsHarmonicReplacement A hv hh' → h' =ᵐ[volume.restrict (Metric.ball center R)] h := by
  obtain ⟨h, hh, hrep⟩ := replacement_construct center R κ Λ hR hκ hΛ A hA v hv
  refine ⟨h, hh, hrep, replacement_energy_bound center R κ Λ hR hκ hΛ A hA v h hv hh hrep, ?_⟩
  intro h' hh' hrep'
  let Ω := Metric.ball center R
  let hd := witnessSub hh' hh
  have hd0 : DeGiorgi.MemH01 (fun x => h' x - h x) Ω := by
    have ht := hrep.1.sub hrep'.1
    convert ht using 1
    ext x
    ring
  let q : H01Space Ω := ⟨witnessPair hd, (H01Space_mem_iff Ω Metric.isOpen_ball _ hd).mpr hd0⟩
  have hz := (hrep.2 _ hd0 hd).2
  have hz' := (hrep'.2 _ hd0 hd).2
  rw [matrix_inner_toLp A (weak_gradient_memLp Ω h hh) (weak_gradient_memLp Ω _ hd)] at hz
  rw [matrix_inner_toLp A (weak_gradient_memLp Ω h' hh') (weak_gradient_memLp Ω _ hd)] at hz'
  let g := (weak_gradient_memLp Ω _ hd).toLp hd.weakGrad
  let M := (matrixActionLinear A).compLpL 2 (volume.restrict Ω)
  have hsub : g = (weak_gradient_memLp Ω h' hh').toLp hh'.weakGrad -
      (weak_gradient_memLp Ω h hh).toLp hh.weakGrad :=
    MemLp.toLp_sub (weak_gradient_memLp Ω h' hh') (weak_gradient_memLp Ω h hh)
  have hb0 : frozenForm A Ω (q, q) = 0 := by
    rw [frozenForm_eq_inner]
    change inner ℝ (M g) g = 0
    rw [hsub]
    rw [map_sub, inner_sub_left]
    change inner ℝ (M ((weak_gradient_memLp Ω h hh).toLp hh.weakGrad)) g = 0 at hz
    change inner ℝ (M ((weak_gradient_memLp Ω h' hh').toLp hh'.weakGrad)) g = 0 at hz'
    rw [hsub] at hz hz'
    rw [hz, hz']
    ring
  obtain ⟨_, c, hc, hco⟩ := frozenForm_bounded_coercive center R κ Λ hR hκ hΛ A hA
  have hnorm := hco q
  rw [hb0] at hnorm
  have hq0 : q = 0 := by
    apply norm_eq_zero.mp
    have hzero : c * ‖q‖ ^ 2 = 0 := le_antisymm hnorm (mul_nonneg hc.le (sq_nonneg _))
    have hsq0 := (mul_eq_zero.mp hzero).resolve_left hc.ne'
    exact (sq_eq_zero_iff).mp hsq0
  have hf0 : hd.memLp.toLp (fun x => h' x - h x) = 0 := by
    exact congrArg (fun t : H01Space Ω => t.val.ofLp.1) hq0
  have hae : (fun x => h' x - h x) =ᵐ[volume.restrict Ω] 0 := by
    apply (MemLp.toLp_eq_toLp_iff hd.memLp (MemLp.zero)).mp
    simpa using hf0
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp hx

end SeifertSurfaces.WeakSchauder
