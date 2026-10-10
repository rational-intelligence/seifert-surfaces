import ReplacementPairTools

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace SeifertSurfaces.WeakSchauder
set_option maxHeartbeats 3000000

lemma replacement_construct (center : V) (R κ Λ : ℝ)
    (hR : 0 < R) (hκ : 0 < κ) (hΛ : κ ≤ Λ) (A : Mat)
    (hA : CoefficientBounds (fun _ => A) (Metric.ball center R) κ Λ)
    (v : V → ℝ) (hv : H1Witness v (Metric.ball center R)) :
    ∃ (h : V → ℝ) (hh : H1Witness h (Metric.ball center R)), IsHarmonicReplacement A hv hh := by
  classical
  let Ω := Metric.ball center R
  letI := H01Space_complete Ω
  obtain ⟨hb, c, hc, hcoercive⟩ := frozenForm_bounded_coercive center R κ Λ hR hκ hΛ A hA
  let L := (frozenLoad_bounded_linear center R κ Λ hR hκ hΛ A hA v hv).toContinuousLinearMap
  obtain ⟨p, hp, _⟩ := real_lax_milgram (frozenForm A Ω) hb c hc hcoercive L
  obtain ⟨w, hw, hw0, hwP⟩ := H01Space_realize Ω Metric.isOpen_ball p
  let h := fun x => v x + w x
  let hh := hv.add hw
  refine ⟨h, hh, ?_, ?_⟩
  · simpa [h] using hw0.smul (-1)
  · intro φ hφ0 hφ
    let q : H01Space Ω := ⟨witnessPair hφ, (H01Space_mem_iff Ω Metric.isOpen_ball φ hφ).mpr hφ0⟩
    refine ⟨matrix_inner_integrable A (weak_gradient_memLp Ω h hh) (weak_gradient_memLp Ω φ hφ), ?_⟩
    have hpg : p.val.ofLp.2 = (weak_gradient_memLp Ω w hw).toLp hw.weakGrad := by
      exact (congrArg (fun t : SobolevPair Ω => t.ofLp.2) hwP).symm
    have hpq := hp q
    change frozenForm A Ω (p, q) = frozenLoad A hv q at hpq
    rw [frozenForm_eq_inner, frozenLoad_eq_inner] at hpq
    change inner ℝ ((matrixActionLinear A).compLp p.val.ofLp.2)
      ((weak_gradient_memLp Ω φ hφ).toLp hφ.weakGrad) =
      -inner ℝ ((matrixActionLinear A).compLp ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad))
        ((weak_gradient_memLp Ω φ hφ).toLp hφ.weakGrad) at hpq
    rw [hpg] at hpq
    rw [matrix_inner_toLp A (weak_gradient_memLp Ω h hh) (weak_gradient_memLp Ω φ hφ)]
    have hsum : (weak_gradient_memLp Ω h hh).toLp hh.weakGrad =
        (weak_gradient_memLp Ω v hv).toLp hv.weakGrad + (weak_gradient_memLp Ω w hw).toLp hw.weakGrad :=
      MemLp.toLp_add (weak_gradient_memLp Ω v hv) (weak_gradient_memLp Ω w hw)
    rw [hsum]
    change inner ℝ (((matrixActionLinear A).compLpL 2 (volume.restrict Ω))
      ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad + (weak_gradient_memLp Ω w hw).toLp hw.weakGrad))
      ((weak_gradient_memLp Ω φ hφ).toLp hφ.weakGrad) = 0
    simp only [map_add, inner_add_left]
    change inner ℝ (((matrixActionLinear A).compLpL 2 (volume.restrict Ω))
      ((weak_gradient_memLp Ω w hw).toLp hw.weakGrad)) ((weak_gradient_memLp Ω φ hφ).toLp hφ.weakGrad) =
      -inner ℝ (((matrixActionLinear A).compLpL 2 (volume.restrict Ω))
      ((weak_gradient_memLp Ω v hv).toLp hv.weakGrad)) ((weak_gradient_memLp Ω φ hφ).toLp hφ.weakGrad) at hpq
    linarith

end SeifertSurfaces.WeakSchauder
