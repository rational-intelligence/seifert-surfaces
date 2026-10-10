import B1HalfDiscOffsetClosure_v468
import B1HalfDiscBarrierWeakTest_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The classical barrier identity extends to every completed native H10 test. -/
theorem halfdisc_classical_form_completed_identity_v468
    (R : ℝ) (O : Set E2) (hO : IsOpen O) (hUO : halfDisc R ⊆ O)
    (a : E2 → Mat2) (b : E2 → E2) (c v : E2 → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hb : ContDiffOn ℝ ∞ b O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : ContDiff ℝ ∞ v)
    (hvlp : MemLp v 2 (volume.restrict (halfDisc R)))
    (hdvlp : MemLp (planarGradient v) 2 (volume.restrict (halfDisc R)))
    (hLlp : MemLp (classicalL a b c v) 2 (volume.restrict (halfDisc R)))
    (F : Pair (halfDisc R) →L[ℝ] Pair (halfDisc R) →L[ℝ] ℝ)
    (hFeq : ∀ p q, F p q =
      ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (p.snd x)) (q.snd x) -
        (inner ℝ (b x) (p.snd x) + c x * p.fst x) * q.fst x) :
    ∀ q : X (halfDisc R), F (pack (halfDisc R) v (planarGradient v) hvlp hdvlp) q.val =
      -(∫ x in halfDisc R, classicalL a b c v x * val (halfDisc R) q x) := by
  let U := halfDisc R
  let μ := volume.restrict U
  let ell : Pair U →L[ℝ] ℝ := (innerSL ℝ (hLlp.toLp (classicalL a b c v))).comp
    (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) (Lp E2 2 μ))
  let V := pack U v (planarGradient v) hvlp hdvlp
  have hclosed : IsClosed {q : Pair U | F V q + ell q = 0} :=
    isClosed_eq ((F V).continuous.add ell.continuous) continuous_const
  have hsmooth : SmoothGraph U ⊆ {q : Pair U | F V q + ell q = 0} := by
    rintro q ⟨φ,hφ,hg,hs,hφc,ht,rfl⟩
    have hform := halfdisc_classical_form_identity_v468 R O hO hUO a b c v ha hb hc hv φ hs hφc ht
    have hF : F V (pack U φ (planarGradient φ) hφ hg) =
        ∫ x in U, inner ℝ (matrixAction (a x) (planarGradient v x)) (planarGradient φ x) -
          (inner ℝ (b x) (planarGradient v x) + c x * v x) * φ x := by
      rw [hFeq]
      apply integral_congr_ae
      filter_upwards [hvlp.coeFn_toLp,hdvlp.coeFn_toLp,hφ.coeFn_toLp,hg.coeFn_toLp] with x hvx hdvx hφx hgx
      change inner ℝ (matrixAction (a x) ((hdvlp.toLp _) x)) ((hg.toLp _) x) -
        (inner ℝ (b x) ((hdvlp.toLp _) x) + c x * (hvlp.toLp _) x) * (hφ.toLp _) x = _
      rw [hvx,hdvx,hφx,hgx]
    have hell : ell (pack U φ (planarGradient φ) hφ hg) =
        ∫ x in U, classicalL a b c v x * φ x := by
      change inner ℝ (hLlp.toLp _) (hφ.toLp φ) = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hLlp.coeFn_toLp,hφ.coeFn_toLp] with x hx hφx
      rw [hx,hφx,Real.inner_apply]
    change F V (pack U φ (planarGradient φ) hφ hg) + ell (pack U φ (planarGradient φ) hφ hg) = 0
    rw [hF,hell,hform.2.2,neg_add_cancel]
  intro q
  have hspace : (space U : Set (Pair U)) = closure (SmoothGraph U) := by
    rw [Submodule.topologicalClosure_coe,halfdisc_smoothGraph_span_export_v468 R]
  have hmem : q.val ∈ closure (SmoothGraph U) := by rw [← hspace]; exact q.property
  have hz := closure_minimal hsmooth hclosed hmem
  change F V q.val + ell q.val = 0 at hz
  have hell : ell q.val = ∫ x in U, classicalL a b c v x * val U q x := by
    change inner ℝ (hLlp.toLp _) (valLp U q) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hLlp.coeFn_toLp] with x hx
    rw [hx,Real.inner_apply]
    rfl
  rw [hell] at hz
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency
