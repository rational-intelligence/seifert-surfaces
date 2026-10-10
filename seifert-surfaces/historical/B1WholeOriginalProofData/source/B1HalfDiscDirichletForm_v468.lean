import B1HalfDiscNativeSpace_v468
import LaxMilgramRelease
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem bounded_field_L2_operator_v468
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure E2) (C : E2 → F → G) (K : ℝ) (hK : 0 < K)
    (hadd : ∀ x v w, C x (v + w) = C x v + C x w)
    (hsmul : ∀ x (a : ℝ) v, C x (a • v) = a • C x v)
    (hmeas : ∀ f : E2 → F, MemLp f 2 μ → AEStronglyMeasurable (fun x => C x (f x)) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ v, ‖C x v‖ ≤ K * ‖v‖) :
    ∃ T : Lp F 2 μ →L[ℝ] Lp G 2 μ,
      ∀ f : Lp F 2 μ, (T f : E2 → G) =ᵐ[μ] fun x => C x (f x) := by
  have mapped (f : E2 → F) (hf : MemLp f 2 μ) : MemLp (fun x => C x (f x)) 2 μ := by
    apply hf.of_le_mul (hmeas f hf)
    filter_upwards [hbound] with x hx
    exact hx (f x)
  let T : Lp F 2 μ → Lp G 2 μ := fun f =>
    (mapped f (Lp.memLp f)).toLp (fun x => C x (f x))
  have Tcoe (f : Lp F 2 μ) : (T f : E2 → G) =ᵐ[μ] fun x => C x (f x) :=
    (mapped f (Lp.memLp f)).coeFn_toLp
  have Tadd (f g : Lp F 2 μ) : T (f + g) = T f + T g := by
    apply Lp.ext
    filter_upwards [Tcoe (f + g), Tcoe f, Tcoe g, Lp.coeFn_add f g,
      Lp.coeFn_add (T f) (T g)] with x hab ha hb hfg htab
    rw [hab, htab, hfg]
    change C x (f x + g x) = T f x + T g x
    rw [ha,hb]
    exact hadd x (f x) (g x)
  have Tsmul (a : ℝ) (f : Lp F 2 μ) : T (a • f) = a • T f := by
    apply Lp.ext
    filter_upwards [Tcoe (a • f), Tcoe f, Lp.coeFn_smul a f,
      Lp.coeFn_smul a (T f)] with x haf hf haf' hat
    rw [haf, hat, haf']
    change C x (a • f x) = a • T f x
    rw [hf]
    exact hsmul x a (f x)
  let Tlin : Lp F 2 μ →ₗ[ℝ] Lp G 2 μ :=
    { toFun := T, map_add' := Tadd, map_smul' := Tsmul }
  have Tnorm (f : Lp F 2 μ) : ‖Tlin f‖ ≤ K * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Tcoe f, hbound] with x hx hb
    change ‖T f x‖ ≤ K * ‖f x‖
    rw [hx]
    exact hb (f x)
  exact ⟨Tlin.mkContinuous K Tnorm, Tcoe⟩

/-- The full principal/drift/zeroth-order form acts on the literal L²-pair space. -/
theorem halfdisc_full_form_data_v468 (R : ℝ) (a : E2 → Mat2)
    (b : E2 → E2) (c : E2 → ℝ)
    (ha : ∀ i j, AEStronglyMeasurable (fun x => a x i j) (volume.restrict (halfDisc R)))
    (hb : AEStronglyMeasurable b (volume.restrict (halfDisc R)))
    (hc : AEStronglyMeasurable c (volume.restrict (halfDisc R)))
    (A B C : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (haBound : ∀ x ∈ halfDisc R, ∀ v, ‖matrixAction (a x) v‖ ≤ A * ‖v‖)
    (hbBound : ∀ x ∈ halfDisc R, ‖b x‖ ≤ B)
    (hcBound : ∀ x ∈ halfDisc R, |c x| ≤ C) :
    ∃ F : Pair (halfDisc R) →L[ℝ] Pair (halfDisc R) →L[ℝ] ℝ,
      (∀ p q, F p q =
        ∫ x in halfDisc R, inner ℝ (matrixAction (a x) (p.snd x)) (q.snd x) -
          (inner ℝ (b x) (p.snd x) + c x * p.fst x) * q.fst x) ∧
      (∀ u du v dv, MemLp u 2 (volume.restrict (halfDisc R)) →
        MemLp du 2 (volume.restrict (halfDisc R)) →
        MemLp v 2 (volume.restrict (halfDisc R)) →
        MemLp dv 2 (volume.restrict (halfDisc R)) →
        IntegrableOn (fun x => inner ℝ (matrixAction (a x) (du x)) (dv x) -
          (inner ℝ (b x) (du x) + c x * u x) * v x) (halfDisc R)) := by
  let U := halfDisc R
  let μ := volume.restrict U
  have hU : MeasurableSet U := by
    change MeasurableSet (Metric.ball (0 : E2) R ∩ {x : E2 | 0 < x 1})
    exact (Metric.isOpen_ball.inter (isOpen_lt continuous_const
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have maadd (x : E2) (v w : E2) : matrixAction (a x) (v + w) =
      matrixAction (a x) v + matrixAction (a x) w := by
    ext i
    simp [matrixAction, mul_add, Finset.sum_add_distrib]
  have masmul (x : E2) (t : ℝ) (v : E2) : matrixAction (a x) (t • v) =
      t • matrixAction (a x) v := by
    ext i
    simp [matrixAction, Finset.mul_sum, mul_left_comm]
    ring
  have mameas (f : E2 → E2) (hf : MemLp f 2 μ) :
      AEStronglyMeasurable (fun x => matrixAction (a x) (f x)) μ := by
    have coord (j : Fin 2) : MemLp (fun x => f x j) 2 μ :=
      hf.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) j)
    have hm (i : Fin 2) : AEStronglyMeasurable (fun x => ∑ j, a x i j * f x j) μ := by
      simp only [Fin.sum_univ_two]
      exact ((ha i 0).mul (coord 0).aestronglyMeasurable).add
        ((ha i 1).mul (coord 1).aestronglyMeasurable)
    have hp : AEMeasurable (fun x => fun i : Fin 2 => ∑ j, a x i j * f x j) μ :=
      AEMeasurable.of_eval fun i => (hm i).aemeasurable
    exact ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp_aemeasurable hp).aestronglyMeasurable
  obtain ⟨Ta,hTa⟩ := bounded_field_L2_operator_v468 μ
    (fun x v => matrixAction (a x) v) A hA maadd masmul mameas
    (by filter_upwards [ae_restrict_mem hU] with x hx; exact haBound x hx)
  obtain ⟨Tb,hTb⟩ := bounded_field_L2_operator_v468 μ
    (fun x v => inner ℝ (b x) v) B hB
    (fun x v w => inner_add_right _ _ _)
    (fun x t v => by simp [inner_smul_right])
    (fun f hf => hb.inner hf.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem hU] with x hx
      intro v
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hbBound x hx) (norm_nonneg v)))
  obtain ⟨Tc,hTc⟩ := bounded_field_L2_operator_v468 μ
    (fun (x : E2) (v : ℝ) => c x * v) C hC
    (fun x v w => mul_add _ _ _)
    (fun x t v => by simp [mul_left_comm])
    (fun f hf => hc.mul hf.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem hU] with x hx
      intro v
      simpa only [Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right (hcBound x hx) (abs_nonneg v))
  let fst : Pair U →L[ℝ] Lp ℝ 2 μ := WithLp.fstL 2 ℝ _ _
  let snd : Pair U →L[ℝ] Lp E2 2 μ := WithLp.sndL 2 ℝ _ _
  let lower : Pair U →L[ℝ] Lp ℝ 2 μ := Tb.comp snd + Tc.comp fst
  let F : Pair U →L[ℝ] Pair U →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (Ta.comp snd) snd -
      (innerSL ℝ).bilinearComp lower fst
  have mappedA (du : E2 → E2) (hdu : MemLp du 2 μ) :
      MemLp (fun x => matrixAction (a x) (du x)) 2 μ := by
    apply hdu.of_le_mul (mameas du hdu)
    filter_upwards [ae_restrict_mem hU] with x hx
    exact haBound x hx (du x)
  have mappedB (du : E2 → E2) (hdu : MemLp du 2 μ) :
      MemLp (fun x => inner ℝ (b x) (du x)) 2 μ := by
    apply hdu.of_le_mul (hb.inner hdu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hU] with x hx
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hbBound x hx) (norm_nonneg _))
  have mappedC (u : E2 → ℝ) (hu : MemLp u 2 μ) :
      MemLp (fun x => c x * u x) 2 μ := by
    apply hu.of_le_mul (hc.mul hu.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hU] with x hx
    simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
      mul_le_mul_of_nonneg_right (hcBound x hx) (abs_nonneg (u x))
  have hint (u : E2 → ℝ) (du : E2 → E2) (v : E2 → ℝ) (dv : E2 → E2)
      (hu : MemLp u 2 μ) (hdu : MemLp du 2 μ)
      (hv : MemLp v 2 μ) (hdv : MemLp dv 2 μ) :
      Integrable (fun x => inner ℝ (matrixAction (a x) (du x)) (dv x)) μ ∧
      Integrable (fun x => (inner ℝ (b x) (du x) + c x * u x) * v x) μ := by
    constructor
    · apply (L2.integrable_inner (𝕜 := ℝ)
        ((mappedA du hdu).toLp _) (hdv.toLp dv)).congr
      filter_upwards [(mappedA du hdu).coeFn_toLp, hdv.coeFn_toLp] with x hx hdx
      rw [hx,hdx]
    · let hl := (mappedB du hdu).add (mappedC u hu)
      apply (L2.integrable_inner (𝕜 := ℝ) (hl.toLp _) (hv.toLp v)).congr
      filter_upwards [hl.coeFn_toLp,hv.coeFn_toLp] with x hx hvx
      rw [hx,hvx,Real.inner_apply]
      rfl
  refine ⟨F,?_,?_⟩
  · intro p q
    change inner ℝ (Ta p.snd) q.snd - inner ℝ (Tb p.snd + Tc p.fst) q.fst = _
    rw [L2.inner_def,L2.inner_def]
    have hi := hint p.fst p.snd q.fst q.snd (Lp.memLp _) (Lp.memLp _) (Lp.memLp _) (Lp.memLp _)
    rw [← integral_sub]
    · apply integral_congr_ae
      filter_upwards [hTa p.snd,hTb p.snd,hTc p.fst,Lp.coeFn_add (Tb p.snd) (Tc p.fst)] with x ha hb hc hadd
      rw [ha,hadd]
      simp only [Pi.add_apply]
      rw [hb,hc,Real.inner_apply]
    · exact L2.integrable_inner (Ta p.snd) q.snd
    · exact L2.integrable_inner (Tb p.snd + Tc p.fst) q.fst
  · intro u du v dv hu hdu hv hdv
    exact (hint u du v dv hu hdu hv hdv).1.sub (hint u du v dv hu hdu hv hdv).2

end SeifertSurfaces.OriginalEndpoints.B1Tangency
