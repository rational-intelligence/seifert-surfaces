import IsothermalPDEData
import WeakPoincarePotential
noncomputable section
open Set Topology MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
open SeifertSurfaces.AppendixACoordinates

/-- A1.4(c): the continuous distributionally closed rotated flux has a same-alpha potential. -/
theorem weak_harmonic_conjugate_potential (R : ℝ) (A : E2 → Mat2)
    (G : InverseMetricData R A) (M : E2 → Mat2) (y : E2) (r : ℝ)
    (hr : 0 < r) (symmetric : SymmetricOn M (Metric.ball y r))
    (elliptic : UniformEllipticOn M (Metric.ball y r))
    (holder : ∀ i j, ∃ C : ℝ≥0,
      HolderOnWith C G.alpha (fun x => M x i j) (Metric.ball y r))
    (a : E2 → ℝ) (regular : ScalarC1AlphaOn G.alpha a (Metric.ball y r))
    (weak : WeakLinearEquationOn (Metric.ball y r) (normalizedInverse M)
      (fun _ => 0) (fun _ => 0) a (planarGradient a)) :
    ∃ b : E2 → ℝ, b y = 0 ∧ ScalarC1AlphaOn G.alpha b (Metric.ball y r) ∧
      ∀ x ∈ Metric.ball y r,
        planarGradient b x = rotation (matrixAction (normalizedInverse M x) (planarGradient a x)) := by
  classical
  let F : E2 → E2 := fun x =>
    rotation (matrixAction (normalizedInverse M x) (planarGradient a x))
  have hdet (x : E2) (hx : x ∈ Metric.ball y r) : 0 < Matrix.det (M x) := by
    obtain ⟨ell, C, hell, hC, hbound⟩ := elliptic
    apply Matrix.PosDef.det_pos
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · ext i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using symmetric x hx j i
    · intro z hz
      let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm z
      have hp : p ≠ 0 := by
        intro h
        apply hz
        have hh := congrArg (EuclideanSpace.equiv (Fin 2) ℝ) h
        simpa only [p, ContinuousLinearEquiv.apply_symm_apply, map_zero] using hh
      have hpos : 0 < inner ℝ p (matrixAction (M x) p) :=
        (mul_pos hell (sq_pos_of_pos (norm_pos_iff.mpr hp))).trans_le (hbound x hx p).1
      change 0 < ∑ i : Fin 2, (∑ j : Fin 2, M x i j * z j) * z i at hpos
      simpa only [Matrix.mulVec, dotProduct, star_trivial, mul_comm] using hpos
  let Z : E2 → (Fin 6 → ℝ) := fun z =>
    ![M z 0 0, M z 0 1, M z 1 0, M z 1 1, planarGradient a z 0, planarGradient a z 1]
  let D : (Fin 6 → ℝ) → ℝ := fun t => t 0 * t 3 - t 1 * t 2
  let g : (Fin 6 → ℝ) → (Fin 2 → ℝ) := fun t =>
    ![-(Real.sqrt (D t) * (D t)⁻¹ * (-t 2 * t 4 + t 0 * t 5)),
      Real.sqrt (D t) * (D t)⁻¹ * (t 3 * t 4 - t 1 * t 5)]
  have hrep (z : E2) : g (Z z) = fun i => F z i := by
    change g (Z z) = ![-(∑ j : Fin 2,
      (Real.sqrt (Matrix.det (M z)) • (M z)⁻¹) 1 j * planarGradient a z j),
      ∑ j : Fin 2, (Real.sqrt (Matrix.det (M z)) • (M z)⁻¹) 0 j * planarGradient a z j]
    ext i
    fin_cases i <;>
      simp [g, D, Z, Matrix.inv_def, Ring.inverse_eq_inv,
        Matrix.adjugate_fin_two, Matrix.det_fin_two, Fin.sum_univ_two] <;> ring
  have hlocal : ∀ x ∈ Metric.ball y r, ∃ s : ℝ, 0 < s ∧
      Metric.ball x s ⊆ Metric.ball y r ∧ ∀ i : Fin 2, ∃ C : ℝ≥0,
        HolderOnWith C G.alpha (fun z => F z i) (Metric.ball x s) := by
    intro x hx
    obtain ⟨s₀, hs₀, hsub, ha⟩ := regular.2 x hx
    have hZcoord : ∀ i : Fin 6, ∃ C : ℝ≥0,
        HolderOnWith C G.alpha (fun z => Z z i) (Metric.ball x s₀) := by
      intro i
      fin_cases i
      · obtain ⟨C, h⟩ := holder 0 0
        exact ⟨C, h.mono hsub⟩
      · obtain ⟨C, h⟩ := holder 0 1
        exact ⟨C, h.mono hsub⟩
      · obtain ⟨C, h⟩ := holder 1 0
        exact ⟨C, h.mono hsub⟩
      · obtain ⟨C, h⟩ := holder 1 1
        exact ⟨C, h.mono hsub⟩
      · exact ha 0
      · exact ha 1
    choose C hC using hZcoord
    have hZ : HolderOnWith (∑ i, C i) G.alpha Z (Metric.ball x s₀) := by
      intro u hu v hv
      apply edist_pi_le_iff.mpr
      intro i
      exact ((hC i).mono_const (Finset.single_le_sum (fun j _ => show 0 ≤ C j from zero_le)
        (Finset.mem_univ i))) u hu v hv
    have hDx : D (Z x) ≠ 0 := by
      change M x 0 0 * M x 1 1 - M x 0 1 * M x 1 0 ≠ 0
      rw [← Matrix.det_fin_two]
      exact (hdet x hx).ne'
    have hD : ContDiffAt ℝ 1 D (Z x) :=
      ((contDiff_apply ℝ ℝ 0).contDiffAt.mul (contDiff_apply ℝ ℝ 3).contDiffAt).sub
        ((contDiff_apply ℝ ℝ 1).contDiffAt.mul (contDiff_apply ℝ ℝ 2).contDiffAt)
    have hg : ContDiffAt ℝ 1 g (Z x) := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i
      · exact (((hD.sqrt hDx).mul (hD.inv hDx)).mul
          (((contDiff_apply ℝ ℝ 2).contDiffAt.neg.mul (contDiff_apply ℝ ℝ 4).contDiffAt).add
            ((contDiff_apply ℝ ℝ 0).contDiffAt.mul (contDiff_apply ℝ ℝ 5).contDiffAt))).neg
      · exact ((hD.sqrt hDx).mul (hD.inv hDx)).mul
          (((contDiff_apply ℝ ℝ 3).contDiffAt.mul (contDiff_apply ℝ ℝ 4).contDiffAt).sub
            ((contDiff_apply ℝ ℝ 1).contDiffAt.mul (contDiff_apply ℝ ℝ 5).contDiffAt))
    obtain ⟨K, V, hV, hgV⟩ := hg.exists_lipschitzOnWith
    have hcZ : ContinuousAt Z x :=
      (hZ.continuousOn G.alpha_pos).continuousAt (Metric.ball_mem_nhds x hs₀)
    obtain ⟨s₁, hs₁, hsV⟩ := Metric.mem_nhds_iff.mp (hcZ.preimage_mem_nhds hV)
    let s := min s₀ s₁
    have hs : 0 < s := lt_min hs₀ hs₁
    have hs0 : Metric.ball x s ⊆ Metric.ball x s₀ := Metric.ball_subset_ball (min_le_left _ _)
    have hs1 : Metric.ball x s ⊆ Metric.ball x s₁ := Metric.ball_subset_ball (min_le_right _ _)
    have hcomp : HolderOnWith (K * ∑ i, C i) G.alpha (g ∘ Z) (Metric.ball x s) := by
      simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using
        hgV.holderOnWith.comp (hZ.mono hs0) (fun z hz => hsV (hs1 hz))
    refine ⟨s, hs, hs0.trans hsub, fun i => ⟨K * ∑ j, C j, ?_⟩⟩
    intro u hu v hv
    have h := (edist_le_pi_edist (g (Z u)) (g (Z v)) i).trans (hcomp u hu v hv)
    simpa only [hrep] using h
  have hcontinuous : ContinuousOn F (Metric.ball y r) := by
    intro x hx
    obtain ⟨s, hs, hsub, hh⟩ := hlocal x hx
    have hc : ContinuousAt (fun z i => F z i) x := by
      apply continuousAt_pi.mpr
      intro i
      obtain ⟨C, hC⟩ := hh i
      exact (hC.continuousOn G.alpha_pos).continuousAt (Metric.ball_mem_nhds x hs)
    exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.continuousAt.comp hc).continuousWithinAt
  have hclosed : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball y r →
      IntegrableOn (fun x => F x 1 * planarGradient φ x 0 -
        F x 0 * planarGradient φ x 1) (Metric.ball y r) ∧
      (∫ x in Metric.ball y r, F x 1 * planarGradient φ x 0 -
        F x 0 * planarGradient φ x 1) = 0 := by
    intro φ hφ hcφ hsφ
    have h := weak.2 φ hφ hcφ hsφ
    have hpoint (x : E2) : F x 1 * planarGradient φ x 0 - F x 0 * planarGradient φ x 1 =
        inner ℝ (matrixAction (normalizedInverse M x) (planarGradient a x)) (planarGradient φ x) -
        (inner ℝ (0 : E2) (planarGradient a x) + (0 : ℝ) * a x) * φ x := by
      simp only [inner_zero_left, zero_mul, zero_add, sub_zero, PiLp.inner_apply,
        Fin.sum_univ_two, RCLike.inner_apply, starRingEnd_apply, star_trivial]
      change (matrixAction (normalizedInverse M x) (planarGradient a x)) 0 * planarGradient φ x 0 -
        -(matrixAction (normalizedInverse M x) (planarGradient a x)) 1 * planarGradient φ x 1 = _
      ring
    simpa only [hpoint] using h
  exact continuous_weak_poincare_ball_original_alpha y r hr G.alpha G.alpha_pos F
    hcontinuous hlocal hclosed

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower
