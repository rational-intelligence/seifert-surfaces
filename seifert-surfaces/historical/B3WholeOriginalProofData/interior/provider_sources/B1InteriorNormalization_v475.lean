import B1InteriorLocalPositive_v475
import B1ChartMetricProvider
noncomputable section
open Set Topology Function MeasureTheory
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Internal literal data for dividing two classical solutions.  Its positive
solution is constructed by native_local_positive_classical_v475. -/
structure InteriorNormalizationData_v475 where
  O : Set E2
  isOpen_O : IsOpen O
  a : E2 → Mat2
  b : E2 → E2
  c : E2 → ℝ
  u : E2 → ℝ
  h : E2 → ℝ
  elliptic : SmoothEllipticOn a b c O
  smooth_u : ContDiffOn ℝ ∞ u O
  smooth_h : ContDiffOn ℝ ∞ h O
  h_positive : ∀ x ∈ O, 0 < h x
  u_classical : ∀ x ∈ O, classicalL a b c u x = 0
  h_classical : ∀ x ∈ O, classicalL a b c h x = 0

namespace InteriorNormalizationData_v475
def v (N : InteriorNormalizationData_v475) (x : E2) : ℝ := N.u x/N.h x
def leading (N : InteriorNormalizationData_v475) (x : E2) : Mat2 := N.h x • N.a x
def drift (N : InteriorNormalizationData_v475) (x : E2) : E2 :=
  matrixAction (N.a x) (planarGradient N.h x)+N.h x • N.b x
def factor (N : InteriorNormalizationData_v475) (x : E2) : ℝ :=
  (Real.sqrt (Matrix.det (N.leading x)))⁻¹
def normalizedA (N : InteriorNormalizationData_v475) (x : E2) : Mat2 :=
  N.factor x • N.leading x
def normalizedB (N : InteriorNormalizationData_v475) (x : E2) : E2 :=
  N.factor x • N.drift x-matrixAction (N.leading x) (planarGradient N.factor x)
end InteriorNormalizationData_v475

/-- All normalized coefficients are derived from the literal smooth data;
the determinant factor includes the induced drift correction. -/
theorem native_interior_normalized_coefficients_v475
    (N : InteriorNormalizationData_v475)
    (H : Set E2) (hcompact : IsCompact H) (hconvex : Convex ℝ H)
    (hnonempty : H.Nonempty) (hHO : H ⊆ N.O) :
    SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0) H ∧
    (∀ i j, LipschitzBoundOn (fun x => N.normalizedA x i j) H) ∧
    BoundedOn N.normalizedB H ∧
    (∀ x ∈ H, Matrix.det (N.normalizedA x) = 1) ∧
    (∀ x ∈ H, ContDiffAt ℝ ∞ N.factor x) := by
  classical
  obtain ⟨ha,hb,hc,hsym,ell,C,hell,hC,hbounds⟩ := N.elliptic
  have hO := N.isOpen_O
  have hapos (x : E2) (hx : x ∈ H) : 0 < Matrix.det (N.a x) := by
    have hM : (N.a x).PosDef := by
      apply Matrix.posDef_iff_dotProduct_mulVec.mpr
      constructor
      · rw [Matrix.isHermitian_iff_isSymm]
        ext i j
        exact hsym x (hHO hx) j i
      · intro q hq
        let p : E2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm q
        have hp : p ≠ 0 := by
          intro hp
          apply hq
          simpa [p] using congrArg (EuclideanSpace.equiv (Fin 2) ℝ) hp
        have hpos : 0 < inner ℝ p (matrixAction (N.a x) p) :=
          lt_of_lt_of_le (mul_pos hell (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hp)))
            (hbounds x (hHO hx) p).1
        simpa [p, matrixAction, EuclideanSpace.inner_eq_star_dotProduct,
          Matrix.vecHead, Matrix.vecTail, mul_comm] using hpos
    exact hM.det_pos
  have hhpos (x : E2) (hx : x ∈ H) : 0 < N.h x := by
    exact N.h_positive x (hHO hx)
  have hh : ContDiffOn ℝ ∞ N.h H := N.smooth_h.mono hHO
  have hlead (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => N.leading x i j) H := by
    exact hh.mul ((ha i j).mono (hHO))
  have hleadpos (x : E2) (hx : x ∈ H) : 0 < Matrix.det (N.leading x) := by
    change 0 < Matrix.det (N.h x • N.a x)
    rw [Matrix.det_smul]
    change 0 < N.h x ^ 2 * Matrix.det (N.a x)
    exact mul_pos (sq_pos_of_pos (hhpos x hx)) (hapos x hx)
  have hdetsmooth : ContDiffOn ℝ ∞ (fun x => Matrix.det (N.leading x)) H := by
    simp only [Matrix.det_fin_two]
    exact ((hlead 0 0).mul (hlead 1 1)).sub ((hlead 0 1).mul (hlead 1 0))
  have hfactor : ContDiffOn ℝ ∞ N.factor H := by
    exact (hdetsmooth.sqrt (fun x hx => (hleadpos x hx).ne')).inv
      (fun x hx => (Real.sqrt_pos.2 (hleadpos x hx)).ne')
  have hfpos (x : E2) (hx : x ∈ H) : 0 < N.factor x :=
    inv_pos.mpr (Real.sqrt_pos.2 (hleadpos x hx))
  have hnormsmooth (i j : Fin 2) : ContDiffOn ℝ ∞ (fun x => N.normalizedA x i j) H :=
    hfactor.mul (hlead i j)
  let t : E2 → ℝ := fun x => N.factor x * N.h x
  have ht : ContinuousOn t H := (hfactor.mul hh).continuousOn
  have htpos (x : E2) (hx : x ∈ H) : 0 < t x := mul_pos (hfpos x hx) (hhpos x hx)
  obtain ⟨xmin, hxmin, hmin⟩ := hcompact.exists_isMinOn hnonempty ht
  obtain ⟨xmax, hxmax, hmax⟩ := hcompact.exists_isMaxOn hnonempty ht
  have hquad (x p : E2) :
      inner ℝ p (matrixAction (N.normalizedA x) p) = t x * inner ℝ p (matrixAction (N.a x) p) := by
    have hact : matrixAction (N.normalizedA x) p = t x • matrixAction (N.a x) p := by
      apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
      funext i
      delta matrixAction InteriorNormalizationData_v475.normalizedA InteriorNormalizationData_v475.leading
      simp only [Matrix.smul_apply, smul_eq_mul,
        Fin.sum_univ_two, map_smul, ContinuousLinearEquiv.apply_symm_apply, Pi.smul_apply, t]
      ring
    rw [hact, inner_smul_right]
  have hnSym : SymmetricOn N.normalizedA H := by
    intro x hx i j
    change N.factor x * (N.h x * N.a x i j) = N.factor x * (N.h x * N.a x j i)
    rw [hsym x (hHO hx) i j]
  have hnEll : UniformEllipticOn N.normalizedA H := by
    refine ⟨t xmin * ell, t xmax * C, mul_pos (htpos xmin hxmin) hell,
      mul_pos (htpos xmax hxmax) hC, ?_⟩
    intro x hx p
    rw [hquad]
    constructor
    · calc
        t xmin * ell * ‖p‖ ^ 2 = t xmin * (ell * ‖p‖ ^ 2) := by ring
        _ ≤ t x * (ell * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right (hmin hx) (by positivity)
        _ ≤ t x * inner ℝ p (matrixAction (N.a x) p) :=
          mul_le_mul_of_nonneg_left (hbounds x (hHO hx) p).1 (htpos x hx).le
    · calc
        t x * inner ℝ p (matrixAction (N.a x) p) ≤ t x * (C * ‖p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbounds x (hHO hx) p).2 (htpos x hx).le
        _ ≤ t xmax * (C * ‖p‖ ^ 2) := mul_le_mul_of_nonneg_right (hmax hx) (by positivity)
        _ = t xmax * C * ‖p‖ ^ 2 := by ring
  have hnLip : ∀ i j, LipschitzBoundOn (fun x => N.normalizedA x i j) H := by
    intro i j
    obtain ⟨L, hL⟩ := (hnormsmooth i j).exists_lipschitzOnWith (by simp) hconvex hcompact
    exact ⟨L, L.coe_nonneg, fun x hx y hy => hL.dist_le_mul x hx y hy⟩
  have hnDet : ∀ x ∈ H, Matrix.det (N.normalizedA x) = 1 := by
    intro x hx
    change Matrix.det (N.factor x • N.leading x) = 1
    rw [Matrix.det_smul]
    change ((Real.sqrt (Matrix.det (N.leading x)))⁻¹) ^ 2 * Matrix.det (N.leading x) = 1
    rw [inv_pow, Real.sq_sqrt (hleadpos x hx).le]
    exact inv_mul_cancel₀ (hleadpos x hx).ne'
  have hhAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.h x :=
    (N.smooth_h x (hHO hx)).contDiffAt (hO.mem_nhds (hHO hx))
  have haAt (i j : Fin 2) (x : E2) (hx : x ∈ H) :
      ContDiffAt ℝ ∞ (fun y => N.a y i j) x :=
    (ha i j x (hHO hx)).contDiffAt (hO.mem_nhds (hHO hx))
  have hleadAt (i j : Fin 2) (x : E2) (hx : x ∈ H) :
      ContDiffAt ℝ ∞ (fun y => N.leading y i j) x :=
    (hhAt x hx).mul (haAt i j x hx)
  have hfactorAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.factor x := by
    have hd : ContDiffAt ℝ ∞ (fun y => Matrix.det (N.leading y)) x := by
      simp only [Matrix.det_fin_two]
      exact ((hleadAt 0 0 x hx).mul (hleadAt 1 1 x hx)).sub
        ((hleadAt 0 1 x hx).mul (hleadAt 1 0 x hx))
    exact (hd.sqrt (hleadpos x hx).ne').inv (Real.sqrt_pos.2 (hleadpos x hx)).ne'
  have hgradient (f : E2 → ℝ) (x : E2) (hf : ContDiffAt ℝ ∞ f x) :
      ContDiffAt ℝ ∞ (planarGradient f) x := by
    delta planarGradient
    apply ContDiffAt.sum
    intro i hi
    exact ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).smul contDiffAt_const
  have haction (a : E2 → Mat2) (p : E2 → E2) (x : E2)
      (ha : ∀ i j, ContDiffAt ℝ ∞ (fun y => a y i j) x)
      (hp : ContDiffAt ℝ ∞ p x) : ContDiffAt ℝ ∞ (fun y => matrixAction (a y) (p y)) x := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.contDiff.contDiffAt.comp
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro j hj
    exact (ha i j).mul ((EuclideanSpace.proj (𝕜 := ℝ) (j : Fin 2)).contDiff.contDiffAt.comp x hp)
  have hdriftAt (x : E2) (hx : x ∈ H) : ContDiffAt ℝ ∞ N.drift x := by
    exact (haction N.a (planarGradient N.h) x (fun i j => haAt i j x hx)
      (hgradient N.h x (hhAt x hx))).add
      ((hhAt x hx).smul ((hb x (hHO hx)).contDiffAt (hO.mem_nhds (hHO hx))))
  have hnormb : ContDiffOn ℝ ∞ N.normalizedB H := by
    intro x hx
    exact (((hfactorAt x hx).smul (hdriftAt x hx)).sub
      (haction N.leading (planarGradient N.factor) x (fun i j => hleadAt i j x hx)
        (hgradient N.factor x (hfactorAt x hx)))).contDiffWithinAt
  have hsmooth : SmoothEllipticOn N.normalizedA N.normalizedB (fun _ => 0) H :=
    ⟨hnormsmooth, hnormb, contDiffOn_const, hnSym, hnEll⟩
  obtain ⟨Cb,hCb⟩ := hcompact.exists_bound_of_continuousOn hnormb.continuousOn
  have hbb : BoundedOn N.normalizedB H :=
    ⟨max Cb 0, le_max_right _ _, fun x hx => (hCb x hx).trans (le_max_left _ _)⟩
  exact ⟨hsmooth,hnLip,hbb,hnDet,hfactorAt⟩

#print axioms native_interior_normalized_coefficients_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
