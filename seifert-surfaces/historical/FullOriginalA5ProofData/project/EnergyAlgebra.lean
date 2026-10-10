import WeakTestExtension

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology BigOperators ContDiff
namespace SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.QuasilinearLocalization

set_option maxHeartbeats 800000 in
theorem cutoff_pointwise_energy
    (a : E2 →L[ℝ] E2) (c d X Y : E2) (b : E2 →L[ℝ] ℝ) (q f t e κ M D : ℝ)
    (hκ : 0 < κ) (hM : 0 ≤ M) (hD : 0 ≤ D) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hell : κ * ‖X‖ ^ 2 ≤ inner ℝ (a X) X)
    (ha : ‖a‖ ≤ M) (hc : ‖c‖ ≤ M) (hd : ‖d‖ ≤ M)
    (hb : ‖b‖ ≤ M) (hq : |q| ≤ M) (hf : |f| ≤ M) (hY : ‖Y‖ ≤ D) :
    (κ / 2) * (e ^ 2 * ‖X‖ ^ 2) ≤
      inner ℝ (a X + t • c + d) (e ^ 2 • X + (2 * e * t) • Y) -
        (b X + q * t + f) * (e ^ 2 * t) +
      ((2 * M * (D + 1)) ^ 2 / κ + 4 * M * (D + 1)) * (t ^ 2 + 1) := by
  let w := e * ‖X‖
  let z := |t| + 1
  let A := 2 * M * (D + 1)
  have hw : 0 ≤ w := mul_nonneg he0 (norm_nonneg _)
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he2 : e ^ 2 ≤ e := by nlinarith
  have he2' : e ^ 2 ≤ 1 := he2.trans he1
  have ht : |t| ≤ z := by dsimp [z]; linarith
  have hnorma : ‖a X‖ ≤ M * ‖X‖ :=
    (a.le_opNorm X).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hnormb : |b X| ≤ M * ‖X‖ :=
    (b.le_opNorm X).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hnormcd : ‖t • c + d‖ ≤ M * z := by
    calc
      _ ≤ ‖t • c‖ + ‖d‖ := norm_add_le _ _
      _ = |t| * ‖c‖ + ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |t| * M + M := add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) hd
      _ = M * z := by dsimp [z]; ring
  have hnormqf : |q * t + f| ≤ M * z := by
    calc
      _ ≤ |q * t| + |f| := abs_add_le _ _
      _ ≤ M * |t| + M := by rw [abs_mul]; gcongr
      _ = _ := by dsimp [z]; ring
  have hx1 : |inner ℝ (a X) ((2 * e * t) • Y)| ≤ 2 * M * D * w * z := by
    calc
      _ ≤ ‖a X‖ * ‖(2 * e * t) • Y‖ := abs_real_inner_le_norm _ _
      _ = ‖a X‖ * (2 * e * |t| * ‖Y‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg he0]
        norm_num
      _ ≤ (M * ‖X‖) * (2 * e * z * D) := by gcongr
      _ = _ := by dsimp [w]; ring
  have hx2 : |inner ℝ (t • c + d) (e ^ 2 • X)| ≤ M * w * z := by
    calc
      _ ≤ ‖t • c + d‖ * ‖e ^ 2 • X‖ := abs_real_inner_le_norm _ _
      _ = ‖t • c + d‖ * (e ^ 2 * ‖X‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ (M * z) * (e * ‖X‖) := by gcongr
      _ = _ := by dsimp [w]; ring
  have hx3 : |inner ℝ (t • c + d) ((2 * e * t) • Y)| ≤ 2 * M * D * z ^ 2 := by
    calc
      _ ≤ ‖t • c + d‖ * ‖(2 * e * t) • Y‖ := abs_real_inner_le_norm _ _
      _ = ‖t • c + d‖ * (2 * e * |t| * ‖Y‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg he0]
        norm_num
      _ ≤ (M * z) * (2 * 1 * z * D) := by gcongr
      _ = _ := by ring
  have hx4 : |b X * (e ^ 2 * t)| ≤ M * w * z := by
    calc
      _ = |b X| * (e ^ 2 * |t|) := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg e)]
      _ ≤ (M * ‖X‖) * (e * z) := by gcongr
      _ = _ := by dsimp [w]; ring
  have hx5 : |(q * t + f) * (e ^ 2 * t)| ≤ M * z ^ 2 := by
    calc
      _ = |q * t + f| * (e ^ 2 * |t|) := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg e)]
      _ ≤ (M * z) * (1 * z) := by gcongr
      _ = _ := by ring
  have hcoerc : κ * w ^ 2 ≤ e ^ 2 * inner ℝ (a X) X := by
    have hh := mul_le_mul_of_nonneg_left hell (sq_nonneg e)
    dsimp [w]
    nlinarith
  have hraw : κ * w ^ 2 ≤
      inner ℝ (a X + t • c + d) (e ^ 2 • X + (2 * e * t) • Y) -
      (b X + q * t + f) * (e ^ 2 * t) + A * w * z + A * z ^ 2 := by
    rw [add_assoc (a X), inner_add_left, inner_add_right, inner_add_right, real_inner_smul_right]
    have h1 := (abs_le.mp hx1).1
    have h2 := (abs_le.mp hx2).1
    have h3 := (abs_le.mp hx3).1
    have h4 := (abs_le.mp hx4).2
    have h5 := (abs_le.mp hx5).2
    have hMzz : 0 ≤ M * z ^ 2 := mul_nonneg hM (sq_nonneg _)
    dsimp [A]
    nlinarith
  have hyoung : A * w * z ≤ κ / 2 * w ^ 2 + (A ^ 2 / (2 * κ)) * z ^ 2 := by
    have hsq := sq_nonneg (κ * w - A * z)
    have hid : κ / 2 * w ^ 2 + (A ^ 2 / (2 * κ)) * z ^ 2 - A * w * z =
        (κ * w - A * z) ^ 2 / (2 * κ) := by
      field_simp
      <;> ring
    have hn := div_nonneg hsq (show 0 ≤ 2 * κ by positivity)
    linarith only [hid, hn]
  have hz2 : z ^ 2 ≤ 2 * (t ^ 2 + 1) := by
    have ht2 := sq_abs t
    have hsq := sq_nonneg (|t| - 1)
    dsimp [z]
    nlinarith
  have hK : 0 ≤ A ^ 2 / (2 * κ) + A := by positivity
  have hlast := mul_le_mul_of_nonneg_left hz2 hK
  have hid : (A ^ 2 / (2 * κ) + A) * (2 * (t ^ 2 + 1)) =
      (A ^ 2 / κ + 2 * A) * (t ^ 2 + 1) := by ring
  rw [hid] at hlast
  have hh : κ / 2 * w ^ 2 ≤
      inner ℝ (a X + t • c + d) (e ^ 2 • X + (2 * e * t) • Y) -
      (b X + q * t + f) * (e ^ 2 * t) + (A ^ 2 / κ + 2 * A) * (t ^ 2 + 1) := by
    nlinarith only [hraw, hyoung, hlast]
  dsimp [w, A] at hh
  convert hh using 1 <;> ring

end SeifertSurfaces.QuasilinearProviderBridge.EnergyHelpers
