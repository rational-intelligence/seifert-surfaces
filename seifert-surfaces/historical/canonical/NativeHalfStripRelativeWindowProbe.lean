import NativeHalfStripPackageProbe
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

/-! A local reverse containment for the actual straight halfstrip.  The
halfplane germ is supplied by the sector template's native boundary field. -/
theorem native_halfstrip_relative_frame_window_from_halfplane
    (A : SectorModel) (origin e m : Euc 2) (clock : ℝ → ℝ)
    (H : ℝ) (hH : 0 < H)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo (-1:ℝ) 1))
    (hr : ∀ t ∈ Ioo (-1:ℝ) 1, deriv clock t ≠ 0)
    (hmap : MapsTo (fun z : ℝ × ℝ => origin + clock z.1 • e + z.2 • m)
       (Ioo (-1:ℝ) 1 ×ˢ Ico 0 H) A.domain)
    (hboundary : ∀ t ∈ Ioo (-1:ℝ) 1,
       origin + clock t • e ∈ A.domain ∩ frontier A.domain)
    (hside : ∀ t ∈ Ioo (-1:ℝ) 1,
      ∀ᶠ z in 𝓝 (origin + clock t • e),
        z ∈ A.domain ↔ 0 ≤ inner ℝ m (z - (origin + clock t • e)))
    (t0 : ℝ) (ht0 : t0 ∈ Ioo (-1:ℝ) 1) :
    ∃ W : Set (Euc 2), IsOpen W ∧ origin + clock t0 • e ∈ W ∧
      ∀ y ∈ A.domain ∩ W,
        ∃ u v : ℝ, u ∈ Ioo (-1:ℝ) 1 ∧ v ∈ Ico 0 H ∧
          y = origin + clock u • e + v • m := by
  let hc := (hclock t0 ht0).contDiffAt (isOpen_Ioo.mem_nhds ht0)
  have hd := (hc.hasStrictDerivAt (by norm_num)).hasStrictFDerivAt_equiv (hr t0 ht0)
  let R0 : OpenPartialHomeomorph ℝ ℝ := hd.toOpenPartialHomeomorph clock
  let R := R0.restr (Ioo (-1 : ℝ) 1)
  have htR : t0 ∈ R.source := by
    rw [show R.source = R0.source ∩ Ioo (-1 : ℝ) 1 from R0.restr_source' _ isOpen_Ioo]
    exact ⟨hd.mem_toOpenPartialHomeomorph_source, ht0⟩
  have hclockR : clock t0 ∈ R.target := by
    exact R.map_source htR
  let D := seamFrameMap e m
  have hbij := seamFrameMap_bijective e m he hm hem
  let L : (ℝ × ℝ) ≃L[ℝ] Euc 2 := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  let B : (ℝ × ℝ) ≃ₜ Euc 2 := L.toHomeomorph.trans (Homeomorph.addLeft origin)
  have hB_apply (z : ℝ × ℝ) : B z = origin + z.1 • e + z.2 • m := by
    change origin + D z = _
    rw [seamFrameMap_apply]
    exact (add_assoc origin (z.1 • e) (z.2 • m)).symm
  obtain ⟨N, hNside, hN, hN0⟩ := mem_nhds_iff.mp (hside t0 ht0)
  let Q : Set (ℝ × ℝ) :=
    (R.target ×ˢ Ioo (-H / 2) (H / 2)) ∩ B ⁻¹' N
  let W : Set (Euc 2) := B '' Q
  have hQopen : IsOpen Q :=
    (R.open_target.prod isOpen_Ioo).inter ((B.isOpen_preimage).mpr hN)
  have hWopen : IsOpen W := B.isOpenMap Q hQopen
  have hQ0 : (clock t0, 0) ∈ Q := by
    refine ⟨⟨hclockR, by constructor <;> linarith⟩, ?_⟩
    rw [mem_preimage]
    simpa only [hB_apply, zero_smul, add_zero] using hN0
  have hyW : origin + clock t0 • e ∈ W := by
    refine ⟨(clock t0, 0), hQ0, ?_⟩
    simp only [hB_apply, zero_smul, add_zero]
  refine ⟨W, hWopen, hyW, ?_⟩
  rintro y ⟨hyA, hyW'⟩
  obtain ⟨z, hzQ, rfl⟩ := hyW'
  have hzN : B z ∈ N := hzQ.2
  have hzside := (hNside hzN).mp hyA
  have hzvert : 0 ≤ z.2 := by
    have hcoord : inner ℝ m (B z - (origin + clock t0 • e)) = z.2 := by
      rw [hB_apply]
      rw [real_inner_comm] at hem
      simp only [inner_sub_right, inner_add_right, inner_smul_right,
        real_inner_self_eq_norm_sq, hm, one_pow, mul_one, hem, mul_zero]
      ring
    rw [hcoord] at hzside
    exact hzside
  refine ⟨(R.symm z.1), z.2, ?_, ?_, ?_⟩
  · have hsrc := R.map_target hzQ.1.1
    rw [show R.source = R0.source ∩ Ioo (-1 : ℝ) 1 from R0.restr_source' _ isOpen_Ioo] at hsrc
    exact hsrc.2
  · constructor
    · exact hzvert
    · have hzlt : z.2 < H / 2 := hzQ.1.2.2
      linarith
  · have hclock : clock (R.symm z.1) = z.1 := R.right_inv hzQ.1.1
    rw [hB_apply, hclock]

/-- The forward native halfstrip and regular boundary clock determine the
same inward halfplane as the actual sector domain, including a pi apex. -/
theorem native_halfstrip_boundary_halfplane
    (A : SectorModel) (origin e m : Euc 2) (clock : ℝ → ℝ)
    (H : ℝ) (hH : 0 < H)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo (-1:ℝ) 1))
    (hr : ∀ t ∈ Ioo (-1:ℝ) 1, deriv clock t ≠ 0)
    (hmap : MapsTo (fun z : ℝ × ℝ => origin + clock z.1 • e + z.2 • m)
       (Ioo (-1:ℝ) 1 ×ˢ Ico 0 H) A.domain)
    (hboundary : ∀ t ∈ Ioo (-1:ℝ) 1,
       origin + clock t • e ∈ A.domain ∩ frontier A.domain)
    (t0 : ℝ) (ht0 : t0 ∈ Ioo (-1:ℝ) 1) :
    ∀ᶠ z in 𝓝 (origin + clock t0 • e),
      z ∈ A.domain ↔ 0 ≤ inner ℝ m (z - (origin + clock t0 • e)) := by
  let x := origin + clock t0 • e
  let q : ℝ → Euc 2 := fun t => origin + clock (t0 + t) • e
  have hqc := (hclock t0 ht0).contDiffAt (isOpen_Ioo.mem_nhds ht0)
  have hq : HasDerivAt q (deriv clock t0 • e) 0 := by
    have hadd : HasDerivAt (fun t : ℝ => t0 + t) 1 0 :=
      (hasDerivAt_id 0).const_add t0
    have hcd : HasDerivAt clock (deriv clock t0) (t0 + (0 : ℝ)) := by
      simpa only [add_zero] using (hqc.differentiableAt (by norm_num)).hasDerivAt
    convert! ((hcd.comp 0 hadd).smul_const e).const_add origin using 1 <;>
      simp [q, Function.comp_def]
  have hqx : q 0 = x := by simp [q, x]
  have hv : deriv clock t0 • e ≠ 0 := by
    exact smul_ne_zero (hr t0 ht0) (by intro h; rw [h, norm_zero] at he; norm_num at he)
  have hqb : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ A.domain ∩ frontier A.domain := by
    have ht : ∀ᶠ t in 𝓝 (0 : ℝ), t0 + t ∈ Ioo (-1 : ℝ) 1 :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (isOpen_Ioo.mem_nhds (by simpa using ht0))
    filter_upwards [ht] with t ht
    exact hboundary _ ht
  have hxregular : x ≠ 0 ∨ A.angle = Real.pi := by
    by_cases hx0 : x = 0
    · exact Or.inr (regular_curve_in_sector_frontier_forces_pi A q _
        (hqx.trans hx0) hq hv hqb).2
    · exact Or.inl hx0
  obtain ⟨e0, n, he0, hn, he0n, hnx, hnside⟩ :=
    native_sector_orthonormal_boundary_frame A x (hboundary t0 ht0) hxregular
  have hnvel := defining_derivative_zero_on_boundary_curve A.domain (innerSL ℝ n)
    x (deriv clock t0 • e) q hqx hq (innerSL ℝ n).contDiff.contDiffAt hnside hqb
  have hne : inner ℝ n e = 0 := by
    have hs : fderiv ℝ (innerSL ℝ n) x = innerSL ℝ n := (innerSL ℝ n).hasFDerivAt.fderiv
    rw [hs] at hnvel
    change inner ℝ n (deriv clock t0 • e) = 0 at hnvel
    rw [inner_smul_right] at hnvel
    exact (mul_eq_zero.mp hnvel).resolve_left (hr t0 ht0)
  have hen : inner ℝ e n = 0 := by rw [real_inner_comm]; exact hne
  let a : ℝ := inner ℝ m n
  have hna : n = a • m := by
    have hrec := seamFrame_reconstruction e m n he hm hem
    simpa only [hen, zero_smul, zero_add] using hrec
  obtain ⟨ε, hε, hεside⟩ := Metric.mem_nhds_iff.mp hnside
  let b := min ε H / 2
  have hb : 0 < b := half_pos (lt_min hε hH)
  have hbε : b < ε := by dsimp [b]; linarith [min_le_left ε H]
  have hbH : b < H := by dsimp [b]; linarith [min_le_right ε H]
  have hbball : x + b • m ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hm,
      mul_one, Real.norm_eq_abs, abs_of_pos hb]
    exact hbε
  have hzA : x + b • m ∈ A.domain := hmap (x := (t0, b)) ⟨ht0, hb.le, hbH⟩
  have hab : 0 ≤ b * a := by
    have hnonneg := (hεside hbball).mp hzA
    rw [inner_add_right, hnx, inner_smul_right, zero_add, real_inner_comm m n] at hnonneg
    exact hnonneg
  have ha : 0 ≤ a := (mul_nonneg_iff_of_pos_left hb).mp hab
  have habs : |a| = 1 := by
    rw [hna, norm_smul, hm, mul_one, Real.norm_eq_abs] at hn
    exact hn
  have ha1 : a = 1 := by rwa [abs_of_nonneg ha] at habs
  have hnm : n = m := by simpa [ha1] using hna
  rw [hnm] at hnside hnx
  filter_upwards [hnside] with z hz
  change z ∈ A.domain ↔ 0 ≤ inner ℝ m (z - x)
  simpa only [inner_sub_right, hnx, sub_zero] using hz

/-- Exact reverse relative containment in the same straight frame and
original clock, derived only from the forward native hypotheses. -/
theorem native_halfstrip_relative_frame_window
    (A : SectorModel) (origin e m : Euc 2) (clock : ℝ → ℝ)
    (H : ℝ) (hH : 0 < H)
    (he : ‖e‖ = 1) (hm : ‖m‖ = 1) (hem : inner ℝ e m = 0)
    (hclock : ContDiffOn ℝ 1 clock (Ioo (-1:ℝ) 1))
    (hr : ∀ t ∈ Ioo (-1:ℝ) 1, deriv clock t ≠ 0)
    (hmap : MapsTo (fun z : ℝ × ℝ => origin + clock z.1 • e + z.2 • m)
       (Ioo (-1:ℝ) 1 ×ˢ Ico 0 H) A.domain)
    (hboundary : ∀ t ∈ Ioo (-1:ℝ) 1,
       origin + clock t • e ∈ A.domain ∩ frontier A.domain)
    (t0 : ℝ) (ht0 : t0 ∈ Ioo (-1:ℝ) 1) :
    ∃ W : Set (Euc 2), IsOpen W ∧ origin + clock t0 • e ∈ W ∧
      ∀ y ∈ A.domain ∩ W,
        ∃ u v : ℝ, u ∈ Ioo (-1:ℝ) 1 ∧ v ∈ Ico 0 H ∧
          y = origin + clock u • e + v • m := by
  exact native_halfstrip_relative_frame_window_from_halfplane A origin e m clock H hH
    he hm hem hclock hr hmap hboundary
    (native_halfstrip_boundary_halfplane A origin e m clock H hH he hm hem hclock hr hmap hboundary)
    t0 ht0

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
