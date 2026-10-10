import A5OutwardDefiningSign
import A7HalfSpaceSignV464
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- The existing strict normal-sign theorem controls both closed sides and
the exact zero set. -/
theorem strict_normal_derivative_full_sign
    (q : Euc 2 → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : HasStrictFDerivAt q (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) 0)
    (hb : ∀ᶠ z in 𝓝 (0 : Euc 2), z 0 = 0 → q z = 0) :
    ∀ᶠ z in 𝓝 (0 : Euc 2),
      (0 ≤ q z ↔ 0 ≤ z 0) ∧ (q z ≤ 0 ↔ z 0 ≤ 0) ∧ (q z = 0 ↔ z 0 = 0) := by
  have hpos := A7Support.halfspace_sign_of_strict_derivative (by simp) hc hq hb
  let N := -(ContinuousLinearMap.id ℝ (Euc 2))
  have hn : Tendsto (fun z : Euc 2 => -z) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.continuousAt (x := (0 : Euc 2)) |>.tendsto
  have hqN : HasStrictFDerivAt q (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) (N 0) := by
    simpa only [map_zero] using hq
  have hneg : HasStrictFDerivAt (fun z : Euc 2 => -q (-z))
      (c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) 0 := by
    have hh : HasStrictFDerivAt (fun z : Euc 2 => -q (-z))
        (-((c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp N)) 0 :=
      (hqN.comp 0 N.hasStrictFDerivAt).neg
    have hm : -((c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).comp N) =
        c • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) := by
      ext z
      simp [N]
    rwa [hm] at hh
  have hbn : ∀ᶠ z in 𝓝 (0 : Euc 2), z 0 = 0 → -q (-z) = 0 := by
    filter_upwards [hn.eventually hb] with z hz
    intro hz0
    rw [hz (by simp only [PiLp.neg_apply, hz0, neg_zero]), neg_zero]
  have hnp := A7Support.halfspace_sign_of_strict_derivative (by simp) hc hneg hbn
  filter_upwards [hpos, hn.eventually hnp] with z hp hm
  have hnonpos : q z ≤ 0 ↔ z 0 ≤ 0 := by simpa only [neg_neg, PiLp.neg_apply, neg_nonneg] using hm
  exact ⟨hp, hnonpos, by
    constructor
    · intro hz
      exact le_antisymm (hnonpos.mp hz.le) (hp.mp hz.ge)
    · intro hz
      exact le_antisymm (hnonpos.mpr hz.le) (hp.mpr hz.ge)⟩

/-- Two C1 defining functions vanishing along the same regular curve and
having opposite normal derivatives define opposite local sides. The local
straightening map is constructed from the curve and one transverse vector. -/
theorem opposite_defining_functions_local_sides
    (s t : Euc 2 → ℝ) (p v w : Euc 2) (γ : ℝ → Euc 2)
    (hs : ContDiffAt ℝ 1 s p) (ht : ContDiffAt ℝ 1 t p)
    (hγ : ContDiffAt ℝ 1 γ 0) (hγd : HasDerivAt γ v 0)
    (hγ0 : γ 0 = p) (hv : v ≠ 0)
    (hsγ : ∀ᶠ r in 𝓝 (0 : ℝ), s (γ r) = 0)
    (htγ : ∀ᶠ r in 𝓝 (0 : ℝ), t (γ r) = 0)
    (hsw : fderiv ℝ s p w < 0) (htw : 0 < fderiv ℝ t p w) :
    (∀ᶠ z in 𝓝 p,
      (0 ≤ s z ↔ t z ≤ 0) ∧ (s z ≤ 0 ↔ 0 ≤ t z) ∧ (s z = 0 ↔ t z = 0)) ∧
    ∀ I ∈ 𝓝 (0 : ℝ), ∀ᶠ z in 𝓝 p, s z = 0 → ∃ r ∈ I, γ r = z := by
  have hds := (hs.differentiableAt (by norm_num)).hasFDerivAt
  have hdt := (ht.differentiableAt (by norm_num)).hasFDerivAt
  have hds_v : fderiv ℝ s p v = 0 := by
    have hd := hds.comp_hasDerivAt_of_eq 0 hγd hγ0.symm
    have heq : (s ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := hsγ
    exact hd.deriv.symm.trans (heq.deriv_eq.trans (deriv_const 0 0))
  have hdt_v : fderiv ℝ t p v = 0 := by
    have hd := hdt.comp_hasDerivAt_of_eq 0 hγd hγ0.symm
    have heq : (t ∘ γ) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := htγ
    exact hd.deriv.symm.trans (heq.deriv_eq.trans (deriv_const 0 0))
  let π₀ := EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)
  let π₁ := EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  let Φ : Euc 2 → Euc 2 := fun z => γ (z 1) + z 0 • w
  let D := π₁.smulRight v + π₀.smulRight w
  have hΦ0 : Φ 0 = p := by simpa [Φ] using hγ0
  have hΦ : ContDiffAt ℝ 1 Φ 0 := by
    exact (hγ.comp (0 : Euc 2) π₁.contDiff.contDiffAt).add
      (π₀.contDiff.contDiffAt.smul contDiffAt_const)
  have hΦd : HasFDerivAt Φ D 0 := by
    have hγ' : HasFDerivAt (γ ∘ π₁) (π₁.smulRight v) (0 : Euc 2) := by
      have hh := hγd.hasFDerivAt.comp (0 : Euc 2) π₁.hasFDerivAt
      have hm : (ContinuousLinearMap.toSpanSingleton ℝ v).comp π₁ = π₁.smulRight v := by
        ext z
        rfl
      rwa [hm] at hh
    exact hγ'.add (π₀.hasFDerivAt.smul_const w)
  have hDinj : Function.Injective D := by
    apply (injective_iff_map_eq_zero D).mpr
    intro z hz
    have he := congrArg (fderiv ℝ s p) hz
    have he0 : z 0 * fderiv ℝ s p w = 0 := by
      simpa [D, π₀, π₁, map_add, map_smul, hds_v] using he
    have hz0 : z 0 = 0 := (mul_eq_zero.mp he0).resolve_right (ne_of_lt hsw)
    have he1 : z 1 • v = 0 := by simpa [D, π₀, π₁, hz0] using hz
    have hz1 : z 1 = 0 := (smul_eq_zero.mp he1).resolve_right hv
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hDbij : Function.Bijective D := ⟨hDinj, LinearMap.surjective_of_injective hDinj⟩
  let L := ContinuousLinearEquiv.ofBijective D
    (LinearMap.ker_eq_bot.mpr hDbij.injective) (LinearMap.range_eq_top.mpr hDbij.surjective)
  have hΦL : HasFDerivAt Φ (L : Euc 2 →L[ℝ] Euc 2) 0 := hΦd
  let e := hΦ.toOpenPartialHomeomorph Φ hΦL (by norm_num)
  have he0 : (0 : Euc 2) ∈ e.source := hΦ.mem_toOpenPartialHomeomorph_source hΦL (by norm_num)
  have heinv : Tendsto e.symm (𝓝 p) (𝓝 (0 : Euc 2)) := by
    simpa only [show e 0 = p from hΦ0] using e.tendsto_symm he0
  have hrow (A : Euc 2 →L[ℝ] ℝ) (hAv : A v = 0) :
      A.comp D = (A w) • π₀ := by
    ext z
    simp [D, map_smul, hAv, mul_comm]
  have hsΦ : ContDiffAt ℝ 1 (s ∘ Φ) 0 := (hΦ0.symm ▸ hs).comp 0 hΦ
  have htΦ : ContDiffAt ℝ 1 (t ∘ Φ) 0 := (hΦ0.symm ▸ ht).comp 0 hΦ
  have hsd : HasFDerivAt (s ∘ Φ) ((fderiv ℝ s p w) • π₀) 0 := by
    have hd := (hΦ0.symm ▸ hds).comp 0 hΦd
    rwa [hΦ0, hrow _ hds_v] at hd
  have htd : HasFDerivAt (t ∘ Φ) ((fderiv ℝ t p w) • π₀) 0 := by
    have hd := (hΦ0.symm ▸ hdt).comp 0 hΦd
    rwa [hΦ0, hrow _ hdt_v] at hd
  have hsdn : HasFDerivAt (fun z => -s (Φ z)) ((-fderiv ℝ s p w) • π₀) 0 := by
    change HasFDerivAt (-s ∘ Φ) ((-fderiv ℝ s p w) • π₀) 0
    rw [neg_smul]
    exact hsd.neg
  have hbS : ∀ᶠ z in 𝓝 (0 : Euc 2), z 0 = 0 → -s (Φ z) = 0 := by
    filter_upwards [π₁.continuous.continuousAt.tendsto.eventually hsγ] with z hz
    intro hz0
    change s (γ (z 1)) = 0 at hz
    simp [Φ, hz0, hz]
  have hbT : ∀ᶠ z in 𝓝 (0 : Euc 2), z 0 = 0 → t (Φ z) = 0 := by
    filter_upwards [π₁.continuous.continuousAt.tendsto.eventually htγ] with z hz
    intro hz0
    change t (γ (z 1)) = 0 at hz
    simp [Φ, hz0, hz]
  have hsides := strict_normal_derivative_full_sign (fun z => -s (Φ z)) (-fderiv ℝ s p w)
    (neg_pos.mpr hsw) (hsΦ.neg.hasStrictFDerivAt' hsdn (by norm_num)) hbS
  have htides := strict_normal_derivative_full_sign (t ∘ Φ) (fderiv ℝ t p w)
    htw (htΦ.hasStrictFDerivAt' htd (by norm_num)) hbT
  have hres : ∀ᶠ z in 𝓝 (0 : Euc 2),
      (0 ≤ s (Φ z) ↔ t (Φ z) ≤ 0) ∧ (s (Φ z) ≤ 0 ↔ 0 ≤ t (Φ z)) ∧
      (s (Φ z) = 0 ↔ t (Φ z) = 0) := by
    filter_upwards [hsides, htides] with z hz ht'
    dsimp only [Function.comp_apply] at ht'
    exact ⟨(by simpa only [neg_nonpos] using hz.2.1.trans ht'.2.1.symm),
      (by simpa only [neg_nonneg] using hz.1.trans ht'.1.symm),
      (by simpa only [neg_eq_zero] using hz.2.2.trans ht'.2.2.symm)⟩
  have hright : ∀ᶠ z in 𝓝 p, Φ (e.symm z) = z := by
    have hr := e.eventually_right_inverse' he0
    change ∀ᶠ z in 𝓝 (Φ 0), Φ (e.symm z) = z at hr
    rwa [hΦ0] at hr
  constructor
  · filter_upwards [heinv.eventually hres, hright] with z hz hez
    rwa [hez] at hz
  · intro I hI
    have htang : Tendsto (fun z => π₁ (e.symm z)) (𝓝 p) (𝓝 (0 : ℝ)) :=
      π₁.continuous.continuousAt.tendsto.comp heinv
    filter_upwards [heinv.eventually hsides, hright, htang.eventually hI] with z hz hez hzI
    intro hzS
    have hn : (e.symm z) 0 = 0 := hz.2.2.mp (by rw [hez, hzS, neg_zero])
    refine ⟨π₁ (e.symm z), hzI, ?_⟩
    dsimp only [Φ] at hez
    rw [hn, zero_smul, add_zero] at hez
    exact hez

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
