import A5OppositeSides
import A5SectorProjectedInverse

set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Two actual C1 sector sheets with opposite outward tangent vectors have
no new projected collisions near a regular common seam. Every collision
represents the same original ambient point. -/
theorem two_sector_projection_collisions_are_same_point
    (A : Fin 2 → SectorModel) (G : Fin 2 → Euc 2 → Euc 3)
    (q : Fin 2 → ℝ → Euc 2) (v n : Fin 2 → Euc 2) (γ : ℝ → Euc 3)
    (hq : ∀ k, HasDerivAt (q k) (v k) 0)
    (hboundary : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), q k t ∈ (A k).domain ∩ frontier (A k).domain)
    (himage : ∀ k, ∀ᶠ t in 𝓝 (0 : ℝ), G k (q k t) = γ t)
    (hregular : ∀ k, q k 0 ≠ 0 ∨ (A k).angle = Real.pi)
    (hG : ∀ k, ContDiffWithinAt ℝ 1 (G k) (A k).domain (q k 0))
    (hframe : ∀ k, LinearIndependent ℝ (![v k, n k] : Fin 2 → Euc 2))
    (hinward : ∀ k, ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε,
      q k 0 - b • n k ∈ (A k).domain)
    (hbalance : (fderivWithin ℝ (G 0) (A 0).domain (q 0 0)) (n 0) +
      (fderivWithin ℝ (G 1) (A 1).domain (q 1 0)) (n 1) = 0)
    (P : Euc 3 →L[ℝ] Euc 2)
    (hP : ∀ k, Function.Bijective (P.comp (fderivWithin ℝ (G k) (A k).domain (q k 0))))
    (hcurve : ContDiffAt ℝ 1 (P ∘ γ) 0) (hvelocity : deriv (P ∘ γ) 0 ≠ 0) :
    ∃ r : Fin 2 → ℝ, (∀ k, 0 < r k) ∧
      ∀ y₀ ∈ Metric.ball (q 0 0) (r 0) ∩ (A 0).domain,
      ∀ y₁ ∈ Metric.ball (q 1 0) (r 1) ∩ (A 1).domain,
        P (G 0 y₀) = P (G 1 y₁) → G 0 y₀ = G 1 y₁ := by
  classical
  let x : Fin 2 → Euc 2 := fun k => q k 0
  let D : Fin 2 → Euc 2 →L[ℝ] Euc 3 := fun k => fderivWithin ℝ (G k) (A k).domain (x k)
  let p := P (γ 0)
  have hx (k : Fin 2) : x k ∈ (A k).domain ∩ frontier (A k).domain :=
    (hboundary k).self_of_nhds
  have hGx (k : Fin 2) : G k (x k) = γ 0 := (himage k).self_of_nhds
  choose s hs hs0 hsurj hside using fun k =>
    regular_sector_boundary_defining_function (A k) (x k) (hx k) (hregular k)
  choose e hes hep heq hec heic heder heinv using fun k =>
    C1_sector_projected_local_diffeomorphism (A k) (G k) (x k) (hx k).1 (hregular k) (hG k) P (hP k)
  have hep' (k : Fin 2) : e k (x k) = p := (hep k).trans (congrArg P (hGx k))
  have heinverse (k : Fin 2) : (e k).symm p = x k := by
    rw [← hep' k, (e k).left_inv (hes k)]
  have hic (k : Fin 2) : ContDiffAt ℝ 1 (e k).symm p := by
    simpa only [hGx k] using heic k
  have hid (k : Fin 2) : (fderiv ℝ (e k).symm p).comp (P.comp (D k)) =
      ContinuousLinearMap.id ℝ (Euc 2) := by
    simpa only [hGx k] using heinv k
  let β : Fin 2 → Euc 2 → ℝ := fun k => s k ∘ (e k).symm
  have hβ (k : Fin 2) : ContDiffAt ℝ 1 (β k) p := by
    exact ((heinverse k).symm ▸ (hs k).of_le (by simp)).comp p (hic k)
  have hβd (k : Fin 2) : fderiv ℝ (β k) p =
      (fderiv ℝ (s k) (x k)).comp (fderiv ℝ (e k).symm p) := by
    have hd : HasFDerivAt (s k) (fderiv ℝ (s k) (x k)) ((e k).symm p) :=
      (heinverse k).symm ▸ ((hs k).differentiableAt (by simp)).hasFDerivAt
    exact (hd.comp p ((hic k).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have hβnormal (k : Fin 2) : fderiv ℝ (β k) p (P (D k (n k))) =
      fderiv ℝ (s k) (x k) (n k) := by
    rw [hβd]
    have hi := congrArg (fun L : Euc 2 →L[ℝ] Euc 2 => L (n k)) (hid k)
    exact congrArg (fderiv ℝ (s k) (x k)) hi
  have hcoordzero (k : Fin 2) : ∀ᶠ t in 𝓝 (0 : ℝ), s k (q k t) = 0 := by
    have hz := defining_function_zero_on_frontier (A k).domain (s k) (x k)
      ((hs k).of_le (by simp)) (hside k)
    filter_upwards [(hq k).continuousAt.tendsto.eventually hz, hboundary k] with t ht hb
    exact ht hb
  have hout (k : Fin 2) : fderiv ℝ (s k) (x k) (n k) < 0 := by
    apply regular_defining_function_outward_sign (A k).domain (s k) (x k) (v k) (n k)
      ((hs k).differentiableAt (by simp)).hasFDerivAt (hs0 k) (hsurj k)
    · exact defining_derivative_zero_on_boundary_curve (A k).domain (s k) (x k) (v k)
        (q k) rfl (hq k) ((hs k).of_le (by simp)) (hside k) (hboundary k)
    · exact hframe k
    · exact hside k
    · exact hinward k
  have hqinverse (k : Fin 2) : ∀ᶠ t in 𝓝 (0 : ℝ), (e k).symm (P (γ t)) = q k t := by
    have hqt : Tendsto (q k) (𝓝 (0 : ℝ)) (𝓝[(A k).domain] (x k)) :=
      tendsto_nhdsWithin_iff.mpr ⟨(hq k).continuousAt.tendsto,
        (hboundary k).mono (fun _ h => h.1)⟩
    filter_upwards [hqt.eventually (heq k), himage k,
      (hq k).continuousAt.preimage_mem_nhds ((e k).open_source.mem_nhds (hes k))] with t ht he htS
    change (e k) (q k t) = P (G k (q k t)) at ht
    rw [← he, ← ht]
    exact (e k).left_inv htS
  have hzero (k : Fin 2) : ∀ᶠ t in 𝓝 (0 : ℝ), β k ((P ∘ γ) t) = 0 := by
    filter_upwards [hqinverse k, hcoordzero k] with t hi hz
    change s k ((e k).symm (P (γ t))) = 0
    rw [hi, hz]
  let w := P (D 0 (n 0))
  have hw : w = -P (D 1 (n 1)) := by
    have he := congrArg P hbalance
    rw [map_add, map_zero] at he
    exact eq_neg_of_add_eq_zero_left he
  have hsneg : fderiv ℝ (β 0) p w < 0 := by rw [hβnormal]; exact hout 0
  have htpos : 0 < fderiv ℝ (β 1) p w := by rw [hw, map_neg, hβnormal]; exact neg_pos.mpr (hout 1)
  obtain ⟨hsides, hcover⟩ := opposite_defining_functions_local_sides (β 0) (β 1) p
    (deriv (P ∘ γ) 0) w (P ∘ γ) (hβ 0) (hβ 1) hcurve
    (hcurve.differentiableAt (by norm_num)).hasDerivAt rfl hvelocity (hzero 0) (hzero 1) hsneg htpos
  let I : Set ℝ := {t | ∀ k : Fin 2, G k ((e k).symm (P (γ t))) = γ t}
  have hI : I ∈ 𝓝 (0 : ℝ) := by
    apply Filter.eventually_all.mpr
    intro k
    filter_upwards [hqinverse k, himage k] with t hi he
    rw [hi]
    exact he
  have hzerograph : ∀ᶠ z in 𝓝 p, β 0 z = 0 → G 0 ((e 0).symm z) = G 1 ((e 1).symm z) := by
    filter_upwards [hcover I hI] with z hz
    intro hz0
    obtain ⟨t, ht, htz⟩ := hz hz0
    rw [← htz]
    exact (ht 0).trans (ht 1).symm
  let W : Set (Euc 2) := {z | (0 ≤ β 0 z ↔ β 1 z ≤ 0) ∧
    (β 0 z = 0 ↔ β 1 z = 0) ∧
    (β 0 z = 0 → G 0 ((e 0).symm z) = G 1 ((e 1).symm z))}
  have hW : W ∈ 𝓝 p := by
    filter_upwards [hsides, hzerograph] with z hz hg
    exact ⟨hz.1, hz.2.2, hg⟩
  have hgood (k : Fin 2) : ∀ᶠ y in 𝓝[(A k).domain] (x k),
      (e k).symm (P (G k y)) = y ∧ 0 ≤ β k (P (G k y)) ∧ P (G k y) ∈ W := by
    have hpcont : ContinuousWithinAt (P ∘ G k) (A k).domain (x k) :=
      P.continuous.continuousAt.comp_continuousWithinAt (hG k).continuousWithinAt
    have hWp : ∀ᶠ z in 𝓝 p, z ∈ W := hW
    have hpW : ∀ᶠ y in 𝓝[(A k).domain] (x k), P (G k y) ∈ W :=
      hpcont.tendsto.eventually (by simpa only [Function.comp_apply, hGx k] using hWp)
    filter_upwards [heq k, nhdsWithin_le_nhds ((e k).open_source.mem_nhds (hes k)),
      (hside k).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin, hpW] with y he hyS hys hy hyW
    have hi : (e k).symm (P (G k y)) = y := by
      change (e k) y = P (G k y) at he
      rw [← he]
      exact (e k).left_inv hyS
    exact ⟨hi, by change 0 ≤ s k ((e k).symm (P (G k y))); rw [hi]; exact hys.mp hy, hyW⟩
  choose r hr hball using fun k => Metric.mem_nhdsWithin_iff.mp (hgood k)
  refine ⟨r, hr, ?_⟩
  intro y₀ hy₀ y₁ hy₁ he
  have h₀ := hball 0 hy₀
  have h₁ := hball 1 hy₁
  have hw₀ := h₀.2.2
  have hb₁ : β 1 (P (G 0 y₀)) = 0 :=
    le_antisymm (hw₀.1.mp h₀.2.1) (he ▸ h₁.2.1)
  have hb₀ := hw₀.2.1.mpr hb₁
  have hg := hw₀.2.2 hb₀
  rw [h₀.1, he, h₁.1] at hg
  exact hg

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
