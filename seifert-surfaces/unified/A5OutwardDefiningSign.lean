import A5SectorBoundaryCoordinates
import A5SeamTangents

set_option autoImplicit false
open scoped ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

/-- Local side equality and continuity force the defining function to
vanish on the actual domain frontier nearby. -/
theorem defining_function_zero_on_frontier
    (S : Set (Euc 2)) (s : Euc 2 → ℝ) (x : Euc 2)
    (hs : ContDiffAt ℝ 1 s x)
    (hside : ∀ᶠ z in 𝓝 x, z ∈ S ↔ 0 ≤ s z) :
    ∀ᶠ z in 𝓝 x, z ∈ S ∩ frontier S → s z = 0 := by
  filter_upwards [hs.eventually (by norm_num), eventually_eventually_nhds.mpr hside] with z hsz hsidez
  intro hz
  have hn : 0 ≤ s z := hsidez.self_of_nhds.mp hz.1
  by_contra he
  have hp : 0 < s z := lt_of_le_of_ne hn (Ne.symm he)
  have hS : S ∈ 𝓝 z := by
    filter_upwards [hsidez, hsz.continuousAt.eventually_const_lt hp] with y hys hyp
    exact hys.mpr hyp.le
  exact hz.2.2 (mem_interior_iff_mem_nhds.mpr hS)

/-- The actual lifted seam velocity is annihilated by the local domain
defining covector. -/
theorem defining_derivative_zero_on_boundary_curve
    (S : Set (Euc 2)) (s : Euc 2 → ℝ) (x v : Euc 2)
    (q : ℝ → Euc 2) (hqx : q 0 = x) (hq : HasDerivAt q v 0)
    (hs : ContDiffAt ℝ 1 s x)
    (hside : ∀ᶠ z in 𝓝 x, z ∈ S ↔ 0 ≤ s z)
    (hboundary : ∀ᶠ t in 𝓝 (0 : ℝ), q t ∈ S ∩ frontier S) :
    fderiv ℝ s x v = 0 := by
  have ht : Tendsto q (𝓝 (0 : ℝ)) (𝓝 x) := hqx ▸ hq.continuousAt.tendsto
  have heq : (s ∘ q) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [ht.eventually (defining_function_zero_on_frontier S s x hs hside), hboundary] with t ht hb
    exact ht hb
  have hd := (hs.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hq hqx.symm
  exact hd.deriv.symm.trans (heq.deriv_eq.trans (deriv_const 0 0))

/-- Unit and orthogonality equations make the edge velocity and outward
coordinate vector independent, through the actual piece derivative. -/
theorem conormal_coordinate_frame
    (D : Euc 2 →L[ℝ] Euc 3) (v n : Euc 2) (hv : v ≠ 0)
    (L : Euc 3 →L[ℝ] ℝ) (hunit : L (D n) = 1) (horth : L (D v) = 0) :
    LinearIndependent ℝ (![v, n] : Fin 2 → Euc 2) := by
  apply linearIndependent_fin2.mpr
  refine ⟨?_, ?_⟩
  · intro hn
    change n = 0 at hn
    simp [hn] at hunit
  · intro a ha
    change a • n = v at ha
    have he := congrArg (fun w => L (D w)) ha
    simp only [map_smul, hunit, horth, smul_eq_mul, mul_one] at he
    subst a
    exact hv (by simpa using ha.symm)

/-- A nonzero boundary covector is strictly negative on an outward direction
once that direction and the edge velocity are independent. The supplied
inward segments determine the sign. -/
theorem regular_defining_function_outward_sign
    (S : Set (Euc 2)) (s : Euc 2 → ℝ) (x v n : Euc 2)
    (hs : HasFDerivAt s (fderiv ℝ s x) x) (hs0 : s x = 0)
    (hregular : Function.Surjective (fderiv ℝ s x))
    (hv : fderiv ℝ s x v = 0)
    (hframe : LinearIndependent ℝ (![v, n] : Fin 2 → Euc 2))
    (hside : ∀ᶠ z in 𝓝 x, z ∈ S ↔ 0 ≤ s z)
    (hinward : ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ Ioo (0 : ℝ) ε, x - b • n ∈ S) :
    fderiv ℝ s x n < 0 := by
  let p : ℝ → Euc 2 := fun b => x - b • n
  have hp : HasDerivAt p (-n) 0 := by
    simpa only [one_smul, id_eq, p] using ((hasDerivAt_id (0 : ℝ)).smul_const n).const_sub x
  have hpx : p 0 = x := by simp [p]
  have hd : HasDerivAt (s ∘ p) (-(fderiv ℝ s x n)) 0 := by
    simpa only [map_neg] using hs.comp_hasDerivAt_of_eq 0 hp hpx.symm
  obtain ⟨ε, hε, hin⟩ := hinward
  have hsidep : ∀ᶠ b in 𝓝 (0 : ℝ), p b ∈ S ↔ 0 ≤ s (p b) :=
    (hpx ▸ hp.continuousAt.tendsto).eventually hside
  have hnonneg : 0 ≤ -(fderiv ℝ s x n) := by
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [hsidep.filter_mono nhdsWithin_le_nhds,
      (gt_mem_nhds hε).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0)] with b hb hbe hbpos
    have hpnonneg := hb.mp (hin b ⟨hbpos, hbe⟩)
    simpa only [Function.comp_apply, zero_add, hpx, hs0, sub_zero, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr hbpos.le) hpnonneg
  have hne : fderiv ℝ s x n ≠ 0 := by
    intro hn
    have hspan : Submodule.span ℝ (range (![v, n] : Fin 2 → Euc 2)) = ⊤ :=
      hframe.span_eq_top_of_card_eq_finrank (by simp [Euc])
    have hle : Submodule.span ℝ (range (![v, n] : Fin 2 → Euc 2)) ≤
        (fderiv ℝ s x).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hv
      · exact hn
    rw [hspan] at hle
    obtain ⟨y, hy⟩ := hregular 1
    have hy0 := hle (Submodule.mem_top : y ∈ (⊤ : Submodule ℝ (Euc 2)))
    change fderiv ℝ s x y = 0 at hy0
    linarith
  exact lt_of_le_of_ne (by linarith) hne

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
