import VM02aDirectMethod
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Piecewise

noncomputable section
open Set Topology Function
open scoped ContDiff NNReal

namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates

/-! Extend one monotone interpolated arc to a genuine continuous lift of
the same original sign and degree.  These seam data will be supplied by the
actual original affine arc construction, rather than added to the minimizer. -/
private theorem original_periodic_lift_patch_v411
    {R : ℝ} (Ω : SmoothFlatJordanDomain R) (theta : ℝ → ℝ) (sigma : ℝ)
    (lift : WeakMonotoneBoundaryLift Ω theta sigma)
    (s a : ℝ) (ha : 0 < a) (haT : 2 * a < 2 * Real.pi)
    (eta : ℝ → ℝ) (heta : Continuous eta)
    (hmono : Monotone (fun t => sigma * eta t))
    (hleft : eta (s - a) = theta (s - a))
    (hright : eta (s + a) = theta (s + a)) :
    ∃ theta' : ℝ → ℝ,
      WeakMonotoneBoundaryLift Ω theta' sigma ∧
      (∀ t ∈ Icc (s - a) (s + a), theta' t = eta t) ∧
      (∀ t ∈ Icc (s + a) (s - a + 2 * Real.pi), theta' t = theta t) := by
  classical
  let T : ℝ := 2 * Real.pi
  have hT : 0 < T := by dsimp [T]; positivity
  letI : Fact (0 < T) := ⟨hT⟩
  let u : ℝ := s - a
  let v : ℝ := s + a
  have huv : u < v := by dsimp [u, v]; linarith
  have hvT : v < u + T := by dsimp [u, v, T]; linarith
  let H : ℝ → ℝ := fun t => if t ≤ v then eta t else theta t
  have hHv : H v = theta v := by simp [H, v, hright]
  have hHu : H u = theta u := by simp only [H, if_pos huv.le]; exact hleft
  have hHT : H (u + T) = theta (u + T) := by
    simp only [H, if_neg (not_le_of_gt hvT)]
  have hHcont : Continuous H := by
    apply heta.if _ lift.2.1
    intro t ht
    change t ∈ frontier (Iic v) at ht
    have ht' : t = v := by simpa only [frontier_Iic, mem_singleton_iff] using ht
    subst t
    exact hright
  have hHmono : Monotone (fun t => sigma * H t) := by
    intro x y hxy
    by_cases hy : y ≤ v
    · have hx : x ≤ v := hxy.trans hy
      simp only [H, if_pos hx, if_pos hy]
      exact hmono hxy
    · by_cases hx : x ≤ v
      · simp only [H, if_pos hx, if_neg hy]
        have h1 := hmono hx
        have h2 := lift.2.2.1 (le_of_lt (lt_of_not_ge hy))
        change sigma * eta x ≤ sigma * eta (s + a) at h1
        rw [hright] at h1
        exact h1.trans h2
      · simp only [H, if_neg hx, if_neg hy]
        exact lift.2.2.1 hxy
  let E : ℝ → ℝ := fun t => H t - theta t
  have hE : Continuous E := hHcont.sub lift.2.1
  have hEends : E u = E (u + T) := by simp [E, hHu, hHT]
  let P : ℝ → ℝ := fun t => AddCircle.liftIco T u E (t : AddCircle T)
  have hP : Continuous P :=
    (AddCircle.liftIco_continuous hEends hE.continuousOn).comp (AddCircle.continuous_mk' T)
  have hPperiod : Periodic P T := by
    intro t
    dsimp only [P]
    rw [AddCircle.coe_add_period]
  let theta' : ℝ → ℝ := fun t => theta t + P t
  have hcont : Continuous theta' := lift.2.1.add hP
  have hperiod (t : ℝ) : theta' (t + T) = theta' t + sigma * T := by
    dsimp only [theta']
    rw [hPperiod]
    have h := lift.2.2.2 t
    change theta (t + T) = theta t + sigma * T at h
    rw [h]
    ring
  have hIco (t : ℝ) (ht : t ∈ Ico u (u + T)) : theta' t = H t := by
    dsimp only [theta', P]
    rw [AddCircle.liftIco_coe_apply ht]
    dsimp [E]
    ring
  have hIcc (t : ℝ) (ht : t ∈ Icc u (u + T)) : theta' t = H t := by
    rcases ht.2.eq_or_lt with heq | hlt
    · subst t
      rw [hperiod, hIco u ⟨le_rfl, lt_add_of_pos_right _ hT⟩, hHu, hHT]
      exact (lift.2.2.2 u).symm
    · exact hIco t ⟨ht.1, hlt⟩
  have hσsq : sigma * sigma = 1 := by rcases lift.1 with h | h <;> rw [h] <;> norm_num
  let n : ℝ → ℤ := fun t => toIcoDiv hT u t
  let modt : ℝ → ℝ := fun t => toIcoMod hT u t
  have hmod (t : ℝ) : modt t ∈ Ico u (u + T) := toIcoMod_mem_Ico hT u t
  have hdecomp (t : ℝ) : modt t + (n t : ℝ) * T = t := by
    simpa only [modt, n, zsmul_eq_mul] using toIcoMod_add_toIcoDiv_zsmul hT u t
  have hPmod (t : ℝ) : P t = P (modt t) := by
    dsimp only [P]
    congr 1
    dsimp only [modt, toIcoMod]
    rw [AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, sub_zero]
  have hθerror : Periodic (fun t => theta t - sigma * t) T := by
    intro t
    dsimp only
    have h := lift.2.2.2 t
    change theta (t + T) = theta t + sigma * T at h
    rw [h]
    ring
  have hvalue (t : ℝ) : theta' t = H (modt t) + sigma * ((n t : ℝ) * T) := by
    have herror := (hθerror.int_mul (n t)).sub_eq t
    have hmodexpr : t - (n t : ℝ) * T = modt t := by linarith [hdecomp t]
    simp only [zsmul_eq_mul, hmodexpr] at herror
    have hh := hIco (modt t) (hmod t)
    dsimp only [theta'] at hh ⊢
    rw [hPmod]
    linear_combination hh - herror - sigma * (hdecomp t)
  have hsvalue (t : ℝ) : sigma * theta' t = sigma * H (modt t) + (n t : ℝ) * T := by
    rw [hvalue, mul_add, ← mul_assoc sigma sigma, hσsq, one_mul]
  have hnmono : Monotone n := by
    intro x y hxy
    dsimp only [n]
    rw [toIcoDiv_eq_floor, toIcoDiv_eq_floor]
    exact Int.floor_mono ((div_le_div_iff_of_pos_right hT).mpr (sub_le_sub_right hxy _))
  have hHends : sigma * H (u + T) = sigma * H u + T := by
    rw [hHT, hHu]
    have h := lift.2.2.2 u
    change theta (u + T) = theta u + sigma * T at h
    rw [h, mul_add, ← mul_assoc sigma sigma, hσsq, one_mul]
  have hmon : Monotone (fun t => sigma * theta' t) := by
    intro x y hxy
    dsimp only
    rw [hsvalue, hsvalue]
    rcases (hnmono hxy).eq_or_lt with hn | hn
    · have hmods : modt x ≤ modt y := by
        have hnx : (n x : ℝ) = (n y : ℝ) := by exact_mod_cast hn
        have hx := hdecomp x
        have hy := hdecomp y
        rw [← hnx] at hy
        linarith
      have hh := hHmono hmods
      dsimp only at hh
      have hnx : (n x : ℝ) = (n y : ℝ) := by exact_mod_cast hn
      rw [hnx]
      linarith
    · have hnx : (n x : ℝ) + 1 ≤ (n y : ℝ) := by
        exact_mod_cast (Int.add_one_le_iff.mpr hn)
      have hstep := mul_le_mul_of_nonneg_right hnx hT.le
      have h1 := hHmono (hmod x).2.le
      have h2 := hHmono (hmod y).1
      dsimp only at h1 h2
      rw [hHends] at h1
      nlinarith
  refine ⟨theta', ⟨lift.1, hcont, hmon, hperiod⟩, ?_, ?_⟩
  · intro t ht
    rw [hIcc t ⟨ht.1, ht.2.trans hvT.le⟩]
    exact if_pos ht.2
  · intro t ht
    rw [hIcc t ⟨huv.le.trans ht.1, ht.2⟩]
    by_cases htv : t = v
    · subst t
      exact hHv
    · exact if_neg (not_le.mpr (lt_of_le_of_ne ht.1 (Ne.symm htv)))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
