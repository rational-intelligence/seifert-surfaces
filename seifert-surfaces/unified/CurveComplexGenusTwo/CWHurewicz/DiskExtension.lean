import Mathlib

namespace CurveComplexGenusTwo.CWHurewicz

open Topology Metric

private abbrev Disk (n : ℕ) := ↥(closedBall (0 : Fin n → ℝ) 1)
private abbrev Sphere (n : ℕ) := ↥(sphere (0 : Fin n → ℝ) 1)

private def polar (n : ℕ) : C(unitInterval × Sphere n, Disk n) :=
  ⟨fun p => ⟨p.1.1 • p.2.1, by
      rw [mem_closedBall, dist_zero_right]
      have hunit : ‖p.2.1‖ = 1 := by simpa using p.2.2
      simpa [norm_smul, abs_of_nonneg p.1.2.1, hunit] using p.1.2.2⟩,
    by fun_prop⟩

private theorem polar_surjective (n : ℕ) [Nonempty (Sphere n)] :
    Function.Surjective (polar n) := by
  intro x
  by_cases hx : x.1 = 0
  · let z : Sphere n := Classical.choice inferInstance
    refine ⟨(0, z), ?_⟩
    apply Subtype.ext
    simp [polar, hx]
  · let q : ({0}ᶜ : Set (Fin n → ℝ)) := ⟨x.1, hx⟩
    let z : Sphere n := (homeomorphUnitSphereProd (Fin n → ℝ) q).1
    let t : unitInterval := ⟨‖x.1‖, by
      constructor
      · exact norm_nonneg _
      · simpa only [mem_closedBall, dist_zero_right] using x.2⟩
    refine ⟨(t, z), ?_⟩
    apply Subtype.ext
    simpa [polar, q, z, t, homeomorphUnitSphereProd_apply_fst_coe,
      smul_smul] using (by
        have h : (‖x.1‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hx
        simp [h] : ‖x.1‖ • (‖x.1‖⁻¹ • x.1) = x.1)

private theorem polar_quotient (n : ℕ) [Nonempty (Sphere n)] :
    IsQuotientMap (polar n) :=
  .of_surjective_continuous (polar_surjective n) (polar n).continuous

private theorem sphere_nonempty_succ (n : ℕ) : Nonempty (Sphere (n + 1)) := by
  refine ⟨⟨fun _ => (1 : ℝ), ?_⟩⟩
  simp [Sphere, Pi.norm_def, Finset.sup_const]

/-- A nullhomotopy of a sphere map descends along the radial quotient to a
continuous disk extension. -/
theorem sphereMap_extends_disk (n : ℕ) [Nonempty (Sphere n)]
    {Y : Type*} [TopologicalSpace Y] (f : C(Sphere n, Y)) (y₀ : Y)
    (H : ContinuousMap.Homotopy f (ContinuousMap.const (Sphere n) y₀)) :
    ∃ F : C(Disk n, Y), ∀ z : Sphere n, F ⟨z.1, sphere_subset_closedBall z.2⟩ = f z := by
  let G : C(unitInterval × Sphere n, Y) := H.symm.toContinuousMap
  have hfactor : Function.FactorsThrough G (polar n) := by
    intro a b hab
    have ht : a.1 = b.1 := by
      have heq := congrArg (fun x : Disk n => ‖x.1‖) hab
      have ha : ‖a.2.1‖ = 1 := by simpa using a.2.2
      have hb : ‖b.2.1‖ = 1 := by simpa using b.2.2
      apply Subtype.ext
      simpa [polar, norm_smul, ha, hb, abs_of_nonneg a.1.2.1,
        abs_of_nonneg b.1.2.1] using heq
    by_cases hzero : (a.1.1 : ℝ) = 0
    · have hbzero : (b.1.1 : ℝ) = 0 := ht ▸ hzero
      simpa [G, hzero, hbzero] using
        show H.symm (a.1, a.2) = H.symm (b.1, b.2) by
          rw [show a.1 = (0 : unitInterval) from Subtype.ext hzero,
            show b.1 = (0 : unitInterval) from Subtype.ext hbzero]
          simp
    · have hz : a.2 = b.2 := by
        apply Subtype.ext
        apply smul_right_injective (Fin n → ℝ) hzero
        have hv := congrArg Subtype.val hab
        simpa [polar, ← ht] using hv
      exact congrArg G (Prod.ext ht hz)
  let F := (polar_quotient n).lift G hfactor
  refine ⟨F, ?_⟩
  intro z
  have hp : (polar n) (1, z) = (⟨z.1, sphere_subset_closedBall z.2⟩ : Disk n) := by
    apply Subtype.ext
    simp [polar]
  rw [← hp]
  change ((polar_quotient n).lift G hfactor) ((polar n) (1, z)) = f z
  rw [← ContinuousMap.comp_apply, (polar_quotient n).lift_comp]
  exact H.symm.apply_one z

/-- The boundary-nullhomotopy extension in every dimension, including the
empty boundary of the zero-cell. -/
theorem sphereMap_extends_disk_all (n : ℕ)
    {Y : Type*} [TopologicalSpace Y] (f : C(Sphere n, Y)) (y₀ : Y)
    (H : ContinuousMap.Homotopy f (ContinuousMap.const (Sphere n) y₀)) :
    ∃ F : C(Disk n, Y), ∀ z : Sphere n,
      F ⟨z.1, sphere_subset_closedBall z.2⟩ = f z := by
  cases n with
  | zero =>
    refine ⟨ContinuousMap.const _ y₀, ?_⟩
    intro z
    have hz : False := by simpa [Pi.norm_def] using z.2
    exact hz.elim
  | succ n =>
    letI : Nonempty (Sphere (n + 1)) := sphere_nonempty_succ n
    exact sphereMap_extends_disk (n + 1) f y₀ H

end CurveComplexGenusTwo.CWHurewicz
