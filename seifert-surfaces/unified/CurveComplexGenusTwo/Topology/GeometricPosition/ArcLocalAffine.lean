import Schoenflies.Subarc
import Schoenflies.Plane
import Mathlib
namespace CurveComplex
/-- An interior point of a genuine embedded arc locally contained in an affine
line has a FULL local affine-line image. Mere subset inclusion is promoted to
exact local image equality without assuming a crossing certificate. -/
theorem position_arc_local_affine
    {A U : Set Schoenflies.Plane} {a b p : Schoenflies.Plane}
    (hA : Schoenflies.IsArcBetween A a b)
    (hp : p ∈ A) (hpa : p ≠ a) (hpb : p ≠ b)
    (hU : IsOpen U) (hpU : p ∈ U)
    (m : ℝ) (hline : ∀ z ∈ A ∩ U, z 1 = p 1 + m * (z 0 - p 0)) :
    ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧
      ∀ z ∈ W, (z ∈ A ↔ z 1 = p 1 + m * (z 0 - p 0)) := by
  classical
  obtain ⟨f, hf, hi, hfr, hf0, hf1⟩ := hA
  obtain ⟨t, ht, hft⟩ := hfr.symm ▸ hp
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne ht.1
    intro h
    exact hpa (by simpa [← h, hf0] using hft.symm)
  have ht1 : t < 1 := by
    apply lt_of_le_of_ne ht.2
    intro h
    exact hpb (by simpa [h, hf1] using hft.symm)
  have hnear : f ⁻¹' U ∈ nhds t :=
    (hf.continuousAt (Icc_mem_nhds ht0 ht1)).preimage_mem_nhds
      (by rw [hft]; exact hU.mem_nhds hpU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let η : ℝ := min ε (min t (1-t)) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by dsimp [η]; linarith [min_le_left ε (min t (1-t))]
  have hηt : η < t := by
    have hh := (min_le_right ε (min t (1-t))).trans (min_le_left t (1-t))
    dsimp [η]; linarith
  have hη1 : η < 1-t := by
    have hh := (min_le_right ε (min t (1-t))).trans (min_le_right t (1-t))
    dsimp [η]; linarith
  let l := t-η
  let r := t+η
  have hlr : l < r := by dsimp [l,r]; linarith
  have hlt : l < t := by dsimp [l]; linarith
  have htr : t < r := by dsimp [r]; linarith
  have hsub : Set.Icc l r ⊆ unitInterval := by
    intro x hx
    constructor <;> dsimp [l,r] at hx <;> linarith [hx.1, hx.2]
  have hfU (x : ℝ) (hx : x ∈ Set.Icc l r) : f x ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [l,r] at hx
    constructor <;> linarith [hx.1, hx.2]
  have hfA (x : ℝ) (hx : x ∈ Set.Icc l r) : f x ∈ A :=
    hfr ▸ Set.mem_image_of_mem f (hsub hx)
  let q : ℝ → ℝ := fun x => f x 0
  have hqc : ContinuousOn q (Set.Icc l r) :=
    (EuclideanSpace.proj 0).continuous.continuousOn.comp (hf.mono hsub) (fun _ _ => Set.mem_univ _)
  have hqi : Set.InjOn q (Set.Icc l r) := by
    intro x hx y hy heq
    apply hi (hsub hx) (hsub hy)
    ext i
    fin_cases i
    · exact heq
    · change f x 1 = f y 1
      rw [hline (f x) ⟨hfA x hx, hfU x hx⟩,
        hline (f y) ⟨hfA y hy, hfU y hy⟩]
      change p 1 + m * (q x - p 0) = p 1 + m * (q y - p 0)
      rw [heq]
  have hmid : q t ∈ Set.Ioo (min (q l) (q r)) (max (q l) (q r)) := by
    rcases hqc.strictMonoOn_of_injOn_Icc' hlr.le hqi with hm | hm
    · have hlt' := hm (Set.left_mem_Icc.mpr hlr.le) ⟨hlt.le,htr.le⟩ hlt
      have htr' := hm ⟨hlt.le,htr.le⟩ (Set.right_mem_Icc.mpr hlr.le) htr
      rw [min_eq_left (hlt'.trans htr').le, max_eq_right (hlt'.trans htr').le]
      exact ⟨hlt',htr'⟩
    · have hlt' := hm (Set.left_mem_Icc.mpr hlr.le) ⟨hlt.le,htr.le⟩ hlt
      have htr' := hm ⟨hlt.le,htr.le⟩ (Set.right_mem_Icc.mpr hlr.le) htr
      rw [min_eq_right (htr'.trans hlt').le, max_eq_left (htr'.trans hlt').le]
      exact ⟨htr',hlt'⟩
  have hcoord : Set.Icc (min (q l) (q r)) (max (q l) (q r)) ⊆ q '' Set.Icc l r := by
    rcases le_total (q l) (q r) with h | h
    · simpa [min_eq_left h, max_eq_right h] using intermediate_value_Icc hlr.le hqc
    · simpa [min_eq_right h, max_eq_left h] using intermediate_value_Icc' hlr.le hqc
  let W := U ∩ {z : Schoenflies.Plane | min (q l) (q r) < z 0 ∧ z 0 < max (q l) (q r)}
  refine ⟨W, hU.inter ?_, ?_, Set.inter_subset_left, ?_⟩
  · exact (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  · refine ⟨hpU, ?_⟩
    simpa only [q, hft, Set.mem_setOf_eq, Set.mem_Ioo] using hmid
  · intro z hz
    constructor
    · intro hzA
      exact hline z ⟨hzA,hz.1⟩
    · intro hzline
      obtain ⟨x, hx, hqx⟩ := hcoord ⟨hz.2.1.le,hz.2.2.le⟩
      have hfz : f x = z := by
        ext i
        fin_cases i
        · exact hqx
        · change f x 1 = z 1
          rw [hline (f x) ⟨hfA x hx, hfU x hx⟩, hzline]
          change p 1 + m * (q x - p 0) = p 1 + m * (z 0 - p 0)
          rw [hqx]
      exact hfz ▸ hfA x hx
end CurveComplex
