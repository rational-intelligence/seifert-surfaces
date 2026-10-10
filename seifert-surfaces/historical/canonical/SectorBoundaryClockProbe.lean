import OriginalA25SourceDefinitionsV464
import A5NativeSeamSector
import A5NativeLocalCover
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology MeasureTheory Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal

private theorem sectorUnit_norm_one (t : ℝ) : ‖sectorUnit t‖ = 1 := by
  have he : ‖sectorUnit t‖ ^ 2 = 1 := by
    simp [EuclideanSpace.real_norm_sq_eq, sectorUnit, Fin.sum_univ_two,
      Real.cos_sq_add_sin_sq]
  nlinarith [norm_nonneg (sectorUnit t)]

private theorem sectorUnit_angle_ne_zero (θ : ℝ) (hθ : 0 < θ)
    (hθπ : θ < 2 * Real.pi) : sectorUnit θ ≠ sectorUnit 0 := by
  intro he
  have ht : θ = 0 := by
    apply Circle.exp_injOn_Icc (by simpa using hθπ)
      (show θ ∈ Icc (0 : ℝ) θ from ⟨hθ.le, le_rfl⟩)
      (show (0 : ℝ) ∈ Icc (0 : ℝ) θ from ⟨le_rfl, hθ.le⟩)
    apply Subtype.ext
    have hc := congrArg (fun z : Euc 2 => z 0) he
    have hs := congrArg (fun z : Euc 2 => z 1) he
    simp only [sectorUnit, Matrix.cons_val_zero, Matrix.cons_val_one] at hc hs
    change Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((0 : ℂ) * Complex.I)
    simp only [Complex.exp_mul_I]
    norm_cast
    norm_num [hc, hs]
  exact hθ.ne' ht

/-- The actual two boundary rays of a sector form a continuous topological
line, including the reflex case. No differentiability of this clock at a
nonstraight apex is asserted. -/
def sectorBoundaryClock (θ : ℝ) (t : ℝ) : Euc 2 :=
  if 0 ≤ t then t • sectorUnit 0 else (-t) • sectorUnit θ

theorem sectorBoundaryClock_continuous (θ : ℝ) : Continuous (sectorBoundaryClock θ) := by
  apply Continuous.if_le (continuous_id.smul continuous_const)
    (continuous_id.neg.smul continuous_const) continuous_const continuous_id
  intro t ht
  change (0 : ℝ) = t at ht
  simp [← ht]

theorem sectorBoundaryClock_norm (θ t : ℝ) : ‖sectorBoundaryClock θ t‖ = |t| := by
  by_cases ht : 0 ≤ t
  · simp only [sectorBoundaryClock, if_pos ht, norm_smul, sectorUnit_norm_one,
      Real.norm_eq_abs, mul_one]
  · simp only [sectorBoundaryClock, if_neg ht, norm_smul, sectorUnit_norm_one,
      Real.norm_eq_abs, abs_neg, mul_one]

theorem sectorBoundaryClock_injective (θ : ℝ) (hθ : 0 < θ)
    (hθπ : θ < 2 * Real.pi) : Function.Injective (sectorBoundaryClock θ) := by
  intro t s he
  have habs : |t| = |s| := by
    simpa only [sectorBoundaryClock_norm] using congrArg norm he
  by_cases ht : 0 ≤ t <;> by_cases hs : 0 ≤ s
  · simpa only [abs_of_nonneg ht, abs_of_nonneg hs] using habs
  · have hts : t = -s := by simpa only [abs_of_nonneg ht, abs_of_neg (lt_of_not_ge hs)] using habs
    have hsp : -s ≠ 0 := neg_ne_zero.mpr (ne_of_lt (lt_of_not_ge hs))
    have hu : sectorUnit 0 = sectorUnit θ := by
      apply smul_right_injective (Euc 2) hsp
      simp only [sectorBoundaryClock, if_pos ht, if_neg hs] at he
      rwa [hts] at he
    exact (sectorUnit_angle_ne_zero θ hθ hθπ hu.symm).elim
  · have hts : -t = s := by simpa only [abs_of_neg (lt_of_not_ge ht), abs_of_nonneg hs] using habs
    have htp : -t ≠ 0 := neg_ne_zero.mpr (ne_of_lt (lt_of_not_ge ht))
    have hu : sectorUnit θ = sectorUnit 0 := by
      apply smul_right_injective (Euc 2) htp
      simp only [sectorBoundaryClock, if_neg ht, if_pos hs] at he
      rwa [← hts] at he
    exact (sectorUnit_angle_ne_zero θ hθ hθπ hu).elim
  · have : -t = -s := by simpa only [abs_of_neg (lt_of_not_ge ht), abs_of_neg (lt_of_not_ge hs)] using habs
    linarith

theorem sectorBoundaryClock_mem_boundary (θ t : ℝ) :
    sectorBoundaryClock θ t ∈ sectorBoundary θ := by
  by_cases ht : 0 ≤ t
  · exact ⟨t, ht, Or.inl (by simp [sectorBoundaryClock, ht])⟩
  · exact ⟨-t, neg_nonneg.mpr (le_of_lt (lt_of_not_ge ht)),
      Or.inr (by simp [sectorBoundaryClock, ht])⟩



/-- The two-ray boundary clock is an embedding with an explicit continuous
left inverse, for every native opening strictly between zero and two pi. -/
theorem sectorBoundaryClock_embedding (θ : ℝ) (hθ : 0 < θ)
    (hθπ : θ < 2 * Real.pi) : IsEmbedding (sectorBoundaryClock θ) := by
  have hc : Real.cos θ ≠ 1 := by
    intro hc
    have hs : Real.sin θ = 0 := by
      have h := Real.cos_sq_add_sin_sq θ
      rw [hc] at h
      nlinarith [sq_nonneg (Real.sin θ)]
    apply sectorUnit_angle_ne_zero θ hθ hθπ
    ext i
    fin_cases i <;> simp [sectorUnit, hc, hs]
  let L : Euc 2 → ℝ := fun x =>
    ((1 - Real.cos θ) * x 0 - Real.sin θ * x 1) / (1 - Real.cos θ)
  have hL : Continuous L := by dsimp only [L]; fun_prop
  have hinv : Function.LeftInverse L (sectorBoundaryClock θ) := by
    intro t
    by_cases ht : 0 ≤ t
    · simp only [sectorBoundaryClock, if_pos ht]
      dsimp [L, sectorUnit]
      field_simp
      simp
      ring
    · simp only [sectorBoundaryClock, if_neg ht]
      dsimp [L, sectorUnit]
      field_simp
      nlinarith [Real.cos_sq_add_sin_sq θ]
  exact hinv.isEmbedding hL (sectorBoundaryClock_continuous θ)

/-- The literal native sector boundary is exactly the two-ray clock image.
The ball radius gives the open clock interval without losing the apex. -/
theorem sectorBoundaryClock_image (A : SectorModel) (ha : A.interiorChart = false) :
    sectorBoundaryClock A.angle '' Ioo (-A.radius) A.radius = A.boundary := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hb := sectorBoundaryClock_mem_boundary A.angle t
    refine ⟨?_, by simpa [SectorModel.boundary, ha] using hb⟩
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, sectorBoundaryClock_norm]
      exact abs_lt.mpr ht
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨r, hr, he | he⟩ := hb
      · exact ⟨r, hr, 0, ⟨le_rfl, A.angle_positive.le⟩, he⟩
      · exact ⟨r, hr, A.angle, ⟨A.angle_positive.le, le_rfl⟩, he⟩
  · intro hy
    have hb : y ∈ sectorBoundary A.angle := by simpa [SectorModel.boundary, ha] using hy.2
    have hn : ‖y‖ < A.radius := by
      simpa only [Metric.mem_ball, dist_zero_right] using hy.1.1
    obtain ⟨r, hr, he | he⟩ := hb
    · have hrR : r < A.radius := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, sectorUnit_norm_one, mul_one] at hn
        exact hn
      refine ⟨r, ⟨by linarith [A.radius_positive], hrR⟩, ?_⟩
      simpa [sectorBoundaryClock, hr] using he.symm
    · have hrR : r < A.radius := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, sectorUnit_norm_one, mul_one] at hn
        exact hn
      refine ⟨-r, ⟨by linarith, by linarith [A.radius_positive]⟩, ?_⟩
      by_cases hz : r = 0
      · subst r
        simp [sectorBoundaryClock] at he ⊢
        exact he.symm
      · have hneg : ¬0 ≤ -r := by linarith [lt_of_le_of_ne hr (Ne.symm hz)]
        simpa [sectorBoundaryClock, hneg] using he.symm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
