import A5CornerCylinderRegularityV472

set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers
universe u v

def leftClock (t : Time) : Time := Set.projIcc 0 1 (by norm_num) (2 * (t : ℝ))
def rightClock (t : Time) : Time := Set.projIcc 0 1 (by norm_num) (2 * (t : ℝ) - 1)

theorem leftClock_continuous : Continuous leftClock := by unfold leftClock; fun_prop
theorem rightClock_continuous : Continuous rightClock := by unfold rightClock; fun_prop

theorem leftClock_first (t : Time) : leftClock (affineTime firstHalfWindow t) = t := by
  have he : 2 * (affineTime firstHalfWindow t : ℝ) = (t : ℝ) := by
    simp [affineTime, firstHalfWindow]
  simp only [leftClock, he]
  exact Set.projIcc_of_mem _ t.property

theorem rightClock_second (t : Time) : rightClock (affineTime secondHalfWindow t) = t := by
  have he : 2 * (affineTime secondHalfWindow t : ℝ) - 1 = (t : ℝ) := by
    simp [affineTime, secondHalfWindow]; ring
  simp only [rightClock, he]
  exact Set.projIcc_of_mem _ t.property

def splice {S : Type u} {M : Type v} (f g : Time × S → M) (p : Time × S) : M :=
  if (p.1 : ℝ) ≤ 1 / 2 then f (leftClock p.1, p.2) else g (rightClock p.1, p.2)

theorem splice_first {S : Type u} {M : Type v} (f g : Time × S → M)
    (p : Time × S) : splice f g (affineCylinder firstHalfWindow p) = f p := by
  have ht : (affineTime firstHalfWindow p.1 : ℝ) ≤ 1 / 2 := by
    dsimp [affineTime, firstHalfWindow]
    linarith [p.1.property.2]
  change (if (affineTime firstHalfWindow p.1 : ℝ) ≤ 1 / 2 then
    f (leftClock (affineTime firstHalfWindow p.1), p.2) else _) = _
  rw [if_pos ht, leftClock_first]

theorem splice_second {S : Type u} {M : Type v} (f g : Time × S → M)
    (hjoin : ∀ x, f (1,x) = g (0,x)) (p : Time × S) :
    splice f g (affineCylinder secondHalfWindow p) = g p := by
  by_cases ht : (affineTime secondHalfWindow p.1 : ℝ) ≤ 1 / 2
  · have hz : p.1 = 0 := by
      apply Subtype.ext
      dsimp [affineTime, secondHalfWindow] at ht
      change (p.1 : ℝ) = 0
      linarith [p.1.property.1]
    have hleft : leftClock (affineTime secondHalfWindow p.1) = 1 := by
      rw [hz]
      norm_num [leftClock, affineTime, secondHalfWindow, Set.projIcc]
    simpa only [splice, affineCylinder, if_pos ht, hleft, ← hz] using hjoin p.2
  · change (if (affineTime secondHalfWindow p.1 : ℝ) ≤ 1 / 2 then _ else
      g (rightClock (affineTime secondHalfWindow p.1), p.2)) = _
    rw [if_neg ht, rightClock_second]

theorem splice_continuous {S : Type u} {M : Type v}
    [TopologicalSpace S] [TopologicalSpace M] (f g : Time × S → M)
    (hf : Continuous f) (hg : Continuous g) (hjoin : ∀ x, f (1,x) = g (0,x)) :
    Continuous (splice f g) := by
  apply continuous_if_le (continuous_subtype_val.comp continuous_fst) continuous_const
    (hf.comp ((leftClock_continuous.comp continuous_fst).prodMk continuous_snd)).continuousOn
    (hg.comp ((rightClock_continuous.comp continuous_fst).prodMk continuous_snd)).continuousOn
  intro p hp
  change (p.1 : ℝ) = 1 / 2 at hp
  have hl : leftClock p.1 = 1 := by
    apply Subtype.ext
    norm_num [leftClock, hp, Set.projIcc]
  have hr : rightClock p.1 = 0 := by
    apply Subtype.ext
    norm_num [rightClock, hp, Set.projIcc]
  simpa only [Function.comp_apply, hl, hr] using hjoin p.2

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

theorem affine_graph_smooth (w : AffineTimeWindow) :
    ContMDiff ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3)) ∞
      (affineCylinder (Y := M) w) := (affineTime_properties w).2.1.prodMap contMDiff_id

theorem affine_graph_rank (w : AffineTimeWindow) (p : Time × M) :
    Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3))
      (affineCylinder (Y := M) w) p) := by
  change Function.Injective (mfderiv ((𝓡∂ 1).prod (𝓡∂ 3)) ((𝓡∂ 1).prod (𝓡∂ 3))
    (Prod.map (affineTime w) (id : M → M)) p)
  rw [mfderiv_prodMap ((affineTime_properties w).2.1.mdifferentiableAt (by simp))
    mdifferentiableAt_id, mfderiv_id]
  intro a b hab
  change (mfderiv (𝓡∂ 1) (𝓡∂ 1) (affineTime w) p.1 a.1, a.2) =
    (mfderiv (𝓡∂ 1) (𝓡∂ 1) (affineTime w) p.1 b.1, b.2) at hab
  obtain ⟨ht, hx⟩ := Prod.mk.inj hab
  exact Prod.ext ((affineTime_properties w).2.2.1 p.1 ht) hx

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal.NearbyDeformations
