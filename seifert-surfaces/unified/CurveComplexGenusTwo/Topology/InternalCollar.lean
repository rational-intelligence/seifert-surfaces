import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.ArcComplement
import Schoenflies.Accessible
import Schoenflies.SkeletonAccess
import Schoenflies.Subarc
open Set Metric unitInterval
namespace Schoenflies

/-- A collar of a compact internal subarc can avoid the entire original arc.
The extra open set contains the original image and controls the collar size. -/
theorem internal_collar_avoiding_full_arc
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I)
    {l s t r : ℝ} (hl : 0 ≤ l) (hls : l < s) (hst : s < t)
    (htr : t < r) (hr : r ≤ 1)
    {O : Set Plane} (hO : IsOpen O) (hfO : f '' Icc l r ⊆ O) :
    Nonempty (ArcCollar O (f '' I) (f '' Icc s t)) := by
  have hs : 0 < s := hl.trans_lt hls
  have ht : t < 1 := htr.trans_le hr
  have hNoBall : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {t r : ℝ}, t ∈ Ioo (0 : ℝ) 1 → 0 < r →
        ¬ ball (f t) r ⊆ f '' I := by
    intro f hf hi t r ht hr
    intro hsub
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    obtain ⟨δ, hδ, hδspec⟩ := Metric.continuousWithinAt_iff.mp
      (hf t ⟨ht.1.le, ht.2.le⟩) r hr
    let d : ℝ := min δ (min t (1-t)) / 2
    have hd : 0 < d := by dsimp [d]; positivity
    have hdδ : d < δ := by dsimp [d]; have := min_le_left δ (min t (1-t)); linarith
    have hdt : d < t := by dsimp [d]; have := (min_le_right δ (min t (1-t))).trans (min_le_left t (1-t)); linarith
    have hd1 : d < 1-t := by dsimp [d]; have := (min_le_right δ (min t (1-t))).trans (min_le_right t (1-t)); linarith
    have hsI : t-d ∈ I := ⟨by linarith, by linarith [ht.2]⟩
    have huI : t+d ∈ I := ⟨by linarith [ht.1], by linarith⟩
    have hsball : f (t-d) ∈ ball (f t) r := hδspec hsI (by
      rw [Real.dist_eq]; have : t-d-t = -d := by ring
      rw [this, abs_neg, abs_of_pos hd]; exact hdδ)
    have huball : f (t+d) ∈ ball (f t) r := hδspec huI (by
      rw [Real.dist_eq]; have : t+d-t = d := by ring
      rw [this, abs_of_pos hd]; exact hdδ)
    obtain ⟨V₁, hV₁open, hV₁⟩ := image_isRelOpen hf hi (U := Iio t) isOpen_Iio
    obtain ⟨V₂, hV₂open, hV₂⟩ := image_isRelOpen hf hi (U := Ioi t) isOpen_Ioi
    let B := ball (f t) r \ {f t}
    have hB : IsPreconnected B := (isConnected_ball_diff_singleton hr).isPreconnected
    have hcover : B ⊆ V₁ ∪ V₂ := by
      rintro z ⟨hz, hzne⟩
      obtain ⟨s, hs, rfl⟩ := hsub hz
      have hst : s ≠ t := by rintro rfl; exact hzne rfl
      rcases lt_or_gt_of_ne hst with h | h
      · left
        have : f s ∈ V₁ ∩ f '' I := by rw [← hV₁]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1
      · right
        have : f s ∈ V₂ ∩ f '' I := by rw [← hV₂]; exact ⟨s, ⟨h, hs⟩, rfl⟩
        exact this.1
    have hs : (B ∩ V₁).Nonempty := by
      refine ⟨f (t-d), ⟨hsball, ?_⟩, ?_⟩
      · intro h
        have := hi hsI ⟨ht.1.le, ht.2.le⟩ h
        linarith
      · have : f (t-d) ∈ V₁ ∩ f '' I := by
          rw [← hV₁]; exact ⟨t-d, ⟨show t-d < t by linarith, hsI⟩, rfl⟩
        exact this.1
    have hu : (B ∩ V₂).Nonempty := by
      refine ⟨f (t+d), ⟨huball, ?_⟩, ?_⟩
      · intro h
        have := hi huI ⟨ht.1.le, ht.2.le⟩ h
        linarith
      · have : f (t+d) ∈ V₂ ∩ f '' I := by
          rw [← hV₂]; exact ⟨t+d, ⟨show t < t+d by linarith, huI⟩, rfl⟩
        exact this.1
    obtain ⟨z, hzB, hz₁, hz₂⟩ := hB V₁ V₂ hV₁open hV₂open hcover hs hu
    have hzImage := hsub hzB.1
    obtain ⟨s, hs, rfl⟩ : z ∈ f '' (Iio t ∩ I) := by rw [hV₁]; exact ⟨hz₁, hzImage⟩
    obtain ⟨u, hu, heq⟩ : f s ∈ f '' (Ioi t ∩ I) := by rw [hV₂]; exact ⟨hz₂, hzImage⟩
    have := hi hu.2 hs.2 heq
    have hut : t < u := hu.1
    have hst : s < t := hs.1
    linarith
  have hAccessibleInternal : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → ∀ U : Set ℝ, IsOpen U → t ∈ U →
        ∃ p ∈ f '' (U ∩ I), StronglyAccessible (f '' I)ᶜ p := by
    intro f hf hi t ht U hU htU
    have htI : t ∈ I := ⟨ht.1.le, ht.2.le⟩
    obtain ⟨r, hr, hrsub⟩ := exists_ball_inter_subset_image hf hi hU
      (show f t ∈ f '' (U ∩ I) from ⟨t, ⟨htU, htI⟩, rfl⟩)
    obtain ⟨q, hqball, hq⟩ := Set.not_subset.mp
      (hNoBall hf hi ht (show 0 < r / 3 by linarith))
    have hcompact : IsCompact (f '' I) := isCompact_I.image_of_continuousOn hf
    obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn
      (show (f '' I).Nonempty from ⟨f t, t, htI, rfl⟩)
      (Continuous.continuousOn (continuous_const.dist continuous_id : Continuous (fun z : Plane => dist q z)))
    have hnear : ∀ z ∈ f '' I, dist q p ≤ dist q z := fun z hz => isMinOn_iff.mp hmin z hz
    have hpball : p ∈ ball (f t) r := by
      have hdist : dist q (f t) < r / 3 := hqball
      have hle := hnear (f t) ⟨t, htI, rfl⟩
      have htri := dist_triangle p q (f t)
      rw [dist_comm p q] at htri
      change dist p (f t) < r
      linarith
    exact ⟨p, hrsub ⟨hpball, hp⟩,
      stronglyAccessible_of_isMinOn hq hp hnear (connectedComponentIn_subset _ _)⟩
  have hInternalSplit : ∀ {f : ℝ → Plane}, ContinuousOn f I → InjOn f I →
      ∀ {l s t r : ℝ}, 0 ≤ l → l < s → s < t → t < r → r ≤ 1 →
      ∃ u v : ℝ, u ∈ Ioo l s ∧ v ∈ Ioo t r ∧
        ∃ A : Set Plane, IsArcBetween A (f u) (f v) ∧
          A ∩ (f '' I) = {f u, f v} ∧
          IsJordanCurve (A ∪ (f '' Icc u v)) := by
    intro f hf hi l s t r hl hls hst htr hr
    obtain ⟨p, ⟨u, hu, rfl⟩, hpu⟩ := hAccessibleInternal hf hi
      (show (l+s)/2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (Ioo l s) isOpen_Ioo ⟨by linarith, by linarith⟩
    obtain ⟨q, ⟨v, hv, rfl⟩, hpv⟩ := hAccessibleInternal hf hi
      (show (t+r)/2 ∈ Ioo (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
      (Ioo t r) isOpen_Ioo ⟨by linarith, by linarith⟩
    have huv : u < v := hu.1.2.trans (hst.trans hv.1.1)
    have hne : f u ≠ f v := fun h => (ne_of_lt huv) (hi hu.2 hv.2 h)
    have hAccU : PolyAccessible (f '' I)ᶜ (f u) := by
      obtain ⟨z, hz, _, hseg⟩ := hpu.openSegment_subset
      exact PolyAccessible.of_openSegment hz hseg
    have hAccV : PolyAccessible (f '' I)ᶜ (f v) := by
      obtain ⟨z, hz, _, hseg⟩ := hpv.openSegment_subset
      exact PolyAccessible.of_openSegment hz hseg
    have hArc : IsArc (f '' I) := ⟨f, hf, hi, rfl⟩
    obtain ⟨A, _, hA, havoid⟩ := exists_simple_arc_of_polyAccessible
      hArc.isClosed.isOpen_compl (arc_complement hArc).isPreconnected hne hAccU hAccV
    have hmeet : A ∩ (f '' I) = {f u, f v} := by
      apply Subset.antisymm
      · intro z hz
        by_contra h
        exact havoid ⟨hz.1, h⟩ hz.2
      · rintro z (rfl | rfl)
        · exact ⟨hA.left_mem, u, hu.2, rfl⟩
        · exact ⟨hA.right_mem, v, hv.2, rfl⟩
    have hSubarc : IsArcBetween (f '' Icc u v) (f u) (f v) := by
      simpa [uIcc_of_le huv.le] using
        isArcBetween_subarc_of_injOn_I hf hi hu.2 hv.2 (ne_of_lt huv)
    refine ⟨u, v, hu.1, hv.1, A, hA, hmeet,
      IsJordanCurve.of_two_arcs hA hSubarc.reverse ?_⟩
    intro z hzA hzS
    have hzI : z ∈ f '' I := image_mono
      (show Icc u v ⊆ I from fun r hr => ⟨hu.2.1.trans hr.1, hr.2.trans hv.2.2⟩) hzS
    have : z ∈ ({f u, f v} : Set Plane) := hmeet ▸ ⟨hzA, hzI⟩
    simpa using this
  obtain ⟨u, v, hu, hv, A, hA, hmeet, hJ⟩ := hInternalSplit hf hi hl hls hst htr hr
  have huI : u ∈ I := ⟨(hl.trans_lt hu.1).le, (hu.2.trans (hst.trans ht)).le⟩
  have hvI : v ∈ I := ⟨(hs.trans (hst.trans hv.1)).le, (hv.2.trans_le hr).le⟩
  have huv : u < v := hu.2.trans (hst.trans hv.1)
  let P := f '' Icc u v
  let R := f '' Icc 0 u ∪ f '' Icc v 1
  let D := O \ R
  have hP : IsArcBetween P (f u) (f v) := by
    simpa [P, uIcc_of_le huv.le] using
      isArcBetween_subarc_of_injOn_I hf hi huI hvI (ne_of_lt huv)
  have hRI : R ⊆ f '' I := by
    rintro z (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨r, ⟨hr.1, hr.2.trans huI.2⟩, rfl⟩
    · exact ⟨r, ⟨hvI.1.trans hr.1, hr.2⟩, rfl⟩
  have hPI : P ⊆ f '' I := image_mono (fun r hr => ⟨huI.1.trans hr.1, hr.2.trans hvI.2⟩)
  have hRc : IsClosed R := by
    apply IsClosed.union
    · exact (isCompact_Icc.image_of_continuousOn
        (hf.mono (fun r hr => ⟨hr.1, hr.2.trans huI.2⟩))).isClosed
    · exact (isCompact_Icc.image_of_continuousOn
        (hf.mono (fun r hr => ⟨hvI.1.trans hr.1, hr.2⟩))).isClosed
  have hD : IsOpen D := hO.sdiff hRc
  have huD : f u ∉ D := fun h => h.2 (Or.inl ⟨u, ⟨huI.1, le_rfl⟩, rfl⟩)
  have hvD : f v ∉ D := fun h => h.2 (Or.inr ⟨v, ⟨le_rfl, hvI.2⟩, rfl⟩)
  have hPD : P \ {f u, f v} ⊆ D := by
    rintro z ⟨⟨r, hr, rfl⟩, hne⟩
    refine ⟨hfO ⟨r, ⟨hu.1.le.trans hr.1, hr.2.trans hv.2.le⟩, rfl⟩, ?_⟩
    rintro (⟨q, hq, heq⟩ | ⟨q, hq, heq⟩)
    · have hqr := hi ⟨hq.1, hq.2.trans huI.2⟩
        ⟨huI.1.trans hr.1, hr.2.trans hvI.2⟩ heq
      have hru : r = u := le_antisymm (hqr ▸ hq.2) hr.1
      exact hne (by simp [hru])
    · have hqr := hi ⟨hvI.1.trans hq.1, hq.2⟩
        ⟨huI.1.trans hr.1, hr.2.trans hvI.2⟩ heq
      have hrv : r = v := le_antisymm hr.2 (hqr ▸ hq.1)
      exact hne (by simp [hrv])
  have hmeetP : A ∩ P = {f u, f v} := by
    apply Subset.antisymm
    · intro z hz
      exact hmeet ▸ ⟨hz.1, hPI hz.2⟩
    · rintro z (rfl | rfl)
      · exact ⟨hA.left_mem, hP.left_mem⟩
      · exact ⟨hA.right_mem, hP.right_mem⟩
  have hcollars := hasArcCollars_of_jordan_arc_split hD hA hP hmeetP hJ huD hvD hPD
  have hK : f '' Icc s t ⊆ D ∩ P := by
    rintro z ⟨r, hr, rfl⟩
    have hrP : f r ∈ P := ⟨r, ⟨hu.2.le.trans hr.1, hr.2.trans hv.1.le⟩, rfl⟩
    refine ⟨hPD ⟨hrP, ?_⟩, hrP⟩
    have hrI : r ∈ I := ⟨hs.le.trans hr.1, hr.2.trans ht.le⟩
    rintro (heq | heq)
    · have := hi hrI huI heq
      linarith [hr.1, hu.2]
    · have := hi hrI hvI heq
      linarith [hr.2, hv.1]
  have hcK : IsCompact (f '' Icc s t) := isCompact_Icc.image_of_continuousOn
    (hf.mono (fun r hr => ⟨hs.le.trans hr.1, hr.2.trans ht.le⟩))
  have hpK : IsPreconnected (f '' Icc s t) := isPreconnected_Icc.image f
    (hf.mono (fun r hr => ⟨hs.le.trans hr.1, hr.2.trans ht.le⟩))
  have hnK : (f '' Icc s t).Nontrivial := by
    refine ⟨f s, ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩,
      f t, ⟨t, ⟨hst.le, le_rfl⟩, rfl⟩, ?_⟩
    exact fun h => (ne_of_lt hst) (hi ⟨hs.le, (hst.trans ht).le⟩ ⟨(hs.trans hst).le, ht.le⟩ h)
  obtain ⟨C⟩ := hcollars _ hK hcK hpK hnK
  refine ⟨{ C with nbhd_subset := fun z hz => (C.nbhd_subset hz).1, nbhd_diff := ?_ }⟩
  rw [← C.nbhd_diff]
  ext z
  constructor
  · exact fun hz => ⟨hz.1, fun hzP => hz.2 (hPI hzP)⟩
  · rintro ⟨hz, hzP⟩
    refine ⟨hz, ?_⟩
    rintro ⟨r, hr, rfl⟩
    by_cases hru : r < u
    · exact (C.nbhd_subset hz).2 (Or.inl ⟨r, ⟨hr.1, hru.le⟩, rfl⟩)
    by_cases hrv : v < r
    · exact (C.nbhd_subset hz).2 (Or.inr ⟨r, ⟨hrv.le, hr.2⟩, rfl⟩)
    exact hzP ⟨r, ⟨not_lt.mp hru, not_lt.mp hrv⟩, rfl⟩
end Schoenflies
#print axioms Schoenflies.internal_collar_avoiding_full_arc

namespace Schoenflies
/-- Arbitrarily small collars near the endpoint, still avoiding the entire arc. -/
theorem endpoint_small_internal_collars
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ T < 1 ∧ ∀ s t : ℝ, 0 < s → s < t → t < T →
      Nonempty (ArcCollar (ball (f 0) ε) (f '' I) (f '' Icc s t)) := by
  obtain ⟨r, hr, hball⟩ := Metric.continuousWithinAt_iff.mp (hf 0 (by simp)) ε hε
  let T : ℝ := min r 1 / 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hTr : T < r := by dsimp [T]; have := min_le_left r (1 : ℝ); linarith
  have hT1 : T < 1 := by dsimp [T]; have := min_le_right r (1 : ℝ); linarith
  refine ⟨T, hT, hT1, ?_⟩
  intro s t hs hst ht
  apply internal_collar_avoiding_full_arc hf hi (le_refl 0) hs hst ht hT1.le isOpen_ball
  rintro z ⟨u, hu, rfl⟩
  apply hball ⟨hu.1, hu.2.trans hT1.le⟩
  simpa [Real.dist_eq, abs_of_nonneg hu.1] using hu.2.trans_lt hTr

/-- A connected track approaching a common core point meets a track of the next collar.
No arbitrary global choices of left/right orientation are required. -/
theorem collar_track_transition
    {D P K S : Set Plane} (C : ArcCollar D P K) {p : Plane}
    (hp : p ∈ K) (hclose : p ∈ closure S) (havoid : S ⊆ Pᶜ) :
    (S ∩ C.left).Nonempty ∨ (S ∩ C.right).Nonempty := by
  obtain ⟨z, hzN, hzS⟩ := mem_closure_iff.mp hclose C.nbhd C.isOpen_nbhd (C.subset_nbhd hp)
  have hz : z ∈ C.nbhd \ P := ⟨hzN, havoid hzS⟩
  rw [C.nbhd_diff] at hz
  rcases hz with hz | hz
  · exact Or.inl ⟨z, hzS, hz⟩
  · exact Or.inr ⟨z, hzS, hz⟩
end Schoenflies
#print axioms Schoenflies.endpoint_small_internal_collars
#print axioms Schoenflies.collar_track_transition
namespace Schoenflies
/-- Compatible connected tracks can be chosen along any overlapping collar chain.
Each chosen track retains the size bound of its own collar. -/
theorem exists_compatible_collar_tracks
    {P : Set Plane} {D K : ℕ → Set Plane}
    (C : ∀ n, ArcCollar (D n) P (K n))
    (hover : ∀ n, (K n ∩ K (n+1)).Nonempty) :
    ∃ S : ℕ → Set Plane,
      (∀ n, IsConnected (S n) ∧ S n ⊆ D n \ P ∧ K n ⊆ closure (S n)) ∧
      ∀ n, (S n ∩ S (n+1)).Nonempty := by
  classical
  let T := fun n => {S : Set Plane // IsConnected S ∧ S ⊆ D n \ P ∧ K n ⊆ closure S}
  have hleft (n : ℕ) : IsConnected (C n).left ∧
      (C n).left ⊆ D n \ P ∧ K n ⊆ closure (C n).left :=
    ⟨(C n).isConnected_left, (C n).left_subset_diff, (C n).subset_closure_left⟩
  have hright (n : ℕ) : IsConnected (C n).right ∧
      (C n).right ⊆ D n \ P ∧ K n ⊆ closure (C n).right :=
    ⟨(C n).isConnected_right, (C n).right_subset_diff, (C n).subset_closure_right⟩
  have hnext : ∀ n, ∀ a : T n, ∃ b : T (n+1), ((a : Set Plane) ∩ (b : Set Plane)).Nonempty := by
    intro n a
    obtain ⟨p, hp, hp'⟩ := hover n
    have ha : (a : Set Plane) ⊆ Pᶜ := fun z hz => (a.property.2.1 hz).2
    rcases collar_track_transition (C (n+1)) hp' (a.property.2.2 hp) ha with h | h
    · exact ⟨⟨(C (n+1)).left, hleft (n+1)⟩, h⟩
    · exact ⟨⟨(C (n+1)).right, hright (n+1)⟩, h⟩
  let next := fun n (a : T n) => Classical.choose (hnext n a)
  let seq : ∀ n, T n := fun n => Nat.rec ⟨(C 0).left, hleft 0⟩ next n
  refine ⟨fun n => (seq n).val, fun n => (seq n).property, ?_⟩
  intro n
  exact Classical.choose_spec (hnext n (seq n))
end Schoenflies
#print axioms Schoenflies.exists_compatible_collar_tracks
namespace Schoenflies
/-- An actual compatible shrinking chain of connected complementary tracks.
This does not assert an injective limiting curve. -/
theorem endpoint_compatible_small_tracks
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I) :
    ∃ t : ℕ → ℝ, ∃ S : ℕ → Set Plane,
      (∀ n, 0 < t n ∧ t (n+1) < t n) ∧
      (∀ n, IsConnected (S n) ∧
        S n ⊆ ball (f 0) (1 / ((n : ℝ) + 1)) \ (f '' I) ∧
        f '' Icc (t (n+2)) (t n) ⊆ closure (S n)) ∧
      ∀ n, (S n ∩ S (n+1)).Nonempty := by
  classical
  have hex (n : ℕ) := endpoint_small_internal_collars hf hi
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  let T := fun n => Classical.choose (hex n)
  have hT (n : ℕ) : 0 < T n ∧ T n < 1 ∧ ∀ s t : ℝ,
      0 < s → s < t → t < T n →
      Nonempty (ArcCollar (ball (f 0) (1 / ((n : ℝ)+1))) (f '' I) (f '' Icc s t)) :=
    Classical.choose_spec (hex n)
  let t : ℕ → ℝ := Nat.rec (T 0 / 2) (fun n a => min (a / 2) (T (n+1) / 2))
  have ht (n : ℕ) : 0 < t n ∧ t n < T n := by
    induction n with
    | zero => dsimp [t]; constructor <;> linarith [(hT 0).1]
    | succ n ih =>
      change 0 < min (t n / 2) (T (n+1) / 2) ∧ min (t n / 2) (T (n+1) / 2) < T (n+1)
      constructor
      · exact lt_min (by linarith [ih.1]) (by linarith [(hT (n+1)).1])
      · exact (min_le_right _ _).trans_lt (by linarith [(hT (n+1)).1])
  have hdec (n : ℕ) : t (n+1) < t n := by
    change min (t n / 2) (T (n+1) / 2) < t n
    exact (min_le_left _ _).trans_lt (by linarith [(ht n).1])
  have hC (n : ℕ) : Nonempty (ArcCollar (ball (f 0) (1 / ((n : ℝ)+1)))
      (f '' I) (f '' Icc (t (n+2)) (t n))) :=
    (hT n).2.2 _ _ (ht (n+2)).1 ((hdec (n+1)).trans (hdec n)) (ht n).2
  let C := fun n => Classical.choice (hC n)
  have hover (n : ℕ) : (f '' Icc (t (n+2)) (t n) ∩
      f '' Icc (t ((n+1)+2)) (t (n+1))).Nonempty := by
    refine ⟨f (t (n+1)), ⟨t (n+1), ⟨(hdec (n+1)).le, (hdec n).le⟩, rfl⟩,
      t (n+1), ⟨?_, le_rfl⟩, rfl⟩
    exact ((hdec (n+2)).trans (hdec (n+1))).le
  obtain ⟨S, hS, hmeet⟩ := exists_compatible_collar_tracks C hover
  exact ⟨t, S, fun n => ⟨(ht n).1, hdec n⟩, hS, hmeet⟩
end Schoenflies
#print axioms Schoenflies.endpoint_compatible_small_tracks
namespace Schoenflies
/-- Open connected complementary regions with consecutive overlap and radii tending to zero. -/
theorem endpoint_compatible_open_regions
    {f : ℝ → Plane} (hf : ContinuousOn f I) (hi : InjOn f I) :
    ∃ U : ℕ → Set Plane,
      (∀ n, IsOpen (U n) ∧ IsConnected (U n) ∧
        U n ⊆ ball (f 0) (1 / ((n : ℝ) + 1)) \ (f '' I)) ∧
      ∀ n, (U n ∩ U (n+1)).Nonempty := by
  classical
  obtain ⟨t, S, _, hS, hinter⟩ := endpoint_compatible_small_tracks hf hi
  let z := fun n => (hS n).1.nonempty.some
  have hz (n : ℕ) : z n ∈ S n := (hS n).1.nonempty.some_mem
  let D := fun (n : ℕ) => ball (f 0) (1 / ((n : ℝ)+1)) \ (f '' I)
  let U := fun n => connectedComponentIn (D n) (z n)
  have hSU (n : ℕ) : S n ⊆ U n :=
    (hS n).1.isPreconnected.subset_connectedComponentIn (hz n) (hS n).2.1
  have hc : IsClosed (f '' I) := (isCompact_I.image_of_continuousOn hf).isClosed
  refine ⟨U, ?_, ?_⟩
  · intro n
    refine ⟨(isOpen_ball.sdiff hc).connectedComponentIn, ?_, connectedComponentIn_subset _ _⟩
    exact isConnected_connectedComponentIn_iff.mpr ((hS n).2.1 (hz n))
  · intro n
    obtain ⟨p, hp, hp'⟩ := hinter n
    exact ⟨p, hSU n hp, hSU (n+1) hp'⟩
end Schoenflies
#print axioms Schoenflies.endpoint_compatible_open_regions
