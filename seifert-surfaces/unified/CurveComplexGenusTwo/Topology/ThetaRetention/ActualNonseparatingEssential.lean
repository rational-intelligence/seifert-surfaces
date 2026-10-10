import CurveComplexGenusTwo.Topology.ThetaRetention.ActualNonseparatingMinimalPosition
import ClassificationOfSurfaces.Moise.Brouwer

namespace CurveComplex
open Set Topology
open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

/-- A genuine embedded curve with connected complement on a closed surface
cannot bound a disk. No hyperelliptic model or essentiality premise is used. -/
theorem source_nonseparating_curve_essential
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (hns : Nonseparating c) : Essential c := by
  have hconn : IsConnected c.imageᶜ := hns
  classical
  intro hc
  obtain ⟨f, hf, hboundary⟩ := hc
  let P := EuclideanSpace ℝ (Fin 2)
  let B := Metric.closedBall (0 : P) 1
  let O := Metric.ball (0 : P) 1
  let A : Set B := {x | (x : P) ∈ O}
  let C : Set B := {x | (x : P) ∈ Metric.sphere (0 : P) 1}
  have hfnot : ¬ Function.Surjective f := by
    intro hsurj
    let h : B ≃ₜ S := IsHomeomorph.homeomorph f
      (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hf, hsurj⟩)
    obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := P).mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
    let pB : B := ⟨p, Metric.sphere_subset_closedBall hp⟩
    let e := chartAt P (h pB)
    let g : e.target → P := fun y => (h.symm (e.symm y) : P)
    have hgcont : Continuous g := continuous_subtype_val.comp
      (h.symm.continuous.comp
        (e.symm.continuousOn.comp_continuous continuous_subtype_val
          (fun y => y.property)))
    have hginj : Function.Injective g := by
      intro y z hyz
      have hhs : h.symm (e.symm y) = h.symm (e.symm z) := Subtype.ext hyz
      exact Subtype.ext (e.symm.injOn y.property z.property (h.symm.injective hhs))
    have hopen : IsOpen (Set.range g) :=
      isOpen_range_of_isOpen_of_continuous_injective
        (modelWithCornersSelf ℝ P) e.open_target g hgcont hginj
    have hpim : p ∈ Set.range g := by
      refine ⟨⟨e (h pB), e.map_source (mem_chart_source P (h pB))⟩, ?_⟩
      dsimp [g]
      rw [e.left_inv (mem_chart_source P (h pB)), h.symm_apply_apply]
    have hsub : Set.range g ⊆ B := by
      rintro _ ⟨y, rfl⟩
      exact (h.symm (e.symm y)).property
    have hpint : p ∈ interior B := (hopen.subset_interior_iff.mpr hsub) hpim
    rw [interior_closedBall (0 : P) (by norm_num : (1 : ℝ) ≠ 0)] at hpint
    exact (ne_of_lt hpint) hp
  simp only [Function.Surjective, not_forall, not_exists] at hfnot
  obtain ⟨x, hx⟩ := hfnot
  have hnV : (Set.range f)ᶜ.Nonempty := ⟨x, by rintro ⟨y, hy⟩; exact hx y hy⟩
  have hopenV : IsOpen (Set.range f)ᶜ :=
    (isCompact_range f.continuous).isClosed.isOpen_compl
  let g : O → S := fun x => f ⟨x, Metric.ball_subset_closedBall x.property⟩
  have hgcont : Continuous g := f.continuous.comp
    (continuous_subtype_val.subtype_mk _)
  have hginj : Function.Injective g := by
    intro x y hxy
    have heq : (⟨x, Metric.ball_subset_closedBall x.property⟩ : B) =
        ⟨y, Metric.ball_subset_closedBall y.property⟩ := hf.injective hxy
    exact Subtype.ext (congrArg (fun z : B => (z : P)) heq)
  have hgim : Set.range g = f '' A := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Metric.ball_subset_closedBall x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hopenU : IsOpen (f '' A) := by
    rw [← hgim]
    exact isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersSelf ℝ P) Metric.isOpen_ball g hgcont hginj
  have hnU : (f '' A).Nonempty := by
    refine ⟨f ⟨0, by simp⟩, ⟨0, by simp⟩, ?_, rfl⟩
    change dist (0 : P) 0 < 1
    simp
  have hdisj : Disjoint (f '' A) (Set.range f)ᶜ := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hx
    exact hx ⟨y, rfl⟩
  have hUc : f '' A ⊆ c.imageᶜ := by
    rintro _ ⟨y, hy, rfl⟩ hcy
    rw [← hboundary] at hcy
    obtain ⟨z, hz, hfz⟩ := hcy
    have hzy : z = y := hf.injective hfz
    subst z
    exact (ne_of_lt hy) hz
  have hVc : (Set.range f)ᶜ ⊆ c.imageᶜ := by
    intro y hy hcy
    rw [← hboundary] at hcy
    obtain ⟨z, hz, hfz⟩ := hcy
    exact hy ⟨z, hfz⟩
  have hcover : c.imageᶜ ⊆ f '' A ∪ (Set.range f)ᶜ := by
    intro y hy
    by_cases hr : y ∈ Set.range f
    · obtain ⟨z, rfl⟩ := hr
      left
      refine ⟨z, ?_, rfl⟩
      have hne : (z : P) ∉ Metric.sphere (0 : P) 1 := by
        intro hz
        exact hy (hboundary ▸ Set.mem_image_of_mem f hz)
      have hzle := z.property
      change dist (z : P) 0 ≤ 1 at hzle
      change dist (z : P) 0 < 1
      exact lt_of_le_of_ne hzle hne
    · exact Or.inr hr
  rcases hconn.isPreconnected.subset_or_subset hopenU hopenV hdisj hcover with h | h
  · obtain ⟨x, hx⟩ := hnV
    exact Set.disjoint_left.mp hdisj (h (hVc hx)) hx
  · obtain ⟨x, hx⟩ := hnU
    exact Set.disjoint_left.mp hdisj hx (h (hUc hx))


end CurveComplex

#print axioms CurveComplex.source_nonseparating_curve_essential
