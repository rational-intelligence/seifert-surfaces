import ClassificationOfSurfaces.Topology.InvarianceOfDomain
import Schoenflies.JordanClosed
import Mathlib.Analysis.Normed.Module.Connected

set_option maxHeartbeats 1000000

namespace CurveComplex

open Set Topology
open Metric
open Bornology

private abbrev Plane := Schoenflies.Plane
private abbrev UnitDisc := Metric.closedBall (0 : Plane) 1
private def DiscInterior : Set UnitDisc :=
  {x | (x : Plane) ∈ Metric.ball 0 1}
private def DiscBoundary : Set UnitDisc :=
  {x | (x : Plane) ∈ Metric.sphere 0 1}

/-- The image of the open part of an embedded disc is open in the plane.
This is the exact invariance-of-domain point needed for region recognition. -/
theorem embedded_disc_interior_isOpen
    [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane]
    (d : C(UnitDisc, Plane)) (hd : IsEmbedding d) :
    IsOpen (d '' DiscInterior) := by
  classical
  let f : Plane → Plane := fun x =>
    if h : x ∈ Metric.closedBall 0 1 then d ⟨x, h⟩ else 0
  have hf_eq : ∀ (x : Plane) (hx : x ∈ Metric.ball 0 1),
      f x = d ⟨x, Metric.ball_subset_closedBall hx⟩ := by
    intro x hx
    dsimp [f]
    rw [dite_eq_left (Metric.ball_subset_closedBall hx)]
  have hf_cont : ContinuousOn f (Metric.ball (0 : Plane) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : Metric.ball (0 : Plane) 1 → UnitDisc :=
      fun x => ⟨x, Metric.ball_subset_closedBall x.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hcont : Continuous (fun x : Metric.ball (0 : Plane) 1 => d (j x)) :=
      d.continuous.comp hj
    have heq : (Metric.ball (0 : Plane) 1).domRestrict f =
        (fun x : Metric.ball (0 : Plane) 1 => d (j x)) := by
      funext x
      exact hf_eq x x.property
    rw [heq]
    exact hcont
  have hf_inj : Set.InjOn f (Metric.ball (0 : Plane) 1) := by
    intro x hx y hy hxy
    have hxy' : d (⟨x, Metric.ball_subset_closedBall hx⟩ : UnitDisc) =
        d (⟨y, Metric.ball_subset_closedBall hy⟩ : UnitDisc) := by
      simpa [hf_eq x hx, hf_eq y hy] using hxy
    exact congrArg Subtype.val (hd.injective hxy')
  have hopen :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
      f (Metric.ball (0 : Plane) 1)
      Metric.isOpen_ball hf_cont hf_inj
  convert hopen using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, by simpa [DiscInterior] using hf_eq x.val hx⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, Metric.ball_subset_closedBall hx⟩, hx, (hf_eq x hx).symm⟩

/-- A bounded component of the complement of a Jordan curve is its inside. -/
private theorem bounded_open_component_eq_inside
    (C U : Set Plane) (hC : Schoenflies.IsJordanCurve C)
    (hopen : IsOpen U) (hpre : IsPreconnected U) (hne : U.Nonempty)
    (hbounded : IsBounded U) (hsub : U ⊆ Cᶜ)
    (hfront : frontier U ⊆ C) :
    U = Schoenflies.inside C := by
  have hfr : frontier U ∩ Cᶜ = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
    exact fun hz => hz.2 (hfront hz.1)
  obtain ⟨x, hx⟩ := hne
  have hcompEq : connectedComponentIn Cᶜ x = U :=
    Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint
      hopen hpre hsub hfr hx
  have hsep := Schoenflies.jordan_curve_theorem hC
  have hxside : x ∈ Schoenflies.inside C ∨ x ∈ Schoenflies.outside C := by
    change x ∈ Schoenflies.inside C ∪ Schoenflies.outside C
    rw [Schoenflies.inside_union_outside]
    exact hsub hx
  rcases hxside with hxI | hxO
  · exact hcompEq.symm.trans (hsep.connectedComponentIn_eq_inside hxI)
  · have hout : Schoenflies.outside C = U :=
      (hsep.connectedComponentIn_eq_outside hxO).symm.trans hcompEq
    exact False.elim (hsep.not_isBounded_outside (hout ▸ hbounded))

/-- Region recognition for an embedded planar closed disc. Once invariance of
domain supplies openness of the interior image, compactness and connected
components identify the image with the bounded Jordan region plus boundary. -/
theorem embedded_disc_range_eq_closed_inside
    [LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint Plane]
    (d : C(UnitDisc, Plane)) (hd : IsEmbedding d)
    (C : Set Plane)
    (hC : Schoenflies.IsJordanCurve C)
    (hboundary : d '' DiscBoundary = C) :
    Set.range d = Schoenflies.inside C ∪ C := by
  classical
  have hcompact : IsCompact (Set.range d) :=
    by simpa only [Set.image_univ] using isCompact_univ.image d.continuous
  have hopen : IsOpen (d '' DiscInterior) := embedded_disc_interior_isOpen d hd
  have hsplit : Set.range d = d '' DiscInterior ∪ C := by
    rw [← hboundary]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      by_cases hx : (x : Plane) ∈ Metric.ball 0 1
      · exact Or.inl ⟨x, hx, rfl⟩
      · have hxs : (x : Plane) ∈ Metric.sphere 0 1 := by
          have hclosed : ‖(x : Plane)‖ ≤ 1 := by
            have hp := x.property
            change dist (x : Plane) 0 ≤ 1 at hp
            simpa [dist_zero_right] using hp
          rw [mem_sphere_zero_iff_norm]
          exact le_antisymm hclosed (le_of_not_gt (by simpa [Metric.mem_ball, dist_zero_right] using hx))
        exact Or.inr ⟨x, hxs, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, rfl⟩
      · exact ⟨x, rfl⟩
  have hinside_eq : Schoenflies.inside C = d '' DiscInterior := by
    have hpre : IsPreconnected (d '' DiscInterior) := by
      have hball : IsPreconnected (Metric.ball (0 : Plane) 1) :=
        Metric.isPreconnected_ball
      let j : Metric.ball (0 : Plane) 1 → UnitDisc :=
        fun x => ⟨x, Metric.ball_subset_closedBall x.property⟩
      have hj : Continuous j := continuous_subtype_val.subtype_mk _
      let g : Plane → Plane := fun x =>
        if h : x ∈ Metric.ball 0 1 then d (j ⟨x, h⟩) else 0
      have hg : ContinuousOn g (Metric.ball (0 : Plane) 1) := by
        rw [continuousOn_iff_continuous_domRestrict]
        convert d.continuous.comp hj using 1
        funext x
        change g (x : Plane) = d (j x)
        dsimp [g]
        rw [dite_eq_left x.property]
      have hImg : g '' Metric.ball (0 : Plane) 1 = d '' DiscInterior := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨j ⟨x, hx⟩, hx, by
            dsimp [g]
            rw [dite_eq_left hx]⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, by
            dsimp [g]
            have hx' : (x : Plane) ∈ Metric.ball 0 1 := hx
            rw [dite_eq_left hx']
            ⟩
      rw [← hImg]
      exact hball.image g hg
    have hcomp : d '' DiscInterior ⊆ Cᶜ := by
      intro z hz hzC
      rcases hz with ⟨x, hx, rfl⟩
      have hzbd : d x ∈ d '' DiscBoundary := by
        rw [hboundary]
        exact hzC
      rcases hzbd with ⟨y, hy, hxy⟩
      have hxy' : x = y := hd.injective hxy.symm
      have hxnorm : ‖(x : Plane)‖ < 1 := by
        simpa only [DiscInterior, Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right] using hx
      have hynorm : ‖(y : Plane)‖ = 1 := by
        simpa only [DiscBoundary, Set.mem_ofPred_eq, mem_sphere_zero_iff_norm] using hy
      have hval : (x : Plane) = (y : Plane) := congrArg Subtype.val hxy'
      rw [hval] at hxnorm
      linarith
    have hclosed : IsClosed (Set.range d) := hcompact.isClosed
    have hUsub : d '' DiscInterior ⊆ Set.range d := by
      rintro z ⟨x, hx, rfl⟩
      exact ⟨x, rfl⟩
    have hfront : frontier (d '' DiscInterior) ⊆ C := by
      intro z hz
      have hzcl : z ∈ closure (d '' DiscInterior) := hz.1
      have hzrange : z ∈ Set.range d := by
        have := closure_mono hUsub hzcl
        rwa [hclosed.closure_eq] at this
      rcases hsplit.subset hzrange with hzU | hzC
      · exact False.elim (hz.2 (by rwa [hopen.interior_eq]))
      · exact hzC
    have hboundedU : IsBounded (d '' DiscInterior) := by
      apply hcompact.isBounded.subset
      exact hUsub
    have hne : (d '' DiscInterior).Nonempty := by
      refine ⟨d ⟨0, ?_⟩, ⟨⟨0, ?_⟩, ?_, rfl⟩⟩
      all_goals simp [DiscInterior, Metric.mem_closedBall, Metric.mem_ball]
    exact (bounded_open_component_eq_inside C (d '' DiscInterior)
      hC hopen hpre hne hboundedU hcomp hfront).symm
  rw [hsplit, hinside_eq]

end CurveComplex
