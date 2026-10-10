import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Homotopy.Lifting

namespace CurveComplex

open Topology

/-- A nullhomotopic map has a lift through any covering map with a point above
its contraction point. This uses the covering homotopy lifting property. -/
theorem exists_lift_of_nullhomotopic
    {A S E : Type*} [TopologicalSpace A]
    [TopologicalSpace S] [TopologicalSpace E]
    (p : E → S) (hp : IsCoveringMap p)
    (f : C(A, S)) (hf : f.Nullhomotopic)
    (hsurj : Function.Surjective p) :
    ∃ g : C(A, E), (⟨p, hp.continuous⟩ : C(E, S)).comp g = f := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  obtain ⟨e, he⟩ := hsurj x
  let R := H.symm
  let g₀ : C(A, E) := ContinuousMap.const A e
  have hzero : ∀ a : A, R (0, a) = p (g₀ a) := by
    intro a
    calc
      R (0, a) = x := R.apply_zero a
      _ = p e := he.symm
      _ = p (g₀ a) := rfl
  let K := hp.liftHomotopy R g₀ hzero
  let g : C(A, E) := ⟨fun a => K (1, a),
    K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨g, ?_⟩
  ext a
  have hK := congrFun (hp.liftHomotopy_lifts R g₀ hzero) (1, a)
  exact hK.trans (R.apply_one a)

/-- A nullhomotopy of a map lifts through a covering map once its initial map
has a lift. Connectedness of the domain makes the lifted endpoint constant. -/
theorem nullhomotopic_lift_of_covering
    {A S E : Type*} [TopologicalSpace A] [PreconnectedSpace A] [Nonempty A]
    [TopologicalSpace S] [TopologicalSpace E]
    (p : E → S) (hp : IsCoveringMap p)
    (f : C(A, S)) (g : C(A, E))
    (hpg : (⟨p, hp.continuous⟩ : C(E, S)).comp g = f)
    (hf : f.Nullhomotopic) : g.Nullhomotopic := by
  obtain ⟨x, ⟨H⟩⟩ := hf
  have hzero : ∀ a : A, H (0, a) = p (g a) := by
    intro a
    calc
      H (0, a) = f a := H.apply_zero a
      _ = p (g a) := by
        exact (congrFun (congrArg DFunLike.coe hpg) a).symm
  let K := hp.liftHomotopy H g hzero
  let y : E := K (1, Classical.arbitrary A)
  have hend : ∀ a : A, K (1, a) = y := by
    intro a
    have hconst : ∀ a b : A, p (K (1, a)) = p (K (1, b)) := by
      intro a b
      have ha := congrFun (hp.liftHomotopy_lifts H g hzero) (1, a)
      have hb := congrFun (hp.liftHomotopy_lifts H g hzero) (1, b)
      calc
        p (K (1, a)) = H (1, a) := ha
        _ = x := H.map_one_left a
        _ = H (1, b) := (H.map_one_left b).symm
        _ = p (K (1, b)) := hb.symm
    exact hp.const_of_comp
      (K.continuous.comp (continuous_const.prodMk continuous_id))
      hconst a (Classical.arbitrary A)
  refine ⟨y, ⟨{
    toContinuousMap := K
    map_zero_left := hp.liftHomotopy_zero H g hzero
    map_one_left := hend
  }⟩⟩

/-- A nullhomotopic simple closed curve lifts to a simple closed curve in a
surjective cover. The lifted curve is also nullhomotopic. -/
theorem exists_embedded_nullhomotopic_lift_of_covering
    {S E : Type*} [TopologicalSpace S] [TopologicalSpace E]
    (p : E → S) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (c : Curve S)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic) :
    ∃ g : C(Circle, E),
      (⟨p, hp.continuous⟩ : C(E, S)).comp g =
        (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)) ∧
      IsEmbedding g ∧ g.Nullhomotopic := by
  let f : C(Circle, S) := ⟨c.map, c.embedded.continuous⟩
  obtain ⟨g, hpg⟩ := exists_lift_of_nullhomotopic p hp f hc hsurj
  have hg : IsEmbedding g := by
    apply IsEmbedding.of_comp g.continuous hp.continuous
    have hfun : p ∘ (g : Circle → E) = c.map := by
      funext z
      exact congrArg (fun m : C(Circle, S) => m z) hpg
    change IsEmbedding (p ∘ (g : Circle → E))
    rw [hfun]
    exact c.embedded
  exact ⟨g, hpg, hg, nullhomotopic_lift_of_covering p hp f g hpg hc⟩

/-- Project an embedded disc through a continuous map when its projection is
injective on the disc. This isolates the exact descent condition needed after
constructing a disc in a universal cover. -/
theorem boundsDisc_of_injective_projected_lift
    {S E : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace E]
    (c : Curve S) (p : C(E, S))
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E))
    (hd : IsEmbedding d)
    (hproj : Set.InjOn p (Set.range d))
    (hboundary : (p.comp d) ''
      {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = c.image) :
    BoundsDisc c := by
  have hinj : Function.Injective (p.comp d) := by
    intro x y hxy
    apply hd.injective
    apply hproj ⟨x, rfl⟩ ⟨y, rfl⟩
    exact hxy
  refine ⟨p.comp d, ?_, hboundary⟩
  exact ((p.comp d).continuous.isClosedEmbedding hinj).isEmbedding

/-- A compact disc whose boundary is a lifted curve descends to a disc in the
base if the covering projection does not identify points of that disc. -/
theorem boundsDisc_of_covering_disc
    {S E : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace E]
    (c : Curve S) (p : E → S) (hp : IsCoveringMap p)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E))
    (hd : IsEmbedding d)
    (hproj : Set.InjOn p (Set.range d))
    (hboundary : ((⟨p, hp.continuous⟩ : C(E, S)).comp d) ''
      {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = c.image) :
    BoundsDisc c :=
  boundsDisc_of_injective_projected_lift c ⟨p, hp.continuous⟩ d hd hproj hboundary

/-- The exact cover-to-base transfer for a nullhomotopic embedded curve.
Planar Schoenflies must supply `d` for the lifted curve; geometric deck-action
control must supply `hproj`. Neither follows from covering-map lifting alone. -/
theorem boundsDisc_of_lifted_disc_and_projection_injective
    {S E : Type*} [TopologicalSpace S] [T2Space S] [TopologicalSpace E]
    (p : E → S) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (c : Curve S)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)).Nullhomotopic)
    (hgeometry : ∀ g : C(Circle, E),
      (⟨p, hp.continuous⟩ : C(E, S)).comp g =
        (⟨c.map, c.embedded.continuous⟩ : C(Circle, S)) →
      IsEmbedding g →
      ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E),
        IsEmbedding d ∧
        d '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = Set.range g ∧
        Set.InjOn p (Set.range d)) :
    BoundsDisc c := by
  obtain ⟨g, hpg, hg, _⟩ :=
    exists_embedded_nullhomotopic_lift_of_covering p hp hsurj c hc
  obtain ⟨d, hd, hbd, hproj⟩ := hgeometry g hpg hg
  apply boundsDisc_of_covering_disc c p hp d hd hproj
  rw [ContinuousMap.coe_comp, Set.image_comp, hbd]
  have hrange : p '' Set.range g = c.image := by
    have hfun : p ∘ (g : Circle → E) = c.map := by
      funext z
      exact congrArg (fun m : C(Circle, S) => m z) hpg
    rw [← Set.range_comp]
    rw [hfun]
    rfl
  exact hrange

end CurveComplex
