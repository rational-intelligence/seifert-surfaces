import GeometricArea
import Mathlib.Topology.Constructions
import Mathlib.Logic.Relation

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology IsManifold
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

structure CyclicPolygon where
  count : ℕ
  count_ge_three : 3 ≤ count
  next : Equiv.Perm (Fin count)
  next_index : ∀ i, (next i).val = (i.val + 1) % count
  vertex : Fin count → Euc 3
  edges_nonzero : ∀ i, vertex (next i) ≠ vertex i

def polygonEdge (P : CyclicPolygon) (i : Fin P.count) (t : Time) : Euc 3 :=
  (1 - (t : ℝ)) • P.vertex i + (t : ℝ) • P.vertex (P.next i)
def polygonEndpointGlue (P : CyclicPolygon) (p q : Fin P.count × Time) : Prop :=
  p.2 = 1 ∧ q.2 = 0 ∧ q.1 = P.next p.1
def polygonSetoid (P : CyclicPolygon) : Setoid (Fin P.count × Time) :=
  Relation.EqvGen.setoid (polygonEndpointGlue P)
abbrev PolygonDomain (P : CyclicPolygon) := Quotient (polygonSetoid P)

theorem polygonEdge_respects (P : CyclicPolygon) :
    ∀ p q, (polygonSetoid P).r p q → polygonEdge P p.1 p.2 = polygonEdge P q.1 q.2 := by
  intro p q h
  induction h with
  | rel p q h =>
      rcases h with ⟨hp, hq, hi⟩
      simp [polygonEdge, hp, hq, hi]
  | refl p => rfl
  | symm p q h ih => exact ih.symm
  | trans p q r hpq hqr ihpq ihqr => exact ihpq.trans ihqr
def polygonMap (P : CyclicPolygon) : PolygonDomain P → Euc 3 :=
  Quotient.lift (fun p => polygonEdge P p.1 p.2) (polygonEdge_respects P)
theorem polygonDomain_circle_exists (P : CyclicPolygon) :
    ∃ e : Circle ≃ₜ PolygonDomain P, ∃ t₀ : ℝ,
      ∀ (i : Fin P.count) (s : Time),
        e (Circle.exp (t₀ + 2 * Real.pi * (i.val + (s : ℝ)) / P.count)) =
          Quotient.mk (polygonSetoid P) (i, s) := by
  classical
  have exp_eq_exp (x y : ℝ) : Circle.exp x = Circle.exp y ↔
      ∃ m : ℤ, x = y + m * (2 * Real.pi) := by
    rw [Circle.ext_iff, Circle.coe_exp, Circle.coe_exp,
      Complex.exp_eq_exp_iff_exists_int]
    refine exists_congr fun m => ?_
    rw [← mul_assoc, ← add_mul, mul_left_inj' Complex.I_ne_zero]
    norm_cast
  have exp_two_pi : Circle.exp (2 * Real.pi) = 1 := by
    apply Subtype.ext
    simp [Circle.coe_exp, Complex.exp_mul_I]
  have periodic_exp : Function.Periodic Circle.exp (2 * Real.pi) := by
    intro r
    rw [Circle.exp_add, exp_two_pi, mul_one]
  have exp_surjective : Function.Surjective Circle.exp := by
    intro z
    refine ⟨Complex.arg (z : ℂ), Subtype.ext ?_⟩
    simpa [Circle.coe_exp] using Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  have hn : 0 < P.count := lt_of_lt_of_le (by norm_num) P.count_ge_three
  have hnR : 0 < (P.count : ℝ) := by exact_mod_cast hn
  have hn0 : (P.count : ℝ) ≠ 0 := ne_of_gt hnR
  let c : Fin P.count × Time → ℝ := fun p => p.1.val + (p.2 : ℝ)
  have cbounds (p : Fin P.count × Time) : 0 ≤ c p ∧ c p ≤ P.count := by
    dsimp [c]
    have hi : (p.1.val : ℝ) + 1 ≤ P.count := by exact_mod_cast p.1.isLt
    constructor <;> nlinarith [p.2.property.1, p.2.property.2,
      Nat.cast_nonneg (α := ℝ) p.1.val]
  have glue (i j : Fin P.count) (s t : Time) (hs : s = 1) (ht : t = 0)
      (hnext : j = P.next i) :
      Quotient.mk (polygonSetoid P) (i, s) = Quotient.mk (polygonSetoid P) (j, t) := by
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨hs, ht, hnext⟩)
  have ceq (p q : Fin P.count × Time) (h : c p = c q) :
      Quotient.mk (polygonSetoid P) p = Quotient.mk (polygonSetoid P) q := by
    rcases p with ⟨i, s⟩
    rcases q with ⟨j, t⟩
    dsimp [c] at h
    have forward (i j : Fin P.count) (s t : Time)
        (hij : i.val < j.val) (h : (i.val : ℝ) + s = j.val + (t : ℝ)) :
        Quotient.mk (polygonSetoid P) (i, s) = Quotient.mk (polygonSetoid P) (j, t) := by
      have hijR : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
      have hs : s = 1 := Subtype.ext (by
        change (s : ℝ) = 1
        nlinarith [s.property.2, t.property.1])
      have ht : t = 0 := Subtype.ext (by
        change (t : ℝ) = 0
        nlinarith [s.property.2, t.property.1])
      have hij_eq : i.val + 1 = j.val := by
        have : (i.val : ℝ) + 1 = j.val := by simpa [hs, ht] using h
        exact_mod_cast this
      apply glue i j s t hs ht
      apply Fin.ext
      rw [P.next_index, hij_eq, Nat.mod_eq_of_lt j.isLt]
    rcases lt_trichotomy i.val j.val with hij | hij | hij
    · exact forward i j s t hij h
    · have hi : i = j := Fin.ext hij
      subst j
      have ht : s = t := Subtype.ext (by linarith)
      subst t
      rfl
    · exact (forward j i t s hij h.symm).symm
  have wrap (p q : Fin P.count × Time) (hp : c p = P.count) (hq : c q = 0) :
      Quotient.mk (polygonSetoid P) p = Quotient.mk (polygonSetoid P) q := by
    rcases p with ⟨i, s⟩
    rcases q with ⟨j, t⟩
    dsimp [c] at hp hq
    have hiR : (i.val : ℝ) + 1 ≤ P.count := by exact_mod_cast i.isLt
    have hs : s = 1 := Subtype.ext (by
      change (s : ℝ) = 1
      nlinarith [s.property.2])
    have ht : t = 0 := Subtype.ext (by
      change (t : ℝ) = 0
      nlinarith [t.property.1, Nat.cast_nonneg (α := ℝ) j.val])
    have hi : i.val + 1 = P.count := by
      have : (i.val : ℝ) + 1 = P.count := by simpa [hs] using hp
      exact_mod_cast this
    have hj : j.val = 0 := by
      have : (j.val : ℝ) = 0 := by simpa [ht] using hq
      exact_mod_cast this
    apply glue i j s t hs ht
    apply Fin.ext
    simp [P.next_index, hi, hj]
  let a : Fin P.count × Time → Circle := fun p => Circle.exp (2 * Real.pi * c p / P.count)
  have ha (p q : Fin P.count × Time) (h : (polygonSetoid P).r p q) : a p = a q := by
    induction h with
    | rel p q h =>
        rcases h with ⟨hp, hq, hi⟩
        dsimp [a, c]
        rw [hp, hq, hi]
        simp only [Set.Icc.coe_one, Set.Icc.coe_zero, add_zero, P.next_index]
        by_cases hnxt : p.1.val + 1 < P.count
        · rw [Nat.mod_eq_of_lt hnxt, Nat.cast_add, Nat.cast_one]
        · have hv : p.1.val + 1 = P.count := by omega
          have hvR : (p.1.val : ℝ) + 1 = P.count := by exact_mod_cast hv
          rw [hvR]
          simp [hv, hn0, exp_two_pi]
    | refl p => rfl
    | symm p q h ih => exact ih.symm
    | trans p q r hpq hqr ihpq ihqr => exact ihpq.trans ihqr
  have ainj (p q : Fin P.count × Time) (h : a p = a q) :
      Quotient.mk (polygonSetoid P) p = Quotient.mk (polygonSetoid P) q := by
    obtain ⟨m, hm⟩ := (exp_eq_exp _ _).mp h
    have heq : c p = c q + (m : ℝ) * P.count := by
      field_simp [hn0] at hm
      nlinarith [Real.pi_pos]
    obtain ⟨hp0, hpn⟩ := cbounds p
    obtain ⟨hq0, hqn⟩ := cbounds q
    rcases lt_trichotomy m 0 with hm | hm | hm
    · have hmI : m ≤ -1 := by omega
      have hmR : (m : ℝ) ≤ -1 := by exact_mod_cast hmI
      have hprod : (m : ℝ) * P.count ≤ -(P.count : ℝ) := by nlinarith
      have hp : c p = 0 := by nlinarith
      have hq : c q = P.count := by nlinarith
      exact (wrap q p hq hp).symm
    · subst m
      exact ceq p q (by simpa using heq)
    · have hmI : 1 ≤ m := by omega
      have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast hmI
      have hprod : (P.count : ℝ) ≤ (m : ℝ) * P.count := by nlinarith
      have hp : c p = P.count := by nlinarith
      have hq : c q = 0 := by nlinarith
      exact wrap p q hp hq
  let f : PolygonDomain P → Circle := Quotient.lift a ha
  have hf : Continuous f := by
    apply Continuous.quotient_lift
    dsimp [a, c]
    have hv : Continuous (fun p : Fin P.count × Time => (p.1.val : ℝ)) :=
      (continuous_of_discreteTopology : Continuous (fun i : Fin P.count => (i.val : ℝ))).comp
        continuous_fst
    exact Circle.exp.continuous.comp
      ((continuous_const.mul (hv.add (continuous_subtype_val.comp continuous_snd))).div_const _)
  have hfinj : Function.Injective f := by
    intro p q
    refine Quotient.inductionOn₂ p q ?_
    intro x y h
    exact ainj x y h
  have hsurj : Function.Surjective f := by
    intro z
    have hz : z ∈ Circle.exp '' Icc (0 : ℝ) (2 * Real.pi) := by
      rw [show Icc (0 : ℝ) (2 * Real.pi) = Icc 0 (0 + 2 * Real.pi) by simp,
        periodic_exp.image_Icc (by positivity), Set.mem_range]
      exact exp_surjective z
    obtain ⟨r, hr, hrz⟩ := hz
    let x : ℝ := r * P.count / (2 * Real.pi)
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (mul_nonneg hr.1 (Nat.cast_nonneg _)) (by positivity)
    have hxn : x ≤ P.count := by
      dsimp [x]
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hr.2]
    have preim (i : Fin P.count) (s : Time) (h : c (i, s) = x) :
        f (Quotient.mk (polygonSetoid P) (i, s)) = z := by
      change Circle.exp (2 * Real.pi * c (i, s) / P.count) = z
      rw [h]
      convert hrz using 1
      dsimp [x]
      field_simp [hn0]
    by_cases hx : x = P.count
    · let i : Fin P.count := ⟨P.count - 1, by omega⟩
      refine ⟨Quotient.mk (polygonSetoid P) (i, 1), preim i 1 ?_⟩
      dsimp [c, i]
      rw [hx]
      have hi : P.count - 1 + 1 = P.count := by omega
      exact_mod_cast hi
    · have hxlt : x < P.count := lt_of_le_of_ne hxn hx
      let i : Fin P.count := ⟨Nat.floor x, (Nat.floor_lt hx0).2 hxlt⟩
      let s : Time := ⟨x - (Nat.floor x : ℝ), by
        exact ⟨sub_nonneg.mpr (Nat.floor_le hx0),
          (Nat.self_sub_floor_lt_one x).le⟩⟩
      refine ⟨Quotient.mk (polygonSetoid P) (i, s), preim i s ?_⟩
      dsimp [c, i, s]
      ring
  let e : PolygonDomain P ≃ₜ Circle :=
    (Equiv.ofBijective f ⟨hfinj, hsurj⟩).toHomeomorphOfContinuousClosed hf hf.isClosedMap
  refine ⟨e.symm, 0, ?_⟩
  intro i s
  apply e.injective
  simp only [Homeomorph.apply_symm_apply]
  change Circle.exp (0 + 2 * Real.pi * (i.val + (s : ℝ)) / P.count) =
    Circle.exp (2 * Real.pi * c (i, s) / P.count)
  simp [c]

structure PolygonalKnot where
  polygon : CyclicPolygon
  parametrization : Circle ≃ₜ PolygonDomain polygon
  positive_traversal : ∃ t₀ : ℝ, ∀ (i : Fin polygon.count) (s : Time),
    parametrization (Circle.exp (t₀ + 2 * Real.pi * (i.val + (s : ℝ)) / polygon.count)) =
      Quotient.mk (polygonSetoid polygon) (i, s)
  embedding : IsEmbedding (polygonMap polygon)
  edge_intersections : ∀ i j, i ≠ j →
    Set.range (polygonEdge polygon i) ∩ Set.range (polygonEdge polygon j) ⊆
      {polygon.vertex i, polygon.vertex (polygon.next i)} ∩
      {polygon.vertex j, polygon.vertex (polygon.next j)}

def polygonLoop (P : PolygonalKnot) : Circle → Euc 3 :=
  polygonMap P.polygon ∘ P.parametrization
def planarProjection (x : Euc 3) : Euc 2 := !₂[x 0, x 1]
def polygonProjectedTangent (P : PolygonalKnot) (i : Fin P.polygon.count) : Euc 2 :=
  planarProjection (P.polygon.vertex (P.polygon.next i) - P.polygon.vertex i)
def orientedPlaneDet (x y : Euc 2) : ℝ := x 0 * y 1 - x 1 * y 0

structure DiagramCrossing (P : PolygonalKnot) where
  first : Fin P.polygon.count
  second : Fin P.polygon.count
  distinct : first ≠ second
  firstParameter : Time
  secondParameter : Time
  first_interior : 0 < (firstParameter : ℝ) ∧ (firstParameter : ℝ) < 1
  second_interior : 0 < (secondParameter : ℝ) ∧ (secondParameter : ℝ) < 1
  projected_equal :
    planarProjection (polygonEdge P.polygon first firstParameter) =
      planarProjection (polygonEdge P.polygon second secondParameter)
  transverse : orientedPlaneDet (polygonProjectedTangent P first)
    (polygonProjectedTangent P second) ≠ 0
  overFirst : Bool
  heights : if overFirst then
    polygonEdge P.polygon second secondParameter 2 <
      polygonEdge P.polygon first firstParameter 2
    else polygonEdge P.polygon first firstParameter 2 <
      polygonEdge P.polygon second secondParameter 2
  sign : ℤ
  sign_eq : sign = if
    (if overFirst then 1 else -1 : ℝ) *
      orientedPlaneDet (polygonProjectedTangent P first) (polygonProjectedTangent P second) > 0
    then 1 else -1

structure RegularOrientedDiagram (P : PolygonalKnot) where
  crossingCount : ℕ
  crossing : Fin crossingCount → DiagramCrossing P
  projected_edges_nonzero : ∀ i, polygonProjectedTangent P i ≠ 0
  vertices_distinct : Function.Injective (planarProjection ∘ P.polygon.vertex)
  no_vertex_crossing : ∀ i j (s : Time), 0 < (s : ℝ) → (s : ℝ) < 1 →
    planarProjection (P.polygon.vertex i) ≠ planarProjection (polygonEdge P.polygon j s)
  crossing_positions_distinct : Function.Injective
    (fun k => planarProjection (polygonEdge P.polygon (crossing k).first (crossing k).firstParameter))
  crossings_complete : ∀ i j (s t : Time), i ≠ j →
    0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    planarProjection (polygonEdge P.polygon i s) = planarProjection (polygonEdge P.polygon j t) →
    ∃ k, ((crossing k).first = i ∧ (crossing k).second = j ∧
      (crossing k).firstParameter = s ∧ (crossing k).secondParameter = t) ∨
      ((crossing k).first = j ∧ (crossing k).second = i ∧
      (crossing k).firstParameter = t ∧ (crossing k).secondParameter = s)
  no_triples : ∀ i j k (s t r : Time), i ≠ j → j ≠ k → i ≠ k →
    0 < (s : ℝ) → (s : ℝ) < 1 → 0 < (t : ℝ) → (t : ℝ) < 1 →
    0 < (r : ℝ) → (r : ℝ) < 1 →
    planarProjection (polygonEdge P.polygon i s) = planarProjection (polygonEdge P.polygon j t) →
    planarProjection (polygonEdge P.polygon i s) ≠ planarProjection (polygonEdge P.polygon k r)

structure PositiveCircleDiffeomorph where
  diffeomorph : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞
  angleLift : ℝ → ℝ
  lift_smooth : ContDiff ℝ ∞ angleLift
  lift_period : ∀ t, angleLift (t + 2 * Real.pi) = angleLift t + 2 * Real.pi
  lift_positive : ∀ t, 0 < deriv angleLift t
  lift_eq : ∀ t, Circle.exp (angleLift t) = diffeomorph (Circle.exp t)

structure StereographicPlacement (K : OrientedKnot) where
  pole : ThreeSphere
  avoids_knot : pole ∉ Set.range (K.component 0)
  chart : OpenPartialHomeomorph ThreeSphere (Euc 3)
  source_eq : chart.source = {pole}ᶜ
  target_eq : chart.target = univ
  chart_smooth : chart ∈ maximalAtlas (𝓡 3) ∞ ThreeSphere

/-- Actual finite-coordinate piecewise isotopy, not an arbitrary homotopy. -/
structure PiecewiseCurveIsotopy (f g : Circle → Euc 3) where
  stage : Time → C(Circle, Euc 3)
  embedding : ∀ t, IsEmbedding (stage t)
  continuous_family : Continuous (fun p : Time × Circle => stage p.1 p.2)
  initial : (stage 0 : Circle → Euc 3) = f
  terminal : (stage 1 : Circle → Euc 3) = g
  count : ℕ
  coordinate : Fin count → C(Time × Time, Time × Circle)
  coordinate_embedding : ∀ i, IsEmbedding (coordinate i)
  source_regular : ∀ i, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1)) 1 (coordinate i)
  source_injective : ∀ i p, Function.Injective
    (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod (𝓡 1)) (coordinate i) p)
  covers : (⋃ i, Set.range (coordinate i)) = univ
  target_regular : ∀ i, ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) 1
    (fun p => ((coordinate i p).1, stage (coordinate i p).1 (coordinate i p).2))
  target_injective : ∀ i p, Function.Injective
    (mfderiv ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3))
      (fun p => ((coordinate i p).1, stage (coordinate i p).1 (coordinate i p).2)) p)
  smooth_interiors : ∀ i,
    ContMDiffOn ((𝓡∂ 1).prod (𝓡∂ 1)) ((𝓡∂ 1).prod 𝓘(ℝ, Euc 3)) ∞
      (fun p => ((coordinate i p).1, stage (coordinate i p).1 (coordinate i p).2))
      (((𝓡∂ 1).prod (𝓡∂ 1)).interior (Time × Time))

structure PolygonSmoothing (P : PolygonalKnot) where
  curve : Circle → Euc 3
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 3) ∞ curve
  radius : ℝ
  radius_pos : 0 < radius
  close : ∀ z, dist (curve z) (polygonLoop P z) < radius
  unchanged : ∀ z, (∀ i, polygonLoop P z ∉ Metric.ball (P.polygon.vertex i) radius) →
    curve z = polygonLoop P z
  separated_nonadjacent : ∀ i j, i ≠ j → P.polygon.next i ≠ j → P.polygon.next j ≠ i →
    Disjoint (Metric.thickening radius (Set.range (polygonEdge P.polygon i)))
      (Metric.thickening radius (Set.range (polygonEdge P.polygon j)))
  knot_isotopy : PiecewiseCurveIsotopy (polygonLoop P) curve

structure DiagramKnotIdentification {K : OrientedKnot} (T : TubularNeighborhood K) where
  placement : StereographicPlacement K
  polygon : PolygonalKnot
  diagram : RegularOrientedDiagram polygon
  smoothing : PolygonSmoothing polygon
  ambient : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞
  parameter : PositiveCircleDiffeomorph
  identifies : ∀ z,
    ambient (placement.chart.symm (smoothing.curve z)) = K.component 0 (parameter.diffeomorph z)
  supported : ∀ x ∉ Set.range (T.tube 0), ambient x = x

theorem stereographic_placement_exists (K : OrientedKnot) (T : TubularNeighborhood K) :
    Nonempty (StereographicPlacement K) := by
  let w : TubeDisk := ⟨EuclideanSpace.single 0 1, by
    simp [tubeDiskOpen, Metric.mem_ball, dist_zero_right]⟩
  let pole : ThreeSphere := T.tube 0 (1, w)
  have hpole : pole ∉ Set.range (K.component 0) := by
    rintro ⟨z, hz⟩
    have h := (T.smoothEmbedding 0).isEmbedding.injective
      (show T.tube 0 (z, ⟨0, Metric.mem_ball_self zero_lt_two⟩) =
        T.tube 0 (1, w) by rw [T.core]; exact hz)
    have hw := congrArg (fun p : TubeDomain => (p.2 : Euc 2) 0) h
    simp [w] at hw
  haveI : Fact (Module.finrank ℝ (Euc 4) = 3 + 1) := ⟨by simp [Euc]⟩
  refine ⟨⟨pole, hpole, stereographic' 3 pole, stereographic'_source pole,
    stereographic'_target pole, ?_⟩⟩
  apply subset_maximalAtlas
  exact ⟨pole, rfl⟩

end
end SeifertSurfaces.LongitudeProducers
