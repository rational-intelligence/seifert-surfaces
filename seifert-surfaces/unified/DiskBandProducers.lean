import DiagramApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff
open Set Topology
open DifferentialGeometry.Topology.PiecewiseLinear
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

structure PiecewiseAffineArc where
  count : ℕ
  count_pos : 0 < count
  time : Fin (count + 1) → Time
  strict_time : StrictMono time
  first_time : time 0 = 0
  last_time : time (Fin.last count) = 1
  vertex : Fin (count + 1) → Euc 2
  map : C(Time, Euc 2)
  affine : ∀ i : Fin count, ∀ t : Time,
    time i.castSucc ≤ t → t ≤ time i.succ →
    map t = (1 - ((t : ℝ) - time i.castSucc) /
      ((time i.succ : ℝ) - time i.castSucc)) • vertex i.castSucc +
      (((t : ℝ) - time i.castSucc) / ((time i.succ : ℝ) - time i.castSucc)) • vertex i.succ
  embedding : IsEmbedding map

structure CrossingNeighborhood {P : PolygonalKnot} (c : DiagramCrossing P) where
  radius : ℝ
  radius_pos : 0 < radius
  beforeFirst : Time
  afterFirst : Time
  beforeSecond : Time
  afterSecond : Time
  first_order : 0 < (beforeFirst : ℝ) ∧ beforeFirst < c.firstParameter ∧
    c.firstParameter < afterFirst ∧ (afterFirst : ℝ) < 1
  second_order : 0 < (beforeSecond : ℝ) ∧ beforeSecond < c.secondParameter ∧
    c.secondParameter < afterSecond ∧ (afterSecond : ℝ) < 1
  first_entry : planarProjection (polygonEdge P.polygon c.first beforeFirst) ∈
    Metric.sphere (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) radius
  first_exit : planarProjection (polygonEdge P.polygon c.first afterFirst) ∈
    Metric.sphere (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) radius
  second_entry : planarProjection (polygonEdge P.polygon c.second beforeSecond) ∈
    Metric.sphere (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) radius
  second_exit : planarProjection (polygonEdge P.polygon c.second afterSecond) ∈
    Metric.sphere (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) radius
  only_two_strands : planarProjection '' Set.range (polygonLoop P) ∩
    Metric.closedBall (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) radius =
    (planarProjection ∘ polygonEdge P.polygon c.first) '' Icc beforeFirst afterFirst ∪
    (planarProjection ∘ polygonEdge P.polygon c.second) '' Icc beforeSecond afterSecond

structure ResolvedCrossing {P : PolygonalKnot} (c : DiagramCrossing P) where
  neighborhood : CrossingNeighborhood c
  firstToSecond : PiecewiseAffineArc
  secondToFirst : PiecewiseAffineArc
  first_start : firstToSecond.map 0 = planarProjection (polygonEdge P.polygon c.first neighborhood.beforeFirst)
  first_end : firstToSecond.map 1 = planarProjection (polygonEdge P.polygon c.second neighborhood.afterSecond)
  second_start : secondToFirst.map 0 = planarProjection (polygonEdge P.polygon c.second neighborhood.beforeSecond)
  second_end : secondToFirst.map 1 = planarProjection (polygonEdge P.polygon c.first neighborhood.afterFirst)
  disjoint : Disjoint (Set.range firstToSecond.map) (Set.range secondToFirst.map)
  inside : Set.range firstToSecond.map ∪ Set.range secondToFirst.map ⊆
    Metric.closedBall (planarProjection (polygonEdge P.polygon c.first c.firstParameter)) neighborhood.radius

structure OrientedResolution {P : PolygonalKnot} (D : RegularOrientedDiagram P) where
  crossing : ∀ k, ResolvedCrossing (D.crossing k)
  neighborhoods_disjoint : Pairwise (fun i j => Disjoint
    (Metric.closedBall (planarProjection (polygonEdge P.polygon (D.crossing i).first (D.crossing i).firstParameter))
      (crossing i).neighborhood.radius)
    (Metric.closedBall (planarProjection (polygonEdge P.polygon (D.crossing j).first (D.crossing j).firstParameter))
      (crossing j).neighborhood.radius))
  count : ℕ
  count_pos : 0 < count
  loop : Fin count → PolygonalKnot
  planar : ∀ i j, (loop i).polygon.vertex j 2 = 0
  disjoint_loops : Pairwise (fun i j => Disjoint
    (Set.range (planarProjection ∘ polygonLoop (loop i)))
    (Set.range (planarProjection ∘ polygonLoop (loop j))))
  image_eq : (⋃ i, Set.range (planarProjection ∘ polygonLoop (loop i))) =
    ((planarProjection '' Set.range (polygonLoop P)) \ (⋃ k,
      Metric.ball (planarProjection (polygonEdge P.polygon (D.crossing k).first (D.crossing k).firstParameter))
        (crossing k).neighborhood.radius)) ∪
      (⋃ k, Set.range (crossing k).firstToSecond.map ∪ Set.range (crossing k).secondToFirst.map)
  oriented_segments : ∀ i j, ∃ a b : Euc 2, a ≠ b ∧
    planarProjection ((loop i).polygon.vertex j) = a ∧
    planarProjection ((loop i).polygon.vertex ((loop i).polygon.next j)) = b ∧
    ((∃ k s t, s < t ∧ a = planarProjection (polygonEdge P.polygon k s) ∧
      b = planarProjection (polygonEdge P.polygon k t)) ∨
     (∃ k s t, s < t ∧
       ((a = (crossing k).firstToSecond.map s ∧ b = (crossing k).firstToSecond.map t) ∨
        (a = (crossing k).secondToFirst.map s ∧ b = (crossing k).secondToFirst.map t))))



def closedTriangle (a b c : Euc 2) : Set (Euc 2) :=
  {x | ∃ r s t : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ 0 ≤ t ∧ r + s + t = 1 ∧
    x = r • a + s • b + t • c}
abbrev ClosedDisk2 := ↥(Metric.closedBall (0 : Euc 2) 1)

/-- A genuine finite planar disk, with a concrete triangulated carrier and
an actual disk homeomorphism. The planar Jordan/Schoenflies bridge is a
producer theorem below, never assumed for every loop. -/
structure FinitePlanarDisk (P : PolygonalKnot) where
  vertexCount : ℕ
  vertex : Fin vertexCount → Euc 2
  triangleCount : ℕ
  triangle : Fin triangleCount → Fin 3 → Fin vertexCount
  nondegenerate : ∀ i, orientedPlaneDet
    (vertex (triangle i 1) - vertex (triangle i 0))
    (vertex (triangle i 2) - vertex (triangle i 0)) ≠ 0
  diskHomeomorph : ClosedDisk2 ≃ₜ ↥(⋃ i,
    closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2)))
  boundary : C(Circle, ↥(⋃ i,
    closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2))))
  boundary_embedding : IsEmbedding boundary
  boundary_eq : Set.range (fun z => (boundary z : Euc 2)) =
    frontier (⋃ i, closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2)))
  parametrization_eq : ∀ z, (boundary z : Euc 2) = planarProjection (polygonLoop P z)

namespace FinitePlanarDisk
def region {P : PolygonalKnot} (D : FinitePlanarDisk P) : Set (Euc 2) :=
  ⋃ i, closedTriangle (D.vertex (D.triangle i 0)) (D.vertex (D.triangle i 1)) (D.vertex (D.triangle i 2))
abbrev Carrier {P : PolygonalKnot} (D : FinitePlanarDisk P) := ↥D.region
def lifted {P : PolygonalKnot} (D : FinitePlanarDisk P) (height : ℝ) (x : D.Carrier) : Euc 3 :=
  !₂[(x : Euc 2) 0, (x : Euc 2) 1, height]
end FinitePlanarDisk


/-- Candidate adapter statement. It requires independent statement review. -/
theorem polygonLoop_planar_projection_embedding (P : PolygonalKnot)
    (hplanar : ∀ i, P.polygon.vertex i 2 = 0) :
    IsEmbedding (planarProjection ∘ polygonLoop P) := by
  have hz : ∀ q : PolygonDomain P.polygon, polygonMap P.polygon q 2 = 0 := by
    intro q
    refine Quotient.inductionOn q ?_
    rintro ⟨i, t⟩
    change ((1 - (t : ℝ)) • P.polygon.vertex i +
      (t : ℝ) • P.polygon.vertex (P.polygon.next i)) 2 = 0
    simp [hplanar]
  have hc : Continuous (planarProjection ∘ polygonLoop P) := by
    have : Continuous planarProjection := by
      change Continuous (fun x : Euc 3 => !₂[x 0, x 1])
      fun_prop
    exact this.comp (P.embedding.continuous.comp P.parametrization.continuous)
  have hi : Function.Injective (planarProjection ∘ polygonLoop P) := by
    intro z w h
    apply P.parametrization.injective
    apply P.embedding.injective
    ext i
    fin_cases i
    · exact congrArg (fun x : Euc 2 => x 0) h
    · exact congrArg (fun x : Euc 2 => x 1) h
    · exact (hz _).trans (hz _).symm
  exact (hc.isClosedEmbedding hi).isEmbedding

/-- Candidate adapter statement. The original cyclic parametrization must
actually cover every edge, including their endpoints. -/
theorem polygonLoop_planar_range_edges (P : PolygonalKnot) :
    Set.range (planarProjection ∘ polygonLoop P) =
      ⋃ i, segment ℝ (planarProjection (P.polygon.vertex i))
        (planarProjection (P.polygon.vertex (P.polygon.next i))) := by
  have edge_formula (i : Fin P.polygon.count) (t : Time) :
      planarProjection (polygonEdge P.polygon i t) =
        (1 - (t : ℝ)) • planarProjection (P.polygon.vertex i) +
          (t : ℝ) • planarProjection (P.polygon.vertex (P.polygon.next i)) := by
    ext j
    fin_cases j <;> rfl
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨i, t⟩, ht⟩ := Quotient.mk_surjective (P.parametrization z)
    apply Set.mem_iUnion.mpr
    refine ⟨i, 1 - (t : ℝ), (t : ℝ), sub_nonneg.mpr t.2.2,
      t.2.1, sub_add_cancel _ _, ?_⟩
    change _ = planarProjection (polygonMap P.polygon (P.parametrization z))
    rw [← ht]
    exact (edge_formula i t).symm
  · intro hx
    obtain ⟨i, r, s, hr, hs, hrs, heq⟩ := Set.mem_iUnion.mp hx
    let t : Time := ⟨s, hs, by linarith⟩
    obtain ⟨z, hz⟩ := P.parametrization.surjective
      (Quotient.mk (polygonSetoid P.polygon) (i, t))
    refine ⟨z, ?_⟩
    change planarProjection (polygonMap P.polygon (P.parametrization z)) = x
    rw [hz]
    change planarProjection (polygonEdge P.polygon i t) = x
    rw [edge_formula]
    change (1 - s) • _ + s • _ = x
    have : 1 - s = r := by linarith
    rwa [this]

/-- Candidate adapter statement for extracting triangle faces from a
geometric simplicial complex into the literal approved carrier definition. -/
theorem closedTriangle_eq_convexHull (a b c : Euc 2) :
    closedTriangle a b c = convexHull ℝ ({a, b, c} : Set (Euc 2)) := by
  have hconv : Convex ℝ (closedTriangle a b c) := by
    rintro x ⟨r, s, t, hr, hs, ht, hsum, rfl⟩
      y ⟨r', s', t', hr', hs', ht', hsum', rfl⟩ u v hu hv huv
    refine ⟨u * r + v * r', u * s + v * s', u * t + v * t',
      add_nonneg (mul_nonneg hu hr) (mul_nonneg hv hr'),
      add_nonneg (mul_nonneg hu hs) (mul_nonneg hv hs'),
      add_nonneg (mul_nonneg hu ht) (mul_nonneg hv ht'), ?_, ?_⟩
    · nlinarith
    · simp [smul_add, add_smul, smul_smul]
      module
  apply Set.Subset.antisymm
  · rintro x ⟨r, s, t, hr, hs, ht, hsum, rfl⟩
    apply mem_convexHull_of_exists_fintype (![r, s, t] : Fin 3 → ℝ)
      (![a, b, c] : Fin 3 → Euc 2)
    · intro i
      fin_cases i <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using hsum
    · intro i
      fin_cases i <;> simp
    · simp [Fin.sum_univ_succ, add_assoc]
  · apply convexHull_min _ hconv
    intro x hx
    change x = a ∨ x = b ∨ x = c at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 1, 0, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
    · exact ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩

/-- Candidate finite triangle adapter; this uses actual affine independence. -/
theorem orientedPlaneDet_ne_zero_of_affineIndependent (a b c : Euc 2)
    (h : AffineIndependent ℝ (![a, b, c] : Fin 3 → Euc 2)) :
    orientedPlaneDet (b - a) (c - a) ≠ 0 := by
  intro hdet
  change (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 at hdet
  have hw0 : ∑ i : Fin 3, (![c 0 - b 0, a 0 - c 0, b 0 - a 0] : Fin 3 → ℝ) i = 0 := by
    simp [Fin.sum_univ_succ]
  have hv0 : ∑ i : Fin 3, (![c 0 - b 0, a 0 - c 0, b 0 - a 0] : Fin 3 → ℝ) i •
      (![a, b, c] : Fin 3 → Euc 2) i = 0 := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_succ] <;> nlinarith [hdet]
  have hb0 := h.eq_zero_of_sum_eq_zero (s := Finset.univ) hw0 hv0 2 (Finset.mem_univ _)
  have hc0 := h.eq_zero_of_sum_eq_zero (s := Finset.univ) hw0 hv0 1 (Finset.mem_univ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at hb0 hc0
  have hw1 : ∑ i : Fin 3, (![c 1 - b 1, a 1 - c 1, b 1 - a 1] : Fin 3 → ℝ) i = 0 := by
    simp [Fin.sum_univ_succ]
  have hv1 : ∑ i : Fin 3, (![c 1 - b 1, a 1 - c 1, b 1 - a 1] : Fin 3 → ℝ) i •
      (![a, b, c] : Fin 3 → Euc 2) i = 0 := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_succ] <;> nlinarith [hb0, hc0]
  have hb1 := h.eq_zero_of_sum_eq_zero (s := Finset.univ) hw1 hv1 2 (Finset.mem_univ _)
  have hba : b = a := by
    ext i
    fin_cases i
    · exact sub_eq_zero.mp hb0
    · exact sub_eq_zero.mp hb1
  have heq : (1 : Fin 3) = 0 := h.injective (by simpa using hba)
  norm_num at heq



/-- P1 candidate: the actual polygonal image is a PL circle. -/
theorem polygonLoop_planar_isPLSphere (P : PolygonalKnot)
    (hplanar : ∀ i, P.polygon.vertex i 2 = 0) :
    DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere 1
      (Set.range (planarProjection ∘ polygonLoop P)) := by
  classical
  obtain ⟨t₀, ht₀⟩ := P.positive_traversal
  let n : ℝ := P.polygon.count
  have hnNat := P.polygon.count_ge_three
  have hn : 3 ≤ n := by dsimp [n]; exact_mod_cast hnNat
  have hn0 : n ≠ 0 := by linarith
  have hπ : 2 * Real.pi ≠ 0 := by positivity
  let γ : ℝ → Euc 2 := fun t =>
    planarProjection (polygonLoop P (Circle.exp (t₀ + 2 * Real.pi * t / n)))
  have hcontinuous : Continuous γ := by
    exact (polygonLoop_planar_projection_embedding P hplanar).continuous.comp
      (Circle.exp.continuous.comp (by fun_prop))
  have heq (s t : ℝ) (hst : γ s = γ t) : ∃ m : ℤ, s = t + m * n := by
    have hcircle := (polygonLoop_planar_projection_embedding P hplanar).injective hst
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
    refine ⟨m, ?_⟩
    apply (mul_left_inj' hπ).mp
    have hm' := congrArg (fun x : ℝ => x * n) hm
    rw [add_mul, add_mul, add_mul, div_mul_cancel₀ _ hn0,
      div_mul_cancel₀ _ hn0] at hm'
    linear_combination hm'
  have hcloses : γ n = γ 0 := by
    change planarProjection (polygonLoop P (Circle.exp (t₀ + 2 * Real.pi * n / n))) =
      planarProjection (polygonLoop P (Circle.exp (t₀ + 2 * Real.pi * 0 / n)))
    simp only [mul_div_cancel_right₀ _ hn0, mul_zero, zero_div, add_zero]
    rw [Circle.exp_add_two_pi]
  have hcoverpoint (t : ℝ) (ht : t ∈ Icc 0 n) :
      ∃ i : Fin P.polygon.count, t ∈ Icc (i.val : ℝ) (i.val + 1) := by
    by_cases he : t = n
    · let i : Fin P.polygon.count := ⟨P.polygon.count - 1,
        Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 3) hnNat) (by decide : 0 < 1)⟩
      refine ⟨i, ?_⟩
      have hi : ((i.val : ℕ) : ℝ) + 1 = n := by
        dsimp [i, n]
        exact_mod_cast (Nat.sub_add_cancel ((by decide : 1 ≤ 3).trans hnNat))
      exact ⟨by linarith, by linarith⟩
    · let i : Fin P.polygon.count := ⟨Nat.floor t, by
        apply (Nat.floor_lt ht.1).2
        exact lt_of_le_of_ne ht.2 he⟩
      exact ⟨i, Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
  let A : Fin P.polygon.count → ℝ →ᵃ[ℝ] Euc 2 := fun i =>
    (AffineMap.lineMap (planarProjection (P.polygon.vertex i))
      (planarProjection (P.polygon.vertex (P.polygon.next i)))).comp
      (AffineMap.lineMap (-(i.val : ℝ)) (1 - i.val))
  have hedge (i : Fin P.polygon.count) (x : ℝ)
      (hx : x ∈ Icc (i.val : ℝ) (i.val + 1)) : γ x = A i x := by
    let s : Time := ⟨x - i.val, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    have hs : (i.val : ℝ) + (s : ℝ) = x := by dsimp [s]; ring
    change planarProjection (polygonMap P.polygon
      (P.parametrization (Circle.exp (t₀ + 2 * Real.pi * x / n)))) = A i x
    rw [← hs, ht₀ i s]
    change planarProjection (polygonEdge P.polygon i s) = A i ((i.val : ℝ) + (s : ℝ))
    dsimp only [polygonEdge, planarProjection, A]
    simp only [AffineMap.comp_apply, AffineMap.lineMap_apply_module,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ext j
    fin_cases j <;> dsimp [s] <;> ring
  have hinterval (a b : ℝ) : IsHPolytope (Icc a b) := by
    refine ⟨isCompact_Icc, Bool, inferInstance,
      (fun f => if f then (LinearMap.id : ℝ →ₗ[ℝ] ℝ) else -LinearMap.id),
      (fun f => if f then b else -a), ?_⟩
    ext x
    constructor
    · intro hx f
      cases f
      · change -x ≤ -a
        linarith [hx.1]
      · change x ≤ b
        exact hx.2
    · intro hx
      have hl := hx false
      have hu := hx true
      change -x ≤ -a at hl
      change x ≤ b at hu
      exact ⟨by linarith, hu⟩
  have hPL (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ n) :
      IsPiecewiseAffineOn γ (Icc a b) := by
    let C : Fin P.polygon.count → Set ℝ := fun i =>
      Icc (max a i.val) (min b (i.val + 1))
    have hC : (⋃ i, C i) = Icc a b := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨(le_max_left _ _).trans hi.1, hi.2.trans (min_le_left _ _)⟩
      · intro hx
        obtain ⟨i, hi⟩ := hcoverpoint x ⟨ha.trans hx.1, hx.2.trans hb⟩
        exact Set.mem_iUnion.mpr ⟨i, max_le hx.1 hi.1, le_min hx.2 hi.2⟩
    intro x hx
    refine ⟨Fin P.polygon.count, inferInstance, C, A, ?_, ?_⟩
    · intro i
      refine ⟨hinterval _ _, ?_, ?_⟩
      · intro y hy
        exact ⟨(le_max_left _ _).trans hy.1, hy.2.trans (min_le_left _ _)⟩
      · intro y hy
        exact hedge i y ⟨(le_max_right _ _).trans hy.1, hy.2.trans (min_le_right _ _)⟩
    · rw [hC]
      exact self_mem_nhdsWithin
  have hinj (a b : ℝ) (hab : b - a < n) : InjOn γ (Icc a b) := by
    intro s hs t ht hst
    obtain ⟨m, hm⟩ := heq s t hst
    have hml : (-1 : ℝ) * n < (m : ℝ) * n := by linarith [hs.1, ht.2]
    have hmu : (m : ℝ) * n < 1 * n := by linarith [hs.2, ht.1]
    have hml' : (-1 : ℝ) < m := (mul_lt_mul_iff_right₀ (by linarith : 0 < n)).mp
      (by simpa only [mul_comm] using hml)
    have hmu' : (m : ℝ) < 1 := (mul_lt_mul_iff_right₀ (by linarith : 0 < n)).mp
      (by simpa only [mul_comm] using hmu)
    have hm0 : m = 0 := by
      have hmlz : (-1 : ℤ) < m := by exact_mod_cast hml'
      have hmuz : m < (1 : ℤ) := by exact_mod_cast hmu'
      apply le_antisymm
      · exact Int.le_sub_one_of_lt hmuz
      · exact Int.add_one_le_iff.mpr hmlz
    simpa only [hm0, Int.cast_zero, zero_mul, add_zero] using hm
  have hmeet (s t : ℝ) (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 1 n)
      (hst : γ s = γ t) : γ s = γ 0 ∨ γ s = γ 1 := by
    obtain ⟨m, hm⟩ := heq s t hst
    have hml : (-1 : ℝ) * n ≤ (m : ℝ) * n := by linarith [hs.1, ht.2]
    have hmu : (m : ℝ) * n < 1 * n := by linarith [hs.2, ht.1]
    have hml' : (-1 : ℝ) ≤ m := (mul_le_mul_iff_right₀ (by linarith : 0 < n)).mp
      (by simpa only [mul_comm] using hml)
    have hmu' : (m : ℝ) < 1 := (mul_lt_mul_iff_right₀ (by linarith : 0 < n)).mp
      (by simpa only [mul_comm] using hmu)
    have hm_cases : m = -1 ∨ m = 0 := by
      have hmlz : (-1 : ℤ) ≤ m := by exact_mod_cast hml'
      have hmuz : m < (1 : ℤ) := by exact_mod_cast hmu'
      by_cases hm1 : m = -1
      · exact Or.inl hm1
      · refine Or.inr (le_antisymm (Int.le_sub_one_of_lt hmuz) ?_)
        exact Int.add_one_le_iff.mpr (lt_of_le_of_ne hmlz (Ne.symm hm1))
    rcases hm_cases with hm1 | hm0
    · have hs0 : s = 0 := by
        simp only [hm1, Int.cast_neg, Int.cast_one, neg_one_mul] at hm
        linarith [hs.1, ht.2]
      exact Or.inl (congrArg γ hs0)
    · have hs1 : s = 1 := by
        simp only [hm0, Int.cast_zero, zero_mul, add_zero] at hm
        linarith [hs.2, ht.1]
      exact Or.inr (congrArg γ hs1)
  have himage : γ '' Icc 0 n = Set.range (planarProjection ∘ polygonLoop P) := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (t₀ + 2 * Real.pi * t / n), rfl⟩
    · rintro y ⟨z, rfl⟩
      obtain ⟨⟨i, s⟩, his⟩ := Quotient.mk_surjective (P.parametrization z)
      have hzi : Circle.exp (t₀ + 2 * Real.pi * (i.val + (s : ℝ)) / n) = z := by
        apply P.parametrization.injective
        exact (ht₀ i s).trans his
      refine ⟨i.val + (s : ℝ), ?_, ?_⟩
      · constructor
        · exact add_nonneg (Nat.cast_nonneg _) s.2.1
        · have hi : (i.val : ℝ) + 1 ≤ n := by
            dsimp [n]
            exact_mod_cast (show i.val + 1 ≤ P.polygon.count from i.isLt)
          linarith [s.2.2]
      · change planarProjection (polygonLoop P (Circle.exp
          (t₀ + 2 * Real.pi * (i.val + (s : ℝ)) / n))) = _
        rw [hzi]
        rfl
  let B : Set (Euc 2) := γ '' Icc 1 n
  have hAarc : Schoenflies.IsArcBetween (γ '' Icc 0 1) (γ 0) (γ 1) :=
    ⟨γ, hcontinuous.continuousOn, hinj 0 1 (by linarith), rfl, rfl, rfl⟩
  let η : ℝ → Euc 2 := fun t => γ (n + (1 - n) * t)
  have hηimage : η '' Icc 0 1 = B := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      exact ⟨n + (1 - n) * t, ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩, rfl⟩
    · rintro y ⟨s, hs, rfl⟩
      refine ⟨(n - s) / (n - 1), ?_, ?_⟩
      · exact ⟨div_nonneg (by linarith [hs.2]) (by linarith),
          (div_le_one (by linarith : 0 < n - 1)).mpr (by linarith [hs.1])⟩
      · change γ (n + (1 - n) * ((n - s) / (n - 1))) = γ s
        apply congrArg γ
        have hh := div_mul_cancel₀ (n - s) (show n - 1 ≠ 0 by linarith)
        linear_combination -hh
  have hBarc : Schoenflies.IsArcBetween B (γ 0) (γ 1) := by
    refine ⟨η, (hcontinuous.comp (by fun_prop)).continuousOn, ?_, hηimage, ?_, ?_⟩
    · intro s hs t ht hst
      have hs' : n + (1 - n) * s ∈ Icc 1 n :=
        ⟨by nlinarith [hs.2], by nlinarith [hs.1]⟩
      have ht' : n + (1 - n) * t ∈ Icc 1 n :=
        ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
      have h := hinj 1 n (by linarith) hs' ht' hst
      have hh : (1 - n) * s = (1 - n) * t := by linarith
      exact (mul_left_inj' (by linarith : 1 - n ≠ 0)).mp
        (by simpa only [mul_comm] using hh)
    · simpa only [η, mul_zero, add_zero] using hcloses
    · dsimp [η]
      apply congrArg γ
      ring
  have hcut : Schoenflies.IsCutPair (Set.range (planarProjection ∘ polygonLoop P))
      (γ 0) (γ 1) (γ '' Icc 0 1) B := by
    refine ⟨hAarc, hBarc, ?_, ?_⟩
    · change γ '' Icc 0 1 ∪ γ '' Icc 1 n = _
      rw [← image_union, Icc_union_Icc_eq_Icc (by norm_num) (by linarith), himage]
    · apply Set.Subset.antisymm
      · rintro y ⟨⟨s, hs, hsy⟩, t, ht, hty⟩
        have hst : γ s = γ t := hsy.trans hty.symm
        rcases hmeet s t hs ht hst with h | h
        · exact Set.mem_insert_iff.mpr (Or.inl (hsy.symm.trans h))
        · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (hsy.symm.trans h)))
      · intro y hy
        rcases Set.mem_insert_iff.mp hy with h | h
        · subst y
          exact ⟨⟨0, by norm_num, rfl⟩, n, ⟨by linarith, le_rfl⟩, hcloses⟩
        · have hy1 := Set.mem_singleton_iff.mp h
          subst y
          exact ⟨⟨1, by norm_num, rfl⟩, 1, ⟨le_rfl, by linarith⟩, rfl⟩
  exact isPLSphere_one_of_isCutPair hcut
    (isPLBall_image_Icc_of_isPiecewiseAffineOn (by norm_num : (0 : ℝ) < 1)
      (hPL 0 1 le_rfl (by linarith)) (hinj 0 1 (by linarith)))
    (isPLBall_image_Icc_of_isPiecewiseAffineOn (by linarith : (1 : ℝ) < n)
      (hPL 1 n (by norm_num) le_rfl) (hinj 1 n (by linarith)))

/-- P2 candidate: extract actual finite nondegenerate planar triangles from
the same finite complex filling the closure of an actual open region. -/
theorem finite_planar_complex_triangle_carrier
    (K : Geometry.SimplicialComplex ℝ (Euc 2)) (hfinite : K.faces.Finite)
    (U : Set (Euc 2)) (hU : IsOpen U) (hK : K.space = closure U) :
    ∃ (vertexCount : ℕ) (vertex : Fin vertexCount → Euc 2)
      (triangleCount : ℕ) (triangle : Fin triangleCount → Fin 3 → Fin vertexCount),
      (∀ i, ({vertex (triangle i 0), vertex (triangle i 1), vertex (triangle i 2)} :
        Finset (Euc 2)) ∈ K.faces) ∧
      (∀ i, ({vertex (triangle i 0), vertex (triangle i 1), vertex (triangle i 2)} :
        Finset (Euc 2)).card = 3) ∧
      (∀ i, orientedPlaneDet
        (vertex (triangle i 1) - vertex (triangle i 0))
        (vertex (triangle i 2) - vertex (triangle i 0)) ≠ 0) ∧
      (⋃ i, closedTriangle (vertex (triangle i 0))
        (vertex (triangle i 1)) (vertex (triangle i 2))) = K.space := by
  classical
  let F := {s : Finset (Euc 2) // s ∈ K.faces ∧ s.card = 3}
  have hF : Finite F := ((hfinite.subset (by intro s hs; exact hs.1)).to_subtype)
  letI : Fintype F := Fintype.ofFinite F
  let n := Fintype.card F
  let e : Fin n ≃ F := (Fintype.equivFin F).symm
  let v : ∀ i : Fin n, Fin 3 ≃ ((e i).1 : Finset (Euc 2)) :=
    fun i => (Finset.equivFinOfCardEq (e i).2.2).symm
  let points : Fin n → Fin 3 → Euc 2 := fun i j => (v i j).1
  have hpoints (i : Fin n) : ({points i 0, points i 1, points i 2} : Finset (Euc 2)) = (e i).1 := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact (v i 0).2
      · exact (v i 1).2
      · exact (v i 2).2
    · intro hx
      obtain ⟨j, hj⟩ := (v i).surjective ⟨x, hx⟩
      have hvalue : points i j = x := congrArg Subtype.val hj
      rw [← hvalue]
      fin_cases j
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hpointset (i : Fin n) : ({points i 0, points i 1, points i 2} : Set (Euc 2)) = (e i).1 := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Euc 2) => (s : Set (Euc 2))) (hpoints i)
  have hi (i : Fin n) : AffineIndependent ℝ (points i) :=
    (K.indep (e i).2.1).comp_embedding (v i).toEmbedding
  have hdet (i : Fin n) : orientedPlaneDet (points i 1 - points i 0)
      (points i 2 - points i 0) ≠ 0 := by
    apply orientedPlaneDet_ne_zero_of_affineIndependent
    convert hi i using 1
    funext j
    fin_cases j <;> rfl
  have hcover : (⋃ i, closedTriangle (points i 0) (points i 1) (points i 2)) = K.space := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      rw [closedTriangle_eq_convexHull, hpointset] at hx
      exact K.convexHull_subset_space (e i).2.1 hx
    · intro x hx
      haveI : Finite K.faces := hfinite.to_subtype
      have hc := DifferentialGeometry.Topology.PiecewiseLinear.closure_subset_biUnion_convexHull_faces_card_eq_finrank_succ
        K hU (hK.symm ▸ subset_closure) (hK ▸ hx)
      obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hc
      have hs3 : s.card = 3 := by simpa [Euc] using hs.2
      let f : F := ⟨s, hs.1, hs3⟩
      let i := e.symm f
      have he : (e i).1 = s := congrArg Subtype.val (e.apply_symm_apply f)
      apply Set.mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [closedTriangle_eq_convexHull, hpointset, he]
      exact hxs
  let index : Fin n × Fin 3 ≃ Fin (n * 3) := finProdFinEquiv
  let vertex : Fin (n * 3) → Euc 2 := fun k =>
    points (index.symm k).1 (index.symm k).2
  let triangle : Fin n → Fin 3 → Fin (n * 3) := fun i j => index (i, j)
  have hvalue (i : Fin n) (j : Fin 3) : vertex (triangle i j) = points i j := by
    dsimp only [vertex, triangle]
    rw [index.symm_apply_apply]
  refine ⟨n * 3, vertex, n, triangle, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [hvalue, hpoints]
    exact (e i).2.1
  · intro i
    simp only [hvalue, hpoints]
    exact (e i).2.2
  · intro i
    simpa only [hvalue] using hdet i
  · simpa only [hvalue] using hcover

/-- P3 candidate: an actual homeomorphism from the literal planar closed
unit disk to the standard two-simplex, whose ambient coordinate space is R3. -/
theorem closedDisk2_stdSimplex_homeomorph_exists :
    Nonempty (ClosedDisk2 ≃ₜ ↥(Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) := by
  let T : Set (Euc 2) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}
  have hc0 : Continuous (fun x : Euc 2 => x 0) := by fun_prop
  have hc1 : Continuous (fun x : Euc 2 => x 1) := by fun_prop
  have hclosed : IsClosed T := by
    exact (isClosed_le continuous_const hc0).inter
      ((isClosed_le continuous_const hc1).inter
        (isClosed_le (hc0.add hc1) continuous_const))
  have hconv : Convex ℝ T := by
    intro x hx y hy u v hu hv huv
    change 0 ≤ u * x 0 + v * y 0 ∧ 0 ≤ u * x 1 + v * y 1 ∧
      (u * x 0 + v * y 0) + (u * x 1 + v * y 1) ≤ 1
    exact ⟨add_nonneg (mul_nonneg hu hx.1) (mul_nonneg hv hy.1),
      add_nonneg (mul_nonneg hu hx.2.1) (mul_nonneg hv hy.2.1), by
        nlinarith [mul_nonneg hu (sub_nonneg.mpr hx.2.2),
          mul_nonneg hv (sub_nonneg.mpr hy.2.2)]⟩
  have hbounded : Bornology.IsBounded T := by
    refine Metric.isBounded_closedBall.subset (s := T) (t := Metric.closedBall 0 2) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hn : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
      simpa [Fin.sum_univ_succ, Real.norm_eq_abs] using
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) x
    have h0 : x 0 ≤ 1 := by linarith [hx.2.1, hx.2.2]
    have h1 : x 1 ≤ 1 := by linarith [hx.1, hx.2.2]
    nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr h0),
      mul_nonneg hx.2.1 (sub_nonneg.mpr h1), norm_nonneg x]
  have hinterior : (interior T).Nonempty := by
    let c : Euc 2 := !₂[(1 / 4 : ℝ), (1 / 4 : ℝ)]
    refine ⟨c, mem_interior_iff_mem_nhds.mpr ?_⟩
    apply Filter.mem_of_superset (Metric.ball_mem_nhds c (by norm_num : (0 : ℝ) < 1 / 8))
    intro x hx
    have hn : ‖x - c‖ < 1 / 8 := by
      change dist x c < 1 / 8 at hx
      simpa only [dist_eq_norm] using hx
    have h0 : |x 0 - 1 / 4| < 1 / 8 := by
      exact lt_of_le_of_lt (PiLp.norm_apply_le (x - c) 0) hn
    have h1 : |x 1 - 1 / 4| < 1 / 8 := by
      exact lt_of_le_of_lt (PiLp.norm_apply_le (x - c) 1) hn
    change 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1
    rcases abs_lt.mp h0 with ⟨h0l, h0u⟩
    rcases abs_lt.mp h1 with ⟨h1l, h1u⟩
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨g, hgint, hgclosed, hgfront⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconv hinterior hbounded
  have hg : g '' T = Metric.closedBall (0 : Euc 2) 1 := by
    simpa only [hclosed.closure_eq] using hgclosed
  let hball : ClosedDisk2 ≃ₜ ↥T :=
    (Homeomorph.setCongr hg.symm).trans (g.image T).symm
  let hs : ↥T ≃ₜ ↥(Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := {
    toFun := fun x => ⟨![1 - x.1 0 - x.1 1, x.1 0, x.1 1], by
      refine ⟨?_, ?_⟩
      · intro i
        fin_cases i
        · dsimp
          linarith [x.2.2.2]
        · exact x.2.1
        · exact x.2.2.1
      · simp [Fin.sum_univ_succ]
      ⟩
    invFun := fun y => ⟨!₂[y.1 1, y.1 2], by
      refine ⟨y.2.1 1, y.2.1 2, ?_⟩
      change y.1 1 + y.1 2 ≤ 1
      have hsum : y.1 0 + y.1 1 + y.1 2 = 1 := by
        simpa [Fin.sum_univ_succ, add_assoc] using y.2.2
      linarith [y.2.1 0]⟩
    left_inv := fun x => by
      apply Subtype.ext
      ext i
      fin_cases i <;> rfl
    right_inv := fun y => by
      apply Subtype.ext
      funext i
      fin_cases i
      · have hsum : y.1 0 + y.1 1 + y.1 2 = 1 := by
          simpa [Fin.sum_univ_succ, add_assoc] using y.2.2
        change 1 - y.1 1 - y.1 2 = y.1 0
        linarith
      · rfl
      · rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      fun_prop
    continuous_invFun := by
      apply Continuous.subtype_mk
      change Continuous (fun y : ↥(Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) =>
        WithLp.toLp 2 ![y.1 1, y.1 2])
      apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
      apply continuous_pi
      intro i
      fin_cases i
      · exact (continuous_apply 1).comp continuous_subtype_val
      · exact (continuous_apply 2).comp continuous_subtype_val
  }
  exact ⟨hball.trans hs⟩

/-- P4 candidate: construct the original parametrized boundary as an actual
map into the same region, retaining both pointwise and frontier equalities. -/
theorem polygonLoop_boundary_restriction_exists (P : PolygonalKnot)
    (hplanar : ∀ i, P.polygon.vertex i 2 = 0) (U : Set (Euc 2))
    (hfrontier : frontier U = Set.range (planarProjection ∘ polygonLoop P))
    (hcontained : Set.range (planarProjection ∘ polygonLoop P) ⊆ U) :
    ∃ boundary : C(Circle, ↥U), IsEmbedding boundary ∧
      Set.range (fun z => (boundary z : Euc 2)) = frontier U ∧
      ∀ z, (boundary z : Euc 2) = planarProjection (polygonLoop P z) := by
  let boundary : C(Circle, ↥U) :=
    ⟨fun z => ⟨planarProjection (polygonLoop P z), hcontained ⟨z, rfl⟩⟩,
      (polygonLoop_planar_projection_embedding P hplanar).continuous.subtype_mk _⟩
  have hboundary : IsEmbedding boundary := by
    apply (IsEmbedding.subtypeVal.of_comp_iff).mp
    exact polygonLoop_planar_projection_embedding P hplanar
  exact ⟨boundary, hboundary, hfrontier.symm, fun _ => rfl⟩


theorem finite_planar_disk_exists (P : PolygonalKnot)
    (hplanar : ∀ i, P.polygon.vertex i 2 = 0) : Nonempty (FinitePlanarDisk P) := by
  let J := Set.range (planarProjection ∘ polygonLoop P)
  have hJ : DifferentialGeometry.Topology.PiecewiseLinear.IsPLSphere 1 J :=
    polygonLoop_planar_isPLSphere P hplanar
  obtain ⟨K, hfinite, hK, hrestriction⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.exists_triangulation_closure_inside_of_isPLSphere_one hJ
  have hJclosed : IsClosed J := by
    exact (isCompact_range (polygonLoop_planar_projection_embedding P hplanar).continuous).isClosed
  obtain ⟨vertexCount, vertex, triangleCount, triangle, hface, hcard, hnondegenerate, hregion⟩ :=
    finite_planar_complex_triangle_carrier K hfinite (Schoenflies.inside J)
      (Schoenflies.isOpen_inside hJclosed) hK
  let region := ⋃ i, closedTriangle (vertex (triangle i 0))
    (vertex (triangle i 1)) (vertex (triangle i 2))
  have hregion_inside : region = closure (Schoenflies.inside J) := hregion.trans hK
  have hfrontier : frontier region = J := by
    rw [hregion_inside]
    exact DifferentialGeometry.Topology.PiecewiseLinear.frontier_closure_inside_of_isPLSphere_one hJ
  have hcontained : J ⊆ region := by
    rw [← hfrontier]
    exact frontier_subset_iff_isClosed.mpr (hregion_inside ▸ isClosed_closure)
  obtain ⟨boundary, hboundary, hboundary_eq, hparametrization⟩ :=
    polygonLoop_boundary_restriction_exists P hplanar region hfrontier hcontained
  obtain ⟨e⟩ := closedDisk2_stdSimplex_homeomorph_exists
  obtain ⟨f, hf⟩ :=
    DifferentialGeometry.Topology.PiecewiseLinear.isPLBall_closure_inside_of_isPLSphere_one hJ
  let diskHomeomorph : ClosedDisk2 ≃ₜ ↥region :=
    e.trans (hf.homeomorph.trans (Homeomorph.setCongr hregion_inside.symm))
  exact ⟨{
    vertexCount := vertexCount
    vertex := vertex
    triangleCount := triangleCount
    triangle := triangle
    nondegenerate := hnondegenerate
    diskHomeomorph := diskHomeomorph
    boundary := boundary
    boundary_embedding := hboundary
    boundary_eq := hboundary_eq
    parametrization_eq := hparametrization
  }⟩


def halfTwistedBand (sign : ℤ) (width : ℝ) (p : Time × Time) : Euc 3 :=
  !₂[(p.1 : ℝ), width * (2 * (p.2 : ℝ) - 1) * Real.cos (Real.pi * (p.1 : ℝ)),
    sign * width * (2 * (p.2 : ℝ) - 1) * Real.sin (Real.pi * (p.1 : ℝ))]

structure DiskBandData {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    (R : OrientedResolution D) where
  disk : ∀ i, FinitePlanarDisk (R.loop i)
  height : Fin R.count → ℝ
  distinct_heights : Function.Injective height
  incident : Fin D.crossingCount → Fin 2 → Fin R.count
  attaching : ∀ k e, C(Time, (disk (incident k e)).Carrier)
  attaching_embedding : ∀ k e, IsEmbedding (attaching k e)
  attaching_boundary : ∀ k e t,
    (attaching k e t : Euc 2) ∈ frontier (disk (incident k e)).region
  attachingAngle : Fin D.crossingCount → Fin 2 → ℝ → ℝ
  attachingAngle_smooth : ∀ k e, ContDiff ℝ ∞ (attachingAngle k e)
  attaching_parameter : ∀ k e t,
    attaching k e t = (disk (incident k e)).boundary (Circle.exp (attachingAngle k e t))
  bandOrientation : Fin D.crossingCount → ℝ
  bandOrientation_unit : ∀ k, bandOrientation k = 1 ∨ bandOrientation k = -1
  oriented_attachment : ∀ k t, 0 ≤ t → t ≤ 1 →
    0 < bandOrientation k * deriv (attachingAngle k 0) t ∧
    bandOrientation k * deriv (attachingAngle k 1) t < 0
  attaching_disjoint : ∀ k e l f, (k, e) ≠ (l, f) →
    Disjoint (Set.range (fun t => (disk (incident k e)).lifted (height (incident k e)) (attaching k e t)))
      (Set.range (fun t => (disk (incident l f)).lifted (height (incident l f)) (attaching l f t)))
  width : Fin D.crossingCount → ℝ
  width_pos : ∀ k, 0 < width k
  bandAmbient : Fin D.crossingCount → Diffeomorph 𝓘(ℝ, Euc 3) 𝓘(ℝ, Euc 3) (Euc 3) (Euc 3) ∞
  band_attachment : ∀ k t,
    bandAmbient k (halfTwistedBand (D.crossing k).sign (width k) (0, t)) =
      (disk (incident k 0)).lifted (height (incident k 0)) (attaching k 0 t) ∧
    bandAmbient k (halfTwistedBand (D.crossing k).sign (width k) (1, t)) =
      (disk (incident k 1)).lifted (height (incident k 1)) (attaching k 1 t)
  bands_disjoint : Pairwise (fun k l => Disjoint
    (Set.range (bandAmbient k ∘ halfTwistedBand (D.crossing k).sign (width k)))
    (Set.range (bandAmbient l ∘ halfTwistedBand (D.crossing l).sign (width l))))
  no_extra_disk_intersection : ∀ k i,
    Set.range (bandAmbient k ∘ halfTwistedBand (D.crossing k).sign (width k)) ∩
      Set.range ((disk i).lifted (height i)) =
      ⋃ e : Fin 2, if incident k e = i then
        Set.range (fun t => (disk (incident k e)).lifted (height (incident k e)) (attaching k e t)) else ∅
  incidence_connected : ∀ i j : Fin R.count,
    Relation.ReflTransGen (fun a b => ∃ k, (incident k 0 = a ∧ incident k 1 = b) ∨
      (incident k 0 = b ∧ incident k 1 = a)) i j

namespace DiskBandData
variable {P : PolygonalKnot} {D : RegularOrientedDiagram P} {R : OrientedResolution D}
abbrev RawPieces (B : DiskBandData R) :=
  (Σ i : Fin R.count, (B.disk i).Carrier) ⊕ (Fin D.crossingCount × (Time × Time))
def rawMap (B : DiskBandData R) : B.RawPieces → Euc 3
  | Sum.inl p => (B.disk p.1).lifted (B.height p.1) p.2
  | Sum.inr p => B.bandAmbient p.1 (halfTwistedBand (D.crossing p.1).sign (B.width p.1) p.2)
def attachmentRelation (B : DiskBandData R) (x y : B.RawPieces) : Prop :=
  ∃ (k : Fin D.crossingCount) (e : Fin 2) (t : Time),
    x = Sum.inl ⟨B.incident k e, B.attaching k e t⟩ ∧
    y = Sum.inr (k, ((if e = 0 then 0 else 1), t))
def gluingSetoid (B : DiskBandData R) : Setoid B.RawPieces :=
  Relation.EqvGen.setoid B.attachmentRelation
abbrev Carrier (B : DiskBandData R) := Quotient B.gluingSetoid
theorem rawMap_respects (B : DiskBandData R) :
    ∀ x y, B.gluingSetoid.r x y → B.rawMap x = B.rawMap y := by
  intro x y h
  change Relation.EqvGen B.attachmentRelation x y at h
  induction h with
  | rel x y h =>
      rcases h with ⟨k, e, t, rfl, rfl⟩
      fin_cases e
      · exact (B.band_attachment k t).1.symm
      · exact (B.band_attachment k t).2.symm
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz
def map (B : DiskBandData R) : B.Carrier → Euc 3 := Quotient.lift B.rawMap B.rawMap_respects
def rawBoundary (B : DiskBandData R) : Set B.RawPieces :=
  {x | match x with
    | Sum.inl p => (p.2 : Euc 2) ∈ frontier (B.disk p.1).region ∧
        ¬ ∃ (k : Fin D.crossingCount) (e : Fin 2) (t : Time), 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧
          Sum.inl p = (Sum.inl ⟨B.incident k e, B.attaching k e t⟩ : B.RawPieces)
    | Sum.inr p => p.2.2 = 0 ∨ p.2.2 = 1}
def boundarySet (B : DiskBandData R) : Set B.Carrier := Quotient.mk B.gluingSetoid '' B.rawBoundary
end DiskBandData

structure DiskBandBoundaryCertificate {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandData R) where
  boundary : C(Circle, B.Carrier)
  boundary_embedding : IsEmbedding boundary
  covers_boundary : Set.range boundary = B.boundarySet
  oriented_diagram_isotopy : PiecewiseCurveIsotopy (B.map ∘ boundary) (polygonLoop P)

structure DiskBandPresentation {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    (R : OrientedResolution D) where
  data : DiskBandData R
  boundary : DiskBandBoundaryCertificate data



theorem disk_band_quotient_embedding {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandData R) : IsEmbedding B.map := by
  letI (i : Fin R.count) : CompactSpace (B.disk i).Carrier :=
    (B.disk i).diskHomeomorph.compactSpace
  have hlift (i : Fin R.count) : Continuous ((B.disk i).lifted (B.height i)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val
    · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp continuous_subtype_val
    · exact continuous_const
  have htwist (k : Fin D.crossingCount) :
      Continuous (halfTwistedBand (D.crossing k).sign (B.width k)) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j <;> dsimp [halfTwistedBand] <;> fun_prop
  have hraw : Continuous B.rawMap := by
    apply continuous_sum_dom.mpr
    constructor
    · apply continuous_sigma
      intro i
      exact hlift i
    · apply continuous_prod_of_discrete_left.mpr
      intro k
      exact (B.bandAmbient k).continuous.comp (htwist k)
  have hcont : Continuous B.map := hraw.quotient_lift B.rawMap_respects
  have hlift_inj (i : Fin R.count) : Function.Injective ((B.disk i).lifted (B.height i)) := by
    intro x y h
    apply Subtype.ext
    ext j
    fin_cases j
    · exact congrArg (fun z : Euc 3 => z 0) h
    · exact congrArg (fun z : Euc 3 => z 1) h
  have htwist_inj (k : Fin D.crossingCount) :
      Function.Injective (halfTwistedBand (D.crossing k).sign (B.width k)) := by
    intro p q h
    have ht : p.1 = q.1 := Subtype.ext (congrArg (fun z : Euc 3 => z 0) h)
    have hcos := congrArg (fun z : Euc 3 => z 1) h
    have hsin := congrArg (fun z : Euc 3 => z 2) h
    dsimp [halfTwistedBand] at hcos hsin
    rw [ht] at hcos hsin
    have hw : B.width k ≠ 0 := ne_of_gt (B.width_pos k)
    have hsign : ((D.crossing k).sign : ℝ) ≠ 0 := by
      rw [(D.crossing k).sign_eq]
      split_ifs <;> norm_num
    have hsecond : (p.2 : ℝ) = (q.2 : ℝ) := by
      by_cases hc : Real.cos (Real.pi * (q.1 : ℝ)) = 0
      · have hs : Real.sin (Real.pi * (q.1 : ℝ)) ≠ 0 := by
          intro hs
          have hid := Real.sin_sq_add_cos_sq (Real.pi * (q.1 : ℝ))
          rw [hc, hs] at hid
          norm_num at hid
        have heq := (mul_right_cancel₀ hs hsin)
        have heq' := (mul_left_cancel₀ (mul_ne_zero hsign hw) heq)
        linarith
      · have heq := (mul_right_cancel₀ hc hcos)
        have heq' := (mul_left_cancel₀ hw heq)
        linarith
    exact Prod.ext ht (Subtype.ext hsecond)
  have hband_inj (k : Fin D.crossingCount) :
      Function.Injective (B.bandAmbient k ∘ halfTwistedBand (D.crossing k).sign (B.width k)) :=
    (B.bandAmbient k).injective.comp (htwist_inj k)
  have hcross (i : Fin R.count) (x : (B.disk i).Carrier)
      (k : Fin D.crossingCount) (p : Time × Time)
      (h : (B.disk i).lifted (B.height i) x =
        B.bandAmbient k (halfTwistedBand (D.crossing k).sign (B.width k) p)) :
      Quotient.mk B.gluingSetoid (Sum.inl ⟨i, x⟩) =
        Quotient.mk B.gluingSetoid (Sum.inr (k, p)) := by
    have hm : (B.disk i).lifted (B.height i) x ∈
        Set.range (B.bandAmbient k ∘ halfTwistedBand (D.crossing k).sign (B.width k)) ∩
          Set.range ((B.disk i).lifted (B.height i)) :=
      ⟨⟨p, h.symm⟩, ⟨x, rfl⟩⟩
    rw [B.no_extra_disk_intersection k i] at hm
    rcases mem_iUnion.mp hm with ⟨e, he⟩
    split_ifs at he with hi
    · subst i
      rcases he with ⟨t, ht⟩
      have hx := hlift_inj _ ht
      subst x
      have hp : ((if e = 0 then 0 else 1), t) = p := by
        apply hband_inj k
        change B.bandAmbient k (halfTwistedBand (D.crossing k).sign (B.width k)
          ((if e = 0 then 0 else 1), t)) = _
        fin_cases e
        · exact ((B.band_attachment k t).1).trans h
        · exact ((B.band_attachment k t).2).trans h
      subst p
      exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨k, e, t, rfl, rfl⟩)
    · exact False.elim he
  have hinj : Function.Injective B.map := by
    intro x y
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    rename_i x y
    intro h
    rcases x with ⟨i, x⟩ | ⟨k, p⟩ <;> rcases y with ⟨j, y⟩ | ⟨l, q⟩
    · change (B.disk i).lifted (B.height i) x = (B.disk j).lifted (B.height j) y at h
      have hij := B.distinct_heights (congrArg (fun z : Euc 3 => z 2) h)
      subst j
      have hxy := hlift_inj i h
      subst y
      rfl
    · exact hcross i x l q h
    · exact (hcross j y k p h.symm).symm
    · change B.bandAmbient k (halfTwistedBand (D.crossing k).sign (B.width k) p) =
        B.bandAmbient l (halfTwistedBand (D.crossing l).sign (B.width l) q) at h
      by_cases hkl : k = l
      · subst l
        have hpq := hband_inj k h
        subst q
        rfl
      · exact False.elim ((Set.disjoint_left.mp (B.bands_disjoint hkl)) ⟨p, rfl⟩ ⟨q, h.symm⟩)
  exact (hcont.isClosedEmbedding hinj).isEmbedding
theorem disk_band_quotient_compact {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandData R) : CompactSpace B.Carrier := by
  letI (i : Fin R.count) : CompactSpace (B.disk i).Carrier :=
    (B.disk i).diskHomeomorph.compactSpace
  infer_instance
theorem disk_band_quotient_connected {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandData R) : ConnectedSpace B.Carrier := by
  letI : PathConnectedSpace ClosedDisk2 :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_closedBall (0 : Euc 2) 1).isPathConnected
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩)
  letI : PathConnectedSpace Time :=
    isPathConnected_iff_pathConnectedSpace.mp ((convex_Icc (0 : ℝ) 1).isPathConnected
      ⟨0, by simp⟩)
  letI (i : Fin R.count) : PathConnectedSpace (B.disk i).Carrier :=
    (B.disk i).diskHomeomorph.pathConnectedSpace
  let qd (i : Fin R.count) (x : (B.disk i).Carrier) : B.Carrier :=
    Quotient.mk B.gluingSetoid (Sum.inl ⟨i, x⟩)
  let qb (k : Fin D.crossingCount) (x : Time × Time) : B.Carrier :=
    Quotient.mk B.gluingSetoid (Sum.inr (k, x))
  have hd (i : Fin R.count) : Continuous (qd i) :=
    continuous_quotient_mk'.comp (continuous_inl.comp continuous_sigmaMk)
  have hb (k : Fin D.crossingCount) : Continuous (qb k) :=
    continuous_quotient_mk'.comp (continuous_inr.comp (continuous_const.prodMk continuous_id))
  have he (k : Fin D.crossingCount) (e : Fin 2) (t : Time) :
      qd (B.incident k e) (B.attaching k e t) = qb k ((if e = 0 then 0 else 1), t) :=
    Quotient.sound (Relation.EqvGen.rel _ _ ⟨k, e, t, rfl, rfl⟩)
  have he0 (k : Fin D.crossingCount) (t : Time) :
      qd (B.incident k 0) (B.attaching k 0 t) = qb k (0, t) := by simpa using he k 0 t
  have he1 (k : Fin D.crossingCount) (t : Time) :
      qd (B.incident k 1) (B.attaching k 1 t) = qb k (1, t) := by simpa using he k 1 t
  have hjd (i : Fin R.count) (x y : (B.disk i).Carrier) : Joined (qd i x) (qd i y) :=
    (PathConnectedSpace.joined x y).map (hd i)
  have hjb (k : Fin D.crossingCount) (x y : Time × Time) : Joined (qb k x) (qb k y) :=
    (PathConnectedSpace.joined x y).map (hb k)
  let anchor (i : Fin R.count) : (B.disk i).Carrier :=
    (B.disk i).diskHomeomorph ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
  have hedge (a b : Fin R.count)
      (h : ∃ k, (B.incident k 0 = a ∧ B.incident k 1 = b) ∨
        (B.incident k 0 = b ∧ B.incident k 1 = a)) :
      Joined (qd a (anchor a)) (qd b (anchor b)) := by
    rcases h with ⟨k, h | h⟩
    · rcases h with ⟨rfl, rfl⟩
      have mid := hjb k (0, 0) (1, 0)
      rw [← he0 k 0, ← he1 k 0] at mid
      exact (hjd _ _ _).trans (mid.trans (hjd _ _ _))
    · rcases h with ⟨rfl, rfl⟩
      have mid := hjb k (0, 0) (1, 0)
      rw [← he0 k 0, ← he1 k 0] at mid
      exact ((hjd _ _ _).trans (mid.trans (hjd _ _ _))).symm
  have hanchors (a b : Fin R.count) : Joined (qd a (anchor a)) (qd b (anchor b)) := by
    have h := B.incidence_connected a b
    induction h with
    | refl => exact Joined.refl _
    | tail h hstep ih => exact ih.trans (hedge _ _ hstep)
  let base : Fin R.count := ⟨0, R.count_pos⟩
  have hall (x : B.Carrier) : Joined (qd base (anchor base)) x := by
    induction x using Quotient.inductionOn with
    | h x =>
      rcases x with ⟨i, x⟩ | ⟨k, x⟩
      · exact (hanchors base i).trans (hjd _ _ _)
      · have h := (hanchors base (B.incident k 0)).trans
          (hjd _ _ (B.attaching k 0 0))
        rw [he0 k 0] at h
        exact h.trans (hjb k (0, 0) x)
  letI : PathConnectedSpace B.Carrier :=
    { nonempty := ⟨qd base (anchor base)⟩
      joined := fun x y => (hall x).symm.trans (hall y) }
  infer_instance



