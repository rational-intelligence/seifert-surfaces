import CurveComplexGenusTwo.Topology.GeometricPosition.SubarcCrosscutChartV2
universe u
namespace CurveComplex.PositionUniverseV2
/-- Select compatible disjoint actual square-crosscut patches for a specified
finite collection of disjoint central parameter subarcs, inside their assigned
old-family charts. Their compact patches meet the whole curve in EXACTLY the
selected central subarcs. -/
theorem position_finite_compatible_crosscuts
    (S : Type u) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : Curve S) (K : Type*) [Fintype K]
    (a b : K → ℝ) (hab : ∀ k, a k < b k)
    (hlen : ∀ k, b k - a k < 2 * Real.pi)
    (e : K → OpenPartialHomeomorph S Schoenflies.Plane)
    (hsub : ∀ k, (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k) ⊆ (e k).source)
    (hdis : ∀ i j, i ≠ j → Disjoint
      ((fun t => c.map (Circle.exp t)) '' Set.Icc (a i) (b i))
      ((fun t => c.map (Circle.exp t)) '' Set.Icc (a j) (b j))) :
    ∃ E : K → OpenPartialHomeomorph S Schoenflies.Plane,
      (∀ k, (E k).source ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint (E i).source (E j).source) ∧
      (∀ k, Schoenflies.Plane.closedSquare 0 1 ⊆ (E k).target) ∧
      (∀ k, (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k) ⊆ (E k).source) ∧
      (∀ k, E k (c.map (Circle.exp (a k))) = Schoenflies.Plane.mk (-1) 0 ∧
        E k (c.map (Circle.exp (b k))) = Schoenflies.Plane.mk 1 0) ∧
      (∀ k x, x ∈ (E k).source → (x ∈ c.image ↔ E k x 1 = 0)) ∧
      (∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩
        c.image = (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k)) := by
  classical
  let C : K → Set S := fun k => (fun t => c.map (Circle.exp t)) '' Set.Icc (a k) (b k)
  have hcompact (k : K) : IsCompact (C k) :=
    isCompact_Icc.image (c.embedded.continuous.comp Circle.exp.continuous)
  have hpairs (i j : K) : ∃ A B : Set S,
      IsOpen A ∧ IsOpen B ∧ C i ⊆ A ∧ C j ⊆ B ∧ (i ≠ j → Disjoint A B) := by
    by_cases hij : i = j
    · exact ⟨Set.univ, Set.univ, isOpen_univ, isOpen_univ,
        Set.subset_univ _, Set.subset_univ _, fun h => (h hij).elim⟩
    · obtain ⟨A, B, hA, hB, hCA, hCB, hAB⟩ :=
        normal_separation (hcompact i).isClosed (hcompact j).isClosed (hdis i j hij)
      exact ⟨A, B, hA, hB, hCA, hCB, fun _ => hAB⟩
  choose A B hA hB hCA hCB hAB using hpairs
  let W : K → Set S := fun i => ⋂ j, A i j ∩ B j i
  have hW (i : K) : IsOpen (W i) :=
    isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i))
  have hCW (i : K) : C i ⊆ W i := by
    intro x hx
    exact Set.mem_iInter.mpr (fun j => ⟨hCA i j hx, hCB j i hx⟩)
  have hWW (i j : K) (hij : i ≠ j) : Disjoint (W i) (W j) := by
    apply (hAB i j hij).mono
    · intro x hx
      exact ((Set.mem_iInter.mp hx) j).1
    · intro x hx
      exact ((Set.mem_iInter.mp hx) i).2
  have hcharts (k : K) := position_subarc_crosscut_chart S c (a k) (b k)
    (hab k) (hlen k) (e k) (W k) (hW k)
    (fun x hx => ⟨hCW k hx, hsub k hx⟩)
  choose E hEW hSquare hArc hleft hright hflat hExact using hcharts
  refine ⟨E, ?_, ?_, hSquare, hArc, ?_, hflat, hExact⟩
  · intro k x hx
    exact (hEW k hx).2
  · intro i j hij
    exact (hWW i j hij).mono
      (fun x hx => (hEW i hx).1) (fun x hx => (hEW j hx).1)
  · intro k
    exact ⟨hleft k, hright k⟩
end CurveComplex.PositionUniverseV2
