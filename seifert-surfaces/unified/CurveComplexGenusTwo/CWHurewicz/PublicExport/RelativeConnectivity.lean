import CurveComplexGenusTwo.CWHurewicz.CWBasic

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

noncomputable def diskBoundaryInclusion (n : ℕ) : C(CellSphere n, CellDisk n) :=
  ⟨fun z => ⟨z.val, Metric.sphere_subset_closedBall z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- A based map of the pair `(Dⁿ, ∂Dⁿ)` into `(X, A)`.
The chosen `b` is a point of the boundary, and `x` lies in `A`. -/
structure RelativeDiskMap (n : ℕ) (X : Type) [TopologicalSpace X]
    (A : Set X) (x : ↥A) (b : CellSphere n) where
  map : C(CellDisk n, X)
  boundary : ∀ z : CellSphere n, map (diskBoundaryInclusion n z) ∈ A
  based : map (diskBoundaryInclusion n b) = x.val

/-- Homotopy through pair maps keeping the chosen boundary basepoint fixed. -/
structure RelativeDiskHomotopy {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n}
    (f g : RelativeDiskMap n X A x b) where
  map : C(unitInterval × CellDisk n, X)
  at_zero : ∀ z, map (⟨0, by norm_num⟩, z) = f.map z
  at_one : ∀ z, map (⟨1, by norm_num⟩, z) = g.map z
  boundary : ∀ t z, map (t, diskBoundaryInclusion n z) ∈ A
  based : ∀ t, map (t, diskBoundaryInclusion n b) = x.val

namespace RelativeDiskHomotopy
variable {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n}
    {f g h : RelativeDiskMap n X A x b}

private def pairProperty (u : C(CellDisk n, X)) : Prop :=
  (∀ z : CellSphere n, u (diskBoundaryInclusion n z) ∈ A) ∧
  u (diskBoundaryInclusion n b) = x.val

private def toWith (H : RelativeDiskHomotopy f g) :
    ContinuousMap.HomotopyWith f.map g.map (pairProperty (x := x) (b := b)) where
  toContinuousMap := H.map
  map_zero_left := H.at_zero
  map_one_left := H.at_one
  prop' t := ⟨H.boundary t, H.based t⟩

private def ofWith (H : ContinuousMap.HomotopyWith f.map g.map
    (pairProperty (x := x) (b := b))) : RelativeDiskHomotopy f g where
  map := H.toHomotopy.toContinuousMap
  at_zero := H.map_zero_left
  at_one := H.map_one_left
  boundary t := (H.prop t).1
  based t := (H.prop t).2

def refl (f : RelativeDiskMap n X A x b) : RelativeDiskHomotopy f f :=
  ofWith (.refl f.map ⟨f.boundary, f.based⟩)

def symm (H : RelativeDiskHomotopy f g) : RelativeDiskHomotopy g f :=
  ofWith H.toWith.symm

noncomputable def trans (F : RelativeDiskHomotopy f g) (G : RelativeDiskHomotopy g h) :
    RelativeDiskHomotopy f h := ofWith (F.toWith.trans G.toWith)
end RelativeDiskHomotopy

def relativeDiskSetoid {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n} :
    Setoid (RelativeDiskMap n X A x b) where
  r f g := Nonempty (RelativeDiskHomotopy f g)
  iseqv := ⟨fun f => ⟨.refl f⟩,
    fun ⟨H⟩ => ⟨H.symm⟩, fun ⟨F⟩ ⟨G⟩ => ⟨F.trans G⟩⟩

abbrev RelativePi (n : ℕ) (X : Type) [TopologicalSpace X]
    (A : Set X) (x : ↥A) (b : CellSphere n) :=
  Quotient (relativeDiskSetoid (n := n) (X := X) (A := A) (x := x) (b := b))

namespace RelativeDiskMap
variable {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n}

def const (x : ↥A) (b : CellSphere n) : RelativeDiskMap n X A x b where
  map := ContinuousMap.const _ x.val
  boundary _ := x.property
  based := rfl

private noncomputable def diskContract (b : CellSphere n) :
    C(I × CellDisk n, CellDisk n) :=
  ⟨fun p => ⟨(1 - (p.1 : ℝ)) • p.2.val + (p.1 : ℝ) • b.val,
    (convex_closedBall (0 : Fin n → ℝ) (1 : ℝ)) p.2.property
      (Metric.sphere_subset_closedBall b.property)
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)⟩,
    by fun_prop⟩

noncomputable def contractOfRangeSubset (f : RelativeDiskMap n X A x b)
    (hf : ∀ z, f.map z ∈ A) : RelativeDiskHomotopy f (const x b) where
  map := f.map.comp (diskContract b)
  at_zero z := by simp [diskContract]
  at_one z := by simpa [diskContract, const, diskBoundaryInclusion] using f.based
  boundary t z := hf _
  based t := by
    change f.map _ = x.val
    convert f.based using 1
    congr 1
    apply Subtype.ext
    change (1 - (t : ℝ)) • b.val + (t : ℝ) • b.val = b.val
    rw [← add_smul]
    simp
end RelativeDiskMap

/-- Compression into the subspace kills the actual relative homotopy set. -/
theorem relativePi_subsingleton_of_compression
    {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n}
    (hc : ∀ f : RelativeDiskMap n X A x b,
      ∃ g : RelativeDiskMap n X A x b,
        Nonempty (RelativeDiskHomotopy f g) ∧ ∀ z, g.map z ∈ A) :
    Subsingleton (RelativePi n X A x b) := by
  let c := RelativeDiskMap.const x b
  have hnull (f : RelativeDiskMap n X A x b) :
      Nonempty (RelativeDiskHomotopy f c) := by
    obtain ⟨g, ⟨H⟩, hg⟩ := hc f
    exact ⟨H.trans (g.contractOfRangeSubset hg)⟩
  refine ⟨fun q r => Quotient.inductionOn₂ q r ?_⟩
  intro f g
  apply Quotient.sound
  obtain ⟨F⟩ := hnull f
  obtain ⟨G⟩ := hnull g
  exact ⟨F.trans G.symm⟩

/-- Exact geometric form of vanishing relative homotopy, using the same
reviewed pair maps and based pair homotopies. -/
theorem relativePi_subsingleton_iff_compression
    {n : ℕ} {X : Type} [TopologicalSpace X]
    {A : Set X} {x : ↥A} {b : CellSphere n} :
    Subsingleton (RelativePi n X A x b) ↔
      ∀ f : RelativeDiskMap n X A x b,
        ∃ g : RelativeDiskMap n X A x b,
          Nonempty (RelativeDiskHomotopy f g) ∧ ∀ z, g.map z ∈ A := by
  constructor
  · intro h f
    refine ⟨.const x b, ?_, fun _ => x.property⟩
    exact Quotient.exact (h.elim (Quotient.mk _ f)
      (Quotient.mk _ (RelativeDiskMap.const x b)))
  · exact relativePi_subsingleton_of_compression

end CurveComplexGenusTwo.CWHurewicz
