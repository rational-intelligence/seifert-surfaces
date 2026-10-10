import WhiteheadSupport.Port.CWCylinderCube
import WhiteheadSupport.Port.CWSphereNormBridge
import WhiteheadSupport.Port.CWBasic

namespace SeifertSurfaces.WhiteheadSupport.Port.CW

universe u v

open Metric Topology

/-- The three closed pieces of the characteristic cylinder boundary. -/
def cylinderFaceZero (n : ℕ) : Set ↥(cylinderBoundary n) :=
  {p | p.val.1 = 0}

def cylinderFaceOne (n : ℕ) : Set ↥(cylinderBoundary n) :=
  {p | p.val.1 = 1}

def cylinderFaceSide (n : ℕ) : Set ↥(cylinderBoundary n) :=
  {p | p.val.2.val ∈ sphere (0 : Fin n → ℝ) 1}

theorem cylinderFaceZero_closed (n : ℕ) : IsClosed (cylinderFaceZero n) := by
  exact isClosed_singleton.preimage (by fun_prop)

theorem cylinderFaceOne_closed (n : ℕ) : IsClosed (cylinderFaceOne n) := by
  exact isClosed_singleton.preimage (by fun_prop)

theorem cylinderFaceSide_closed (n : ℕ) : IsClosed (cylinderFaceSide n) := by
  exact isClosed_sphere.preimage (by fun_prop)

theorem cylinderFaces_cover (n : ℕ) :
    cylinderFaceZero n ∪ cylinderFaceOne n ∪ cylinderFaceSide n = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases cylinderBoundary_cases n p.val p.property with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem cylinderFaceUnion_closed (n : ℕ) :
    IsClosed (cylinderFaceZero n ∪ cylinderFaceOne n ∪ cylinderFaceSide n) := by
  simpa [Set.union_assoc] using (cylinderFaceZero_closed n).union
    ((cylinderFaceOne_closed n).union (cylinderFaceSide_closed n))

theorem cylinderFaceCover_locallyFinite (n : ℕ) :
    LocallyFinite (fun j : Fin 3 =>
      match j with
      | 0 => cylinderFaceZero n
      | 1 => cylinderFaceOne n
      | 2 => cylinderFaceSide n) := by
  exact locallyFinite_of_finite _

theorem cylinderBoundary_face_zero_agrees
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    {x₀ : X} (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (b : CellSphere n) :
    Hn (0, attaching n i b) = (characteristicToStep n i
      ⟨b.val, sphere_subset_closedBall b.property⟩).val := by
  rw [Hn.apply_zero]
  rfl

theorem cylinderBoundary_face_one_agrees
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    {x₀ : X} (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (b : CellSphere n) :
    Hn (1, attaching n i b) = x₀ := by
  exact Hn.apply_one (attaching n i b)

noncomputable def cylinderFaceZeroMap
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (n : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(↥(cylinderFaceZero n), X) :=
  ⟨fun p => characteristic n i p.val.val.2,
    (characteristic n i).continuous.comp
      (continuous_snd.comp
        (continuous_subtype_val.comp continuous_subtype_val))⟩

def cylinderFaceOneMap {X : Type u} [TopologicalSpace X]
    (n : ℕ) (x₀ : X) : C(↥(cylinderFaceOne n), X) :=
  ContinuousMap.const _ x₀

noncomputable def cylinderFaceSideMap
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    {x₀ : X} (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(↥(cylinderFaceSide n), X) :=
  ⟨fun p => Hn (p.val.val.1,
      attaching n i ⟨p.val.val.2.val, p.property⟩), by
    apply Hn.continuous.comp
    apply Continuous.prodMk
    · exact continuous_fst.comp
        (continuous_subtype_val.comp continuous_subtype_val)
    · apply (attaching n i).continuous.comp
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_snd).comp
        (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- Finite closed pasting for the three faces of a cylinder boundary. -/
private noncomputable def glueThreeClosed
    {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (s t u : Set A) (hs : IsClosed s) (ht : IsClosed t) (hu : IsClosed u)
    (hcov : s ∪ t ∪ u = Set.univ)
    (f : C(s, X)) (g : C(t, X)) (h : C(u, X))
    (hfg : ∀ (a : A) (ha : a ∈ s) (hb : a ∈ t),
      f ⟨a, ha⟩ = g ⟨a, hb⟩)
    (hfh : ∀ (a : A) (ha : a ∈ s) (hc : a ∈ u),
      f ⟨a, ha⟩ = h ⟨a, hc⟩)
    (hgh : ∀ (a : A) (hb : a ∈ t) (hc : a ∈ u),
      g ⟨a, hb⟩ = h ⟨a, hc⟩) : C(A, X) := by
  let S : Fin 3 → Set A := Fin.cons s (Fin.cons t (fun _ => u))
  let φ : ∀ j : Fin 3, C(S j, X) :=
    Fin.cons f (Fin.cons g (fun _ => h))
  have hφ : ∀ (i j : Fin 3) (a : A) (hi : a ∈ S i) (hj : a ∈ S j),
      φ i ⟨a, hi⟩ = φ j ⟨a, hj⟩ := by
    intro i j a hi hj
    fin_cases i <;> fin_cases j
    all_goals simp [S, φ] at hi hj ⊢
    all_goals first | rfl | exact hfg a hi hj | exact (hfg a hj hi).symm |
      exact hfh a hi hj | exact (hfh a hj hi).symm |
      exact hgh a hi hj | exact (hgh a hj hi).symm
  have hS : ⋃ j : Fin 3, S j = Set.univ := by
    ext a
    constructor
    · intro _
      trivial
    · intro _
      have ha : a ∈ s ∪ t ∪ u := hcov.symm ▸ Set.mem_univ a
      rcases ha with (ha | ha) | ha
      · exact Set.mem_iUnion.mpr ⟨0, ha⟩
      · exact Set.mem_iUnion.mpr ⟨1, ha⟩
      · exact Set.mem_iUnion.mpr ⟨2, ha⟩
  let F : A → X := Set.liftCover S (fun j => φ j) hφ hS
  have hcl : ∀ j : Fin 3, IsClosed (S j) := by
    intro j
    fin_cases j <;> simp [S]
    · exact hs
    · exact ht
    · exact hu
  have hcont : ∀ j : Fin 3, ContinuousOn F (S j) := by
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun a : S j => F a.val)
    have heq : (fun a : S j => F a.val) = φ j := by
      funext a
      exact Set.liftCover_coe a
    rw [heq]
    exact (φ j).continuous
  exact ⟨F, (locallyFinite_of_finite S).continuous hS hcl hcont⟩

/-- The prescribed zero, one, and lateral data form a continuous map on
the entire cylinder boundary. -/
noncomputable def cylinderBoundaryMap
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (x₀ : X) (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n) :
    C(↥(cylinderBoundary n), X) := by
  apply glueThreeClosed (cylinderFaceZero n) (cylinderFaceOne n)
    (cylinderFaceSide n)
    (cylinderFaceZero_closed n) (cylinderFaceOne_closed n)
    (cylinderFaceSide_closed n) (cylinderFaces_cover n)
    (cylinderFaceZeroMap n i) (cylinderFaceOneMap n x₀)
    (cylinderFaceSideMap n Hn i)
  · intro a ha hb
    have h : (0 : unitInterval) = 1 := ha.symm.trans hb
    exact (zero_ne_one h).elim
  · intro a ha hc
    let b : CellSphere n := ⟨a.val.2.val, hc⟩
    change characteristic n i a.val.2 = Hn (a.val.1, attaching n i b)
    rw [ha]
    exact (cylinderBoundary_face_zero_agrees n Hn i b).symm
  · intro a hb hc
    let b : CellSphere n := ⟨a.val.2.val, hc⟩
    change x₀ = Hn (a.val.1, attaching n i b)
    rw [hb]
    exact (cylinderBoundary_face_one_agrees n Hn i b).symm

theorem cylinderBoundaryMap_zero
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (x₀ : X) (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (w : CellDisk n) :
    cylinderBoundaryMap x₀ n Hn i
      ⟨((0 : unitInterval), w), cylinderBoundary_zero n w⟩ =
      characteristic n i w := by
  unfold cylinderBoundaryMap glueThreeClosed
  dsimp only [ContinuousMap.coe_mk]
  rw [Set.liftCover_of_mem (i := (0 : Fin 3)) (hx := by rfl)]
  rfl

theorem cylinderBoundaryMap_one
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (x₀ : X) (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (w : CellDisk n) :
    cylinderBoundaryMap x₀ n Hn i
      ⟨((1 : unitInterval), w), cylinderBoundary_one n w⟩ = x₀ := by
  unfold cylinderBoundaryMap glueThreeClosed
  dsimp only [ContinuousMap.coe_mk]
  rw [Set.liftCover_of_mem (i := (1 : Fin 3)) (hx := by rfl)]
  rfl

theorem cylinderBoundaryMap_side
    {X : Type u} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)]
    (x₀ : X) (n : ℕ) (Hn : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)))
      ((ContinuousMap.const X x₀).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X))))
    (i : Topology.CWComplex.cell (Set.univ : Set X) n)
    (t : unitInterval) (b : CellSphere n) :
    cylinderBoundaryMap x₀ n Hn i
      ⟨(t, ⟨b.val, sphere_subset_closedBall b.property⟩),
        cylinderBoundary_side n t b⟩ = Hn (t, attaching n i b) := by
  unfold cylinderBoundaryMap glueThreeClosed
  dsimp only [ContinuousMap.coe_mk]
  rw [Set.liftCover_of_mem (i := (2 : Fin 3)) (hx := b.property)]
  rfl

end SeifertSurfaces.WhiteheadSupport.Port.CW
