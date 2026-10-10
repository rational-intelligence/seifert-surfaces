import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.ExcisionClean

namespace CurveComplexGenusTwo.CWHurewicz

open CategoryTheory CategoryTheory.Limits Topology Set

/-- The concrete pointed wedge used by the cubical pinch construction. -/
def geometricWedge (S : Type) (s : S) : Set (S × S) :=
  {p | p.1 = s ∨ p.2 = s}

def geometricFirstAxis {S : Type} (s : S) : Set (geometricWedge S s) :=
  {w | w.val.2 = s}

def geometricSecondAxis {S : Type} (s : S) : Set (geometricWedge S s) :=
  {w | w.val.1 = s}

theorem geometricWedge_axis_cover {S : Type} (s : S) :
    geometricFirstAxis s ∪ geometricSecondAxis s = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  rcases w.property with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The first axis is literally a copy of the pointed space. -/
def geometricFirstAxisHomeo {S : Type} [TopologicalSpace S] (s : S) :
    ↥(geometricFirstAxis s) ≃ₜ S where
  toFun w := w.val.val.1
  invFun z := ⟨⟨(z, s), Or.inr rfl⟩, rfl⟩
  left_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl w.property.symm
  right_inv z := rfl
  continuous_toFun := continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_id.prodMk continuous_const

/-- The first-axis cap cut off away from the wedge point.  For the cube
sphere, `d` is distance from the cube-sphere basepoint in the sphere chart. -/
def geometricExciseFirst {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) : Set (geometricWedge S s) :=
  {w | 1 < d w.val.1}

/-- The exact distance function used for a cube sphere after transporting its
metric through the sphere chart. -/
def geometricChartDistance
    {S T : Type} [TopologicalSpace S] [PseudoMetricSpace T]
    (e : S ≃ₜ T) (s : S) : C(S, ℝ) :=
  ⟨fun z => dist (e z) (e s),
    e.continuous.dist continuous_const⟩

theorem geometricChartDistance_base
    {S T : Type} [TopologicalSpace S] [PseudoMetricSpace T]
    (e : S ≃ₜ T) (s : S) : geometricChartDistance e s s = 0 := by
  simp [geometricChartDistance]

theorem geometricExciseFirst_isOpen {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) : IsOpen (geometricExciseFirst s d) := by
  exact isOpen_Ioi.preimage (d.continuous.comp
    (continuous_fst.comp continuous_subtype_val))

theorem geometricExciseFirst_closure_subset_interior_firstAxis
    {S : Type} [TopologicalSpace S] (s : S) (d : C(S, ℝ))
    (hbase : d s = 0) :
    closure (geometricExciseFirst s d) ⊆
      interior (geometricFirstAxis s) := by
  let D : geometricWedge S s → ℝ := fun w => d w.val.1
  have hD : Continuous D := d.continuous.comp
    (continuous_fst.comp continuous_subtype_val)
  have hclosed : IsClosed {w : geometricWedge S s | 1 ≤ D w} :=
    isClosed_Ici.preimage hD
  have hcl : closure (geometricExciseFirst s d) ⊆
      {w : geometricWedge S s | 1 ≤ D w} := by
    apply closure_minimal
    · intro w hw
      change 1 < D w at hw
      exact le_of_lt hw
    · exact hclosed
  have hopen : IsOpen {w : geometricWedge S s | 0 < D w} :=
    isOpen_Ioi.preimage hD
  have hsubset : {w : geometricWedge S s | 0 < D w} ⊆
      geometricFirstAxis s := by
    intro w hw
    rcases w.property with hfirst | hsecond
    · have : D w = 0 := by simpa [D, hfirst] using hbase
      exact (not_lt_of_ge (le_of_eq this)).elim hw
    · exact hsecond
  intro w hw
  have hdw : 0 < D w := lt_of_lt_of_le (by norm_num) (hcl hw)
  exact interior_maximal hsubset hopen hdw

theorem geometricChartExciseFirst_closure_subset_interior_firstAxis
    {S T : Type} [TopologicalSpace S] [PseudoMetricSpace T]
    (e : S ≃ₜ T) (s : S) :
    closure (geometricExciseFirst s (geometricChartDistance e s)) ⊆
      interior (geometricFirstAxis s) :=
  geometricExciseFirst_closure_subset_interior_firstAxis s
    (geometricChartDistance e s) (geometricChartDistance_base e s)

/-- Inclusion of the second axis into the wedge. -/
def geometricSecondInclusion {S : Type} [TopologicalSpace S] (s : S) :
    C(S, geometricWedge S s) :=
  ⟨fun z => ⟨(s,z), Or.inl rfl⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

/-- Projection of the wedge onto its second coordinate. -/
def geometricSecondProjection {S : Type} [TopologicalSpace S] (s : S) :
    C(geometricWedge S s, S) :=
  ⟨fun w => w.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem geometricSecondProjection_leftInverse
    {S : Type} [TopologicalSpace S] (s : S) :
    (geometricSecondProjection s).comp (geometricSecondInclusion s) =
      ContinuousMap.id S := by
  ext z
  rfl

/-- The second axis avoids every first-axis cap defined above. -/
def geometricSecondRetained {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    C(S, Excised (geometricWedge S s) (geometricExciseFirst s d)) := by
  refine ⟨fun z => ⟨geometricSecondInclusion s z, ?_⟩, ?_⟩
  · change ¬ 1 < d s
    rw [hbase]
    norm_num
  · exact (geometricSecondInclusion s).continuous.subtype_mk _

/-- Projection of the space left after cap excision to the second axis. -/
def geometricRetainedProjection {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) :
    C(Excised (geometricWedge S s) (geometricExciseFirst s d), S) :=
  (geometricSecondProjection s).comp
    ⟨Subtype.val, continuous_subtype_val⟩

theorem geometricRetainedProjection_leftInverse
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    (geometricRetainedProjection s d).comp
        (geometricSecondRetained s d hbase) = ContinuousMap.id S := by
  ext z
  rfl

theorem geometricSecondRetained_inclusion
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Excised (geometricWedge S s) (geometricExciseFirst s d),
        geometricWedge S s)).comp
      (geometricSecondRetained s d hbase) = geometricSecondInclusion s := by
  rfl

theorem geometricSecondInclusion_pair
    {S : Type} [TopologicalSpace S] (s : S) :
    ∀ z ∈ ({s} : Set S),
      geometricSecondInclusion s z ∈ geometricFirstAxis s := by
  intro z hz
  change z = s
  exact hz

theorem geometricSecondProjection_pair
    {S : Type} [TopologicalSpace S] (s : S) :
    ∀ w ∈ geometricFirstAxis s,
      geometricSecondProjection s w ∈ ({s} : Set S) := by
  intro w hw
  exact hw

theorem geometricSecondRetained_pair
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    ∀ z ∈ ({s} : Set S),
      geometricSecondRetained s d hbase z ∈
        excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d) := by
  intro z hz
  exact geometricSecondInclusion_pair s z hz

theorem geometricRetainedProjection_pair
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) :
    ∀ w ∈ excisedSubspace (geometricFirstAxis s)
      (geometricExciseFirst s d),
      geometricRetainedProjection s d w ∈ ({s} : Set S) := by
  intro w hw
  exact hw

/-- The geometric axis inclusion/projection square on relative H₁. -/
theorem geometricRelativeSecond_square
    {S : Type} [TopologicalSpace S] (s : S) :
    homologyToRelative S ({s} : Set S) 1 ≫
        pairRelativeHomologyMap ({s} : Set S) (geometricFirstAxis s)
          (geometricSecondInclusion s) (geometricSecondInclusion_pair s) 1 =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom (geometricSecondInclusion s)) ≫
        homologyToRelative (geometricWedge S s) (geometricFirstAxis s) 1 := by
  exact pairRelativeHomologyMap_commutes _ _ _ _ 1

/-- The cap-excised version of the same absolute-to-relative square. -/
theorem geometricRetainedSecond_square
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    homologyToRelative S ({s} : Set S) 1 ≫
        pairRelativeHomologyMap ({s} : Set S)
          (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
          (geometricSecondRetained s d hbase)
          (geometricSecondRetained_pair s d hbase) 1 =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map
          (TopCat.ofHom (geometricSecondRetained s d hbase)) ≫
        homologyToRelative
          (Excised (geometricWedge S s) (geometricExciseFirst s d))
          (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d)) 1 := by
  exact pairRelativeHomologyMap_commutes _ _ _ _ 1

/-- Actual map on relative homology from the second axis to the wedge. -/
noncomputable def geometricRelativeSecondInclusion
    {S : Type} [TopologicalSpace S] (s : S) :
    relativeHomology S ({s} : Set S) 1 ⟶
      relativeHomology (geometricWedge S s) (geometricFirstAxis s) 1 :=
  pairRelativeHomologyMap ({s} : Set S) (geometricFirstAxis s)
    (geometricSecondInclusion s) (geometricSecondInclusion_pair s) 1

/-- Actual second-coordinate projection on relative homology. -/
noncomputable def geometricRelativeSecondProjection
    {S : Type} [TopologicalSpace S] (s : S) :
    relativeHomology (geometricWedge S s) (geometricFirstAxis s) 1 ⟶
      relativeHomology S ({s} : Set S) 1 :=
  pairRelativeHomologyMap (geometricFirstAxis s) ({s} : Set S)
    (geometricSecondProjection s) (geometricSecondProjection_pair s) 1

theorem geometricRelativeSecond_leftInverse
    {S : Type} [TopologicalSpace S] (s : S) :
    geometricRelativeSecondInclusion s ≫
      geometricRelativeSecondProjection s =
        𝟙 (relativeHomology S ({s} : Set S) 1) := by
  change pairRelativeHomologyMap ({s} : Set S) (geometricFirstAxis s)
      (geometricSecondInclusion s) (geometricSecondInclusion_pair s) 1 ≫
    pairRelativeHomologyMap (geometricFirstAxis s) ({s} : Set S)
      (geometricSecondProjection s) (geometricSecondProjection_pair s) 1 = _
  rw [← pairRelativeHomologyMap_comp]
  simpa only [geometricSecondProjection_leftInverse] using
    pairRelativeHomologyMap_id ({s} : Set S) 1

/-- The retained-axis inclusion after excision, with its actual quotient map. -/
noncomputable def geometricRelativeRetainedInclusion
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    relativeHomology S ({s} : Set S) 1 ⟶
      relativeHomology
        (Excised (geometricWedge S s) (geometricExciseFirst s d))
        (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d)) 1 :=
  pairRelativeHomologyMap ({s} : Set S)
    (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
    (geometricSecondRetained s d hbase)
    (geometricSecondRetained_pair s d hbase) 1

noncomputable def geometricRelativeRetainedProjection
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) :
    relativeHomology
        (Excised (geometricWedge S s) (geometricExciseFirst s d))
        (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d)) 1 ⟶
      relativeHomology S ({s} : Set S) 1 :=
  pairRelativeHomologyMap
    (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
    ({s} : Set S) (geometricRetainedProjection s d)
    (geometricRetainedProjection_pair s d) 1

theorem geometricRelativeRetained_leftInverse
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    geometricRelativeRetainedInclusion s d hbase ≫
      geometricRelativeRetainedProjection s d =
        𝟙 (relativeHomology S ({s} : Set S) 1) := by
  change pairRelativeHomologyMap ({s} : Set S)
      (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
      (geometricSecondRetained s d hbase)
      (geometricSecondRetained_pair s d hbase) 1 ≫
    pairRelativeHomologyMap
      (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
      ({s} : Set S) (geometricRetainedProjection s d)
      (geometricRetainedProjection_pair s d) 1 = _
  rw [← pairRelativeHomologyMap_comp]
  simpa only [geometricRetainedProjection_leftInverse] using
    pairRelativeHomologyMap_id ({s} : Set S) 1

/-- The actual inclusion of the cap-excised wedge into the full wedge. -/
def geometricRetainedAmbientInclusion
    {S : Type} [TopologicalSpace S] (s : S) (d : C(S, ℝ)) :
    C(Excised (geometricWedge S s) (geometricExciseFirst s d),
      geometricWedge S s) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem geometricRetainedAmbientInclusion_pair
    {S : Type} [TopologicalSpace S] (s : S) (d : C(S, ℝ)) :
    ∀ w ∈ excisedSubspace (geometricFirstAxis s)
      (geometricExciseFirst s d),
      geometricRetainedAmbientInclusion s d w ∈ geometricFirstAxis s := by
  intro w hw
  exact hw

/-- The concrete relative map to which singular excision applies. -/
noncomputable def geometricRelativeExcisionMap
    {S : Type} [TopologicalSpace S] (s : S) (d : C(S, ℝ)) :
    relativeHomology
        (Excised (geometricWedge S s) (geometricExciseFirst s d))
        (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d)) 1 ⟶
      relativeHomology (geometricWedge S s) (geometricFirstAxis s) 1 :=
  pairRelativeHomologyMap
    (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
    (geometricFirstAxis s) (geometricRetainedAmbientInclusion s d)
    (geometricRetainedAmbientInclusion_pair s d) 1

theorem geometricRelativeExcisionMap_eq_clean
    {S : Type} [TopologicalSpace S] (s : S) (d : C(S, ℝ)) :
    geometricRelativeExcisionMap s d =
      HomologicalComplex.homologyMap
        (excisionRelativeChainMap (geometricFirstAxis s)
          (geometricExciseFirst s d)) 1 := by
  rfl

/-- The second-axis inclusion commutes with the cap-excision map. -/
theorem geometricRelativeExcision_inclusion_square
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) (hbase : d s = 0) :
    geometricRelativeRetainedInclusion s d hbase ≫
      geometricRelativeExcisionMap s d =
        geometricRelativeSecondInclusion s := by
  change pairRelativeHomologyMap ({s} : Set S)
      (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
      (geometricSecondRetained s d hbase)
      (geometricSecondRetained_pair s d hbase) 1 ≫
    pairRelativeHomologyMap
      (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
      (geometricFirstAxis s) (geometricRetainedAmbientInclusion s d)
      (geometricRetainedAmbientInclusion_pair s d) 1 = _
  rw [← pairRelativeHomologyMap_comp]
  rfl

/-- The second projection commutes with the cap-excision map. -/
theorem geometricRelativeExcision_projection_square
    {S : Type} [TopologicalSpace S]
    (s : S) (d : C(S, ℝ)) :
    geometricRelativeExcisionMap s d ≫
      geometricRelativeSecondProjection s =
        geometricRelativeRetainedProjection s d := by
  change pairRelativeHomologyMap
      (excisedSubspace (geometricFirstAxis s) (geometricExciseFirst s d))
      (geometricFirstAxis s) (geometricRetainedAmbientInclusion s d)
      (geometricRetainedAmbientInclusion_pair s d) 1 ≫
    pairRelativeHomologyMap (geometricFirstAxis s) ({s} : Set S)
      (geometricSecondProjection s) (geometricSecondProjection_pair s) 1 = _
  rw [← pairRelativeHomologyMap_comp]
  rfl

#print axioms geometricExciseFirst_closure_subset_interior_firstAxis
#print axioms geometricRetainedProjection_leftInverse
#print axioms geometricRelativeSecond_square
#print axioms geometricRetainedSecond_square
#print axioms geometricRelativeSecond_leftInverse
#print axioms geometricRelativeRetained_leftInverse
#print axioms geometricRelativeExcisionMap_eq_clean
#print axioms geometricRelativeExcision_inclusion_square
#print axioms geometricRelativeExcision_projection_square

end CurveComplexGenusTwo.CWHurewicz
