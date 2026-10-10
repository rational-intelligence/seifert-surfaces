import CurveComplexGenusTwo.CWHurewicz.PublicExport.PuncturedCell
import CurveComplexGenusTwo.CWHurewicz.PublicExport.RelativeConnectivity
import CurveComplexGenusTwo.CWHurewicz.CWStepT2

namespace CurveComplexGenusTwo.CWHurewicz
open Topology
open scoped unitInterval

/-- All characteristic disks in one successor skeleton. -/
abbrev StageCellIndex (X : Type) [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  Σ m : Fin (n + 1), Topology.CWComplex.cell (Set.univ : Set X) m.val

noncomputable def stagePresentation {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X] (n : ℕ) :
    C((Σ a : StageCellIndex X n, CellDisk a.1.val), ↥(skeletonBelow X (n+1))) :=
  ⟨fun z => characteristicToLaterStep n z.1.1.val (by omega) z.1.2 z.2,
    continuous_sigma (fun a => (characteristicToLaterStep n a.1.val (by omega) a.2).continuous)⟩

theorem stagePresentation_quotient {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X] (n : ℕ) :
    IsQuotientMap (stagePresentation (X := X) n) := by
  constructor
  · apply isCoinducing_iff.mpr
    intro s
    constructor
    · intro hs
      apply continuous_Prop.mp
      apply continuous_step_of_cellwise n
      intro m hm i
      apply continuous_Prop.mpr
      let a : StageCellIndex X n := ⟨⟨m, by omega⟩, i⟩
      exact hs.preimage (continuous_sigmaMk (i := a))
    · intro hs
      exact hs.preimage (stagePresentation n).continuous
  · intro x
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨hmn, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨i, z, hz, heq⟩ := Set.mem_iUnion.mp hm
    refine ⟨⟨⟨⟨m, hmn⟩, i⟩, ⟨z, hz⟩⟩, ?_⟩
    apply Subtype.ext
    exact heq

/-- The restricted characteristic presentation, still with a separate chart
for each cell. This form permits independent continuous local constructions. -/
noncomputable def openStagePresentation {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X] (n : ℕ)
    (U : Set ↥(skeletonBelow X (n+1))) :
    C((Σ a : StageCellIndex X n,
      {z : CellDisk a.1.val // stagePresentation n ⟨a,z⟩ ∈ U}), U) :=
  ⟨fun z => ⟨stagePresentation n ⟨z.1,z.2.val⟩, z.2.property⟩,
    continuous_sigma (fun _a =>
      (((stagePresentation n).continuous.comp continuous_sigmaMk).comp
        continuous_subtype_val).subtype_mk _)⟩

theorem openStagePresentation_quotient {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X] (n : ℕ)
    (U : Set ↥(skeletonBelow X (n+1))) (hU : IsOpen U) :
    IsQuotientMap (openStagePresentation n U) := by
  constructor
  · apply isCoinducing_iff.mpr
    intro s
    constructor
    · intro hs
      have himage : IsOpen (Subtype.val '' s : Set ↥(skeletonBelow X (n+1))) := by
        apply (stagePresentation_quotient n).isOpen_preimage.mp
        apply isOpen_sigma_iff.mpr
        intro a
        have hc := hs.preimage (continuous_sigmaMk (i := a))
        have ho : IsOpen {z : CellDisk a.1.val | stagePresentation n ⟨a,z⟩ ∈ U} :=
          hU.preimage ((stagePresentation n).continuous.comp continuous_sigmaMk)
        have hi := ho.isOpenMap_subtype_val _ hc
        convert hi using 1
        ext z
        constructor
        · rintro ⟨w, hw, heq⟩
          refine ⟨⟨z, ?_⟩, ?_, rfl⟩
          · change stagePresentation n ⟨a,z⟩ ∈ U
            rw [← heq]
            exact w.property
          · change (⟨stagePresentation n ⟨a,z⟩, _⟩ : U) ∈ s
            have he : (⟨stagePresentation n ⟨a,z⟩, heq ▸ w.property⟩ : U) = w :=
              Subtype.ext heq.symm
            exact he.symm ▸ hw
        · rintro ⟨z', hz', heq⟩
          subst z
          exact ⟨⟨stagePresentation n ⟨a,z'.val⟩, z'.property⟩, hz', rfl⟩
      have hpre := himage.preimage (continuous_subtype_val : Continuous (Subtype.val : U → _))
      simpa using hpre
    · intro hs
      exact hs.preimage (openStagePresentation n U).continuous
  · intro x
    obtain ⟨⟨a,z⟩, hz⟩ := (stagePresentation_quotient (X := X) n).surjective x.val
    refine ⟨⟨a, ⟨z, hz ▸ x.property⟩⟩, ?_⟩
    exact Subtype.ext hz



section Radial
variable {X : Type} [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)] [T2Space X]

noncomputable def stageCellCenter (n : ℕ) (a : StageCellIndex X n) :
    ↥(skeletonBelow X (n+1)) :=
  stagePresentation n ⟨a, ⟨0, by simp⟩⟩

def stageWithoutCenters (n : ℕ) (F : Finset (StageCellIndex X n)) :
    Set ↥(skeletonBelow X (n+1)) :=
  {x | ∀ a ∈ F, x ≠ stageCellCenter n a}

theorem stageWithoutCenters_open (n : ℕ) (F : Finset (StageCellIndex X n)) :
    IsOpen (stageWithoutCenters n F) := by
  have he : stageWithoutCenters n F =
      ⋂ a ∈ F, ({stageCellCenter n a} : Set ↥(skeletonBelow X (n+1)))ᶜ := by
    ext x; simp [stageWithoutCenters]
  rw [he]
  exact isOpen_biInter_finset (fun _ _ => isClosed_singleton.isOpen_compl)

abbrev RemovalChart (n : ℕ) (F : Finset (StageCellIndex X n))
    (a : StageCellIndex X n) :=
  {z : CellDisk a.1.val // stagePresentation n ⟨a,z⟩ ∈ stageWithoutCenters n F}

noncomputable def removalChartPuncture (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n) (ha : a ∈ F) :
    C(RemovalChart n F a, PuncturedCellDisk a.1.val) := by
  have hn (z : RemovalChart n F a) : z.val.val ≠ 0 := by
    intro hz
    apply z.property a ha
    apply Subtype.ext
    change Topology.CWComplex.map a.1.val a.2 z.val.val =
      Topology.CWComplex.map a.1.val a.2 0
    rw [hz]
  exact ⟨fun z => ⟨z.val, hn z⟩, continuous_subtype_val.subtype_mk _⟩

noncomputable def removalChartPaths (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n) :
    C(RemovalChart n F a, C(I, X)) := by
  classical
  by_cases ha : a ∈ F
  · exact ContinuousMap.curry ⟨fun p =>
      characteristicRadialHomotopy a.1.val a.2
        (p.2, removalChartPuncture n F a ha p.1),
      (characteristicRadialHomotopy a.1.val a.2).continuous.comp
        (continuous_snd.prodMk ((removalChartPuncture n F a ha).continuous.comp continuous_fst))⟩
  · exact ContinuousMap.curry ⟨fun p => characteristic a.1.val a.2 p.1.val,
      (characteristic a.1.val a.2).continuous.comp
        (continuous_subtype_val.comp continuous_fst)⟩

theorem removalChartPaths_unselected (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n) (ha : a ∉ F)
    (z : RemovalChart n F a) (t : I) :
    removalChartPaths n F a z t = characteristic a.1.val a.2 z.val := by
  simp [removalChartPaths, ha]

theorem removalChartPaths_boundary (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n)
    (z : RemovalChart n F a) (hz : ‖z.val.val‖ = 1) (t : I) :
    removalChartPaths n F a z t = characteristic a.1.val a.2 z.val := by
  classical
  by_cases ha : a ∈ F
  · simp only [removalChartPaths, dite_eq_left ha, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk]
    exact (characteristicRadialHomotopy a.1.val a.2).prop t
      (removalChartPuncture n F a ha z) hz
  · exact removalChartPaths_unselected n F a ha z t

omit [T2Space X] in
private theorem stageIndex_nat_injective (n : ℕ) :
    Function.Injective (fun a : StageCellIndex X n =>
      (⟨a.1.val, a.2⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set X) m)) := by
  rintro ⟨⟨m,hm⟩,i⟩ ⟨⟨k,hk⟩,j⟩ h
  cases h
  rfl

private theorem stageInterior_not_below (n : ℕ) (a : StageCellIndex X n)
    (ha : a.1.val = n) (z : CellDisk a.1.val) (hz : ‖z.val‖ < 1) :
    characteristic a.1.val a.2 z ∉ skeletonBelow X n := by
  have hdis : Disjoint (skeletonBelow X n)
      (Topology.CWComplex.openCell (C := (Set.univ : Set X)) a.1.val a.2) := by
    have he : skeletonBelow X n =
        (Topology.CWComplex.skeletonLT (Set.univ : Set X) n : Set X) := by
      simp [skeletonBelow, Topology.RelCWComplex.coe_skeletonLT]
      rfl
    rw [he]
    exact Topology.CWComplex.disjoint_skeletonLT_openCell (by exact_mod_cast ha.ge)
  intro h
  exact Set.disjoint_left.mp hdis h ⟨z.val, by simpa using hz, rfl⟩

/-- A top-cell interior point has only its own interior chart representative
in the entire stage presentation. -/
theorem stagePresentation_top_fiber (n : ℕ) (a b : StageCellIndex X n)
    (ha : a.1.val = n) (z : CellDisk a.1.val) (w : CellDisk b.1.val)
    (hz : ‖z.val‖ < 1)
    (heq : characteristic a.1.val a.2 z = characteristic b.1.val b.2 w) :
    (⟨a,z⟩ : Σ a : StageCellIndex X n, CellDisk a.1.val) = ⟨b,w⟩ := by
  have hw : ‖w.val‖ < 1 := by
    have hwle : ‖w.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using w.property
    by_contra h
    have hwe : ‖w.val‖ = 1 := le_antisymm hwle (le_of_not_gt h)
    have hmem : characteristic b.1.val b.2 w ∈ skeletonBelow X n := by
      apply skeletonBelow_mono (show b.1.val ≤ n by omega)
      exact (attaching b.1.val b.2 ⟨w.val, by simpa using hwe⟩).property
    exact stageInterior_not_below n a ha z hz (heq ▸ hmem)
  have hab : a = b := by
    by_contra hab
    have hne : (⟨a.1.val, a.2⟩ : Σ m, Topology.CWComplex.cell (Set.univ : Set X) m) ≠
        ⟨b.1.val, b.2⟩ := fun h => hab (stageIndex_nat_injective n h)
    have hdis := Topology.CWComplex.disjoint_openCell_of_ne
      (C := (Set.univ : Set X)) hne
    exact Set.disjoint_left.mp hdis ⟨z.val, by simpa using hz, rfl⟩
      (by
        change characteristic a.1.val a.2 z ∈ _
        rw [heq]
        exact ⟨w.val, by simpa using hw, rfl⟩)
  subst b
  have hzw : z = w := by
    apply Subtype.ext
    apply (Topology.CWComplex.map a.1.val a.2).injOn
    · rw [Topology.CWComplex.source_eq]; simpa using hz
    · rw [Topology.CWComplex.source_eq]; simpa using hw
    · exact heq
  subst w
  rfl

private theorem removalChart_forget_injective (n : ℕ)
    (F : Finset (StageCellIndex X n)) :
    Function.Injective (fun z : Σ a, RemovalChart n F a =>
      (⟨z.1,z.2.val⟩ : Σ a : StageCellIndex X n, CellDisk a.1.val)) := by
  rintro ⟨a,⟨z,hz⟩⟩ ⟨b,⟨w,hw⟩⟩ h
  cases h
  rfl

private theorem removalChartPaths_eq_of_other_rep (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (a b : StageCellIndex X n) (z : RemovalChart n F a) (w : RemovalChart n F b)
    (hne : (⟨a,z.val⟩ : Σ a : StageCellIndex X n, CellDisk a.1.val) ≠ ⟨b,w.val⟩)
    (heq : characteristic a.1.val a.2 z.val = characteristic b.1.val b.2 w.val)
    (t : I) :
    removalChartPaths n F a z t = characteristic a.1.val a.2 z.val := by
  by_cases ha : a ∈ F
  · apply removalChartPaths_boundary
    have hzle : ‖z.val.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using z.val.property
    apply le_antisymm hzle
    by_contra h
    exact hne (stagePresentation_top_fiber n a b (hF a ha) z.val w.val
      (lt_of_not_ge h) heq)
  · exact removalChartPaths_unselected n F a ha z t

noncomputable def removalPresentationPaths (n : ℕ)
    (F : Finset (StageCellIndex X n)) : C((Σ a, RemovalChart n F a), C(I,X)) :=
  ⟨fun z => removalChartPaths n F z.1 z.2,
    continuous_sigma (fun a => (removalChartPaths n F a).continuous)⟩

/-- The local radial paths agree on every characteristic-map identification,
including boundary identifications and overlaps with the whole lower skeleton. -/
theorem removalPresentationPaths_factors (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n) :
    Function.FactorsThrough (removalPresentationPaths n F)
      (openStagePresentation n (stageWithoutCenters n F)) := by
  rintro ⟨a,z⟩ ⟨b,w⟩ heq
  have hv : characteristic a.1.val a.2 z.val = characteristic b.1.val b.2 w.val :=
    congrArg (fun x : stageWithoutCenters n F => x.val.val) heq
  by_cases hrep : (⟨a,z.val⟩ : Σ a : StageCellIndex X n, CellDisk a.1.val) = ⟨b,w.val⟩
  · have h : (⟨a,z⟩ : Σ a, RemovalChart n F a) = ⟨b,w⟩ := by
      apply removalChart_forget_injective n F
      exact hrep
    exact congrArg (removalPresentationPaths n F) h
  · apply ContinuousMap.ext
    intro t
    exact (removalChartPaths_eq_of_other_rep n F hF a b z w hrep hv t).trans
      (hv.trans (removalChartPaths_eq_of_other_rep n F hF b a w z
        (Ne.symm hrep) hv.symm t).symm)

/-- Simultaneous global cell removal on the entire punctured successor
skeleton. Continuity is obtained by its genuine weak CW quotient topology. -/
noncomputable def finiteCellRemovalPaths (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n) :
    C(stageWithoutCenters n F, C(I,X)) :=
  (openStagePresentation_quotient n _ (stageWithoutCenters_open n F)).lift
    (removalPresentationPaths n F) (removalPresentationPaths_factors n F hF)

theorem finiteCellRemovalPaths_chart (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (a : StageCellIndex X n) (z : RemovalChart n F a) (t : I) :
    finiteCellRemovalPaths n F hF
      (openStagePresentation n (stageWithoutCenters n F) ⟨a,z⟩) t =
      removalChartPaths n F a z t := by
  have h := (openStagePresentation_quotient n _ (stageWithoutCenters_open n F)).lift_comp
    (removalPresentationPaths n F) (removalPresentationPaths_factors n F hF)
  exact congrArg (fun f : C((Σ a, RemovalChart n F a), C(I,X)) => f ⟨a,z⟩ t) h

noncomputable def finiteCellRemoval (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n) :
    C(I × stageWithoutCenters n F, X) :=
  (finiteCellRemovalPaths n F hF).uncurry.comp ⟨Prod.swap, continuous_swap⟩

theorem removalChartPaths_zero (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n) (z : RemovalChart n F a) :
    removalChartPaths n F a z 0 = characteristic a.1.val a.2 z.val := by
  classical
  by_cases ha : a ∈ F
  · simp only [removalChartPaths, dite_eq_left ha, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    exact (characteristicRadialHomotopy a.1.val a.2).map_zero_left _
  · exact removalChartPaths_unselected n F a ha z 0

theorem removalChartPaths_endpoint_selected (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (a : StageCellIndex X n) (ha : a ∈ F) (z : RemovalChart n F a) :
    removalChartPaths n F a z 1 ∈ skeletonBelow X n := by
  classical
  simp only [removalChartPaths, dite_eq_left ha, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
  have h := characteristicRadialHomotopy_endpoint_mem a.1.val a.2
    (removalChartPuncture n F a ha z)
  exact skeletonBelow_mono (le_of_eq (hF a ha)) h

theorem removalChartPaths_mem_stage (n : ℕ)
    (F : Finset (StageCellIndex X n)) (a : StageCellIndex X n)
    (z : RemovalChart n F a) (t : I) :
    removalChartPaths n F a z t ∈ skeletonBelow X (n+1) := by
  classical
  by_cases ha : a ∈ F
  · simp only [removalChartPaths, dite_eq_left ha, ContinuousMap.curry_apply, ContinuousMap.coe_mk]
    exact (characteristicToLaterStep n a.1.val (by omega) a.2
      (puncturedCellRadialHomotopy a.1.val (t, removalChartPuncture n F a ha z))).property
  · rw [removalChartPaths_unselected n F a ha]
    exact (characteristicToLaterStep n a.1.val (by omega) a.2 z.val).property

theorem finiteCellRemoval_chart (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (a : StageCellIndex X n) (z : RemovalChart n F a) (t : I) :
    finiteCellRemoval n F hF
      (t, openStagePresentation n (stageWithoutCenters n F) ⟨a,z⟩) =
      removalChartPaths n F a z t := finiteCellRemovalPaths_chart n F hF a z t

theorem finiteCellRemoval_zero (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (x : stageWithoutCenters n F) :
    finiteCellRemoval n F hF (0,x) = x.val.val := by
  obtain ⟨⟨a,z⟩,rfl⟩ := (openStagePresentation_quotient n _
    (stageWithoutCenters_open n F)).surjective x
  rw [finiteCellRemoval_chart]
  exact removalChartPaths_zero n F a z

theorem finiteCellRemoval_mem_stage (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (x : stageWithoutCenters n F) (t : I) :
    finiteCellRemoval n F hF (t,x) ∈ skeletonBelow X (n+1) := by
  obtain ⟨⟨a,z⟩,rfl⟩ := (openStagePresentation_quotient n _
    (stageWithoutCenters_open n F)).surjective x
  rw [finiteCellRemoval_chart]
  exact removalChartPaths_mem_stage n F a z t

/-- The simultaneous deformation fixes the entire lower skeleton,
including points where arbitrarily many cell frontiers meet. -/
theorem finiteCellRemoval_fixed_below (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (x : stageWithoutCenters n F) (hx : x.val.val ∈ skeletonBelow X n) (t : I) :
    finiteCellRemoval n F hF (t,x) = x.val.val := by
  obtain ⟨m,hm⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hmn,hm⟩ := Set.mem_iUnion.mp hm
  obtain ⟨i,z,hz,heq⟩ := Set.mem_iUnion.mp hm
  let a : StageCellIndex X n := ⟨⟨m, by omega⟩,i⟩
  let d : CellDisk m := ⟨z,hz⟩
  have he : stagePresentation n ⟨a,d⟩ = x.val := Subtype.ext heq
  let w : RemovalChart n F a := ⟨d, he.symm ▸ x.property⟩
  have hp : openStagePresentation n (stageWithoutCenters n F) ⟨a,w⟩ = x :=
    Subtype.ext he
  have ha : a ∉ F := by
    intro ha
    have := hF a ha
    change m = n at this
    omega
  rw [← hp, finiteCellRemoval_chart, removalChartPaths_unselected n F a ha]
  rfl

/-- Finite support in the top-dimensional cells; the lower skeleton itself
may contain infinitely many cells. -/
def finiteTopCellSupport (n : ℕ) (F : Finset (StageCellIndex X n)) : Set X :=
  skeletonBelow X n ∪ ⋃ a ∈ F,
    Topology.CWComplex.closedCell (C := (Set.univ : Set X)) a.1.val a.2

/-- Global dimension reduction for an arbitrary point in finite top-cell
support, after the finitely many selected centers have been removed. -/
theorem finiteCellRemoval_endpoint_below (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (x : stageWithoutCenters n F) (hx : x.val.val ∈ finiteTopCellSupport n F) :
    finiteCellRemoval n F hF (1,x) ∈ skeletonBelow X n := by
  rcases hx with hx | hx
  · rw [finiteCellRemoval_fixed_below n F hF x hx]
    exact hx
  · obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    obtain ⟨ha,hx⟩ := Set.mem_iUnion.mp ha
    obtain ⟨z,hz,heq⟩ := hx
    let d : CellDisk a.1.val := ⟨z,hz⟩
    have he : stagePresentation n ⟨a,d⟩ = x.val := Subtype.ext heq
    let w : RemovalChart n F a := ⟨d, he.symm ▸ x.property⟩
    have hp : openStagePresentation n (stageWithoutCenters n F) ⟨a,w⟩ = x :=
      Subtype.ext he
    rw [← hp, finiteCellRemoval_chart]
    exact removalChartPaths_endpoint_selected n F hF a ha w

/-- One complete global dimension-reduction step for an arbitrary source
space. The input map may cross any number of chart frontiers and does not
need to lift to a single characteristic disk. The finite top-cell support
and actual avoidance of its centers are explicit geometric hypotheses. -/
theorem finiteCellDimensionReduction
    {Z : Type*} [TopologicalSpace Z] (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (f : C(Z, ↥(skeletonBelow X (n+1))))
    (hmiss : ∀ z a, a ∈ F → f z ≠ stageCellCenter n a)
    (hsupp : ∀ z, (f z).val ∈ finiteTopCellSupport n F) :
    ∃ g : C(Z, ↥(skeletonBelow X n)),
      Nonempty (ContinuousMap.HomotopyRel
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X (n+1)), X)).comp f)
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n), X)).comp g)
        {z | (f z).val ∈ skeletonBelow X n}) := by
  let u : C(Z, stageWithoutCenters n F) :=
    ⟨fun z => ⟨f z, hmiss z⟩, f.continuous.subtype_mk _⟩
  let g : C(Z, ↥(skeletonBelow X n)) :=
    ⟨fun z => ⟨finiteCellRemoval n F hF (1,u z),
      finiteCellRemoval_endpoint_below n F hF (u z) (hsupp z)⟩,
      ((finiteCellRemoval n F hF).continuous.comp
        (continuous_const.prodMk u.continuous)).subtype_mk _⟩
  refine ⟨g, ⟨{
    toFun := fun p => finiteCellRemoval n F hF (p.1,u p.2)
    continuous_toFun := (finiteCellRemoval n F hF).continuous.comp
      (continuous_fst.prodMk (u.continuous.comp continuous_snd))
    map_zero_left := fun z => finiteCellRemoval_zero n F hF (u z)
    map_one_left := fun _ => rfl
    prop' := fun t z hz => finiteCellRemoval_fixed_below n F hF (u z) hz t }⟩⟩

theorem removalChartPaths_avoids_centers (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (a : StageCellIndex X n) (z : RemovalChart n F a) (t : I)
    (c : StageCellIndex X n) (hc : c ∈ F) :
    removalChartPaths n F a z t ≠ (stageCellCenter n c).val := by
  classical
  by_cases ha : a ∈ F
  · simp only [removalChartPaths, dite_eq_left ha, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk]
    intro heq
    let v : CellDisk a.1.val :=
      puncturedCellRadialHomotopy a.1.val (t, removalChartPuncture n F a ha z)
    have he : characteristic c.1.val c.2 ⟨0,by simp⟩ =
        characteristic a.1.val a.2 v := heq.symm
    have hf := stagePresentation_top_fiber n c a (hF c hc) ⟨0,by simp⟩ v (by simp) he
    have hv : ‖v.val‖ = 0 := by
      have hn := congrArg (fun w : Σ a : StageCellIndex X n, CellDisk a.1.val =>
        ‖w.2.val‖) hf
      simpa using hn.symm
    exact puncturedCellRadialHomotopy_ne_zero a.1.val t
      (removalChartPuncture n F a ha z) (norm_eq_zero.mp hv)
  · rw [removalChartPaths_unselected n F a ha]
    intro heq
    exact z.property c hc (Subtype.ext heq)

theorem finiteCellRemoval_avoids_centers (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    (x : stageWithoutCenters n F) (t : I) (c : StageCellIndex X n) (hc : c ∈ F) :
    finiteCellRemoval n F hF (t,x) ≠ (stageCellCenter n c).val := by
  obtain ⟨⟨a,z⟩,rfl⟩ := (openStagePresentation_quotient n _
    (stageWithoutCenters_open n F)).surjective x
  rw [finiteCellRemoval_chart]
  exact removalChartPaths_avoids_centers n F hF a z t c hc

/-- The entire global deformation stays inside the punctured skeleton. -/
noncomputable def finiteCellRemovalWithin (n : ℕ)
    (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n) :
    C(I × stageWithoutCenters n F, stageWithoutCenters n F) :=
  ⟨fun p => ⟨⟨finiteCellRemoval n F hF p,
      finiteCellRemoval_mem_stage n F hF p.2 p.1⟩,
    fun c hc h => finiteCellRemoval_avoids_centers n F hF p.2 p.1 c hc
      (congrArg Subtype.val h)⟩,
    ((finiteCellRemoval n F hF).continuous.subtype_mk _).subtype_mk _⟩

omit [T2Space X] in
theorem finiteTopCellSupport_subset_stage (n : ℕ)
    (F : Finset (StageCellIndex X n)) :
    finiteTopCellSupport n F ⊆ skeletonBelow X (n+1) := by
  intro x hx
  rcases hx with hx | hx
  · exact skeletonBelow_mono (Nat.le_succ n) hx
  · obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    obtain ⟨_,z,hz,heq⟩ := Set.mem_iUnion.mp ha
    exact heq ▸ (characteristicToLaterStep n a.1.val (by omega) a.2 ⟨z,hz⟩).property

/-- The global finite-support deformation gives dimension reduction in the
reviewed based-pair model without assuming a lift into any single cell. -/
theorem relativeDiskMap_finiteCellDimensionReduction
    (n : ℕ) (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    {A : Set X} {x : ↥A} {k : ℕ} {b : CellSphere k}
    (hA : A ⊆ skeletonBelow X n) (f : RelativeDiskMap k X A x b)
    (hmiss : ∀ z a, a ∈ F → f.map z ≠ (stageCellCenter n a).val)
    (hsupp : ∀ z, f.map z ∈ finiteTopCellSupport n F) :
    ∃ g : RelativeDiskMap k X A x b,
      Nonempty (RelativeDiskHomotopy f g) ∧
      ∀ z, g.map z ∈ skeletonBelow X n := by
  let fs : C(CellDisk k, ↥(skeletonBelow X (n+1))) :=
    ⟨fun z => ⟨f.map z, finiteTopCellSupport_subset_stage n F (hsupp z)⟩,
      f.map.continuous.subtype_mk _⟩
  obtain ⟨g,⟨H⟩⟩ := finiteCellDimensionReduction n F hF fs
    (fun z a ha h => hmiss z a ha (congrArg Subtype.val h)) hsupp
  let gm : C(CellDisk k,X) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow X n),X)).comp g
  have hb (t : I) (z : CellSphere k) :
      H (t,diskBoundaryInclusion k z) = f.map (diskBoundaryInclusion k z) :=
    H.prop t _ (hA (f.boundary z))
  have he (z : CellSphere k) :
      gm (diskBoundaryInclusion k z) = f.map (diskBoundaryInclusion k z) :=
    (H.map_one_left _).symm.trans (hb 1 z)
  let gr : RelativeDiskMap k X A x b := {
    map := gm
    boundary := fun z => (he z).symm ▸ f.boundary z
    based := (he b).trans f.based }
  exact ⟨gr, ⟨{
    map := H.toHomotopy.toContinuousMap
    at_zero := H.map_zero_left
    at_one := H.map_one_left
    boundary := fun t z => (hb t z).symm ▸ f.boundary z
    based := fun t => (hb t b).trans f.based }⟩, fun z => (g z).property⟩

/-- A based disk pair map supported on finitely many top cells and avoiding
their centers is null relative to the lower skeleton, with a concrete global
nullhomotopy rather than an assumption of local characteristic-disk lifts. -/
theorem relativeDiskMap_finiteCellNullhomotopy
    (n : ℕ) (F : Finset (StageCellIndex X n)) (hF : ∀ a ∈ F, a.1.val = n)
    {x : ↥(skeletonBelow X n)} {k : ℕ} {b : CellSphere k}
    (f : RelativeDiskMap k X (skeletonBelow X n) x b)
    (hmiss : ∀ z a, a ∈ F → f.map z ≠ (stageCellCenter n a).val)
    (hsupp : ∀ z, f.map z ∈ finiteTopCellSupport n F) :
    Nonempty (RelativeDiskHomotopy f (RelativeDiskMap.const x b)) := by
  obtain ⟨g,⟨H⟩,hg⟩ := relativeDiskMap_finiteCellDimensionReduction n F hF
    Set.Subset.rfl f hmiss hsupp
  exact ⟨H.trans (g.contractOfRangeSubset hg)⟩

end Radial
end CurveComplexGenusTwo.CWHurewicz
