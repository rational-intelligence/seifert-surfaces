import CurveComplexGenusTwo.CWHurewicz.PublicExport.GlobalCellRemoval

namespace CurveComplexGenusTwo.CWHurewicz
open Topology Metric Set

variable {X : Type} [TopologicalSpace X]
  [Topology.CWComplex (Set.univ : Set X)] [T2Space X]

def stageOpenCore (n : ℕ) (a : StageCellIndex X n) (r : ℝ) :
    Set ↥(skeletonBelow X (n+1)) :=
  {x | x.val ∈ Topology.CWComplex.map a.1.val a.2 '' ball (0 : Fin a.1.val → ℝ) r}

def stageClosedCore (n : ℕ) (a : StageCellIndex X n) (r : ℝ) :
    Set ↥(skeletonBelow X (n+1)) :=
  {x | x.val ∈ Topology.CWComplex.map a.1.val a.2 '' closedBall (0 : Fin a.1.val → ℝ) r}

theorem stageOpenCore_isOpen (n : ℕ) (a : StageCellIndex X n)
    (ha : a.1.val = n) (r : ℝ) (hr : r ≤ 1) : IsOpen (stageOpenCore n a r) := by
  apply (stagePresentation_quotient n).isOpen_preimage.mp
  have he : (stagePresentation n) ⁻¹' stageOpenCore n a r =
      Sigma.mk a '' {z : CellDisk a.1.val | ‖z.val‖ < r} := by
    ext p
    rcases p with ⟨b,w⟩
    constructor
    · rintro ⟨v,hv,heq⟩
      have hvn : ‖v‖ < r := by simpa only [mem_ball,dist_zero_right] using hv
      let z : CellDisk a.1.val := ⟨v, by
        simpa only [mem_closedBall,dist_zero_right] using (hvn.le.trans hr)⟩
      exact ⟨z,hvn,stagePresentation_top_fiber n a b ha z w (hvn.trans_le hr) heq⟩
    · rintro ⟨z,hz,hrep⟩
      rw [← hrep]
      change ‖z.val‖ < r at hz
      exact ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
  rw [he]
  exact isOpenMap_sigmaMk _ (isOpen_lt (continuous_subtype_val.norm) continuous_const)

theorem stageClosedCore_isClosed (n : ℕ) (a : StageCellIndex X n)
    (r : ℝ) (hr : r ≤ 1) : IsClosed (stageClosedCore n a r) := by
  let q : C(↥(closedBall (0 : Fin a.1.val → ℝ) r), ↥(skeletonBelow X (n+1))) :=
    (characteristicToLaterStep n a.1.val (by omega) a.2).comp
      ⟨fun z => ⟨z.val, closedBall_subset_closedBall hr z.property⟩,
        continuous_subtype_val.subtype_mk _⟩
  have he : stageClosedCore n a r = Set.range q := by
    ext x
    constructor
    · rintro ⟨z,hz,heq⟩
      exact ⟨⟨z,hz⟩,Subtype.ext heq⟩
    · rintro ⟨z,rfl⟩
      exact ⟨z.val,z.property,rfl⟩
  rw [he]
  exact (isCompact_range q.continuous).isClosed

/-- The actual inverse characteristic coordinate on a compact inner core. -/
noncomputable def stageCoreCoordinate (n : ℕ) (a : StageCellIndex X n)
    (r : ℝ) (hr : r < 1) : C(stageClosedCore n a r, Fin a.1.val → ℝ) :=
  ⟨fun x => (Topology.CWComplex.map a.1.val a.2).symm x.val.val, by
    apply (Topology.CWComplex.continuousOn_symm a.1.val a.2).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro x
    obtain ⟨z,hz,heq⟩ := x.property
    change x.val.val ∈ _
    rw [← heq]
    apply (Topology.CWComplex.map a.1.val a.2).map_source
    rw [Topology.CWComplex.source_eq]
    exact (closedBall_subset_ball hr) hz⟩

omit [T2Space X] in
theorem stageCoreCoordinate_norm_le (n : ℕ) (a : StageCellIndex X n)
    (r : ℝ) (hr : r < 1) (x : stageClosedCore n a r) :
    ‖stageCoreCoordinate n a r hr x‖ ≤ r := by
  obtain ⟨z,hz,heq⟩ := x.property
  change ‖(Topology.CWComplex.map a.1.val a.2).symm x.val.val‖ ≤ r
  rw [← heq, (Topology.CWComplex.map a.1.val a.2).left_inv
    (by rw [Topology.CWComplex.source_eq]; exact (closedBall_subset_ball hr) hz)]
  simpa only [mem_closedBall,dist_zero_right] using hz

omit [T2Space X] in
theorem stageCoreCoordinate_inverse (n : ℕ) (a : StageCellIndex X n)
    (r : ℝ) (hr : r < 1) (x : stageClosedCore n a r) :
    Topology.CWComplex.map a.1.val a.2 (stageCoreCoordinate n a r hr x) = x.val.val := by
  obtain ⟨z,hz,heq⟩ := x.property
  change Topology.CWComplex.map a.1.val a.2
    ((Topology.CWComplex.map a.1.val a.2).symm x.val.val) = x.val.val
  rw [← heq, (Topology.CWComplex.map a.1.val a.2).left_inv
    (by rw [Topology.CWComplex.source_eq]; exact (closedBall_subset_ball hr) hz)]

omit [T2Space X] in
theorem stageOpenCore_subset_closed (n : ℕ) (a : StageCellIndex X n)
    {r s : ℝ} (hrs : r ≤ s) : stageOpenCore n a r ⊆ stageClosedCore n a s := by
  rintro x ⟨z,hz,he⟩
  exact ⟨z, (closedBall_subset_closedBall hrs) (ball_subset_closedBall hz), he⟩

omit [T2Space X] in
theorem stageClosedCore_subset_open (n : ℕ) (a : StageCellIndex X n)
    {r s : ℝ} (hrs : r < s) : stageClosedCore n a r ⊆ stageOpenCore n a s := by
  rintro x ⟨z,hz,he⟩
  exact ⟨z, (closedBall_subset_ball hrs) hz, he⟩

end CurveComplexGenusTwo.CWHurewicz
