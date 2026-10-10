import CurveComplexGenusTwo.Octagon.GeneralEdgeNeighborhoodWave10
import CurveComplexGenusTwo.Octagon.WindowEdgeEuclidean

namespace CurveComplex.Octagon

private theorem eight_interval_cover (v : ℝ) (hv0 : 0 ≤ v) (hv8 : v ≤ 8) :
    ∃ (i : Side) (t : unitInterval), v = (i.val : ℝ) + (t : ℝ) := by
  by_cases hvlt : v < 8
  · let i : Side := ⟨Nat.floor v, (Nat.floor_lt hv0).2 hvlt⟩
    have hlow : (Nat.floor v : ℝ) ≤ v := Nat.floor_le hv0
    have hhigh : v < (Nat.floor v : ℝ) + 1 := by
      simpa using (Nat.lt_succ_floor v)
    let t : unitInterval := ⟨v - (Nat.floor v : ℝ), by
      constructor <;> linarith⟩
    refine ⟨i, t, ?_⟩
    dsimp [i, t]
    ring
  · have hv : v = 8 := by linarith
    refine ⟨(7 : Side), (1 : unitInterval), ?_⟩
    norm_num [hv]

theorem boundary_point_on_side (x : Disk) (hx : ‖(x : ℂ)‖ = 1) :
    ∃ (i : Side) (t : unitInterval), side i t = x := by
  let z : Circle := ⟨(x : ℂ), by
    change (x : ℂ) ∈ Metric.sphere (0 : ℂ) 1
    exact mem_sphere_zero_iff_norm.mpr hx⟩
  have hcircle : Circle.exp '' Set.Icc (0 : ℝ) (2 * Real.pi) = Set.univ := by
    simpa using (Circle.periodic_exp.image_Icc Real.two_pi_pos (0 : ℝ)).trans
      Circle.exp_surjective.range_eq
  have hz : z ∈ Circle.exp '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
    rw [hcircle]
    trivial
  obtain ⟨θ, hθ, hθz⟩ := hz
  let v : ℝ := 4 * θ / Real.pi
  have hv0 : 0 ≤ v := by
    dsimp [v]
    exact div_nonneg (by nlinarith [hθ.1]) Real.pi_pos.le
  have hv8 : v ≤ 8 := by
    dsimp [v]
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith [hθ.2]
  obtain ⟨i, t, hvt⟩ := eight_interval_cover v hv0 hv8
  refine ⟨i, t, ?_⟩
  apply Subtype.ext
  have hangle : 2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8 = θ := by
    rw [← hvt]
    dsimp [v]
    field_simp [ne_of_gt Real.pi_pos]
    ring
  have hcircle' : Circle.exp
      (2 * Real.pi * ((i.val : ℝ) + (t : ℝ)) / 8) = z := by
    rw [hangle]
    exact hθz
  exact congrArg (fun w : Circle => (w : ℂ)) hcircle'

theorem disk_point_interior_or_side (x : Disk) :
    x ∈ diskInterior ∨ ∃ (i : Side) (t : unitInterval), x = side i t := by
  by_cases hi : x ∈ diskInterior
  · exact Or.inl hi
  · right
    have hxle : ‖(x : ℂ)‖ ≤ 1 := by
      have h := x.property
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h
    have hxnorm : ‖(x : ℂ)‖ = 1 := by
      have hnot : ¬ ‖(x : ℂ)‖ < 1 := hi
      exact le_antisymm hxle (le_of_not_gt hnot)
    obtain ⟨i, t, h⟩ := boundary_point_on_side x hxnorm
    exact ⟨i, t, h.symm⟩

theorem disk_point_interior_or_vertex_or_openSide (x : Disk) :
    x ∈ diskInterior ∨ x ∈ vertexSet ∨
      ∃ (i : Side) (t : unitInterval),
        0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ x = side i t := by
  rcases disk_point_interior_or_side x with hi | ⟨i, t, h⟩
  · exact Or.inl hi
  · by_cases ht0 : t = 0
    · exact Or.inr (Or.inl (h ▸ side_endpoint_mem_vertexSet i t (Or.inl ht0)))
    · by_cases ht1 : t = 1
      · exact Or.inr (Or.inl (h ▸ side_endpoint_mem_vertexSet i t (Or.inr ht1)))
      · right
        right
        refine ⟨i, t, ?_, ?_, h⟩
        · exact lt_of_le_of_ne t.property.1 (Ne.symm (by
            intro hv
            exact ht0 (Subtype.ext hv)))
        · exact lt_of_le_of_ne t.property.2 (by
            intro hv
            exact ht1 (Subtype.ext hv))

abbrev Euclidean2 := EuclideanSpace ℝ (Fin 2)

private def diskInteriorComplex : Set ℂ := {z | ‖z‖ < 1}

private theorem diskInteriorComplex_isOpen : IsOpen diskInteriorComplex := by
  exact isOpen_lt continuous_norm continuous_const

private def diskInteriorComplexHomeomorph :
    diskInterior ≃ₜ diskInteriorComplex where
  toFun x := ⟨(x.1 : ℂ), x.2⟩
  invFun z := ⟨⟨(z : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt z.2⟩, z.2⟩
  left_inv := by
    rintro ⟨⟨z, hz⟩, hi⟩
    rfl
  right_inv := by
    rintro ⟨z, hz⟩
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def complexEuclidean2Homeomorph : ℂ ≃ₜ Euclidean2 :=
  Complex.equivRealProdCLM.toHomeomorph |>.trans
    (Homeomorph.finTwoArrow (X := ℝ)).symm |>.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph

noncomputable def planeEuclidean2Homeomorph : (ℝ × ℝ) ≃ₜ Euclidean2 :=
  (Homeomorph.finTwoArrow (X := ℝ)).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph

def EuclideanLocalChartAt (q : Surface) : Prop :=
  ∃ (W : Set Surface) (U : Set Euclidean2),
    IsOpen W ∧ q ∈ W ∧ IsOpen U ∧ Nonempty (W ≃ₜ U)

theorem interior_euclideanLocalChartAt {x : Disk} (hx : x ∈ diskInterior) :
    EuclideanLocalChartAt (mk x) := by
  let W : Set Surface := mk '' diskInterior
  let U : Set Euclidean2 :=
    complexEuclidean2Homeomorph '' diskInteriorComplex
  have hWopen : IsOpen W := mk_image_diskInterior_isOpen
  have hUopen : IsOpen U :=
    complexEuclidean2Homeomorph.isOpenMap _ diskInteriorComplex_isOpen
  have hhomeo : W ≃ₜ U := by
    let e₁ : diskInterior ≃ₜ W :=
      homeomorph_image_of_open_saturated_inj diskInterior_isOpen
        mk_preimage_image_diskInterior mk_injective_on_diskInterior
    let e₂ : diskInterior ≃ₜ U :=
      diskInteriorComplexHomeomorph.trans
        (complexEuclidean2Homeomorph.image diskInteriorComplex)
    exact e₁.symm.trans e₂
  exact ⟨W, U, hWopen, ⟨x, hx, rfl⟩, hUopen, ⟨hhomeo⟩⟩

theorem edge_euclideanLocalChartAt
    (i : Side) (t : unitInterval)
    (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) < 1) :
    EuclideanLocalChartAt (mk (side i t)) := by
  obtain ⟨V, W, hVopen, hWopen, hqW, ⟨e⟩⟩ :=
    pairedEdge_every_interior_point_euclidean_chart i t ht0 ht1
  let U : Set Euclidean2 := planeEuclidean2Homeomorph '' V
  have hUopen : IsOpen U := planeEuclidean2Homeomorph.isOpenMap V hVopen
  let f : V ≃ₜ U := planeEuclidean2Homeomorph.image V
  exact ⟨W, U, hWopen, hqW, hUopen, ⟨e.symm.trans f⟩⟩

private theorem openChartOfEuclideanLocalChart
    (q : Surface) (h : EuclideanLocalChartAt q) :
    ∃ e : OpenPartialHomeomorph Surface Euclidean2, q ∈ e.source := by
  obtain ⟨W, U, hWopen, hqW, hUopen, ⟨e⟩⟩ := h
  let jW : OpenPartialHomeomorph W Surface :=
    (⟨W, hWopen⟩ : TopologicalSpace.Opens Surface).openPartialHomeomorphSubtypeCoe
      ⟨⟨q, hqW⟩⟩
  let jU : OpenPartialHomeomorph U Euclidean2 :=
    (⟨U, hUopen⟩ : TopologicalSpace.Opens Euclidean2).openPartialHomeomorphSubtypeCoe
      ⟨e ⟨q, hqW⟩⟩
  let chart : OpenPartialHomeomorph Surface Euclidean2 :=
    jW.symm.trans (e.toOpenPartialHomeomorph.trans jU)
  refine ⟨chart, ?_⟩
  have htail : (e.toOpenPartialHomeomorph.trans jU).source = Set.univ := by
    simp [jU]
  change q ∈ (jW.symm.trans (e.toOpenPartialHomeomorph.trans jU)).source
  rw [OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · simpa [jW] using hqW
  · rw [htail]
    trivial

theorem euclideanLocalChartAt_all_of_edge_vertex
    (hEdge : ∀ (i : Side) (t : unitInterval),
      0 < (t : ℝ) → (t : ℝ) < 1 → EuclideanLocalChartAt (mk (side i t)))
    (hVertex : EuclideanLocalChartAt (mk (vertexPoint 0)))
    (q : Surface) : EuclideanLocalChartAt q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    rcases disk_point_interior_or_vertex_or_openSide x with hi | hv | ⟨i, t, ht0, ht1, hx⟩
    · exact interior_euclideanLocalChartAt hi
    · obtain ⟨i, rfl⟩ := hv
      change EuclideanLocalChartAt (mk (vertexPoint i))
      rw [all_geometric_vertices_equal i 0]
      exact hVertex
    · rw [hx]
      exact hEdge i t ht0 ht1

theorem euclideanLocalChartAt_all_of_vertex
    (hVertex : EuclideanLocalChartAt (mk (vertexPoint 0)))
    (q : Surface) : EuclideanLocalChartAt q :=
  euclideanLocalChartAt_all_of_edge_vertex edge_euclideanLocalChartAt hVertex q

@[instance_reducible] noncomputable def chartedSpaceOfEuclideanLocalCharts
    (h : ∀ q : Surface, EuclideanLocalChartAt q) :
    ChartedSpace Euclidean2 Surface where
  atlas := Set.univ
  chartAt q := Classical.choose (openChartOfEuclideanLocalChart q (h q))
  mem_chart_source q := Classical.choose_spec (openChartOfEuclideanLocalChart q (h q))
  chart_mem_atlas _ := Set.mem_univ _

structure TopologicalClosedSurface (S : Type*) [TopologicalSpace S] where
  chartedSpace : ChartedSpace Euclidean2 S
  compact : CompactSpace S
  connected : ConnectedSpace S
  hausdorff : T2Space S

noncomputable def octagonTopologicalClosedSurface_of_vertex
    (hVertex : EuclideanLocalChartAt (mk (vertexPoint 0))) :
    TopologicalClosedSurface Surface where
  chartedSpace := chartedSpaceOfEuclideanLocalCharts
    (euclideanLocalChartAt_all_of_vertex hVertex)
  compact := inferInstance
  connected := inferInstance
  hausdorff := quotient_t2

end CurveComplex.Octagon
