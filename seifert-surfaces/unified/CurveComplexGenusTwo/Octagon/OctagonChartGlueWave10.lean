import CurveComplexGenusTwo.Octagon.VertexChart
import CurveComplexGenusTwo.Octagon.EdgeCollar

namespace CurveComplex.Octagon

/-!
  A reusable quotient-chart transfer.  The geometric work needed at a vertex or
  a paired edge is the construction of an open saturated source on which `mk`
  is injective.  Once that certificate is available, the local chart is a
  direct consequence of the quotient topology.
-/

theorem isOpenEmbedding_domRestrict_of_open_saturated_inj
    {U : Set Disk} (hU : IsOpen U)
    (hsat : mk ⁻¹' (mk '' U) = U)
    (hinj : Set.InjOn mk U) :
    Topology.IsOpenEmbedding (U.domRestrict mk) := by
  have hcont : Continuous (U.domRestrict mk) :=
    continuous_mk.comp continuous_subtype_val
  have hinj' : Function.Injective (U.domRestrict mk) := by
    intro x y hxy
    exact Subtype.ext (hinj x.2 y.2 hxy)
  have hopen : IsOpenMap (U.domRestrict mk) := by
    intro s hs
    have hs' : IsOpen ((Subtype.val : U → Disk) '' s) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap s hs
    have himage : U.domRestrict mk '' s = mk ''
        ((Subtype.val : U → Disk) '' s) := by
      ext q
      simp [Set.mem_image]
    rw [himage]
    apply (quotient_mk.isCoinducing.isOpen_preimage).mp
    have hpre : mk ⁻¹' (mk '' ((Subtype.val : U → Disk) '' s)) =
        ((Subtype.val : U → Disk) '' s) := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
        have hxU : x ∈ U := by
          rw [← hsat]
          exact ⟨z.1, z.2, hxy⟩
        have hxy' : mk x = mk z := hxy.symm
        have heq : x = z := hinj hxU z.2 hxy'
        subst x
        exact ⟨z, hz, rfl⟩
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]
    exact hs'
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont hinj' hopen

noncomputable def local_quotient_homeomorph_of_open_saturated_inj
    {U : Set Disk} (hU : IsOpen U)
    (hsat : mk ⁻¹' (mk '' U) = U)
    (hinj : Set.InjOn mk U) :
    U ≃ₜ mk '' U := by
  let f : U → Surface := U.domRestrict mk
  have hf : Topology.IsOpenEmbedding f :=
    isOpenEmbedding_domRestrict_of_open_saturated_inj hU hsat hinj
  let e₁ : U ≃ₜ Set.range f := hf.toHomeomorph
  let e₂ : Set.range f ≃ₜ mk '' U := Homeomorph.setCongr (by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩)
  exact e₁.trans e₂

/-- The already-proved ordinary interior chart is an instance of the generic
    quotient transfer above. -/
noncomputable def interior_local_quotient_homeomorph :
    diskInterior ≃ₜ mk '' diskInterior := by
  apply local_quotient_homeomorph_of_open_saturated_inj diskInterior_isOpen
  · exact mk_preimage_image_diskInterior
  · exact mk_injective_on_diskInterior

/-! The eight-sector and collar data used by the missing vertex/edge producer. -/

def vertexSectorImage (i : Side) : Set Disk :=
  (fun p : unitInterval × unitInterval => radialSector i p.1 p.2) ''
    (Set.univ : Set (unitInterval × unitInterval))

def vertexSectorUnion : Set Disk := ⋃ i : Side, vertexSectorImage i

theorem vertexSectorUnion_mem_of_image {x : Disk} {i : Side}
    (hx : x ∈ vertexSectorImage i) : x ∈ vertexSectorUnion := by
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

theorem vertexSector_seam_quotient (k : Fin 8) :
    mk (radialSector (vertexCycle k) 0
      (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) =
      mk (radialSector (vertexCycle (next k)) 0
        (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval)) := by
  rw [radialSector_center, radialSector_center]
  exact vertexCycle_glue k

theorem collarPoint_quotient_boundary (i : Side) (t : CollarAngle) :
    mk (collarPoint i ⟨1, by norm_num⟩ t) =
      mk (side i (collarToInterval t)) := by
  rw [collarPoint_boundary]

/-! A nonvacuous collar neighborhood containing the unique quotient vertex
and the interiors of all paired sides. The normal form shows that radius is
constant on every quotient fiber. -/

def outerBand : Set Disk := {x | 1 / 2 < ‖(x : ℂ)‖}

theorem outerBand_isOpen : IsOpen outerBand := by
  exact isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)

theorem side_mem_outerBand (i : Side) (t : unitInterval) :
    side i t ∈ outerBand := by
  simp [outerBand, side_norm]
  norm_num

theorem vertex_mem_outerBand (i : Side) : vertexPoint i ∈ outerBand := by
  exact side_mem_outerBand i 0

theorem norm_eq_of_related {x y : Disk} (h : Relation.r x y) :
    ‖(x : ℂ)‖ = ‖(y : ℂ)‖ := by
  rcases (relation_iff_normalForm.mp h) with rfl | ⟨hx, hy⟩ | hp
  · rfl
  · rcases hx with ⟨i, rfl⟩
    rcases hy with ⟨j, rfl⟩
    simp [vertexPoint, side_norm]
  · rcases hp with ⟨i, t, rfl, rfl⟩
    simp [side_norm]

theorem outerBand_saturated {x y : Disk} (h : Relation.r x y) :
    x ∈ outerBand ↔ y ∈ outerBand := by
  simp only [outerBand, Set.mem_ofPred_eq]
  rw [norm_eq_of_related h]

theorem outerBand_preimage_image :
    mk ⁻¹' (mk '' outerBand) = outerBand := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (outerBand_saturated (Quotient.exact hxy.symm)).2 hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem outerBand_image_isOpen : IsOpen (mk '' outerBand) := by
  apply (quotient_mk.isCoinducing.isOpen_preimage).mp
  rw [outerBand_preimage_image]
  exact outerBand_isOpen

theorem outerBand_vertex_mem : mk (vertexPoint 0) ∈ mk '' outerBand := by
  exact ⟨vertexPoint 0, vertex_mem_outerBand 0, rfl⟩

theorem outerBand_paired_edge_mem (i : Side) (t : unitInterval) :
    mk (side i t) ∈ mk '' outerBand := by
  exact ⟨side i t, side_mem_outerBand i t, rfl⟩

/-- The quotient map restricted to the explicit open collar around the
identified vertex is still a quotient map. The domain is literally its
full preimage, proved equal to `outerBand` above. -/
theorem outerBand_restricted_isQuotientMap :
    Topology.IsQuotientMap ((mk '' outerBand).restrictPreimage mk) :=
  quotient_mk.restrictPreimage_isOpen outerBand_image_isOpen

/-- The local vertex fiber in the explicit collar has all eight geometric
vertices, so no saturated source containing it can be injective under `mk`. -/
theorem outerBand_vertex_fiber :
    mk ⁻¹' ({mk (vertexPoint 0)} : Set Surface) ∩ outerBand = vertexSet := by
  rw [vertex_fiber_eq_vertexSet]
  apply Set.inter_eq_left.mpr
  rintro x ⟨i, rfl⟩
  exact vertex_mem_outerBand i

theorem outerBand_edge_fiber (i : Side) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    mk ⁻¹' ({mk (side i t)} : Set Surface) ∩ outerBand =
      {side i t, side (pair i) (unitInterval.symm t)} := by
  rw [edge_interior_fiber_eq_pair i t ht0 ht1]
  apply Set.inter_eq_left.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · subst x
    exact side_mem_outerBand i t
  · have hx : x = side (pair i) (unitInterval.symm t) := by simpa using h
    subst x
    exact side_mem_outerBand (pair i) (unitInterval.symm t)

/-! Arbitrarily small open stars at the identified vertex. -/

def vertexBallUnion (ε : ℝ) : Set Disk :=
  ⋃ i : Side, Metric.ball (vertexPoint i) ε

theorem vertexBallUnion_isOpen (ε : ℝ) : IsOpen (vertexBallUnion ε) := by
  unfold vertexBallUnion
  exact isOpen_iUnion (fun _ => Metric.isOpen_ball)

theorem vertexSet_subset_vertexBallUnion {ε : ℝ} (hε : 0 < ε) :
    vertexSet ⊆ vertexBallUnion ε := by
  rintro x ⟨i, rfl⟩
  exact Set.mem_iUnion.mpr ⟨i, Metric.mem_ball_self hε⟩

def vertexSaturatedStar (ε : ℝ) : Set Disk :=
  (saturation (vertexBallUnion ε)ᶜ)ᶜ

theorem vertexSaturatedStar_isOpen (ε : ℝ) :
    IsOpen (vertexSaturatedStar ε) :=
  saturation_compl_open (vertexBallUnion_isOpen ε)

theorem vertexSaturatedStar_subset_ballUnion (ε : ℝ) :
    vertexSaturatedStar ε ⊆ vertexBallUnion ε := by
  intro x hx
  by_contra hbad
  exact hx ⟨x, hbad, _root_.Relation.EqvGen.refl x⟩

theorem vertexSaturatedStar_saturated {ε : ℝ} {x y : Disk}
    (hxy : Relation.r x y) :
    x ∈ vertexSaturatedStar ε ↔ y ∈ vertexSaturatedStar ε :=
  saturation_compl_isSaturated hxy

theorem vertexSet_subset_vertexSaturatedStar {ε : ℝ} (hε : 0 < ε) :
    vertexSet ⊆ vertexSaturatedStar ε := by
  intro x hx
  apply relationClass_subset_of_saturatedOpen
    (U := vertexBallUnion ε) (a := x)
  · intro y hy
    have hyx : mk y = mk x := Quotient.sound hy
    have hxv : mk x = mk (vertexPoint 0) := by
      rcases hx with ⟨i, rfl⟩
      exact all_geometric_vertices_equal i 0
    have hyv : y ∈ vertexSet := by
      rw [← vertex_fiber_eq_vertexSet 0]
      exact hyx.trans hxv
    exact vertexSet_subset_vertexBallUnion hε hyv
  · exact _root_.Relation.EqvGen.refl x

theorem vertexSaturatedStar_preimage_image (ε : ℝ) :
    mk ⁻¹' (mk '' vertexSaturatedStar ε) = vertexSaturatedStar ε := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact (vertexSaturatedStar_saturated (Quotient.exact hxy.symm)).2 hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem vertexSaturatedStar_image_isOpen (ε : ℝ) :
    IsOpen (mk '' vertexSaturatedStar ε) := by
  apply (quotient_mk.isCoinducing.isOpen_preimage).mp
  rw [vertexSaturatedStar_preimage_image]
  exact vertexSaturatedStar_isOpen ε

theorem vertexSaturatedStar_vertex_mem {ε : ℝ} (hε : 0 < ε) :
    mk (vertexPoint 0) ∈ mk '' vertexSaturatedStar ε := by
  exact ⟨vertexPoint 0,
    vertexSet_subset_vertexSaturatedStar hε ⟨0, rfl⟩, rfl⟩

theorem vertexSaturatedStar_restricted_isQuotientMap (ε : ℝ) :
    Topology.IsQuotientMap
      ((mk '' vertexSaturatedStar ε).restrictPreimage mk) :=
  quotient_mk.restrictPreimage_isOpen (vertexSaturatedStar_image_isOpen ε)

theorem vertexSaturatedStar_vertex_fiber {ε : ℝ} (hε : 0 < ε) :
    mk ⁻¹' ({mk (vertexPoint 0)} : Set Surface) ∩
      vertexSaturatedStar ε = vertexSet := by
  rw [vertex_fiber_eq_vertexSet]
  exact Set.inter_eq_left.mpr (vertexSet_subset_vertexSaturatedStar hε)

end CurveComplex.Octagon
