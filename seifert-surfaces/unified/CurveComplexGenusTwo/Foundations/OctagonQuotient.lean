import CurveComplexGenusTwo.Foundations.Octagon

namespace CurveComplex.Octagon

/-! Read-only consumer certificate for the finite normal form and quotient data. -/

theorem finite_eqvGen_normal_form {x y : Disk}
    (h : _root_.Relation.EqvGen SideGlue x y) :
    x = y ∨ (x ∈ vertexSet ∧ y ∈ vertexSet) ∨ Pairing x y :=
  eqvGen_normalForm h

theorem quotient_relation_closed_consumer :
    IsClosed {p : Disk × Disk | Relation.r p.1 p.2} :=
  relation_graph_isClosed

theorem quotient_compact_consumer : CompactSpace Surface := by
  infer_instance

theorem quotient_connected_consumer : ConnectedSpace Surface := by
  infer_instance

theorem quotient_interior_chart_consumer :
    Set.InjOn mk diskInterior ∧ IsOpen diskInterior ∧ Continuous mk :=
  interior_chart_input

theorem vertex_fiber_eq_vertexSet (i : Side) :
    mk ⁻¹' ({mk (vertexPoint i)} : Set Surface) = vertexSet := by
  ext x
  constructor
  · intro hx
    have hmk : mk x = mk (vertexPoint i) := hx
    have hrel : Relation.r x (vertexPoint i) := Quotient.exact hmk
    rw [relation_iff_normalForm] at hrel
    rcases hrel with hxy | ⟨hxy, hy⟩ | hp
    · exact hxy ▸ ⟨i, rfl⟩
    · exact hxy
    · exact (pairing_mem_vertexSet hp).mpr ⟨i, rfl⟩
  · intro hx
    rcases hx with ⟨j, rfl⟩
    exact all_geometric_vertices_equal j i

theorem vertex_fiber_isClosed (i : Side) :
    IsClosed (mk ⁻¹' ({mk (vertexPoint i)} : Set Surface)) := by
  rw [vertex_fiber_eq_vertexSet]
  exact vertexSet_isClosed

theorem edge_interior_fiber_eq_pair (i : Side) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    mk ⁻¹' ({mk (side i t)} : Set Surface) =
      {side i t, side (pair i) (unitInterval.symm t)} := by
  ext x
  constructor
  · intro hx
    have hrel : Relation.r x (side i t) := Quotient.exact hx
    rw [relation_iff_normalForm] at hrel
    rcases hrel with hxy | ⟨hxv, hyv⟩ | hp
    · simpa [hxy]
    · exfalso
      rcases (side_mem_vertexSet_iff i t).mp hyv with h | h
      · exact ht0 h
      · exact ht1 h
    · rcases hp with ⟨j, u, hjx, hjy⟩
      have hside : side (pair j) (unitInterval.symm u) = side i t := hjy.symm
      rcases side_eq_same_or_endpoints (pair j) i (unitInterval.symm u) t hside with hsame | hend
      · rcases hsame with ⟨hji, hut⟩
        have hpair : j = pair i := by
          apply Fin.ext
          have hp : j = pair i := by
            simpa [pair_involutive] using congrArg (fun k : Side => pair k) hji
          exact congrArg Fin.val hp
        have hu : u = unitInterval.symm t := by
          apply Subtype.ext
          rw [← unitInterval.symm_symm u, hut]
        rw [hjx, hpair, hu]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      · exfalso
        rcases hend.2 with h | h
        · exact ht0 h
        · exact ht1 h
  · intro hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact Set.mem_singleton _
    · rw [Set.mem_singleton_iff] at h
      rw [h]
      exact (side_pairing i t).symm

end CurveComplex.Octagon
