import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundarySurvivingGraphQuotient
import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryHandleVertices

namespace CurveComplex.Hyperbolic.OneBoundaryRay

noncomputable def handleNumerator {p : ℕ} (i : Fin p) (b : Bool) (t : unitInterval) : ℝ :=
  4*(i:ℝ)+(if b then 1 else 0)+(t:ℝ)

theorem handleNumerator_bounds {p : ℕ} (i : Fin p) (b : Bool) (t : unitInterval) :
    0≤handleNumerator i b t ∧ handleNumerator i b t≤4*(p:ℝ) := by
  have hi : (i:ℝ)+1≤(p:ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  have hn : 0≤(i:ℝ) := by positivity
  have ht0 := t.property.1
  have ht1 := t.property.2
  cases b <;> simp only [handleNumerator,Bool.false_eq_true,↓reduceIte] <;>
    constructor <;> nlinarith

noncomputable def handleEdgeRaw (p : ℕ) (i : Fin p) (b : Bool) :
    C(unitInterval,RawSurvivingBoundary p) where
  toFun t := ⟨⟨Complex.ClosedUnitDisc.bdyPtOfReal (handleNumerator i b t/modelSideCount p),
    handle_boundary_not_mem_rawDeletedArc p _ (handleNumerator_bounds i b t).1
      (handleNumerator_bounds i b t).2⟩,Circle.norm_coe _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (by
      unfold handleNumerator
      fun_prop))

noncomputable def survivingBase (p : ℕ) : actualSurvivingBoundary p :=
  survivingBoundaryQuotientMap p ⟨⟨Complex.ClosedUnitDisc.bdyPtOfReal (0/modelSideCount p),
    handle_boundary_not_mem_rawDeletedArc p 0 (by rfl) (by positivity)⟩,Circle.norm_coe _⟩

noncomputable def handleEdge (p : ℕ) (i : Fin p) (b : Bool) :
    C(unitInterval,actualSurvivingBoundary p) :=
  (survivingBoundaryQuotientMap p).comp (handleEdgeRaw p i b)

theorem handleEdge_source (p : ℕ) (i : Fin p) (b : Bool) :
    handleEdge p i b 0=survivingBase p := by
  apply Subtype.ext
  apply Subtype.ext
  change rawBoundaryClass p (handleNumerator i b 0)=rawBoundaryClass p 0
  have hv := handle_initial_vertex_class p i.val i.isLt.le
  cases b
  · simpa [handleNumerator] using hv
  · have h := (handle_block_vertices p i).1.symm.trans hv
    simpa [handleNumerator] using h

theorem handleEdge_target (p : ℕ) (i : Fin p) (b : Bool) :
    handleEdge p i b 1=survivingBase p := by
  apply Subtype.ext
  apply Subtype.ext
  change rawBoundaryClass p (handleNumerator i b 1)=rawBoundaryClass p 0
  have hv := handle_initial_vertex_class p i.val i.isLt.le
  cases b
  · have h := (handle_block_vertices p i).1.symm.trans hv
    simpa [handleNumerator] using h
  · have h := (handle_block_vertices p i).2.1.symm.trans hv
    have he : handleNumerator i true 1=4*(i:ℝ)+2 := by
      simp [handleNumerator]
      ring
    rw [he]
    exact h

noncomputable def handleLoop (p : ℕ) (i : Fin p) (b : Bool) :
    Path (survivingBase p) (survivingBase p) where
  toFun := handleEdge p i b
  continuous_toFun := (handleEdge p i b).continuous
  source' := handleEdge_source p i b
  target' := handleEdge_target p i b

end CurveComplex.Hyperbolic.OneBoundaryRay
