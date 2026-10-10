import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualOneBoundaryRawCap

namespace CurveComplex.Hyperbolic.OneBoundaryRay
open LeanEval.Topology.ClassificationOfSurfaces

noncomputable def rawBoundaryClass (p : ℕ) (s : ℝ) : Quot (OrientableRel p 1) :=
  Quot.mk (OrientableRel p 1) (Complex.ClosedUnitDisc.bdyPtOfReal (s/modelSideCount p))

theorem handle_block_vertices (p : ℕ) (i : Fin p) :
    rawBoundaryClass p (4*(i:ℝ))=rawBoundaryClass p (4*(i:ℝ)+1) ∧
    rawBoundaryClass p (4*(i:ℝ))=rawBoundaryClass p (4*(i:ℝ)+2) ∧
    rawBoundaryClass p (4*(i:ℝ))=rawBoundaryClass p (4*(i:ℝ)+3) ∧
    rawBoundaryClass p (4*(i:ℝ))=rawBoundaryClass p (4*(i:ℝ)+4) := by
  have ha0 := Quot.sound (OrientableRel.a (p:=p) (n:=1) (0 : unitInterval) i)
  have ha1 := Quot.sound (OrientableRel.a (p:=p) (n:=1) (1 : unitInterval) i)
  have hb0 := Quot.sound (OrientableRel.b (p:=p) (n:=1) (0 : unitInterval) i)
  have hb1 := Quot.sound (OrientableRel.b (p:=p) (n:=1) (1 : unitInterval) i)
  simp only [Nat.cast_one,mul_one] at ha0 ha1 hb0 hb1
  change rawBoundaryClass p (4*(i:ℝ)+0)=rawBoundaryClass p (4*(i:ℝ)+3-0) at ha0
  change rawBoundaryClass p (4*(i:ℝ)+1)=rawBoundaryClass p (4*(i:ℝ)+3-1) at ha1
  change rawBoundaryClass p (4*(i:ℝ)+1+0)=rawBoundaryClass p (4*(i:ℝ)+4-0) at hb0
  change rawBoundaryClass p (4*(i:ℝ)+1+1)=rawBoundaryClass p (4*(i:ℝ)+4-1) at hb1
  have he1 : 4*(i:ℝ)+3-1=4*(i:ℝ)+2 := by ring
  have he2 : 4*(i:ℝ)+1+1=4*(i:ℝ)+2 := by ring
  have he3 : 4*(i:ℝ)+4-1=4*(i:ℝ)+3 := by ring
  simp only [add_zero,sub_zero] at ha0 hb0
  rw [he1] at ha1
  rw [he2,he3] at hb1
  have h01 := ha0.trans (hb1.symm.trans ha1.symm)
  exact ⟨h01,ha0.trans hb1.symm,ha0,h01.trans hb0⟩

theorem handle_initial_vertex_class (p n : ℕ) (hn : n≤p) :
    rawBoundaryClass p (4*(n:ℝ))=rawBoundaryClass p 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnp : n<p := by omega
    have he := (handle_block_vertices p ⟨n,hnp⟩).2.2.2
    have hi := ih (by omega)
    have hs : 4*((n+1:ℕ):ℝ)=4*(n:ℝ)+4 := by push_cast; ring
    rw [hs]
    exact he.symm.trans hi

end CurveComplex.Hyperbolic.OneBoundaryRay
