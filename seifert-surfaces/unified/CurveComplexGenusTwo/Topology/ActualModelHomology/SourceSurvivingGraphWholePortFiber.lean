import CurveComplexGenusTwo.Topology.ActualModelHomology.ActualEdgeParameterQuotientCandidate
import CurveComplexGenusTwo.Topology.ActualModelHomology.SourceSurvivingHandleIntervalOpenEmbedding
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Homotopy.Contractible
namespace CurveComplex.Hyperbolic.OneBoundaryRay
open Set Topology ContinuousMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000
theorem source_surviving_graph_whole_port_fiber (p : ℕ) (k l : RawEdgeIndex p) (t s : unitInterval)
    (hk : match k with | .inl _ => True | .inr _ => (t:ℝ)<1)
    (hl : match l with | .inl _ => True | .inr _ => (s:ℝ)<1) :
    let B : RawEdgeIndex p → unitInterval → Prop := fun k t => t=0 ∨
      match k with | .inl _ => t=1 | .inr _ => False
    Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
      Quot.mk _ (rawEdgePoint l s false) ↔ (k=l ∧ t=s) ∨ (B k t ∧ B l s) := by
  classical
  dsimp only
  let B : RawEdgeIndex p → unitInterval → Prop := fun k t => t=0 ∨
    match k with | .inl _ => t=1 | .inr _ => False
  have hBase (k : RawEdgeIndex p) (t : unitInterval) (h : B k t) :
      Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
        Quot.mk _ (rawBoundaryPoint p 0) := by
    cases k with
    | inl d =>
      rcases d with ⟨i,b⟩
      change t=0 ∨ t=1 at h
      rcases h with rfl|rfl
      · have he := congrArg (fun x : actualSurvivingBoundary p => x.val.val) (handleEdge_source p i b)
        simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
          handleNumerator,rawEdgePoint_handle,rawBoundaryPoint,survivingBase] using he
      · have he := congrArg (fun x : actualSurvivingBoundary p => x.val.val) (handleEdge_target p i b)
        simpa [handleEdge,handleEdgeRaw,survivingBoundaryQuotientMap,rawQuotientMap,
          handleNumerator,rawEdgePoint_handle,rawBoundaryPoint,survivingBase] using he
    | inr u =>
      have ht : t=0 := h.resolve_right id
      subst t
      rw [rawEdgePoint_seam]
      simp
  have hStrict (k : RawEdgeIndex p) (t : unitInterval)
      (hk : match k with | .inl _ => True | .inr _ => (t:ℝ)<1)
      (h : ¬B k t) : 0<(t:ℝ) ∧ (t:ℝ)<1 := by
    have ht0 : 0<(t:ℝ) := by
      by_contra hn
      have ht : t=0 := Subtype.ext (le_antisymm (le_of_not_gt hn) t.property.1)
      exact h (Or.inl ht)
    refine ⟨ht0,?_⟩
    cases k with
    | inl d =>
      by_contra hn
      have ht : t=1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hn))
      exact h (Or.inr ht)
    | inr u => exact hk
  have hInterior (k l : RawEdgeIndex p) (t s : unitInterval)
      (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1)
      (he : Quot.mk (LeanEval.Topology.ClassificationOfSurfaces.OrientableRel p 1) (rawEdgePoint k t false)=
        Quot.mk _ (rawEdgePoint l s false)) : k=l ∧ t=s := by
    have hf := (raw_quotient_interior_fiber k t ht0 ht1 (rawEdgePoint l s false)).mp he
    have hm : rawEdgePoint l s false ∈ rawInteriorPair k t := hf
    exact (rawEdgePoint_mem_interior_pair_iff k l t s ht0 ht1 false).mp hm
  constructor
  · intro he
    by_cases hkt : B k t
    · right
      refine ⟨hkt,?_⟩
      by_contra hls
      have hs := hStrict l s hl hls
      obtain ⟨hkl,hts⟩ := hInterior l k s t hs.1 hs.2 he.symm
      exact hls (hkl.symm ▸ hts.symm ▸ hkt)
    · left
      have ht := hStrict k t hk hkt
      exact hInterior k l t s ht.1 ht.2 he
  · rintro (⟨rfl,rfl⟩|⟨hkt,hls⟩)
    · rfl
    · exact (hBase k t hkt).trans (hBase l s hls).symm
end CurveComplex.Hyperbolic.OneBoundaryRay
