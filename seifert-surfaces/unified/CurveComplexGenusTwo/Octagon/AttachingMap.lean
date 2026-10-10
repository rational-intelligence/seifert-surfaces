import CurveComplexGenusTwo.Foundations.OctagonQuotient
import CurveComplexGenusTwo.Octagon.OctagonAtlasCoverageWave10
import CurveComplexGenusTwo.CWHurewicz.AffineCarrier
open CategoryTheory Convexity
open scoped Simplicial
namespace CurveComplex.Octagon.AttachingMap
def boundaryImage : Set Surface := {x | ∃ i t, x = mk (side i t)}
abbrev BoundaryGraph := boundaryImage
noncomputable def base : BoundaryGraph := ⟨mk (vertexPoint 0), 0, 0, rfl⟩
noncomputable def sideLoop (i : Side) : Path base base where
  toFun t := ⟨mk (side i t), i, t, rfl⟩
  continuous_toFun := (continuous_mk.comp (continuous_side i)).subtype_mk _
  source' := Subtype.ext (all_geometric_vertices_equal i 0)
  target' := Subtype.ext ((congrArg mk (side_end_next i)).trans (all_geometric_vertices_equal _ _))
theorem sideLoop_pair (i : Side) : sideLoop (pair i) = (sideLoop i).symm := by
  ext t
  exact side_pairing_reverse i t
noncomputable def boundaryLoop :=
  (((((((sideLoop 0).trans (sideLoop 1)).trans (sideLoop 2)).trans (sideLoop 3)).trans
    (sideLoop 4)).trans (sideLoop 5)).trans (sideLoop 6)).trans (sideLoop 7)
theorem boundary_word : boundaryLoop =
  (((((((sideLoop 0).trans (sideLoop 1)).trans (sideLoop 0).symm).trans
    (sideLoop 1).symm).trans (sideLoop 4)).trans (sideLoop 5)).trans
    (sideLoop 4).symm).trans (sideLoop 5).symm := by
  unfold boundaryLoop
  have h0 := sideLoop_pair 0
  have h1 := sideLoop_pair 1
  have h4 := sideLoop_pair 4
  have h5 := sideLoop_pair 5
  change sideLoop 2 = _ at h0
  change sideLoop 3 = _ at h1
  change sideLoop 6 = _ at h4
  change sideLoop 7 = _ at h5
  rw [h0, h1, h4, h5]
noncomputable abbrev X := TopCat.of BoundaryGraph
abbrev Sing (n : ℕ) := (TopCat.toSSet.obj X) _⦋n⦌
noncomputable def coord {n : ℕ} (j : Fin (n+1)) :
    C(StdSimplex ℝ (Fin (n+1)), unitInterval) :=
  ⟨fun z => ⟨z.weights j, z.weights_nonneg j, z.weights_apply_le_one j⟩,
    (StdSimplex.continuous_weights_apply ℝ j).subtype_mk _⟩
noncomputable def sideSimplex (i : Side) : Sing 1 :=
  (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).symm
    ((sideLoop i).toContinuousMap.comp (coord 1))
noncomputable def reversalSimplex (i : Side) : Sing 2 :=
  (TopCat.toSSetObjEquiv X (.op ⦋2⦌)).symm
    ((sideLoop i).toContinuousMap.comp (coord 1))
noncomputable def constantSimplex (n : ℕ) : Sing n :=
  (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).symm (ContinuousMap.const _ base)
theorem face_eval {n : ℕ} (s : Sing (n+1)) (j : Fin (n+2))
    (z : StdSimplex ℝ (Fin (n+1))) :
    TopCat.toSSetObjEquiv X (.op ⦋n⦌) ((TopCat.toSSet.obj X).δ j s) z =
      TopCat.toSSetObjEquiv X (.op ⦋n+1⦌) s (z.map j.succAbove) := by rfl
theorem rev_face0 (i : Side) :
    (TopCat.toSSet.obj X).δ 0 (reversalSimplex i) = sideSimplex (pair i) := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [face_eval]
  simp only [reversalSimplex, sideSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  change sideLoop i (coord 1 (z.map (0 : Fin 3).succAbove)) = sideLoop (pair i) (coord 1 z)
  rw [sideLoop_pair]
  change sideLoop i _ = sideLoop i (unitInterval.symm (coord 1 z))
  apply congrArg (sideLoop i)
  apply Subtype.ext
  simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two]
  have ht := z.total
  rw [Finsupp.sum_fintype] at ht <;> try simp
  change (∑ j : Fin 2, z.weights j) = 1 at ht
  rw [Fin.sum_univ_two] at ht
  linarith
theorem rev_face1 (i : Side) :
    (TopCat.toSSet.obj X).δ 1 (reversalSimplex i) = constantSimplex 1 := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [face_eval]
  simp only [reversalSimplex, constantSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_apply, ContinuousMap.const_apply]
  have hz : coord 1 (z.map (1 : Fin 3).succAbove) = 0 := by
    apply Subtype.ext
    simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
      Fin.sum_univ_two]
  rw [hz]
  exact (sideLoop i).source
theorem rev_face2 (i : Side) :
    (TopCat.toSSet.obj X).δ 2 (reversalSimplex i) = sideSimplex i := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [face_eval]
  simp only [reversalSimplex, sideSimplex, Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  apply congrArg (sideLoop i)
  apply Subtype.ext
  simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_two, Fin.succAbove]
theorem const_face (j : Fin 3) :
    (TopCat.toSSet.obj X).δ j (constantSimplex 2) = constantSimplex 1 := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rw [face_eval]
  rfl
open CurveComplexGenusTwo.CWHurewicz
noncomputable def reversalChain (i : Side) : Sing 2 →₀ ℤ :=
  Finsupp.single (reversalSimplex i) 1 + Finsupp.single (constantSimplex 2) 1
theorem reversal_boundary (i : Side) :
    singularBoundaryFinsupp X 1 (reversalChain i) =
      Finsupp.single (sideSimplex i) 1 + Finsupp.single (sideSimplex (pair i)) 1 := by
  simp only [reversalChain, map_add, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, rev_face0, rev_face1, rev_face2, const_face]
  abel
noncomputable def boundaryChain : Sing 1 →₀ ℤ :=
  ∑ i : Side, Finsupp.single (sideSimplex i) 1
noncomputable def fillingChain : Sing 2 →₀ ℤ :=
  reversalChain 0 + reversalChain 1 + reversalChain 4 + reversalChain 5
theorem boundary_chain_filled :
    singularBoundaryFinsupp X 1 fillingChain = boundaryChain := by
  simp only [fillingChain, map_add, reversal_boundary, boundaryChain]
  simp [Fin.sum_univ_succ, pair]
  abel
theorem boundary_chain_mem_range :
    boundaryChain ∈ LinearMap.range (singularBoundaryFinsupp X 1) :=
  ⟨fillingChain, boundary_chain_filled⟩
noncomputable def circleToDisk : C(Circle, Disk) :=
  ⟨fun z => ⟨z, by simpa [Metric.mem_closedBall] using (Circle.norm_coe z).le⟩,
    by fun_prop⟩
noncomputable def attachingMap : C(Circle, BoundaryGraph) where
  toFun z := ⟨mk (circleToDisk z), by
    obtain ⟨i, t, h⟩ := boundary_point_on_side (circleToDisk z) (Circle.norm_coe z)
    exact ⟨i, t, congrArg mk h.symm⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_mk.comp circleToDisk.continuous
noncomputable def circleSide (i : Side) : C(unitInterval, Circle) :=
  ⟨fun t => Circle.exp (2 * Real.pi * ((i.val : ℝ) + t) / 8), by fun_prop⟩
theorem attachingMap_side (i : Side) (t : unitInterval) :
    attachingMap (circleSide i t) = sideLoop i t := by rfl
abbrev CircleSing (n : ℕ) := (TopCat.toSSet.obj (TopCat.of Circle)) _⦋n⦌
noncomputable def circleSideSimplex (i : Side) : CircleSing 1 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
    ((circleSide i).comp (coord 1))
noncomputable def circleBoundaryChain : CircleSing 1 →₀ ℤ :=
  ∑ i : Side, Finsupp.single (circleSideSimplex i) 1
noncomputable def attachingChainMap (n : ℕ) :
    (CircleSing n →₀ ℤ) →ₗ[ℤ] (Sing n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ
    ((TopCat.toSSet.map (TopCat.ofHom attachingMap)).app (.op ⦋n⦌))
theorem attachingMap_singularSide (i : Side) :
    ((TopCat.toSSet.map (TopCat.ofHom attachingMap)).app (.op ⦋1⦌))
      (circleSideSimplex i) = sideSimplex i := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  rfl
theorem attachingChainMap_boundary :
    attachingChainMap 1 circleBoundaryChain = boundaryChain := by
  classical
  simp [circleBoundaryChain, boundaryChain, attachingChainMap,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, attachingMap_singularSide]
theorem attaching_circle_chain_bounds :
    attachingChainMap 1 circleBoundaryChain =
      singularBoundaryFinsupp X 1 fillingChain := by
  rw [attachingChainMap_boundary, boundary_chain_filled]
noncomputable def circleVertex (i : Side) : CircleSing 0 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).symm
    (ContinuousMap.const _ (circleSide i 0))
theorem circle_face1 (i : Side) :
    (TopCat.toSSet.obj (TopCat.of Circle)).δ 1 (circleSideSimplex i) = circleVertex i := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro z
  change circleSide i (coord 1 (z.map (1 : Fin 2).succAbove)) = circleSide i 0
  apply congrArg (circleSide i)
  apply Subtype.ext
  simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
    Fin.sum_univ_succ, Fin.succAbove]
theorem circle_face0 (i : Side) :
    (TopCat.toSSet.obj (TopCat.of Circle)).δ 0 (circleSideSimplex i) =
      circleVertex (next i) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋0⦌)).injective
  apply ContinuousMap.ext
  intro z
  change circleSide i (coord 1 (z.map (0 : Fin 2).succAbove)) = circleSide (next i) 0
  have hz : coord 1 (z.map (0 : Fin 2).succAbove) = 1 := by
    apply Subtype.ext
    simp [coord, StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
      Fin.sum_univ_succ, Fin.succAbove]
  rw [hz]
  apply Subtype.ext
  exact congrArg (fun x : Disk => (x : ℂ)) (side_end_next i)
theorem circle_boundary_is_cycle :
    singularBoundaryFinsupp (TopCat.of Circle) 0 circleBoundaryChain = 0 := by
  simp only [circleBoundaryChain, map_sum, singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, circle_face0, circle_face1, next]
  abel
end CurveComplex.Octagon.AttachingMap
