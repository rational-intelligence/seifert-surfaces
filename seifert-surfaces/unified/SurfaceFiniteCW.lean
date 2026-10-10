import SurfaceInvariants
import DifferentialGeometry.Topology.Simplex.AttachmentRelativeHomology
import DifferentialGeometry.Topology.SimplicialSet.RealizationEulerCharacteristic
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import ClassificationOfSurfaces.Moise.ChartInduction
import CurveComplexGenusTwo.Foundations.RealizationCW
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.PartialHomeomorph.Basic

import Mathlib.Topology.CWComplex.Classical.Finite

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Topology CategoryTheory CategoryTheory.Limits
open Convexity.StdSimplex (coordinateSet)
open scoped Classical
open Metric
open scoped Manifold
namespace SeifertSurfaces.GenusLinking
open SeifertSurfaces.Foundations
noncomputable section

/-- A genuine finite CW decomposition on the actual surface point set.
Mathlib supplies the attaching maps, disjoint open cells, and weak topology.
The existence theorem below applies to every compact smooth surface. -/
structure SurfaceCWDecomposition (S : CompactOrientedSurface.{0}) where
  cw : CWComplex (Set.univ : Set S)
  finiteCells : ∀ k, Finite (cw.cell k)
  dimension_two : ∀ k, 2 < k → IsEmpty (cw.cell k)

open LeanEval.Topology.ClassificationOfSurfaces

private def triangulationVertices {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) : Finset T.Vertex := T.faces.biUnion id

private def triangulationComplex {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) : AbstractSimplicialComplex (triangulationVertices T) where
  faces := {s | s.Nonempty ∧ ∃ t ∈ T.faces,
    s.image Subtype.val ⊆ t}
  isRelLowerSet_faces := by
    intro s hs
    constructor
    · exact hs.1
    · intro t hts ht
      obtain ⟨u, hu, hsu⟩ := hs.2
      exact ⟨ht, u, hu, (Finset.image_subset_image hts).trans hsu⟩
  singleton_mem := by
    intro v
    obtain ⟨t, ht, hvt⟩ := Finset.mem_biUnion.mp v.property
    exact ⟨Finset.singleton_nonempty _, t, ht, by simpa using hvt⟩

private def triangulationCoordinates {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) :
    CurveComplex.RealizationPoint (triangulationComplex T) →
      GeometricRealization T.Vertex T.faces := fun p => by
  classical
  let w : T.Vertex → ℝ := fun v =>
    if h : v ∈ triangulationVertices T then p.weight ⟨v, h⟩ else 0
  refine ⟨w, ?_⟩
  obtain ⟨s, ⟨hs, t, ht, hst⟩, hz, hsum⟩ := p.liesInFace
  refine ⟨⟨?_, ?_⟩, t, ht, ?_⟩
  · intro v
    dsimp [w]
    split_ifs <;> simp_all only [p.nonneg, le_refl]
  · have hall : ∑ v : triangulationVertices T, p.weight v = 1 := by
      rw [← hsum]
      exact (Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hz v hv)).symm
    rw [← hall]
    dsimp [w]
    exact (Finset.sum_attach_eq_sum_dite (triangulationVertices T) p.weight).symm
  · intro v hvt
    dsimp [w]
    split_ifs with hv
    · apply hz
      intro hvs
      exact hvt (hst (Finset.mem_image.mpr ⟨⟨v, hv⟩, hvs, rfl⟩))
    · rfl

private theorem triangulationCoordinates_continuous {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) : Continuous (triangulationCoordinates T) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  by_cases hv : v ∈ triangulationVertices T
  · simpa [triangulationCoordinates, hv] using
      CurveComplex.continuous_weight (triangulationComplex T) ⟨v, hv⟩
  · simpa [triangulationCoordinates, hv] using
      (continuous_const : Continuous (fun _ :
        CurveComplex.RealizationPoint (triangulationComplex T) => (0 : ℝ)))

private theorem triangulationCoordinates_bijective {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) : Function.Bijective (triangulationCoordinates T) := by
  classical
  constructor
  · intro p q hpq
    apply CurveComplex.RealizationPoint.ext
    funext v
    have h := congrArg (fun x : GeometricRealization T.Vertex T.faces => x.1 v.1) hpq
    simpa [triangulationCoordinates, v.property] using h
  · rintro ⟨w, hw, t, ht, hz⟩
    let s : Finset (triangulationVertices T) := Finset.univ.filter (fun v => v.1 ∈ t)
    have htpos : t.Nonempty := Finset.card_pos.mp (by rw [T.faces_card t ht]; decide)
    have hvs (v : T.Vertex) (hv : v ∈ t) : v ∈ triangulationVertices T :=
      Finset.mem_biUnion.mpr ⟨t, ht, hv⟩
    have hsum : ∑ v ∈ s, w v.1 = 1 := by
      have hsumt : ∑ v ∈ t, w v = 1 := by
        rw [← hw.2]
        exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hz v hv)
      rw [← hsumt]
      apply Finset.sum_bij (fun v _ => v.1)
      · intro v hv
        exact (Finset.mem_filter.mp hv).2
      · intro a _ b _ h
        exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v, hvs v hv⟩, by simp [s, hv], rfl⟩
      · intro v hv
        rfl
    let p : CurveComplex.RealizationPoint (triangulationComplex T) := {
      weight := fun v => w v.1
      nonneg := fun v => hw.1 v.1
      liesInFace := ⟨s, ⟨?_, t, ht, ?_⟩, ?_, hsum⟩ }
    · refine ⟨p, ?_⟩
      apply Subtype.ext
      funext v
      dsimp [triangulationCoordinates]
      split_ifs with hv
      · rfl
      · exact (hz v (fun hvt => hv (hvs v hvt))).symm
    · obtain ⟨v, hv⟩ := htpos
      exact ⟨⟨v, hvs v hv⟩, by simp [s, hv]⟩
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hu).2
    · intro v hv
      exact hz v.1 (fun hvt => hv (by simp [s, hvt]))

private theorem finiteRealization_compact {V : Type} [Finite V]
    (K : AbstractSimplicialComplex V) : CompactSpace (CurveComplex.RealizationPoint K) := by
  classical
  have hcover : (Set.univ : Set (CurveComplex.RealizationPoint K)) =
      ⋃ s : K.faces, Set.range (CurveComplex.faceInclusion K s.1 s.2) := by
    ext p
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_range, true_iff]
    obtain ⟨s, hs, x, hx⟩ := CurveComplex.exists_faceInclusion_eq K p
    exact ⟨⟨s, hs⟩, x, hx⟩
  apply isCompact_univ_iff.mp
  rw [hcover]
  exact isCompact_iUnion (fun s => isCompact_range (CurveComplex.continuous_faceInclusion K s.1 s.2))

private def triangulationHomeomorph {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) :
    CurveComplex.RealizationPoint (triangulationComplex T) ≃ₜ X := by
  letI := finiteRealization_compact (triangulationComplex T)
  exact (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (triangulationCoordinates T)
      (triangulationCoordinates_bijective T))
    (triangulationCoordinates_continuous T)).trans T.homeo

private theorem triangulation_face_card {X : Type} [TopologicalSpace X]
    (T : GeometricTriangulation X) {s : Finset (triangulationVertices T)}
    (hs : s ∈ (triangulationComplex T).faces) : s.card ≤ 3 := by
  obtain ⟨_, t, ht, hst⟩ := hs
  have hinj : Function.Injective (Subtype.val : triangulationVertices T → T.Vertex) :=
    Subtype.val_injective
  calc s.card = (s.image Subtype.val).card := (Finset.card_image_of_injective s hinj).symm
       _ ≤ t.card := Finset.card_le_card hst
       _ = 3 := T.faces_card t ht

private def transportedCW {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] (cw : CWComplex (Set.univ : Set X)) (e : X ≃ₜ Y)
    (hf : ∀ n, Finite (cw.cell n))
    (he : ∀ n, 2 < n → IsEmpty (cw.cell n)) : CWComplex (Set.univ : Set Y) := by
  letI := cw
  let m := fun n i => (cw.map n i).trans e.toEquiv.toPartialEquiv
  refine CWComplex.mkFinite Set.univ cw.cell m
    (Filter.eventually_atTop.mpr ⟨3, fun n hn => he n (by omega)⟩)
    hf ?_ ?_ ?_ ?_ ?_ ?_
  · intro n i
    simp [m, PartialEquiv.trans_source, cw.source_eq]
  · intro n i
    exact e.continuous.comp_continuousOn (cw.continuousOn n i)
  · intro n i
    apply (cw.continuousOn_symm n i).comp e.symm.continuous.continuousOn
    intro y hy
    simpa [m, PartialEquiv.trans_target] using hy
  · intro a _ b _ hab
    have h := cw.pairwiseDisjoint' (Set.mem_univ a) (Set.mem_univ b) hab
    simpa [m, Set.image_image, Function.comp_def] using
      Set.disjoint_image_of_injective e.injective h
  · intro n i x hx
    obtain ⟨I, hI⟩ := CWComplex.mapsTo n i
    have hh := hI hx
    simp only [Set.mem_iUnion, Set.mem_image] at hh ⊢
    obtain ⟨k, hk, j, hj, y, hy, heq⟩ := hh
    exact ⟨k, hk, j, y, hy, congrArg e heq⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro y
    have hh : e.symm y ∈ ⋃ (n : ℕ) (i : cw.cell n), cw.map n i '' closedBall 0 1 := by
      rw [cw.union']
      trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hh ⊢
    obtain ⟨n, i, x, hx, heq⟩ := hh
    refine ⟨n, i, x, hx, ?_⟩
    change e (cw.map n i x) = y
    rw [heq, e.apply_symm_apply]

private def triangulationCW {X : Type} [TopologicalSpace X] [T2Space X]
    (T : GeometricTriangulation X) : CWComplex (Set.univ : Set X) :=
  transportedCW (CurveComplex.realizationPointCWComplex (triangulationComplex T))
    (triangulationHomeomorph T) (by
      intro n
      change Finite {s : Finset (triangulationVertices T) //
        s ∈ (triangulationComplex T).faces ∧ s.card = n + 1}
      infer_instance) (by
      intro n hn
      change IsEmpty {s : Finset (triangulationVertices T) //
        s ∈ (triangulationComplex T).faces ∧ s.card = n + 1}
      refine ⟨fun s => ?_⟩
      have h := triangulation_face_card T s.property.1
      have hc := s.property.2
      omega)

private theorem triangulationCW_finite {X : Type} [TopologicalSpace X] [T2Space X]
    (T : GeometricTriangulation X) (n : ℕ) : Finite ((triangulationCW T).cell n) := by
  change Finite {s : Finset (triangulationVertices T) //
    s ∈ (triangulationComplex T).faces ∧ s.card = n + 1}
  infer_instance

private theorem triangulationCW_dimension {X : Type} [TopologicalSpace X] [T2Space X]
    (T : GeometricTriangulation X) (n : ℕ) (hn : 2 < n) :
    IsEmpty ((triangulationCW T).cell n) := by
  change IsEmpty {s : Finset (triangulationVertices T) //
    s ∈ (triangulationComplex T).faces ∧ s.card = n + 1}
  refine ⟨fun s => ?_⟩
  have h := triangulation_face_card T s.property.1
  have hc := s.property.2
  omega

private def assembledCW {J Y : Type} [Finite J] [TopologicalSpace Y] [T2Space Y]
    (A : J → Set Y) [∀ j, Nonempty (A j)]
    (cw : ∀ j, CWComplex (Set.univ : Set (A j)))
    (hf : ∀ j n, Finite ((cw j).cell n))
    (he : ∀ j n, 2 < n → IsEmpty ((cw j).cell n))
    (hd : Pairwise (fun j l => Disjoint (A j) (A l)))
    (hu : ⋃ j, A j = Set.univ) : CWComplex (Set.univ : Set Y) := by
  classical
  let p := fun j => (A j).partialHomeomorphSubtypeCoe (inferInstance : Nonempty (A j))
  let m := fun n (i : Σ j, (cw j).cell n) =>
    ((cw i.1).map n i.2).trans (p i.1).toPartialEquiv
  letI : ∀ j, CWComplex (Set.univ : Set (A j)) := cw
  have hsource (j : J) : (p j).source = Set.univ := rfl
  have hp (j : J) : (p j : A j → Y) = Subtype.val := rfl
  refine CWComplex.mkFinite Set.univ (fun n => Σ j, (cw j).cell n) m
    (Filter.eventually_atTop.mpr ⟨3, fun n hn => ?_⟩) (fun n => ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · letI : ∀ j, IsEmpty ((cw j).cell n) := fun j => he j n (by omega)
    infer_instance
  · letI : ∀ j, Finite ((cw j).cell n) := fun j => hf j n
    infer_instance
  · intro n i
    simp [m, PartialEquiv.trans_source, hsource, (cw i.1).source_eq]
  · intro n i
    exact continuous_subtype_val.comp_continuousOn ((cw i.1).continuousOn n i.2)
  · intro n i
    apply ((cw i.1).continuousOn_symm n i.2).comp
      ((p i.1).continuousOn_symm.mono Set.inter_subset_left)
    intro y hy
    exact hy.2
  · rintro ⟨n,j,i⟩ _ ⟨k,l,t⟩ _ hne
    by_cases hjl : j = l
    · subst l
      have hnt : (⟨n,i⟩ : Σ n, (cw j).cell n) ≠ ⟨k,t⟩ := by
        intro h
        apply hne
        cases h
        rfl
      have h := (cw j).pairwiseDisjoint' (Set.mem_univ _) (Set.mem_univ _) hnt
      simpa [m, p, Set.image_image, Function.comp_def] using
        Set.disjoint_image_of_injective (Subtype.val_injective (p := (· ∈ A j))) h
    · apply (hd hjl).mono
      · rintro y ⟨x,hx,rfl⟩
        exact ((cw j).map n i x).property
      · rintro y ⟨x,hx,rfl⟩
        exact ((cw l).map k t x).property
  · intro n i x hx
    obtain ⟨I,hI⟩ := @CWComplex.mapsTo (A i.1) _ _ (cw i.1) n i.2
    have hh := hI hx
    simp only [Set.mem_iUnion, Set.mem_image] at hh ⊢
    obtain ⟨k,hk,j,hj,y,hy,heq⟩ := hh
    exact ⟨k,hk,⟨i.1,j⟩,y,hy,congrArg Subtype.val heq⟩
  · apply Set.eq_univ_iff_forall.mpr
    intro y
    have hy : y ∈ ⋃ j, A j := by rw [hu]; trivial
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hy
    have hh : (⟨y,hj⟩ : A j) ∈ ⋃ (n : ℕ) (i : (cw j).cell n),
        (cw j).map n i '' closedBall 0 1 := by
      rw [(cw j).union']
      trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hh ⊢
    obtain ⟨n,i,x,hx,heq⟩ := hh
    exact ⟨n,⟨j,i⟩,x,hx,congrArg Subtype.val heq⟩


theorem compact_smooth_surface_finiteCW (S : CompactOrientedSurface.{0}) :
    Nonempty (SurfaceCWDecomposition S) := by
  classical
  letI : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) S
  letI : Finite (ConnectedComponents S) := compact_surface_components_finite S
  let U : ConnectedComponents S → TopologicalSpace.Opens S := fun j =>
    ⟨ConnectedComponents.mk ⁻¹' {j},
      ConnectedComponents.continuous_coe.isOpen_preimage _ (isOpen_discrete _)⟩
  have hU (j : ConnectedComponents S) : IsConnected (U j : Set S) := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe j
    change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
    rw [connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  letI : ∀ j, ConnectedSpace (U j) := fun j =>
    isConnected_iff_connectedSpace.mp (hU j)
  letI : ∀ j, CompactSpace (U j) := fun j =>
    isCompact_iff_compactSpace.mp ((isClosed_discrete {j}).preimage
      ConnectedComponents.continuous_coe).isCompact
  let T : ∀ j, GeometricTriangulation (U j) := fun j =>
    (LeanEval.Topology.ClassificationOfSurfaces.Moise.moise_triangulation_of_boundaries
      (U j)).some
  have hd : Pairwise (fun j l => Disjoint (U j : Set S) (U l : Set S)) := by
    intro j l hjl
    exact (Set.disjoint_singleton.mpr hjl).preimage ConnectedComponents.mk
  have hu : ⋃ j, (U j : Set S) = Set.univ := by
    ext x
    simp [U]
  let W := assembledCW (fun j => (U j : Set S)) (fun j => triangulationCW (T j))
    (fun j n => triangulationCW_finite (T j) n)
    (fun j n hn => triangulationCW_dimension (T j) n hn) hd hu
  refine ⟨{ cw := W, finiteCells := ?_, dimension_two := ?_ }⟩
  · intro n
    change Finite (Σ j, (triangulationCW (T j)).cell n)
    letI : ∀ j, Finite ((triangulationCW (T j)).cell n) := fun j =>
      triangulationCW_finite (T j) n
    infer_instance
  · intro n hn
    change IsEmpty (Σ j, (triangulationCW (T j)).cell n)
    letI : ∀ j, IsEmpty ((triangulationCW (T j)).cell n) := fun j =>
      triangulationCW_dimension (T j) n hn
    infer_instance

def cellEuler {S : CompactOrientedSurface.{0}} (C : SurfaceCWDecomposition S) : ℤ :=
  (Nat.card (C.cw.cell 0) : ℤ) - (Nat.card (C.cw.cell 1) : ℤ) +
    (Nat.card (C.cw.cell 2) : ℤ)

private def cwBallSimplex (n : ℕ) :
    (closedBall 0 1 : Set (Fin n → ℝ)) ≃ₜ coordinateSet ℝ (Fin (n+1)) :=
  CurveComplex.closedBallFinSimplexHomeomorph n

private theorem cwBallSimplex_open (n : ℕ)
    (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    (∀ j, 0 < (cwBallSimplex n x).val j) ↔ x.val ∈ ball 0 1 := by
  have hi := CurveComplex.closedBallFinSimplexHomeomorph_image_openBall n
  change cwBallSimplex n '' {x | x.val ∈ ball 0 1} = {x | ∀ j, 0 < x.val j} at hi
  change cwBallSimplex n x ∈ {x | ∀ j, 0 < x.val j} ↔ _
  rw [← hi]
  exact (cwBallSimplex n).injective.mem_set_image

private theorem cwBallSimplex_boundary (n : ℕ)
    (x : (closedBall 0 1 : Set (Fin n → ℝ))) :
    cwBallSimplex n x ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1)) ↔
      x.val ∈ sphere 0 1 := by
  have hb : x.val ∈ sphere 0 1 ↔ x.val ∉ ball 0 1 := by
    simp only [mem_sphere, mem_ball] at *
    exact ⟨fun h => by rw [h]; exact lt_irrefl _,
      fun h => le_antisymm x.prop (le_of_not_gt h)⟩
  rw [hb, ← cwBallSimplex_open n x]
  change (∃ j, (cwBallSimplex n x).val j = 0) ↔ ¬ ∀ j, 0 < (cwBallSimplex n x).val j
  push_neg
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, hj.le⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, le_antisymm hj ((cwBallSimplex n x).prop.1 j)⟩

private def cwCellToUnion {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (E : Set X) (n : ℕ) (i : RelCWComplex.cell C n) :
    C(coordinateSet ℝ (Fin (n+1)), ↥(E ∪ RelCWComplex.closedCell n i : Set X)) :=
  ⟨fun x => ⟨RelCWComplex.map n i ((cwBallSimplex n).symm x).val,
    Or.inr ⟨_, ((cwBallSimplex n).symm x).prop, rfl⟩⟩,
    ((RelCWComplex.continuousOn n i).restrict.comp (cwBallSimplex n).symm.continuous).subtype_mk _⟩

private def cwAttachingToOld {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (E : Set X) (n : ℕ) (i : RelCWComplex.cell C n)
    (hfront : RelCWComplex.cellFrontier n i ⊆ E) :
    C(DifferentialGeometry.Simplex.boundary (Fin (n+1)), E) :=
  ⟨fun x => ⟨RelCWComplex.map n i ((cwBallSimplex n).symm x.val).val,
    hfront ⟨_, (cwBallSimplex_boundary n _).mp (by simp), rfl⟩⟩,
    (((RelCWComplex.continuousOn n i).restrict.comp (cwBallSimplex n).symm.continuous).comp
      continuous_subtype_val).subtype_mk _⟩

private def cwOldToUnion {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (E : Set X) (n : ℕ) (i : RelCWComplex.cell C n) :
    C(E, ↥(E ∪ RelCWComplex.closedCell n i : Set X)) :=
  ⟨Set.inclusion subset_union_left, continuous_subtype_val.subtype_mk _⟩

private theorem cw_cell_attachment_pushout {X : Type} [TopologicalSpace X] [T2Space X]
    {C : Set X} [CWComplex C] (E : Set X) [CompactSpace E]
    (n : ℕ) (i : RelCWComplex.cell C n)
    (hfront : RelCWComplex.cellFrontier n i ⊆ E)
    (hd : Disjoint (RelCWComplex.openCell n i) E) :
    IsPushout DifferentialGeometry.Simplex.Attachment.boundaryι
      (TopCat.ofHom (cwAttachingToOld E n i hfront))
      (TopCat.ofHom (cwCellToUnion E n i))
      (TopCat.ofHom (cwOldToUnion E n i)) := by
  let D := coordinateSet ℝ (Fin (n+1))
  let P := E ∪ RelCWComplex.closedCell n i
  let r := cwCellToUnion E n i
  let b := cwOldToUnion E n i
  let g := cwAttachingToOld E n i hfront
  have hcomm (a : DifferentialGeometry.Simplex.boundary (Fin (n+1))) :
      r a.val = b (g a) := rfl
  have hboundary (d : D) (hd : d ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))) :
      r d = b (g ⟨d,hd⟩) := rfl
  have hnotBoundary (d : D) (hd : d ∉ DifferentialGeometry.Simplex.boundary (Fin (n+1))) :
      ((cwBallSimplex n).symm d).val ∈ ball 0 1 := by
    apply (cwBallSimplex_open n _).mp
    rw [Homeomorph.apply_symm_apply]
    intro j
    exact lt_of_le_of_ne (d.prop.1 j) (Ne.symm (fun h => hd ⟨j,h⟩))
  have houtside (d : D) (hd' : d ∉ DifferentialGeometry.Simplex.boundary (Fin (n+1))) :
      (r d).val ∉ E := by
    exact hd.notMem_of_mem_left ⟨_, hnotBoundary d hd', rfl⟩
  have hinj {d e : D}
      (hd' : d ∉ DifferentialGeometry.Simplex.boundary (Fin (n+1)))
      (he' : e ∉ DifferentialGeometry.Simplex.boundary (Fin (n+1)))
      (h : r d = r e) : d = e := by
    apply (cwBallSimplex n).symm.injective
    apply Subtype.ext
    apply (RelCWComplex.map n i).injOn
    · rw [RelCWComplex.source_eq]; exact hnotBoundary d hd'
    · rw [RelCWComplex.source_eq]; exact hnotBoundary e he'
    · exact congrArg (fun z : P => z.val) h
  let q : C(D ⊕ E, P) := ⟨Sum.elim r b, r.continuous.sumElim b.continuous⟩
  have hqsurj : Function.Surjective q := by
    rintro ⟨x,hx | hx⟩
    · exact ⟨Sum.inr ⟨x,hx⟩, rfl⟩
    · obtain ⟨y,hy,rfl⟩ := hx
      exact ⟨Sum.inl (cwBallSimplex n ⟨y,hy⟩), by
        apply Subtype.ext
        change RelCWComplex.map n i ((cwBallSimplex n).symm (cwBallSimplex n ⟨y,hy⟩)).val = _
        rw [Homeomorph.symm_apply_apply]⟩
  letI : CompactSpace D := isCompact_iff_compactSpace.mp
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin (n+1)))
  have hq : IsQuotientMap q := q.continuous.isClosedMap.isQuotientMap q.continuous hqsurj
  refine ⟨⟨rfl⟩, ⟨?_⟩⟩
  apply PushoutCocone.isColimitAux'
  intro s
  let f : C(D ⊕ E, s.pt) := ⟨Sum.elim s.inl s.inr,
    s.inl.hom.continuous.sumElim s.inr.hom.continuous⟩
  have hs (a : DifferentialGeometry.Simplex.boundary (Fin (n+1))) :
      s.inl a.val = s.inr (g a) := ConcreteCategory.congr_hom s.condition a
  have hf : Function.FactorsThrough f q := by
    intro x y h
    cases x with
    | inl d =>
      cases y with
      | inl e =>
        change r d = r e at h
        by_cases hd' : d ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))
        · by_cases he' : e ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))
          · have he : g ⟨d,hd'⟩ = g ⟨e,he'⟩ := by
              apply Subtype.ext
              exact congrArg (fun z : P => z.val) h
            exact (hs ⟨d,hd'⟩).trans ((congrArg s.inr he).trans (hs ⟨e,he'⟩).symm)
          · exact False.elim (houtside e he' (by
              rw [← congrArg (fun z : P => z.val) h]
              exact (g ⟨d,hd'⟩).prop))
        · by_cases he' : e ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))
          · exact False.elim (houtside d hd' (by
              rw [congrArg (fun z : P => z.val) h]
              exact (g ⟨e,he'⟩).prop))
          · exact congrArg s.inl (hinj hd' he' h)
      | inr a =>
        change r d = b a at h
        by_cases hd' : d ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))
        · have he : g ⟨d,hd'⟩ = a := Subtype.ext (congrArg (fun z : P => z.val) h)
          exact (hs ⟨d,hd'⟩).trans (congrArg s.inr he)
        · exact False.elim (houtside d hd' (by rw [congrArg (fun z : P => z.val) h]; exact a.prop))
    | inr a =>
      cases y with
      | inl d =>
        change b a = r d at h
        by_cases hd' : d ∈ DifferentialGeometry.Simplex.boundary (Fin (n+1))
        · have he : g ⟨d,hd'⟩ = a := Subtype.ext (congrArg (fun z : P => z.val) h.symm)
          exact ((hs ⟨d,hd'⟩).trans (congrArg s.inr he)).symm
        · exact False.elim (houtside d hd' (by rw [← congrArg (fun z : P => z.val) h]; exact a.prop))
      | inr a' =>
        change b a = b a' at h
        exact congrArg s.inr (Subtype.ext (congrArg (fun z : P => z.val) h))
  let l := TopCat.ofHom (hq.lift f hf)
  have hl (z : D ⊕ E) : l (q z) = f z := ContinuousMap.congr_fun (hq.lift_comp f hf) z
  refine ⟨l, ?_, ?_, ?_⟩
  · ext d; exact hl (Sum.inl d)
  · ext a; exact hl (Sum.inr a)
  · intro m hm hn
    ext x
    obtain ⟨z,rfl⟩ := hqsurj x
    cases z with
    | inl d => exact (ConcreteCategory.congr_hom hm d).trans (hl (Sum.inl d)).symm
    | inr a => exact (ConcreteCategory.congr_hom hn a).trans (hl (Sum.inr a)).symm


open scoped Simplicial

private def boundaryNondegEquiv (n m : ℕ) (hm : m < n) :
    (_root_.SSet.boundary n : _root_.SSet).nonDegenerate m ≃
      (Δ[n] : _root_.SSet).nonDegenerate m where
  toFun x := ⟨x.val.val, (_root_.SSet.Subcomplex.mem_nonDegenerate_iff (_root_.SSet.boundary n) x.val).mp x.prop⟩
  invFun x := ⟨⟨x.val, by rw [_root_.SSet.boundary_obj_eq_univ m n hm]; trivial⟩,
    (_root_.SSet.Subcomplex.mem_nonDegenerate_iff (_root_.SSet.boundary n) _).mpr x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem stdSimplex_cell_card (n m : ℕ) :
    Nat.card ((Δ[n] : _root_.SSet).nonDegenerate m) = Nat.choose (n+1) (m+1) := by
  rw [Nat.card_congr (_root_.SSet.stdSimplex.nonDegenerateEquiv' (n := n) (d := m))]
  change Nat.card {s : Finset (Fin (n+1)) // s.card = m+1} = _
  let e : {s : Finset (Fin (n+1)) // s.card = m+1} ≃
      ↥((Finset.univ : Finset (Fin (n+1))).powersetCard (m+1)) :=
    Equiv.subtypeEquivRight (fun _ => by simp [Finset.mem_powersetCard])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def nativeBoundaryFiniteHomeomorph (n : ℕ) :
    _root_.SSet.toTop.obj (_root_.SSet.boundary n : _root_.SSet) ≃ₜ
      DifferentialGeometry.Simplex.boundary (Fin (n+1)) :=
  ((DifferentialGeometry.SSet.nativeBoundaryHomeomorph n).trans
    (DifferentialGeometry.Simplex.boundaryUliftHomeomorph (Fin (n+1))).symm).trans
      ((Homeomorph.ulift : ULift (coordinateSet ℝ (Fin (n+1))) ≃ₜ coordinateSet ℝ (Fin (n+1))).subtype (fun _ => Iff.rfl))

private theorem coordinateBoundary_finite (n : ℕ) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ
      (TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n+1)))) := by
  exact (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph ℚ
    (nativeBoundaryFiniteHomeomorph n)).mp
      (DifferentialGeometry.SSet.finiteHomologyType_realization ℚ (_root_.SSet.boundary n))

private theorem coordinateBoundary_euler (n : ℕ) (hn : n ≤ 2) :
    DifferentialGeometry.Homology.eulerChar ℚ
      (TopCat.of (DifferentialGeometry.Simplex.boundary (Fin (n+1)))) =
      1 - (-1 : ℤ)^n := by
  rw [← DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph ℚ
    (nativeBoundaryFiniteHomeomorph n),
    DifferentialGeometry.SSet.eulerChar_realization_eq_sum_card_nonDegenerate ℚ
      (_root_.SSet.boundary n) n]
  have hc (m : ℕ) (hm : m ∈ Finset.range n) :
      Nat.card ((_root_.SSet.boundary n : _root_.SSet).nonDegenerate m) =
        Nat.choose (n+1) (m+1) :=
    (Nat.card_congr (boundaryNondegEquiv n m (Finset.mem_range.mp hm))).trans
      (stdSimplex_cell_card n m)
  rw [Finset.sum_congr rfl (fun m hm => congrArg (fun z : ℕ => (-1 : ℤ)^m*z) (hc m hm))]
  interval_cases n <;> norm_num [Finset.sum_range_succ, Nat.choose]

private theorem coordinateSimplex_finite (n : ℕ) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ
      (TopCat.of (coordinateSet ℝ (Fin (n+1)))) := by
  letI : ContractibleSpace (coordinateSet ℝ (Fin (n+1))) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n+1))).contractibleSpace
      ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (n+1))⟩
  exact DifferentialGeometry.Homology.finiteHomologyType_of_contractible ℚ

private theorem coordinateSimplex_euler (n : ℕ) :
    DifferentialGeometry.Homology.eulerChar ℚ
      (TopCat.of (coordinateSet ℝ (Fin (n+1)))) = 1 := by
  letI : ContractibleSpace (coordinateSet ℝ (Fin (n+1))) :=
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin (n+1))).contractibleSpace
      ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin (n+1))⟩
  exact DifferentialGeometry.Homology.eulerChar_of_contractible ℚ

private theorem coordinateSimplex_relative_euler (n : ℕ) (hn : n ≤ 2) :
    DifferentialGeometry.Homology.relativeEulerChar
      (TopCat.of (coordinateSet ℝ (Fin (n+1))))
      (DifferentialGeometry.Simplex.boundary (Fin (n+1))) ℚ = (-1 : ℤ)^n := by
  have hb := coordinateBoundary_finite n
  have hs := coordinateSimplex_finite n
  have h := DifferentialGeometry.Homology.relativeEulerChar_eq_sub
    (TopCat.of (coordinateSet ℝ (Fin (n+1))))
    (DifferentialGeometry.Simplex.boundary (Fin (n+1))) ℚ hb hs
  rw [coordinateSimplex_euler n, coordinateBoundary_euler n hn] at h
  exact h.trans (by ring)


private theorem cw_cell_attachment_euler {X : Type} [TopologicalSpace X] [T2Space X]
    {C : Set X} [CWComplex C] (E : Set X) [CompactSpace E]
    (n : ℕ) (i : RelCWComplex.cell C n) (hn : n ≤ 2)
    (hfront : RelCWComplex.cellFrontier n i ⊆ E)
    (hd : Disjoint (RelCWComplex.openCell n i) E)
    (hE : DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of E)) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ
      (TopCat.of (E ∪ RelCWComplex.closedCell n i : Set X)) ∧
    DifferentialGeometry.Homology.eulerChar ℚ
      (TopCat.of (E ∪ RelCWComplex.closedCell n i : Set X)) =
      DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of E) + (-1 : ℤ)^n := by
  let P := TopCat.of (E ∪ RelCWComplex.closedCell n i : Set X)
  let b := TopCat.ofHom (cwOldToUnion E n i)
  let B := Set.range b
  let R := ModuleCat.of ℚ ℚ
  have h := cw_cell_attachment_pushout E n i hfront hd
  let e : E ≃ₜ B :=
    (DifferentialGeometry.TopCat.Pushout.isClosedEmbedding_inr h
      DifferentialGeometry.Simplex.Attachment.isClosedEmbedding_boundaryι).isEmbedding.toHomeomorph
  have hB : DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of B) :=
    (DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph ℚ e).mp hE
  have hχB : DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of B) =
      DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of E) :=
    (DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph ℚ e).symm
  let K := DifferentialGeometry.Homology.relativeChainComplex
    (TopCat.of (coordinateSet ℝ (Fin (n+1))))
    (DifferentialGeometry.Simplex.boundary (Fin (n+1))) R
  let L := DifferentialGeometry.Homology.relativeChainComplex P B R
  have hK : DifferentialGeometry.HomologicalComplex.finiteHomologyType K :=
    DifferentialGeometry.Homology.finiteHomologyType_relativeChainComplex _ _ ℚ
      (coordinateBoundary_finite n) (coordinateSimplex_finite n)
  let a (m : ℕ) : K.homology m ≅ L.homology m :=
    DifferentialGeometry.Simplex.Attachment.cellRelativeHomologyIso R h m
  have hL : DifferentialGeometry.HomologicalComplex.finiteHomologyType L := by
    constructor
    · intro m
      letI := hK.1 m
      exact (a m).toLinearEquiv.finiteDimensional
    · obtain ⟨N,hN⟩ := hK.2
      exact ⟨N, fun m hm => (hN m hm).of_iso (a m).symm⟩
  have hχ : L.homologyEulerChar = K.homologyEulerChar := by
    apply finsum_congr
    intro m
    rw [(a m).toLinearEquiv.finrank_eq]
  have hP : DifferentialGeometry.Homology.finiteHomologyType ℚ P :=
    DifferentialGeometry.HomologicalComplex.finiteHomologyType_middle
      (DifferentialGeometry.Homology.relativeShortComplex P B R)
      (DifferentialGeometry.Homology.relativeShortExact P B R) hB hL
  refine ⟨hP, ?_⟩
  have hsub := DifferentialGeometry.Homology.relativeEulerChar_eq_sub P B ℚ hB hP
  change L.homologyEulerChar = _ at hsub
  have hval : K.homologyEulerChar = (-1 : ℤ)^n := coordinateSimplex_relative_euler n hn
  rw [hχ, hval, hχB] at hsub
  change DifferentialGeometry.Homology.eulerChar ℚ P = _
  omega


private def cwLower {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (n : ℕ) : Set X :=
  ⋃ (m : Fin n) (i : RelCWComplex.cell C m.val), RelCWComplex.closedCell m.val i

private theorem cwLower_compact {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (n : ℕ) (hf : ∀ m, Finite (RelCWComplex.cell C m)) :
    IsCompact (cwLower (C := C) n) := by
  letI : ∀ m, Finite (RelCWComplex.cell C m) := hf
  exact isCompact_iUnion (fun _ => isCompact_iUnion (fun _ => RelCWComplex.isCompact_closedCell))

private theorem cwFrontier_lower {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n) :
    RelCWComplex.cellFrontier n i ⊆ cwLower (C := C) n := by
  obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n i
  intro x hx
  obtain ⟨m,hm,j,_,hj⟩ := by simpa only [Set.mem_iUnion, exists_prop] using hI hx
  exact Set.mem_iUnion.mpr ⟨⟨m,hm⟩, Set.mem_iUnion.mpr ⟨j,hj⟩⟩

private theorem cw_disjoint_lower {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n) :
    Disjoint (RelCWComplex.openCell n i) (cwLower (C := C) n) := by
  have hsk : cwLower (C := C) n ⊆ CWComplex.skeletonLT C n := by
    intro x hx
    obtain ⟨m,j,hj⟩ := by simpa only [cwLower, Set.mem_iUnion] using hx
    exact (CWComplex.closedCell_subset_skeletonLT m.val j).trans
      (CWComplex.skeletonLT_mono (by exact_mod_cast m.isLt)) hj
  exact (CWComplex.disjoint_skeletonLT_openCell (n := (n : ℕ∞)) (m := n) le_rfl).symm.mono_right hsk

private def cwLevel {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (n : ℕ) (I : Finset (RelCWComplex.cell C n)) : Set X :=
  cwLower (C := C) n ∪ ⋃ i ∈ I, RelCWComplex.closedCell n i

private theorem cwLevel_compact {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (n : ℕ) (hf : ∀ m, Finite (RelCWComplex.cell C m))
    (I : Finset (RelCWComplex.cell C n)) : IsCompact (cwLevel (C := C) n I) := by
  apply (cwLower_compact n hf).union
  rw [show (⋃ i ∈ I, RelCWComplex.closedCell n i) = ⋃ i : I, RelCWComplex.closedCell n i.val by ext x; simp]
  exact isCompact_iUnion (fun i : I => RelCWComplex.isCompact_closedCell (C := C) (n := n) (i := i.val))

private theorem cwLevel_insert {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (n : ℕ) (I : Finset (RelCWComplex.cell C n)) (i : RelCWComplex.cell C n) :
    cwLevel (C := C) n (insert i I) = cwLevel (C := C) n I ∪ RelCWComplex.closedCell n i := by
  ext x
  simp [cwLevel, or_assoc, or_comm, or_left_comm]

private theorem cw_disjoint_level {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (n : ℕ) (I : Finset (RelCWComplex.cell C n))
    (i : RelCWComplex.cell C n) (hi : i ∉ I) :
    Disjoint (RelCWComplex.openCell n i) (cwLevel (C := C) n I) := by
  rw [cwLevel, disjoint_union_right]
  refine ⟨cw_disjoint_lower n i, ?_⟩
  simp only [disjoint_iUnion_right]
  intro j hj
  rw [← RelCWComplex.cellFrontier_union_openCell_eq_closedCell, disjoint_union_right]
  exact ⟨(cw_disjoint_lower n i).mono_right (cwFrontier_lower n j),
    RelCWComplex.disjoint_openCell_of_ne (by
      intro he
      have hij : i = j := eq_of_heq (Sigma.mk.inj_iff.mp he).2
      exact hi (hij.symm ▸ hj))⟩


private theorem cwLevel_euler {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (n : ℕ) (hn : n ≤ 2) (hf : ∀ m, Finite (RelCWComplex.cell C m))
    (hbase : DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of (cwLower (C := C) n)))
    (I : Finset (RelCWComplex.cell C n)) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of (cwLevel (C := C) n I)) ∧
    DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of (cwLevel (C := C) n I)) =
      DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of (cwLower (C := C) n)) +
        (-1 : ℤ)^n * I.card := by
  induction I using Finset.induction_on with
  | empty =>
    have he : cwLevel (C := C) n ∅ = cwLower (C := C) n := by ext x; simp [cwLevel]
    rw [he]
    exact ⟨hbase, by simp⟩
  | @insert i I hi ih =>
    let E := cwLevel (C := C) n I
    letI : CompactSpace E := isCompact_iff_compactSpace.mp (cwLevel_compact n hf I)
    have ha := cw_cell_attachment_euler E n i hn
      ((cwFrontier_lower n i).trans subset_union_left) (cw_disjoint_level n I i hi) ih.1
    have heq := cwLevel_insert n I i
    constructor
    · rw [heq]
      exact ha.1
    · rw [heq, ha.2, ih.2, Finset.card_insert_of_notMem hi]
      push_cast
      ring

private theorem cwLower_succ {X : Type} [TopologicalSpace X] {C : Set X}
    [CWComplex C] (n : ℕ) [Fintype (RelCWComplex.cell C n)] :
    cwLower (C := C) (n+1) = cwLevel (C := C) n Finset.univ := by
  ext x
  simp only [cwLower, cwLevel, Set.mem_iUnion, Set.mem_union, Finset.mem_univ,
    exists_prop, true_and]
  constructor
  · rintro ⟨⟨m,hmn⟩,i,hi⟩
    by_cases hm : m < n
    · exact Or.inl ⟨⟨m,hm⟩,i,hi⟩
    · have hm' : m = n := by omega
      subst m
      exact Or.inr ⟨i,hi⟩
  · rintro (⟨m,i,hi⟩ | ⟨i,hi⟩)
    · exact ⟨⟨m.val,by omega⟩,i,hi⟩
    · exact ⟨⟨n,by omega⟩,i,hi⟩

private theorem cwLower_euler {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X}
    [CWComplex C] (hf : ∀ m, Finite (RelCWComplex.cell C m)) (n : ℕ) (hn : n ≤ 3) :
    DifferentialGeometry.Homology.finiteHomologyType ℚ (TopCat.of (cwLower (C := C) n)) ∧
    DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of (cwLower (C := C) n)) =
      ∑ m ∈ Finset.range n, (-1 : ℤ)^m * Nat.card (RelCWComplex.cell C m) := by
  induction n with
  | zero =>
    have he : cwLower (C := C) 0 = ∅ := by ext x; simp [cwLower]
    rw [he]
    have heul : DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of (∅ : Set X)) = 0 :=
      DifferentialGeometry.Homology.eulerChar_of_isEmpty ℚ
    exact ⟨DifferentialGeometry.Homology.finiteHomologyType_of_subsingleton ℚ, by simpa using heul⟩
  | succ n ih =>
    have hb := ih (by omega)
    letI : Finite (RelCWComplex.cell C n) := hf n
    letI : Fintype (RelCWComplex.cell C n) := Fintype.ofFinite (RelCWComplex.cell C n)
    have ha := cwLevel_euler n (by omega) hf hb.1 Finset.univ
    rw [← cwLower_succ n] at ha
    refine ⟨ha.1, ?_⟩
    rw [ha.2, hb.2, Finset.sum_range_succ, Finset.card_univ, Nat.card_eq_fintype_card]


private theorem cwSurface_lower_three (S : SeifertSurfaces.Foundations.CompactOrientedSurface)
    (C : SurfaceCWDecomposition S) :
    @cwLower S _ Set.univ C.cw 3 = Set.univ := by
  letI : CWComplex (Set.univ : Set S) := C.cw
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set S) m),
      RelCWComplex.closedCell m i := by rw [CWComplex.union]; trivial
  obtain ⟨m,i,hi⟩ := by simpa only [Set.mem_iUnion] using hx
  have hm : m < 3 := by
    by_contra hh
    letI := C.dimension_two m (by omega)
    exact isEmptyElim i
  exact Set.mem_iUnion.mpr ⟨⟨m,hm⟩, Set.mem_iUnion.mpr ⟨i,hi⟩⟩

private theorem suppliedCW_euler (S : SeifertSurfaces.Foundations.CompactOrientedSurface)
    (C : SurfaceCWDecomposition S) :
    DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of S) = cellEuler C := by
  letI : CWComplex (Set.univ : Set S) := C.cw
  have h := cwLower_euler (C := (Set.univ : Set S)) C.finiteCells 3 (by omega)
  rw [cwSurface_lower_three S C] at h
  let e : ↥(Set.univ : Set S) ≃ₜ S := Homeomorph.Set.univ S
  have he := DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph ℚ
    (X := TopCat.of (Set.univ : Set S)) (Y := TopCat.of S) e
  rw [← he, h.2]
  simp [cellEuler, Finset.sum_range_succ]
  rfl

private theorem surfaceSingularEuler_eq (S : SeifertSurfaces.Foundations.CompactOrientedSurface) :
    DifferentialGeometry.Homology.eulerChar ℚ (TopCat.of S) = eulerCharacteristic S := by
  have hz (n : ℕ) (hn : 2 < n) : IsZero (rationalHomology S n) := by
    letI := compact_surface_higher_homology_zero S n hn
    exact ModuleCat.isZero_of_subsingleton _
  rw [DifferentialGeometry.Homology.eulerChar_eq_sum ℚ 2 hz]
  simp [eulerCharacteristic, betti, rationalHomology, Finset.sum_range_succ]
  ring

theorem cellEuler_eq_singularEuler (S : CompactOrientedSurface.{0})
    (C : SurfaceCWDecomposition S) : cellEuler C = eulerCharacteristic S := by
  exact (suppliedCW_euler S C).symm.trans (surfaceSingularEuler_eq S)

theorem cellEuler_independent (S : CompactOrientedSurface.{0})
    (C D : SurfaceCWDecomposition S) : cellEuler C = cellEuler D := by
  exact (cellEuler_eq_singularEuler S C).trans (cellEuler_eq_singularEuler S D).symm

end
end SeifertSurfaces.GenusLinking
