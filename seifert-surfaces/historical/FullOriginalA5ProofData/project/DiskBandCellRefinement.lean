import DiskBandQuotientTopology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

attribute [local instance] Classical.propDecidable

def standardTriangle : Set (Euc 2) :=
  {u | 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ u 0 + u 1 ≤ 1}

def triangleAffine (a b c : Euc 2) (u : Euc 2) : Euc 2 :=
  a + u 0 • (b - a) + u 1 • (c - a)

def triangleVertices {n : ℕ} (triangle : Fin 3 → Fin n) : Finset (Fin n) :=
  Finset.univ.image triangle

def faceCarrier {n : ℕ} (vertex : Fin n → Euc 2) (face : Finset (Fin n)) : Set (Euc 2) :=
  convexHull ℝ (vertex '' (face : Set (Fin n)))

/-- A subdivision of the actual old union; no disjointness of the old list is assumed. -/
structure PlanarDiskRefinement {P : PolygonalKnot} (disk : FinitePlanarDisk P)
    (marked : Finset (Euc 2)) where
  vertexCount : ℕ
  vertex : Fin vertexCount → Euc 2
  vertex_injective : Function.Injective vertex
  count : ℕ
  triangle : Fin count → Fin 3 → Fin vertexCount
  vertex_used : ∀ v, ∃ i : Fin count, v ∈ triangleVertices (triangle i)
  nondegenerate : ∀ i, orientedPlaneDet
    (vertex (triangle i 1) - vertex (triangle i 0))
    (vertex (triangle i 2) - vertex (triangle i 0)) ≠ 0
  triangles_distinct : Function.Injective (fun i => triangleVertices (triangle i))
  covers : (⋃ i, closedTriangle (vertex (triangle i 0))
    (vertex (triangle i 1)) (vertex (triangle i 2))) = disk.region
  refines_old : ∀ i, ∃ j : Fin disk.triangleCount,
    closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2)) ⊆
      closedTriangle (disk.vertex (disk.triangle j 0))
        (disk.vertex (disk.triangle j 1)) (disk.vertex (disk.triangle j 2))
  old_triangles_refined : ∀ j : Fin disk.triangleCount,
    closedTriangle (disk.vertex (disk.triangle j 0))
      (disk.vertex (disk.triangle j 1)) (disk.vertex (disk.triangle j 2)) =
      ⋃ i, if closedTriangle (vertex (triangle i 0))
          (vertex (triangle i 1)) (vertex (triangle i 2)) ⊆
          closedTriangle (disk.vertex (disk.triangle j 0))
            (disk.vertex (disk.triangle j 1)) (disk.vertex (disk.triangle j 2)) then
        closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2))
      else ∅
  intersection : ∀ i j,
    closedTriangle (vertex (triangle i 0)) (vertex (triangle i 1)) (vertex (triangle i 2)) ∩
      closedTriangle (vertex (triangle j 0)) (vertex (triangle j 1)) (vertex (triangle j 2)) =
      faceCarrier vertex (triangleVertices (triangle i) ∩ triangleVertices (triangle j))
  marks_retained : (marked : Set (Euc 2)) ⊆ Set.range vertex
  old_triangle_vertices_retained : ∀ (j : Fin disk.triangleCount) (v : Fin 3),
    disk.vertex (disk.triangle j v) ∈ Set.range vertex
  polygon_vertices_retained : ∀ j, planarProjection (P.polygon.vertex j) ∈ Set.range vertex

namespace PlanarDiskRefinement
variable {P : PolygonalKnot} {disk : FinitePlanarDisk P} {marked : Finset (Euc 2)}
  (F : PlanarDiskRefinement disk marked)

def edgeCarrier (edge : Fin F.vertexCount × Fin F.vertexCount) : Set (Euc 2) :=
  segment ℝ (F.vertex edge.1) (F.vertex edge.2)

def boundaryEdges : Finset (Fin F.vertexCount × Fin F.vertexCount) :=
  Finset.univ.filter fun edge => edge.1 < edge.2 ∧
    (∃ i : Fin F.count, edge.1 ∈ triangleVertices (F.triangle i) ∧
      edge.2 ∈ triangleVertices (F.triangle i)) ∧
    F.edgeCarrier edge ⊆ frontier disk.region

def face (i : Fin F.count) : Euc 2 → Euc 2 :=
  triangleAffine (F.vertex (F.triangle i 0))
    (F.vertex (F.triangle i 1)) (F.vertex (F.triangle i 2))

theorem face_smooth (i : Fin F.count) : ContDiff ℝ ∞ (F.face i) := by
  unfold face triangleAffine
  fun_prop

theorem face_rank (i : Fin F.count) (u : Euc 2) :
    Function.Injective (fderiv ℝ (F.face i) u) := by
  let a := F.vertex (F.triangle i 0)
  let b := F.vertex (F.triangle i 1)
  let c := F.vertex (F.triangle i 2)
  let L : Euc 2 →L[ℝ] Euc 2 :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight (b - a) +
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight (c - a)
  have hder : HasFDerivAt (F.face i) L u := by
    convert (L.hasFDerivAt (x := u)).const_add a using 1
    funext v
    change a + v 0 • (b - a) + v 1 • (c - a) =
      a + (v 0 • (b - a) + v 1 • (c - a))
    exact add_assoc _ _ _
  rw [hder.fderiv]
  have hd : (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) ≠ 0 :=
    F.nondegenerate i
  intro x y h
  have hz : L (x - y) = 0 := by simp only [map_sub, h, sub_self]
  have hz0 := congrArg (fun v : Euc 2 => v 0) hz
  have hz1 := congrArg (fun v : Euc 2 => v 1) hz
  change (x 0 - y 0) * (b 0 - a 0) + (x 1 - y 1) * (c 0 - a 0) = 0 at hz0
  change (x 0 - y 0) * (b 1 - a 1) + (x 1 - y 1) * (c 1 - a 1) = 0 at hz1
  have hx : (x 0 - y 0) *
      ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (c 1 - a 1) * hz0 - (c 0 - a 0) * hz1
  have hy : (x 1 - y 1) *
      ((b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)) = 0 := by
    linear_combination (b 0 - a 0) * hz1 - (b 1 - a 1) * hz0
  have hx' := (mul_eq_zero.mp hx).resolve_right hd
  have hy' := (mul_eq_zero.mp hy).resolve_right hd
  ext j
  fin_cases j
  · exact sub_eq_zero.mp hx'
  · exact sub_eq_zero.mp hy'

theorem face_image (i : Fin F.count) :
    F.face i '' standardTriangle = closedTriangle
      (F.vertex (F.triangle i 0)) (F.vertex (F.triangle i 1)) (F.vertex (F.triangle i 2)) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨1 - u 0 - u 1, u 0, u 1, ?_, hu.1, hu.2.1, ?_, ?_⟩
    · linarith [hu.2.2]
    · ring
    · unfold face triangleAffine
      module
  · rintro ⟨r, s, t, hr, hs, ht, hsum, hx⟩
    refine ⟨!₂[s, t], ?_, ?_⟩
    · change 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1
      exact ⟨hs, ht, by linarith⟩
    · change F.vertex (F.triangle i 0) + s •
        (F.vertex (F.triangle i 1) - F.vertex (F.triangle i 0)) + t •
        (F.vertex (F.triangle i 2) - F.vertex (F.triangle i 0)) = x
      rw [hx]
      have h : r = 1 - s - t := by linarith
      rw [h]
      module

theorem face_mem (i : Fin F.count) (u : ↥standardTriangle) : F.face i u ∈ disk.region := by
  rw [← F.covers]
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [← F.face_image i]
  exact ⟨u, u.property, rfl⟩

def coordinate (i : Fin F.count) : ↥standardTriangle → disk.Carrier :=
  fun u => ⟨F.face i u, F.face_mem i u⟩

theorem coordinate_embedding (i : Fin F.count) : IsEmbedding (F.coordinate i) := by
  let a := F.vertex (F.triangle i 0)
  let b := F.vertex (F.triangle i 1)
  let c := F.vertex (F.triangle i 2)
  let L : Euc 2 →L[ℝ] Euc 2 :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).smulRight (b - a) +
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).smulRight (c - a)
  have hder : HasFDerivAt (F.face i) L 0 := by
    convert (L.hasFDerivAt (x := 0)).const_add a using 1
    funext v
    change a + v 0 • (b - a) + v 1 • (c - a) =
      a + (v 0 • (b - a) + v 1 • (c - a))
    exact add_assoc _ _ _
  have hinj : Function.Injective L := by
    simpa only [hder.fderiv] using F.face_rank i 0
  have hL := (LinearMap.isClosedEmbedding_of_injective
    (f := L.toLinearMap) (LinearMap.ker_eq_bot.mpr hinj)).isEmbedding
  have hf : IsEmbedding (F.face i) := by
    convert (Homeomorph.addLeft a).isEmbedding.comp hL using 1
    funext u
    dsimp [face, triangleAffine, L, a, b, c]
    abel
  exact IsEmbedding.subtypeVal.of_comp_iff.mp (hf.comp IsEmbedding.subtypeVal)

theorem coordinates_cover : (⋃ i, Set.range (F.coordinate i)) = univ := by
  apply eq_univ_of_forall
  intro x
  have hx := (Set.ext_iff.mp F.covers (x : Euc 2)).mpr x.property
  rcases mem_iUnion.mp hx with ⟨i, hi⟩
  rw [← F.face_image i] at hi
  rcases hi with ⟨u, hu, he⟩
  exact mem_iUnion.mpr ⟨i, ⟨u, hu⟩, Subtype.ext he⟩
end PlanarDiskRefinement

namespace DiskBandData
variable {P : PolygonalKnot} {D : RegularOrientedDiagram P}
  {R : OrientedResolution D} (B : DiskBandData R)

def attachmentEndpoint (k : Fin D.crossingCount) (e v : Fin 2) : Euc 2 :=
  (B.attaching k e (if v = 0 then 0 else 1) : Euc 2)

def diskMarks (i : Fin R.count) : Finset (Euc 2) :=
  Finset.univ.biUnion fun k : Fin D.crossingCount =>
    Finset.univ.biUnion fun e : Fin 2 =>
      if B.incident k e = i then Finset.univ.image (B.attachmentEndpoint k e) else ∅

/-- Real extension of the supplied band formula, not a replacement band. -/
def bandFormula (k : Fin D.crossingCount) (p : Euc 2) : Euc 3 :=
  B.bandAmbient k
    !₂[p 0, B.width k * (2 * p 1 - 1) * Real.cos (Real.pi * p 0),
      (D.crossing k).sign * B.width k * (2 * p 1 - 1) * Real.sin (Real.pi * p 0)]

def attachingFormula (k : Fin D.crossingCount) (e : Fin 2) (t : ℝ) : Euc 2 :=
  planarProjection (B.bandFormula k !₂[(if e = 0 then 0 else 1), t])

theorem bandFormula_eq (k : Fin D.crossingCount) (p : Time × Time) :
    B.bandFormula k !₂[(p.1 : ℝ), (p.2 : ℝ)] = B.map (B.bandInclusion k p) := by
  rfl

theorem attachingFormula_eq (k : Fin D.crossingCount) (e : Fin 2) (t : Time) :
    B.attachingFormula k e t = (B.attaching k e t : Euc 2) := by
  fin_cases e
  · ext j
    fin_cases j
    · simpa [attachingFormula, bandFormula, halfTwistedBand, FinitePlanarDisk.lifted,
        planarProjection] using congrArg (fun x : Euc 3 => x 0) (B.band_attachment k t).1
    · simpa [attachingFormula, bandFormula, halfTwistedBand, FinitePlanarDisk.lifted,
        planarProjection] using congrArg (fun x : Euc 3 => x 1) (B.band_attachment k t).1
  · ext j
    fin_cases j
    · simpa [attachingFormula, bandFormula, halfTwistedBand, FinitePlanarDisk.lifted,
        planarProjection] using congrArg (fun x : Euc 3 => x 0) (B.band_attachment k t).2
    · simpa [attachingFormula, bandFormula, halfTwistedBand, FinitePlanarDisk.lifted,
        planarProjection] using congrArg (fun x : Euc 3 => x 1) (B.band_attachment k t).2

theorem attachingFormula_smooth (k : Fin D.crossingCount) (e : Fin 2) :
    ContDiff ℝ ∞ (B.attachingFormula k e) := by
  have hA := (B.bandAmbient k).contDiff
  have hB : ContDiff ℝ ∞ (B.bandFormula k) := by
    unfold bandFormula
    apply hA.comp
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp <;> fun_prop
  have hp : ContDiff ℝ ∞ planarProjection := by
    unfold planarProjection
    apply PiLp.contDiff_toLp.comp
    apply contDiff_pi.mpr
    intro j
    fin_cases j <;> dsimp <;> fun_prop
  apply hp.comp (hB.comp _)
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp <;> fun_prop

def attachmentSpeed (k : Fin D.crossingCount) (e : Fin 2) (t : ℝ) : ℝ :=
  inner ℝ (B.attachingFormula k e t - B.attachmentEndpoint k e 0)
    (B.attachmentEndpoint k e 1 - B.attachmentEndpoint k e 0) /
      ‖B.attachmentEndpoint k e 1 - B.attachmentEndpoint k e 0‖ ^ 2

theorem attachment_endpoints_distinct (k : Fin D.crossingCount) (e : Fin 2) :
    B.attachmentEndpoint k e 0 ≠ B.attachmentEndpoint k e 1 := by
  intro h
  have ht := (B.attaching_embedding k e).injective (Subtype.ext h)
  have hr := congrArg (fun t : Time => (t : ℝ)) ht
  norm_num [attachmentEndpoint] at hr

theorem attachmentSpeed_smooth (k : Fin D.crossingCount) (e : Fin 2) :
    ContDiff ℝ ∞ (B.attachmentSpeed k e) := by
  unfold attachmentSpeed
  exact (((B.attachingFormula_smooth k e).sub contDiff_const).inner ℝ
    contDiff_const).div_const _

theorem attachmentSpeed_endpoints (k : Fin D.crossingCount) (e : Fin 2) :
    B.attachmentSpeed k e 0 = 0 ∧ B.attachmentSpeed k e 1 = 1 := by
  have hzero : B.attachingFormula k e 0 = B.attachmentEndpoint k e 0 :=
    B.attachingFormula_eq k e 0
  have hone : B.attachingFormula k e 1 = B.attachmentEndpoint k e 1 :=
    B.attachingFormula_eq k e 1
  have hn : ‖B.attachmentEndpoint k e 1 - B.attachmentEndpoint k e 0‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (B.attachment_endpoints_distinct k e).symm)
  constructor
  · simp [attachmentSpeed, hzero]
  · simp [attachmentSpeed, hone, real_inner_self_eq_norm_sq, hn]

/-- A noncollinear polygon corner cannot lie in the interior of a regular attaching arc. -/
theorem diskMarks_mem (i : Fin R.count) :
    (B.diskMarks i : Set (Euc 2)) ⊆ (B.disk i).region := by
  intro x hx
  simp only [diskMarks, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at hx
  rcases hx with ⟨k, e, hx⟩
  split_ifs at hx with hi
  · rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    subst i
    exact (B.attaching k e (if v = 0 then 0 else 1)).property
  · simpa using hx

end DiskBandData

/-- The cells remain inside the given quotient and carry literal image equations. -/
structure ActualDiskCellRefinement {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandPresentation R) where
  disk : ∀ i : Fin R.count, PlanarDiskRefinement (B.data.disk i) (B.data.diskMarks i)

namespace ActualDiskCellRefinement
variable {P : PolygonalKnot} {D : RegularOrientedDiagram P}
  {R : OrientedResolution D} {B : DiskBandPresentation R} (F : ActualDiskCellRefinement B)

def attachingEdges (k : Fin D.crossingCount) (e : Fin 2) :
    Finset (Fin (F.disk (B.data.incident k e)).vertexCount ×
      Fin (F.disk (B.data.incident k e)).vertexCount) :=
  (F.disk (B.data.incident k e)).boundaryEdges.filter fun edge =>
    (F.disk (B.data.incident k e)).edgeCarrier edge ⊆
      Set.range (fun t => (B.data.attaching k e t : Euc 2))

def coordinate (i : Fin R.count) (j : Fin (F.disk i).count) :
    ↥standardTriangle → B.data.Carrier :=
  B.data.diskInclusion i ∘ (F.disk i).coordinate j

theorem coordinate_image (i : Fin R.count) (j : Fin (F.disk i).count)
    (u : ↥standardTriangle) :
    B.data.map (F.coordinate i j u) =
      !₂[((F.disk i).face j u) 0, ((F.disk i).face j u) 1, B.data.height i] := by
  exact B.data.map_diskInclusion i ((F.disk i).coordinate j u)

theorem disk_cells_and_actual_bands_cover :
    (⋃ (i : Fin R.count) (j : Fin (F.disk i).count), Set.range (F.coordinate i j)) ∪
      (⋃ k, Set.range (B.data.bandInclusion k)) = univ := by
  have hd : (⋃ (i : Fin R.count) (j : Fin (F.disk i).count), Set.range (F.coordinate i j)) =
      ⋃ i, Set.range (B.data.diskInclusion i) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, hx⟩
      rcases mem_iUnion.mp hx with ⟨j, u, rfl⟩
      exact mem_iUnion.mpr ⟨i, (F.disk i).coordinate j u, rfl⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, u, rfl⟩
      have hu : u ∈ ⋃ j, Set.range ((F.disk i).coordinate j) := by
        rw [(F.disk i).coordinates_cover]
        trivial
      rcases mem_iUnion.mp hu with ⟨j, v, hv⟩
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, v, congrArg (B.data.diskInclusion i) hv⟩⟩
  rw [hd]
  exact B.data.pieces_cover

end ActualDiskCellRefinement

end
end SeifertSurfaces.LongitudeProducers
