import DiskBandProducers
import Mathlib.Topology.Homeomorph.Lemmas

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

namespace DiskBandData
variable {P : PolygonalKnot} {D : RegularOrientedDiagram P}
  {R : OrientedResolution D} (B : DiskBandData R)

/-- These maps use the literal quotient in DiskBandProducers, not a replacement carrier. -/
def diskInclusion (i : Fin R.count) : (B.disk i).Carrier → B.Carrier :=
  fun x => Quotient.mk B.gluingSetoid (Sum.inl ⟨i, x⟩)

def bandInclusion (k : Fin D.crossingCount) : Time × Time → B.Carrier :=
  fun p => Quotient.mk B.gluingSetoid (Sum.inr (k, p))

def bandEnd (e : Fin 2) (t : Time) : Time × Time :=
  ((if e = 0 then 0 else 1), t)

def outerImage : Set (Euc 3) := B.rawMap '' B.rawBoundary

/-- Q1's canonical homeomorphism is Mathlib's bundled range homeomorphism. -/
def imageHomeomorph : B.Carrier ≃ₜ ↥(Set.range B.map) :=
  (disk_band_quotient_embedding B).toHomeomorph

theorem imageHomeomorph_apply (x : B.Carrier) :
    (B.imageHomeomorph x : Euc 3) = B.map x := by
  rfl

theorem imageHomeomorph_boundary :
    Subtype.val '' (B.imageHomeomorph '' B.boundarySet) = B.outerImage := by
  rw [Set.image_image]
  change B.map '' (Quotient.mk B.gluingSetoid '' B.rawBoundary) = _
  rw [Set.image_image]
  rfl

theorem diskInclusion_continuous (i : Fin R.count) : Continuous (B.diskInclusion i) := by
  exact continuous_quotient_mk'.comp (continuous_inl.comp continuous_sigmaMk)

theorem bandInclusion_continuous (k : Fin D.crossingCount) :
    Continuous (B.bandInclusion k) := by
  exact continuous_quotient_mk'.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))

theorem diskInclusion_embedding (i : Fin R.count) : IsEmbedding (B.diskInclusion i) := by
  letI : CompactSpace (B.disk i).Carrier := (B.disk i).diskHomeomorph.compactSpace
  letI : T2Space B.Carrier := (disk_band_quotient_embedding B).t2Space
  apply ((B.diskInclusion_continuous i).isClosedEmbedding _).isEmbedding
  intro x y h
  have hm := congrArg B.map h
  change (B.disk i).lifted (B.height i) x = (B.disk i).lifted (B.height i) y at hm
  apply Subtype.ext
  ext j
  fin_cases j
  · exact congrArg (fun z : Euc 3 => z 0) hm
  · exact congrArg (fun z : Euc 3 => z 1) hm

theorem bandInclusion_embedding (k : Fin D.crossingCount) :
    IsEmbedding (B.bandInclusion k) := by
  letI : T2Space B.Carrier := (disk_band_quotient_embedding B).t2Space
  apply ((B.bandInclusion_continuous k).isClosedEmbedding _).isEmbedding
  intro p q h
  have hm := (B.bandAmbient k).injective (congrArg B.map h)
  change halfTwistedBand (D.crossing k).sign (B.width k) p =
    halfTwistedBand (D.crossing k).sign (B.width k) q at hm
  have ht : p.1 = q.1 := Subtype.ext (congrArg (fun z : Euc 3 => z 0) hm)
  have hc := congrArg (fun z : Euc 3 => z 1) hm
  have hs := congrArg (fun z : Euc 3 => z 2) hm
  dsimp [halfTwistedBand] at hc hs
  rw [ht] at hc hs
  have hw : B.width k ≠ 0 := ne_of_gt (B.width_pos k)
  have hsign : ((D.crossing k).sign : ℝ) ≠ 0 := by
    rw [(D.crossing k).sign_eq]
    split_ifs <;> norm_num
  have hu : (p.2 : ℝ) = (q.2 : ℝ) := by
    by_cases hcos : Real.cos (Real.pi * (q.1 : ℝ)) = 0
    · have hsin : Real.sin (Real.pi * (q.1 : ℝ)) ≠ 0 := by
        intro hsin
        have hid := Real.sin_sq_add_cos_sq (Real.pi * (q.1 : ℝ))
        rw [hcos, hsin] at hid
        norm_num at hid
      have heq := mul_right_cancel₀ hsin hs
      have heq' := mul_left_cancel₀ (mul_ne_zero hsign hw) heq
      linarith
    · have heq := mul_right_cancel₀ hcos hc
      have heq' := mul_left_cancel₀ hw heq
      linarith
  exact Prod.ext ht (Subtype.ext hu)

theorem map_diskInclusion (i : Fin R.count) (x : (B.disk i).Carrier) :
    B.map (B.diskInclusion i x) = (B.disk i).lifted (B.height i) x := by
  rfl

theorem map_bandInclusion (k : Fin D.crossingCount) (p : Time × Time) :
    B.map (B.bandInclusion k p) =
      B.bandAmbient k (halfTwistedBand (D.crossing k).sign (B.width k) p) := by
  rfl

theorem attachment_gluing (k : Fin D.crossingCount) (e : Fin 2) (t : Time) :
    B.diskInclusion (B.incident k e) (B.attaching k e t) =
      B.bandInclusion k (bandEnd e t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨k, e, t, rfl, rfl⟩)

theorem disk_band_intersection (i : Fin R.count) (k : Fin D.crossingCount) :
    Set.range (B.diskInclusion i) ∩ Set.range (B.bandInclusion k) =
      ⋃ e : Fin 2, if B.incident k e = i then
        Set.range (fun t => B.bandInclusion k (bandEnd e t)) else ∅ := by
  ext x
  constructor
  · rintro ⟨⟨u, hu⟩, ⟨p, hp⟩⟩
    have hm : B.map x ∈
        Set.range (B.bandAmbient k ∘ halfTwistedBand (D.crossing k).sign (B.width k)) ∩
          Set.range ((B.disk i).lifted (B.height i)) := by
      constructor
      · exact ⟨p, (B.map_bandInclusion k p).symm.trans (congrArg B.map hp)⟩
      · exact ⟨u, (B.map_diskInclusion i u).symm.trans (congrArg B.map hu)⟩
    rw [B.no_extra_disk_intersection k i] at hm
    rcases mem_iUnion.mp hm with ⟨e, he⟩
    apply mem_iUnion.mpr
    refine ⟨e, ?_⟩
    split_ifs at he ⊢ with hi
    · rcases he with ⟨t, ht⟩
      refine ⟨t, (disk_band_quotient_embedding B).injective ?_⟩
      change B.map (B.bandInclusion k (bandEnd e t)) = B.map x
      rw [← B.attachment_gluing k e t, B.map_diskInclusion]
      exact ht
    · exact False.elim he
  · intro hx
    rcases mem_iUnion.mp hx with ⟨e, he⟩
    split_ifs at he with hi
    · rcases he with ⟨t, rfl⟩
      subst i
      exact ⟨⟨B.attaching k e t, B.attachment_gluing k e t⟩, ⟨bandEnd e t, rfl⟩⟩
    · exact False.elim he

theorem disks_disjoint (i j : Fin R.count) (h : i ≠ j) :
    Disjoint (Set.range (B.diskInclusion i)) (Set.range (B.diskInclusion j)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu⟩ ⟨v, hv⟩
  have hm := congrArg B.map (hu.trans hv.symm)
  rw [B.map_diskInclusion, B.map_diskInclusion] at hm
  have hij := B.distinct_heights (congrArg (fun z : Euc 3 => z 2) hm)
  exact h hij

theorem bands_disjoint_in_quotient (k l : Fin D.crossingCount) (h : k ≠ l) :
    Disjoint (Set.range (B.bandInclusion k)) (Set.range (B.bandInclusion l)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp⟩ ⟨q, hq⟩
  apply Set.disjoint_left.mp (B.bands_disjoint h)
  · exact ⟨p, (B.map_bandInclusion k p).symm.trans (congrArg B.map hp)⟩
  · exact ⟨q, (B.map_bandInclusion l q).symm.trans (congrArg B.map hq)⟩

theorem pieces_cover :
    (⋃ i, Set.range (B.diskInclusion i)) ∪ (⋃ k, Set.range (B.bandInclusion k)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with ⟨i, u⟩ | ⟨k, p⟩
    · exact Or.inl (mem_iUnion.mpr ⟨i, u, rfl⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, p, rfl⟩)

theorem quotient_t2 : T2Space B.Carrier := by
  exact (disk_band_quotient_embedding B).t2Space

theorem quotient_secondCountable : SecondCountableTopology B.Carrier := by
  exact (disk_band_quotient_embedding B).secondCountableTopology

end DiskBandData

theorem presentation_boundary_image {P : PolygonalKnot} {D : RegularOrientedDiagram P}
    {R : OrientedResolution D} (B : DiskBandPresentation R) :
    Set.range (B.data.map ∘ B.boundary.boundary) = B.data.outerImage := by
  rw [Set.range_comp, B.boundary.covers_boundary]
  change B.data.map '' (Quotient.mk B.data.gluingSetoid '' B.data.rawBoundary) = _
  rw [Set.image_image]
  rfl

end
end SeifertSurfaces.LongitudeProducers
