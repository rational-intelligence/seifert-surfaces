import ActualAnnulusSideNormalizationV869
import ActualContainedAnnulusCoordinatesV778

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusTimeReflectionV779
noncomputable section
namespace CompressionActualContainedAnnulusOriginalAmbientLabelsV870

/-- Both original attachment labels and every point of either whole closed
    outer half strip have actual supported ambient extensions to a contained
    annulus. Side normalization is derived. The support closure avoids ALL
    original D and ambient boundary; chart and connector data are constructed. -/
theorem contained_annulus_original_ambient_labels
    {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}
    (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E)
    (D : InteriorCompressingDisk F.embedding) (A B : CompressionAnnulus D)
    (hBA : range B.band ⊆ A.removed)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ R : Circle × Time ≃ₜ Circle × Time,
      (R = Homeomorph.refl _ ∨ R = reflection) ∧
      (∀ z,R (z,middleTime) = (z,middleTime)) ∧
      ∀ k : Fin 2,
        ∃ I : TopologicalAmbientIsotopy E.Carrier,∃ V : Set E.Carrier,
          IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) (range D.toFun) ∧
          Disjoint (closure V) ((𝓡∂ 3).boundary E.Carrier) ∧
          (∀ z,F.embedding.toFun (A.band (z,CompressionAnnulus.sideTime k)) ∈ V) ∧
          (∀ t x,x ∉ V → I.stage t x = x) ∧
          (∀ t x,x ∈ (𝓡∂ 3).boundary E.Carrier → I.stage t x = x) ∧
          ∀ (z : Circle) (t : Time),ε ≤ t.val →
            I.stage 1 (F.embedding.toFun (A.band (half k (z,t)))) =
              F.embedding.toFun (B.band (R (half k (z,t)))) := by
  obtain ⟨β,hβ,hβval,hβcore,hβopen⟩ :=
    CompressionActualContainedAnnulusCoordinatesV778.contained_annulus_coordinates E F D A B hBA
  obtain ⟨R,hR,hRc,hside⟩ :=
    CompressionActualAnnulusSideNormalizationV869.annulus_side_normalization β hβ hβcore hβopen
  let βn : C(Circle × Time,Circle × Time) := ⟨β ∘ R,β.continuous.comp R.continuous⟩
  have hβn : IsEmbedding βn := hβ.comp R.isEmbedding
  have hcn (z : Circle) : βn (z,middleTime) = (z,middleTime) := by
    change β (R (z,middleTime)) = _
    rw [hRc,hβcore]
  refine ⟨R,hR,hRc,?_⟩
  intro k
  obtain ⟨I,V,hV,hVc,hVD,hVbd,hseam,hoff,hbd,hpoint⟩ :=
    CompressionActualOriginalAnnulusAmbientExtensionV868.original_annulus_ambient_half_extension
      E F D A βn hβn hcn k (hside k) ε hε hε1
  refine ⟨I,V,hV,hVc,hVD,hVbd,hseam,hoff,hbd,?_⟩
  intro z t ht
  exact (hpoint z t ht).trans (congrArg F.embedding.toFun (hβval (R (half k (z,t)))))

#print axioms contained_annulus_original_ambient_labels
end CompressionActualContainedAnnulusOriginalAmbientLabelsV870
