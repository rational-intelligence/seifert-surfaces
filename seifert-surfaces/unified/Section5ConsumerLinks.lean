import Section5OpenObligations
import OriginalB2B5V480
import Section5ConsumerAssemblyV480
import Section5VersionTransportV481
import B3DonorBridgeV481
import Section5B2NativeReplayV489

set_option autoImplicit false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section5.ConsumerLinks
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.Section5
open SeifertSurfaces.OriginalEndpoints.Section5.Obligations

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/- These are exact consumer links to the separately reviewed B2--B5 output
package. They do not prove B2--B5 and are not extra inputs of original roots. -/

theorem original_pair_to_B3 (H : Section4.SourceGeometry E)
    (hK : KnotIsNontrivial K) (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2) :
    ∃ D : AppendixBOriginalV479.OriginalPair H.metric H.foliation,
      D.A = A ∧ D.B = B := by
  refine ⟨{ A := A
            B := B
            A_minimum := hA
            B_minimum := hB
            distance_two := hAB
            convex := Section5.WholeAssemblyV480.source_geometry_strictly_convex H
            analytic := H.analytic }, rfl, rfl⟩

theorem B3_interior_native_consumer (H : Section4.SourceGeometry E)
    (D : AppendixBOriginalV479.OriginalPair H.metric H.foliation)
    (hB3 : AppendixBOriginalV479.InteriorTangencyConclusion D) :
    InteriorTangencyResult E D.A D.B := by
  apply Section5.WholeAssemblyV480.interior_tangency_of_local_equations D hB3
  exact Section5.WholeAssemblyV480.b3_donor_local_equation D

theorem B3_collar_native_consumer (H : Section4.SourceGeometry E)
    (D : B1OriginalData H.metric H.foliation)
    (r0 : ℝ) (hr : 0 < r0) (hrD : r0 ≤ D.r0)
    (hcritical : ∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) (s, r) ≠ 0)
    (hfinite : (AppendixBOriginalV479.collarCriticalPoints D).Finite)
    (hzero : ∀ s ∈ AppendixBOriginalV479.collarCriticalPoints D, D.f s 0 = 0)
    (haway : ∀ p ∈ AppendixBOriginalV479.interiorTangencies D.A.1.embedding D.B.1.embedding,
      r0 ≤ AppendixBOriginalV479.extendedRadial D r0 p) :
    CollarTangencyResult E D := by
  exact ⟨r0, hr, hrD, hcritical, hfinite, hzero, haway⟩

theorem B2_push_off_native_consumer (H : Section4.SourceGeometry E)
    {S : CompactOrientedSurface.{0}} (F : NeatEmbedding S E.Carrier)
    (U : Set E.Carrier) (hU : IsOpen U)
    (collar : AppendixBOriginalV479.OneSidedCollar F U)
    (hleaf : H.foliation.BoundaryIn F.toFun) :
    ∃ sigma0 C : ℝ, 0 < sigma0 ∧ ∃ pushed : ℝ → NeatEmbedding S E.Carrier,
      (∀ sigma : ℝ, 0 < sigma → sigma ≤ sigma0 →
        (pushed sigma).image ⊆ U ∧ H.foliation.BoundaryIn (pushed sigma).toFun ∧
        SmoothAmbientIsotopy.Rel F.image (pushed sigma).image ∧
        area H.metric (pushed sigma).toFun - area H.metric F.toFun ≤ C * sigma) ∧
      (∀ sigma sigma' : ℝ, 0 < sigma → sigma ≤ sigma0 →
        0 < sigma' → sigma' ≤ sigma0 →
        SmoothAmbientIsotopy.Rel (pushed sigma).image (pushed sigma').image) := by
  obtain ⟨sigma0, C, hs, _, pushed, hpush, hsame⟩ :=
    Section5.WholeAssemblyV480.b2_original_push_off_native_v489 H.metric H.foliation F U hU
      (Section5.WholeAssemblyV480.one_sided_collar_to_v480 collar) hleaf
  exact ⟨sigma0, C, hs, pushed,
    fun sigma hp hle => hpush sigma ⟨hp, hle⟩,
    fun sigma sigma' hp hle hp' hle' => hsame sigma ⟨hp, hle⟩ sigma' ⟨hp', hle'⟩⟩

end SeifertSurfaces.OriginalEndpoints.Section5.ConsumerLinks
