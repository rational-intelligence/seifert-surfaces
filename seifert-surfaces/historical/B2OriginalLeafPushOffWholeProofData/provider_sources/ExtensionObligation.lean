import NeatTransport
import NormalFiniteContinuation

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.Foundations
universe u v
noncomputable section

-- Original owned obligation, with its reviewed header unchanged.
theorem smooth_isotopy_extension {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SecondCountableTopology M]
    {f g : NeatEmbedding S M} (F : SmoothNormalIsotopy S M f g) :
    ∃ H : SmoothAmbientIsotopy M, ∀ x, H.stage 1 (f.toFun x) = g.toFun x := by
  obtain ⟨H,hH⟩ := AmbientNeatTransport.normal_isotopy_ambient_endpoint F
  refine ⟨H,?_⟩
  intro x
  simpa only [F.initial,F.final] using hH x

end
end SeifertSurfaces.Foundations
