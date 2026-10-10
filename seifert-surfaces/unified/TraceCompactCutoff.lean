import TracePreparations
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations.AmbientNeatTransport
noncomputable section
universe u v

variable {S : CompactOrientedSurface.{u}} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SecondCountableTopology M]
  {f g : NeatEmbedding S M}

/-- The original assumptions suffice for a smooth compact cutoff equal to one
on every spatial point visited by the isotopy. Ambient compactness is unused. -/
theorem normalTrace_exists_compact_cutoff (F : SmoothNormalIsotopy S M f g) :
    ∃ χ : M → ℝ, ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      (∀ t x, χ ((F.stage t).toFun x) = 1) ∧ ∀ y, χ y ∈ Icc 0 1 := by
  letI : LocallyCompactSpace (EuclideanHalfSpace 3) := (𝓡∂ 3).locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanHalfSpace 3) M
  have hK : IsCompact (range (fun p : Time × S => (F.stage p.1).toFun p.2)) :=
    isCompact_range F.smooth_family.continuous
  obtain ⟨K,hKc,hKinside⟩ := exists_compact_superset hK
  obtain ⟨χ,hχone,hχzero,hχrange⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓡∂ 3) hK.isClosed hKinside (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hχrange⟩
  · exact HasCompactSupport.intro hKc hχzero
  · intro t x
    exact hχone.self_of_nhdsSet ((F.stage t).toFun x) (mem_range_self (t, x))

end
end SeifertSurfaces.Foundations.AmbientNeatTransport
