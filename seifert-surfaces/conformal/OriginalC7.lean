import C7Conformal

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SeifertSurfaces.AppendixC.Original

universe u v

abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable (M : Type u) [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold (𝓡 2) ∞ M]
  (S : Type v) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]

/-- A compact smooth subsurface is a surface with smooth boundary, together
with its actual inclusion. The boundary is the frontier of that same image.
Compactness of the source is an ambient instance at each use. -/
structure SmoothSubsurface (j : S → M) : Prop where
  embedding : Topology.IsEmbedding j
  smooth : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ j
  immersion : ∀ p, Function.Injective (mfderiv (𝓡∂ 2) (𝓡 2) j p)
  boundary_image : j '' (𝓡∂ 2).boundary S = frontier (Set.range j)

/-- Restriction of a conformal class uses the differential of the actual
subsurface inclusion; its representatives remain positive rays. -/
def restrictedRepresentative
    (t : SmoothConformalField (𝓡 2) M) (j : S → M) :
    ∀ p : S, TangentSpace (𝓡∂ 2) p →L[ℝ] TangentSpace (𝓡∂ 2) p →L[ℝ] ℝ :=
  fun p => pullbackBilinear (t.representative (j p)) (mfderiv (𝓡∂ 2) (𝓡 2) j p)

/-- The full original Lemma C.7: one smooth global representative, and its
restriction to every actual compact smooth subsurface of a closed surface.
Both equalities refer to the same returned global metric and given class. -/
theorem paper_C7 [T2Space M] [SecondCountableTopology M]
    (t : SmoothConformalField (𝓡 2) M) :
    ∃ g : ContMDiffRiemannianMetric (𝓡 2) ∞ Plane
        (fun p : M => TangentSpace (𝓡 2) p),
      PointwiseConformal (𝓡 2) M g.inner t.representative ∧
      ∀ (S : Type v) [TopologicalSpace S]
        [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold (𝓡∂ 2) ∞ S]
        [T2Space S] [SecondCountableTopology S] [CompactSpace S],
        IsCompact (Set.univ : Set M) →
        ∀ (j : S → M), SmoothSubsurface M S j →
        ∃ gs : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ Plane
            (fun p : S => TangentSpace (𝓡∂ 2) p),
          (∀ p v w, gs.inner p v w =
            g.inner (j p) (mfderiv (𝓡∂ 2) (𝓡 2) j p v)
              (mfderiv (𝓡∂ 2) (𝓡 2) j p w)) ∧
          PointwiseConformal (𝓡∂ 2) S gs.inner (restrictedRepresentative M S t j) := by
  obtain ⟨g, hg⟩ := c7_smooth_metric_representative (𝓡 2) M t
  refine ⟨g, hg, ?_⟩
  intro S _ _ _ _ _ _ _ j hj
  obtain ⟨gs, hgs⟩ := c7_restrict_metric_smooth_up_to_boundary (𝓡 2) M
    (𝓡∂ 2) S j hj.smooth hj.immersion g
  refine ⟨gs, hgs, ?_⟩
  intro p
  obtain ⟨c, hc, hconformal⟩ := hg (j p)
  refine ⟨c, hc, ?_⟩
  intro v w
  rw [hgs]
  exact hconformal _ _

end SeifertSurfaces.AppendixC.Original
