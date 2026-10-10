import Section5BoundaryCompositionReplayV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

/-- Native smoothness, embeddedness and full differential rank of a longitude. -/
theorem longitude_leaf_regular (J : LongitudeFoliation.{0} E) (a : Circle) :
    ContMDiff (𝓡 1) (𝓡∂ 3) ∞ (fun z => J.torus (a,z)) ∧
    IsEmbedding (fun z => J.torus (a,z)) ∧
    ∀ z, Injective (mfderiv (𝓡 1) (𝓡∂ 3) (fun z => J.torus (a,z)) z) := by
  have hs : ContMDiff (𝓡 1) ((𝓡 1).prod (𝓡 1)) ∞ (fun z : Circle => (a,z)) :=
    contMDiff_const.prodMk contMDiff_id
  have hi : ∀ z : Circle, Injective
      (mfderiv (𝓡 1) ((𝓡 1).prod (𝓡 1)) (fun z : Circle => (a,z)) z) := by
    intro z
    rw [mfderiv_prodMk (f := fun _ : Circle => a) (g := fun z : Circle => z)
      mdifferentiableAt_const mdifferentiableAt_id]
    intro v w hvw
    have hsnd := congrArg Prod.snd hvw
    change (mfderiv (𝓡 1) (𝓡 1) (id : Circle → Circle) z) v =
      (mfderiv (𝓡 1) (𝓡 1) (id : Circle → Circle) z) w at hsnd
    rw [mfderiv_id] at hsnd
    exact hsnd
  refine ⟨J.smoothEmbedding.contMDiff.comp hs,
    J.smoothEmbedding.isEmbedding.comp (isEmbedding_prodMkRight a), ?_⟩
  intro z
  change Injective (mfderiv (𝓡 1) (𝓡∂ 3) (J.torus ∘ fun z : Circle => (a,z)) z)
  rw [mfderiv_comp z (J.smoothEmbedding.contMDiff.mdifferentiableAt (by simp))
    (hs.mdifferentiableAt (by simp))]
  exact (J.smoothEmbedding.isImmersion.mfderiv_injective (by simp) _).comp (hi z)

theorem common_boundary_label (J : LongitudeFoliation.{0} E)
    (A B : IncompressibleSpanningSurface.{0} E)
    (hA : J.BoundaryIn A.1.embedding.toFun) (hB : J.BoundaryIn B.1.embedding.toFun)
    (h : SurfaceBoundary E A = SurfaceBoundary E B) :
    ∃ a : Circle, A.1.embedding.toFun '' A.1.surface.boundary = J.leaf a ∧
      B.1.embedding.toFun '' B.1.surface.boundary = J.leaf a := by
  obtain ⟨a,ha⟩ := hA
  exact ⟨a,ha,h.symm.trans ha⟩

theorem longitude_leaf_compact_nonempty (J : LongitudeFoliation.{0} E) (a : Circle) :
    IsCompact (J.leaf a) ∧ (J.leaf a).Nonempty := by
  exact ⟨isCompact_range (longitude_leaf_regular J a).2.1.continuous,
    ⟨J.torus (a,1),mem_range_self 1⟩⟩

#print axioms longitude_leaf_regular
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
