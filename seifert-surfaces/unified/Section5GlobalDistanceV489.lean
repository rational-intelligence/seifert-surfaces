import Section5CompactGermGluingV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
noncomputable section
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}

theorem inward_distance_of_local_germs {ι : Type*} (g : SmoothMetric E.Carrier)
    (U : ι → Set E.Carrier) (r : ι → E.Carrier → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hr : ∀ i, IsInwardDistanceCoordinate g (U i) (r i))
    (V : Set E.Carrier) (hV : IsOpen V) (F : E.Carrier → ℝ)
    (hF : ∀ p ∈ V, ∃ i, p ∈ U i ∧ F =ᶠ[𝓝 p] r i) :
    IsInwardDistanceCoordinate g V F := by
  have hs (p : E.Carrier) (hp : p ∈ V) : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ) ∞ F p := by
    obtain ⟨i,hi,he⟩ := hF p hp
    exact (((hr i).1 p hi).contMDiffAt ((hU i).mem_nhds hi)).congr_of_eventuallyEq he
  refine ⟨fun p hp => (hs p hp).contMDiffWithinAt,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,hi,he⟩ := hF p hp
    rw [he.self_of_nhds]
    exact (hr i).2.1 p hi
  · intro p hp
    obtain ⟨i,hi,he⟩ := hF p hp
    rw [he.self_of_nhds]
    exact (hr i).2.2.1 p hi
  · intro p hp
    obtain ⟨i,hi,he⟩ := hF p hp
    obtain ⟨n,hn,hnr⟩ := (hr i).2.2.2 p hi
    refine ⟨n,hn,?_⟩
    intro w
    have hd := he.mfderiv_eq (I := (𝓡∂ 3)) (I' := 𝓘(ℝ))
    change mfderiv (𝓡∂ 3) 𝓘(ℝ) F p = mfderiv (𝓡∂ 3) 𝓘(ℝ) (r i) p at hd
    change g.inner p n w = mfderivWithin (𝓡∂ 3) 𝓘(ℝ) F V p w
    rw [mfderivWithin_eq_mfderiv (hV.uniqueMDiffWithinAt hp)
      ((hs p hp).mdifferentiableAt (by simp)),hd]
    have hri : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ) (r i) p :=
      (((hr i).1 p hi).contMDiffAt ((hU i).mem_nhds hi)).mdifferentiableAt (by simp)
    have hw := hnr w
    change g.inner p n w = mfderivWithin (𝓡∂ 3) 𝓘(ℝ) (r i) (U i) p w at hw
    rwa [mfderivWithin_eq_mfderiv ((hU i).uniqueMDiffWithinAt hi) hri] at hw

theorem actual_inward_distance_near_compact_boundary (G : A7.SourceGeometry E)
    (S : Set E.Carrier) (hS : IsCompact S) (hSb : S ⊆ (𝓡∂ 3).boundary E.Carrier) :
    ∃ U : Set E.Carrier, IsOpen U ∧ S ⊆ U ∧
      ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r := by
  let C := WarpedBoundaryCollar G.extension (Set.range E.toSphere)
  let U : C → Set E.Carrier := fun c => E.toSphere ⁻¹' c.coordinates.chart.source
  let r : C → E.Carrier → ℝ := fun c => c.radial ∘ E.toSphere
  have hU (c : C) : IsOpen (U c) :=
    c.coordinates.chart.open_source.preimage actual_exterior_smooth_embedding.contMDiff.continuous
  have hcover : S ⊆ ⋃ c : C, U c := by
    intro p hp
    obtain ⟨c,hc⟩ := G.collars p (hSb hp)
    exact mem_iUnion.mpr ⟨c,hc⟩
  have hagree (p : E.Carrier) (hp : p ∈ S) (c d : C)
      (hc : p ∈ U c) (hd : p ∈ U d) : r c =ᶠ[𝓝 p] r d := by
    obtain ⟨W,hW,hpW,hsub,he⟩ := warped_radial_agreement_near_boundary c d
      (E.toSphere p) hc hd ((G.boundary_exact p).mpr (hSb hp))
    have hpre : IsOpen (E.toSphere ⁻¹' W) :=
      hW.preimage actual_exterior_smooth_embedding.contMDiff.continuous
    filter_upwards [hpre.mem_nhds hpW] with q hq
    exact he (E.toSphere q) ⟨hq,⟨q,rfl⟩⟩
  obtain ⟨V,hV,hSV,F,hF⟩ := compact_germ_gluing S hS U r hU hcover hagree
  exact ⟨V,hV,hSV,F,inward_distance_of_local_germs G.metric U r hU
    (fun c => warped_exterior_inward_distance G c) V hV F hF⟩

theorem actual_inward_distance_near_longitude (G : A7.SourceGeometry E)
    (J : LongitudeFoliation.{0} E) (a : Circle) :
    ∃ U : Set E.Carrier, IsOpen U ∧ J.leaf a ⊆ U ∧
      ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r := by
  apply actual_inward_distance_near_compact_boundary G (J.leaf a)
    (longitude_leaf_compact_nonempty J a).1
  intro p hp
  obtain ⟨z,hz⟩ := hp
  rw [← hz]
  exact J.torus_lands_boundary (a,z)

theorem actual_inward_distance_near_entire_boundary (G : A7.SourceGeometry E)
    (J : LongitudeFoliation.{0} E) :
    ∃ U : Set E.Carrier, IsOpen U ∧ (𝓡∂ 3).boundary E.Carrier ⊆ U ∧
      ∃ r : E.Carrier → ℝ, IsInwardDistanceCoordinate G.metric U r := by
  apply actual_inward_distance_near_compact_boundary G ((𝓡∂ 3).boundary E.Carrier) _ subset_rfl
  rw [← J.covers_boundary]
  exact isCompact_range J.smoothEmbedding.contMDiff.continuous

#print axioms actual_inward_distance_near_compact_boundary
#print axioms actual_inward_distance_near_longitude
#print axioms actual_inward_distance_near_entire_boundary
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
