import IncidenceProbe
import SectorBoundaryClockProbe
import BoundaryImageIntervalProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

private theorem embedded_map_through_partial_map
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : PartialHomeomorph Y Z) (f : X → Y) (hf : IsEmbedding f)
    (hm : MapsTo f univ e.source) : IsEmbedding (e ∘ f) := by
  exact e.isEmbedding_restrict.comp (hf.codRestrict e.source (fun x => hm (mem_univ x)))

/-- An actual incident native sector has a boundary interval whose image
contains an open interval of the original isolated seam clock. No boundary
lift or differential regularity is a hypothesis. -/
theorem native_incident_boundary_contains_clock
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (W : Set ℝ) (edge : W → S) (he : IsEmbedding edge) (s : W)
    (U : Set S) (hU : IsOpen U) (hsU : edge s ∈ U)
    (hUB : U ⊆ S.boundaryᶜ)
    (hcut : F.seam.carrier ∩ U ⊆ range edge)
    (hs : edge s ∈ F.seam.carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (p : F.domain i) (hpc : p ∈ ((F.domain i).chart j).map.source)
    (hp : F.parametrization i p = edge s) :
    ∃ Q : Set ℝ, IsOpen Q ∧ Q ⊆ W ∧ (s : ℝ) ∈ Q ∧
      ∀ t : W, (t : ℝ) ∈ Q → ∃ y : Euc 2,
        y ∈ ((F.domain i).chart j).map.target ∩
          frontier ((F.domain i).chart j).map.target ∧
        F.parametrization i (((F.domain i).chart j).map.symm y) = edge t := by
  classical
  let c := (F.domain i).chart j
  let b := sectorBoundaryClock c.model.angle
  let V₀ := Ioo (-c.model.radius) c.model.radius
  have hpb : p ∈ (F.domain i).boundary :=
    native_seam_incident_preimage_boundary E F i p (hp ▸ hs)
  have hyb : c.map p ∈ c.model.boundary := by
    rw [← (F.domain i).boundary_charts j]
    exact ⟨p, ⟨hpb, hpc⟩, rfl⟩
  have hfalse : c.model.interiorChart = false := by
    cases h : c.model.interiorChart
    · rfl
    · simpa [SectorModel.boundary, h] using hyb.2
  have hbimage : b '' V₀ = c.model.boundary := sectorBoundaryClock_image c.model hfalse
  have hbt : MapsTo b V₀ c.map.target := by
    intro t ht
    rw [c.target_eq]
    exact (hbimage ▸ show b t ∈ b '' V₀ from ⟨t, ht, rfl⟩).1
  have hbemb : IsEmbedding (fun t : V₀ => b t) :=
    (sectorBoundaryClock_embedding c.model.angle c.model.angle_positive
      c.model.angle_lt_two_pi).comp Topology.IsEmbedding.subtypeVal
  have hcbemb : IsEmbedding (fun t : V₀ => c.map.symm (b t)) :=
    embedded_map_through_partial_map c.map.symm (fun t : V₀ => b t) hbemb
      (fun t _ => hbt t.property)
  let boundary : ℝ → S := F.parametrization i ∘ c.map.symm ∘ b
  have hbdemb : IsEmbedding (fun t : V₀ => boundary t) :=
    (F.parametrization_embedding i).comp hcbemb
  have hbdcont : ContinuousOn boundary V₀ := by
    exact (continuousOn_iff_continuous_restrict).mpr hbdemb.continuous
  let V := V₀ ∩ boundary ⁻¹' U
  have hV : IsOpen V := hbdcont.isOpen_inter_preimage isOpen_Ioo hU
  have hbdembV : IsEmbedding (fun t : V => boundary t) :=
    hbdemb.comp (Topology.IsEmbedding.inclusion (inter_subset_left))
  have hbdmaps : MapsTo (fun t : V => boundary t) univ (range edge) := by
    intro t _
    apply hcut
    have hcb : c.map.symm (b t) ∈ (F.domain i).boundary := by
      have hbmem : b t ∈ c.model.boundary :=
        hbimage ▸ ⟨t.val, t.property.1, rfl⟩
      rw [← (F.domain i).boundary_charts j] at hbmem
      obtain ⟨p', ⟨hp'b, hp'c⟩, hp'⟩ := hbmem
      rw [← hp', c.map.left_inv hp'c]
      exact hp'b
    have hcut' := F.piece_boundary i ⟨c.map.symm (b t), hcb, rfl⟩
    refine ⟨?_, t.property.2⟩
    rcases hcut' with hseam | hboundary
    · exact hseam
    · exact (hUB t.property.2 hboundary).elim
  obtain ⟨Q, hQ, hQW, hQeq⟩ :=
    embedded_boundary_contains_seam_interval V W hV (fun t => boundary t)
      hbdembV edge he hbdmaps
  have hsQ : (s : ℝ) ∈ Q := by
    apply (hQeq s).mp
    obtain ⟨t, ht, htimage⟩ := (hbimage ▸ hyb : c.map p ∈ b '' V₀)
    have htbd : boundary t = edge s := by
      dsimp only [boundary, Function.comp_apply]
      rw [htimage, c.map.left_inv hpc, hp]
    exact ⟨⟨t, ht, by change boundary t ∈ U; rw [htbd]; exact hsU⟩, htbd⟩
  refine ⟨Q, hQ, hQW, hsQ, ?_⟩
  intro t ht
  obtain ⟨v, hv⟩ := (hQeq t).mpr ht
  have hvb : b v ∈ c.model.boundary := hbimage ▸ ⟨v.val, v.property.1, rfl⟩
  have hvt := hbt v.property.1
  refine ⟨b v, ⟨hvt, ⟨subset_closure hvt, ?_⟩⟩, hv⟩
  rw [c.target_eq, AreaCertificates.sector_model_interior]
  exact fun h => h.2 hvb

/-- The local boundary image conclusion yields a total coordinate function
on an open neighbourhood of the original clock point. Its values are actual
native chart coordinates, with the exact source image equality. -/
theorem native_incident_boundary_coordinate_lift
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (W : Set ℝ) (β : ℝ → S)
    (he : IsEmbedding (fun t : W => β t)) (s : ℝ) (hsW : s ∈ W)
    (U : Set S) (hU : IsOpen U) (hsU : β s ∈ U)
    (hUB : U ⊆ S.boundaryᶜ)
    (hcut : F.seam.carrier ∩ U ⊆ range (fun t : W => β t))
    (hs : β s ∈ F.seam.carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (p : F.domain i) (hpc : p ∈ ((F.domain i).chart j).map.source)
    (hp : F.parametrization i p = β s) :
    ∃ Q : Set ℝ, IsOpen Q ∧ Q ⊆ W ∧ s ∈ Q ∧ ∃ q : ℝ → Euc 2,
      MapsTo q Q (((F.domain i).chart j).map.target ∩
        frontier ((F.domain i).chart j).map.target) ∧
      ∀ t ∈ Q, F.parametrization i (((F.domain i).chart j).map.symm (q t)) = β t := by
  classical
  obtain ⟨Q, hQ, hQW, hsQ, hlift⟩ :=
    native_incident_boundary_contains_clock E F W (fun t => β t) he ⟨s, hsW⟩
      U hU hsU hUB hcut hs i j p hpc hp
  have hex (t : Q) : ∃ y : Euc 2,
      y ∈ ((F.domain i).chart j).map.target ∩
        frontier ((F.domain i).chart j).map.target ∧
      F.parametrization i (((F.domain i).chart j).map.symm y) = β t :=
    hlift ⟨t.val, hQW t.property⟩ t.property
  choose q hqb hqi using hex
  let q' : ℝ → Euc 2 := fun t => if h : t ∈ Q then q ⟨t, h⟩ else 0
  refine ⟨Q, hQ, hQW, hsQ, q', ?_, ?_⟩
  · intro t ht
    simpa only [q', dif_pos ht] using hqb ⟨t, ht⟩
  · intro t ht
    simpa only [q', dif_pos ht] using hqi ⟨t, ht⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
