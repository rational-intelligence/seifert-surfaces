import B1ActualCommonInteriorGraph_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- A genuine zero graph germ in common actual slice charts is a germ of
equality of the two full embedded surface images. -/
theorem native_interior_zero_graph_surface_germ_v475
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (r : E.Carrier) (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hrΦ : E.toSphere r ∈ Φ.source) (hrΨ : E.toSphere r ∈ Ψ.source)
    (hA : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (hB : Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
      Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (p : E2) (e : OpenPartialHomeomorph E2 E2) (u : E2 → ℝ)
    (hp : p ∈ e.source) (hrpair : Ψ (E.toSphere r)=(p,0))
    (heO : e.source ⊆ {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩
      interior (range (𝓡∂ 2)))
    (hgraph : ∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z))
    (hgraphS : ∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z)))
    (hebase : e p ∈ interior (range (𝓡∂ 2)))
    (hzero : native_planar_zero_germ_v475 e.target u (e p)) :
    native_surface_germ_eq_v475 f.image g.image r := by
  classical
  obtain ⟨V,hV,hpV,hVe,hVz⟩ := hzero
  let Z := V ∩ interior (range (𝓡∂ 2))
  have hZ : IsOpen Z := hV.inter isOpen_interior
  have hpZ : e p ∈ Z := ⟨hpV,hebase⟩
  let OΦ := Φ.source ∩ Φ ⁻¹' (Prod.fst ⁻¹' Z)
  let OΨ := Ψ.source ∩ Ψ ⁻¹' (Prod.fst ⁻¹' e.source)
  let Q := OΦ ∩ OΨ
  have hOΦ : IsOpen OΦ := Φ.isOpen_inter_preimage (hZ.preimage continuous_fst)
  have hOΨ : IsOpen OΨ := Ψ.isOpen_inter_preimage (e.open_source.preimage continuous_fst)
  have hQ : IsOpen Q := hOΦ.inter hOΨ
  have hrΦpair : Φ (E.toSphere r)=(e p,0) := by
    have hh := hgraphS p hp
    rw [← hrpair,Ψ.left_inv hrΨ,hVz hpV] at hh
    exact hh
  have hrQ : E.toSphere r ∈ Q := by
    refine ⟨⟨hrΦ,?_⟩,⟨hrΨ,?_⟩⟩
    · change (Φ (E.toSphere r)).1 ∈ Z
      rwa [hrΦpair]
    · change (Ψ (E.toSphere r)).1 ∈ e.source
      rwa [hrpair]
  have hslice (H : Set ThreeSphere) (C : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
      (hex : C '' (C.source ∩ H)=C.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
      (a : ThreeSphere) (ha : a ∈ C.source) :
      a ∈ H ↔ C a ∈ range (𝓡∂ 2) ×ˢ ({0}:Set ℝ) := by
    constructor
    · intro hh
      have hk := mem_image_of_mem C (show a ∈ C.source ∩ H from ⟨ha,hh⟩)
      rw [hex] at hk
      exact hk.2
    · intro hh
      have hk : C a ∈ C '' (C.source ∩ H) := by
        rw [hex]
        exact ⟨C.map_source ha,hh⟩
      obtain ⟨b,⟨hb,hbH⟩,he⟩ := hk
      rwa [C.injOn hb ha he] at hbH
  have hsame : range (E.toSphere ∘ f.toFun) ∩ Q = range (E.toSphere ∘ g.toFun) ∩ Q := by
    ext a
    constructor
    · rintro ⟨ha,hQa⟩
      have hcoords := (hslice _ Φ hA a hQa.1.1).mp ha
      let z := (Φ a).1
      have hzZ : z ∈ Z := hQa.1.2
      have hzT : z ∈ e.target := hVe hzZ.1
      have hparam := hgraph z hzT
      have huZ : u z = 0 := hVz hzZ.1
      have hzsource := heO (e.map_target hzT)
      have hpairA : Φ a=(z,0) := Prod.ext rfl hcoords.2
      rw [huZ,← hpairA] at hparam
      have heq : Ψ.symm (e.symm z,0)=a := Φ.injOn hzsource.1.2 hQa.1.1 hparam
      refine ⟨(hslice _ Ψ hB a hQa.2.1).mpr ?_,hQa⟩
      rw [← heq,Ψ.right_inv hzsource.1.1]
      exact ⟨interior_subset hzsource.2,rfl⟩
    · rintro ⟨ha,hQa⟩
      have hcoords := (hslice _ Ψ hB a hQa.2.1).mp ha
      let z := (Ψ a).1
      have hze : z ∈ e.source := hQa.2.2
      have hpairB : Ψ a=(z,0) := Prod.ext rfl hcoords.2
      have hh := hgraphS z hze
      rw [← hpairB,Ψ.left_inv hQa.2.1] at hh
      have hzZ : e z ∈ Z := by
        have hf := congrArg Prod.fst hh
        change (Φ a).1=e z at hf
        rw [← hf]
        exact hQa.1.2
      have huZ := hVz hzZ.1
      refine ⟨(hslice _ Φ hA a hQa.1.1).mpr ?_,hQa⟩
      rw [hh,huZ]
      exact ⟨interior_subset hzZ.2,rfl⟩
  refine ⟨E.toSphere ⁻¹' Q,hQ.preimage continuous_subtype_val,hrQ,?_⟩
  ext a
  constructor <;> rintro ⟨ha,hQa⟩
  · have hk : E.toSphere a ∈ range (E.toSphere ∘ g.toFun) ∩ Q := by
      rw [← hsame]
      obtain ⟨b,hb⟩ := ha
      exact ⟨⟨b,congrArg E.toSphere hb⟩,hQa⟩
    obtain ⟨b,hb⟩ := hk.1
    exact ⟨⟨b,Subtype.ext hb⟩,hQa⟩
  · have hk : E.toSphere a ∈ range (E.toSphere ∘ f.toFun) ∩ Q := by
      rw [hsame]
      obtain ⟨b,hb⟩ := ha
      exact ⟨⟨b,congrArg E.toSphere hb⟩,hQa⟩
    obtain ⟨b,hb⟩ := hk.1
    exact ⟨⟨b,Subtype.ext hb⟩,hQa⟩

#print axioms native_interior_zero_graph_surface_germ_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
