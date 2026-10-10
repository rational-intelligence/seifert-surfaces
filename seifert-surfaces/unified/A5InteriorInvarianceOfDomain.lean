import A5PuncturedPlane
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import Mathlib.Topology.IsLocalHomeomorph

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations

/-- Invariance of domain through one actual plane chart. -/
theorem open_image_of_injective_in_plane_chart
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (Euc 2)) (U : Set X)
    (hU : IsOpen U) (hUe : U ⊆ e.source)
    (f : X → Euc 2) (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsOpen (f '' U) := by
  let V := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hgc : ContinuousOn (f ∘ e.symm) V :=
    hf.comp (e.symm.continuousOn.mono inter_subset_left) (fun _ hz => hz.2)
  have hgi : InjOn (f ∘ e.symm) V := by
    intro z hz w hw he
    exact e.symm.injOn hz.1 hw.1 (hinj hz.2 hw.2 he)
  have ho := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hV hgc hgi
  have he : (f ∘ e.symm) '' V = f '' U := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm z, hz.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e z, ⟨e.map_source (hUe hz), ?_⟩, ?_⟩
      · change e.symm (e z) ∈ U
        rwa [e.left_inv (hUe hz)]
      · change f (e.symm (e z)) = f z
        rw [e.left_inv (hUe hz)]
  rwa [he] at ho

/-- A continuous planar projection locally injective on a source plane chart
is a genuine local homeomorphism. No openness of the projection is assumed. -/
theorem local_homeomorph_of_plane_chart_injective
    {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X (Euc 2)) (x : X) (hxe : x ∈ e.source)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U)
    (f : X → Euc 2) (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsLocalHomeomorphOn f {x} := by
  let W := U ∩ e.source
  have hW : IsOpen W := hU.inter e.open_source
  have hWx : x ∈ W := ⟨hxU, hxe⟩
  have hfW : Continuous (W.domRestrict f) := (hf.mono inter_subset_left).domRestrict
  have hiW : Function.Injective (W.domRestrict f) := by
    intro a b hab
    exact Subtype.ext (hinj a.property.1 b.property.1 hab)
  have hoW : IsOpenMap (W.domRestrict f) := by
    intro V hV
    obtain ⟨O, hO, rfl⟩ := IsInducing.subtypeVal.isOpen_iff.mp hV
    have ho := open_image_of_injective_in_plane_chart e (W ∩ O) (hW.inter hO)
      (fun _ hz => hz.1.2) f (hf.mono (fun _ hz => hz.1.1))
      (hinj.mono (fun _ hz => hz.1.1))
    have he : W.domRestrict f '' (Subtype.val ⁻¹' O) = f '' (W ∩ O) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ⟨z.property, hz⟩, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz.1⟩, hz.2, rfl⟩
    rwa [he]
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  intro y hy
  rcases mem_singleton_iff.mp hy with rfl
  exact ⟨W, hW.mem_nhds hWx,
    isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr ⟨hfW, hiW, hoW⟩⟩

/-- The native compact surface interior supplies the source plane chart.
Thus a locally injective continuous projection gives the topological input
needed by the vertex-removal covering argument. -/
theorem native_interior_local_homeomorph_of_injective
    (S : CompactOrientedSurface) (x : S) (hx : x ∈ (𝓡∂ 2).interior S)
    (U : Set S) (hU : IsOpen U) (hxU : x ∈ U)
    (f : S → Euc 2) (hf : ContinuousOn f U) (hinj : InjOn f U) :
    IsLocalHomeomorphOn f {x} := by
  let c := extChartAt (𝓡∂ 2) x
  let e : OpenPartialHomeomorph S (Euc 2) := {
    toFun := c
    invFun := c.symm
    source := c.source ∩ c ⁻¹' interior c.target
    target := interior c.target
    map_source' := fun _ h => h.2
    map_target' := by
      intro y hy
      refine ⟨c.map_target (interior_subset hy), ?_⟩
      change c (c.symm y) ∈ interior c.target
      rw [c.right_inv (interior_subset hy)]
      exact hy
    left_inv' := fun _ h => c.left_inv h.1
    right_inv' := fun _ h => c.right_inv (interior_subset h)
    open_source := isOpen_extChartAt_preimage' x isOpen_interior
    open_target := isOpen_interior
    continuousOn_toFun := (continuousOn_extChartAt x).mono inter_subset_left
    continuousOn_invFun := (continuousOn_extChartAt_symm x).mono interior_subset }
  exact local_homeomorph_of_plane_chart_injective e x
    ⟨mem_extChartAt_source x, (ModelWithCorners.isInteriorPoint_iff).mp hx⟩ U hU hxU f hf hinj

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
