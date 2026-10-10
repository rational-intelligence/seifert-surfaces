import IncidenceProbe
import DifferentialGeometry.Topology.InvarianceOfDomainManifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem native_surface_interior_plane_chart (S : CompactOrientedSurface.{u})
    (x : S) (hx : x ∉ S.boundary) :
    ∃ e : OpenPartialHomeomorph S (Euc 2), x ∈ e.source := by
  have hxi : x ∈ (𝓡∂ 2).interior S := by
    rw [← ModelWithCorners.compl_boundary (I := 𝓡∂ 2) (M := S)]
    exact hx
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
  exact ⟨e, mem_extChartAt_source x, (ModelWithCorners.isInteriorPoint_iff).mp hxi⟩

theorem open_range_of_embedded_plane_chart_neighborhood
    {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X (Euc 2))
    (U : Set X) (hU : IsOpen U) (hUe : U ⊆ e.source)
    (f : U → Euc 2) (hf : IsEmbedding f) : IsOpen (range f) := by
  let V := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  let g : V → Euc 2 := fun z => f ⟨e.symm z, z.property.2⟩
  have hg : Continuous g := hf.continuous.comp
    ((e.continuousOn_symm.comp_continuous continuous_subtype_val
      (fun z => z.property.1)).subtype_mk _)
  have hi : Function.Injective g := by
    intro z w hzw
    have h := congrArg Subtype.val (hf.injective hzw)
    exact Subtype.ext (e.symm.injOn z.property.1 w.property.1 h)
  have ho := DifferentialGeometry.Topology.isOpen_range_of_isOpen_of_continuous_injective_real
    𝓘(ℝ, Euc 2) hV g hg hi
  have hr : range g = range f := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨e.symm z, z.property.2⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      have hze : z.val ∈ e.source := hUe z.property
      refine ⟨⟨e z, e.map_source hze, ?_⟩, ?_⟩
      · change e.symm (e z) ∈ U
        rw [e.left_inv hze]
        exact z.property
      · change f ⟨e.symm (e z), _⟩ = f z
        congr 1
        exact Subtype.ext (e.left_inv hze)
  rwa [hr] at ho

/-- An ordinary native seam point has at least two distinct incident whole
pieces. A unique incident piece would embed an open source plane
neighbourhood into its own sector frontier, contradicting invariance of domain. -/
theorem native_seam_at_least_two_incident_pieces
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (hx : x ∈ F.seam.carrier) (hxb : x ∉ S.boundary) :
    ∃ i j : Fin F.pieceCount, i ≠ j ∧ x ∈ range (F.parametrization i) ∧
      x ∈ range (F.parametrization j) := by
  classical
  obtain ⟨i, hi⟩ := native_piece_incidence_nonempty E F x
  by_contra hnot
  have hsingle (j : Fin F.pieceCount) (hj : x ∈ range (F.parametrization j)) : j = i := by
    by_contra hji
    exact hnot ⟨i, j, Ne.symm hji, hi, hj⟩
  obtain ⟨U, hU, hxU, havoid, hcharts, hcover⟩ := native_incident_sector_chart_neighborhood F x
  obtain ⟨j, hxchart, hlocal⟩ := hcharts i hi
  obtain ⟨e, hxe⟩ := native_surface_interior_plane_chart S x hxb
  let V := U ∩ e.source
  have hV : IsOpen V := hU.inter e.open_source
  have hxV : x ∈ V := ⟨hxU, hxe⟩
  have hVR : V ⊆ range (F.parametrization i) := by
    intro z hz
    have hzC : z ∈ ⋃ k, range (F.parametrization k) ∩ U := by rw [hcover]; exact hz.1
    obtain ⟨k, hk, hkU⟩ := mem_iUnion.mp hzC
    by_cases hxk : x ∈ range (F.parametrization k)
    · rwa [hsingle k hxk] at hk
    · have hempty := havoid k hxk
      have hzempty : z ∈ (∅ : Set S) := hempty ▸ ⟨hk, hkU⟩
      exact hzempty.elim
  let B := (F.parametrization_embedding i).toHomeomorph
  let p : V → F.domain i := fun z => B.symm ⟨z, hVR z.property⟩
  have hpemb : IsEmbedding p := B.symm.isEmbedding.comp
    ((IsEmbedding.subtypeVal (p := fun z : S => z ∈ V)).codRestrict
      (range (F.parametrization i)) (fun z => hVR z.property))
  have hpi (z : V) : F.parametrization i (p z) = z := by
    exact congrArg Subtype.val (B.apply_symm_apply ⟨z, hVR z.property⟩)
  have hpc (z : V) : p z ∈ ((F.domain i).chart j).map.source := by
    have hzlocal : z.val ∈ range (F.parametrization i) ∩ U := ⟨hVR z.property, z.property.1⟩
    rw [hlocal] at hzlocal
    obtain ⟨q, ⟨hq, _⟩, hqz⟩ := hzlocal
    have hqp : q = p z := (F.parametrization_embedding i).injective (hqz.trans (hpi z).symm)
    rwa [hqp] at hq
  let f : V → Euc 2 := fun z => ((F.domain i).chart j).map (p z)
  have hfemb : IsEmbedding f := ((F.domain i).chart j).map.isEmbedding_restrict.comp
    (hpemb.codRestrict ((F.domain i).chart j).map.source hpc)
  have hfopen := open_range_of_embedded_plane_chart_neighborhood e V hV inter_subset_right f hfemb
  have hpoint : f ⟨x, hxV⟩ ∈ range f := ⟨⟨x, hxV⟩, rfl⟩
  have htarget : range f ⊆ ((F.domain i).chart j).map.target := by
    rintro y ⟨z, rfl⟩
    exact ((F.domain i).chart j).map.map_source (hpc z)
  have hyfront := native_seam_chart_coordinate_boundary E F i j (p ⟨x, hxV⟩)
    (by rw [hpi]; exact hx) (hpc ⟨x, hxV⟩)
  exact hyfront.2.2 (mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hfopen.mem_nhds hpoint) htarget))

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
