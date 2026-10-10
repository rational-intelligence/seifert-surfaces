import A5NativeBoundaryChartTangents
import A5FiniteTangentLimits

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u

/-- A native closed sector has no isolated image point, including its corner. -/
theorem native_piece_image_point_accumulates
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (x : S) (hx : x ∈ range (F.parametrization i)) :
    x ∈ closure (range (F.parametrization i) \ {x}) := by
  obtain ⟨a,ha⟩ := hx
  have hcover : a ∈ ⋃ j, ((F.domain i).chart j).map.source := by
    rw [(F.domain i).covers]; trivial
  obtain ⟨j,hj⟩ := mem_iUnion.mp hcover
  let b := ((F.domain i).chart j).map
  let y := b a
  have hy : y ∈ b.target := b.map_source hj
  have huniq : UniqueDiffOn ℝ b.target := by
    rw [((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain
  have hyacc : y ∈ closure (b.target \ {y}) :=
    mem_closure_iff_nhds.mpr (clusterPt_principal_iff.mp
      (accPt_principal_iff_clusterPt.mp (huniq y hy).accPt))
  let p := F.parametrization i ∘ b.symm
  have hpc : ContinuousWithinAt p b.target y :=
    (F.parametrization i).continuous.continuousAt.comp_continuousWithinAt (b.symm.continuousOn y hy)
  have hpacc := (hpc.mono sdiff_subset).mem_closure_image hyacc
  have hpx : p y = x := by change F.parametrization i (b.symm (b a)) = x; rw [b.left_inv hj,ha]
  rw [hpx] at hpacc
  apply closure_mono _ hpacc
  rintro z ⟨v,hv,rfl⟩
  refine ⟨⟨b.symm v,rfl⟩,?_⟩
  intro he
  have hpv : b.symm v = a := (F.parametrization_embedding i).injective (he.trans ha.symm)
  apply hv.2
  change v = y
  rw [← b.right_inv hv.1,hpv]

/-- Actual local inverse coordinates on a whole native piece are recovered
from its topological embedding and a chosen actual chart. -/
theorem native_piece_source_coordinate_lift
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (a : F.domain i)
    (ha : a ∈ ((F.domain i).chart j).map.source) :
    ∃ U : Set S, IsOpen U ∧ F.parametrization i a ∈ U ∧
      ∃ q : S → Euc 2,
        q (F.parametrization i a) = ((F.domain i).chart j).map a ∧
        ContinuousOn q (range (F.parametrization i) ∩ U) ∧
        MapsTo q (range (F.parametrization i) ∩ U) ((F.domain i).chart j).map.target ∧
        ∀ x ∈ range (F.parametrization i) ∩ U,
          F.parametrization i (((F.domain i).chart j).map.symm (q x)) = x := by
  classical
  let b := ((F.domain i).chart j).map
  obtain ⟨U,hU,haU,_,hpre,_⟩ := A3GraphLower.embedding_ambient_open_source_isolation
    (F.parametrization i) (F.parametrization_embedding i) a b.source
    ((F.domain i).chart j).source_open ha univ isOpen_univ (mem_univ _)
  let A := range (F.parametrization i) ∩ U
  have hex (x : S) (hx : x ∈ A) : ∃ y ∈ b.target, F.parametrization i (b.symm y) = x := by
    obtain ⟨v,hv⟩ := hx.1
    have hvU : F.parametrization i v ∈ U := hv.symm ▸ hx.2
    have hvb : v ∈ b.source := hpre hvU
    refine ⟨b v,b.map_source hvb,?_⟩
    rw [b.left_inv hvb,hv]
  let q (x : S) := if hx : x ∈ A then (hex x hx).choose else 0
  have hq (x : S) (hx : x ∈ A) : q x ∈ b.target ∧ F.parametrization i (b.symm (q x)) = x := by
    simpa only [q,dite_eq_left hx] using (hex x hx).choose_spec
  have hqc : ContinuousOn q A := continuous_coordinate_lift_of_embedded_image b
    (F.parametrization i) (F.parametrization_embedding i) A id q continuousOn_id
      (fun x hx => (hq x hx).1) (fun x hx => (hq x hx).2)
  refine ⟨U,hU,haU,q,?_,hqc,(fun x hx => (hq x hx).1),fun x hx => (hq x hx).2⟩
  have haA : F.parametrization i a ∈ A := ⟨mem_range_self a,haU⟩
  have hh : b.symm (q (F.parametrization i a)) = a :=
    (F.parametrization_embedding i).injective (hq _ haA).2
  rw [← b.right_inv (hq _ haA).1,hh]

/-- The actual native ambient derivative, pulled back by the recovered
source coordinates, is continuous on its incident piece at the chosen point. -/
theorem native_incident_differential_field
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count) (a : F.domain i)
    (ha : a ∈ ((F.domain i).chart j).map.source)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map (F.parametrization i a)) ∈ c.chart.source) :
    ∃ U : Set S, IsOpen U ∧ F.parametrization i a ∈ U ∧
      ∃ q : S → Euc 2,
        q (F.parametrization i a) = ((F.domain i).chart j).map a ∧
        MapsTo q (range (F.parametrization i) ∩ U) ((F.domain i).chart j).map.target ∧
        (∀ x ∈ range (F.parametrization i) ∩ U,
          F.parametrization i (((F.domain i).chart j).map.symm (q x)) = x) ∧
        ContinuousWithinAt (fun x => fderivWithin ℝ
          (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
          ((F.domain i).chart j).map.target (q x))
          (range (F.parametrization i) ∩ U) (F.parametrization i a) := by
  obtain ⟨U,hU,haU,q,hqa,hqc,hqm,hqe⟩ := native_piece_source_coordinate_lift F i j a ha
  refine ⟨U,hU,haU,q,hqa,hqm,hqe,?_⟩
  let b := ((F.domain i).chart j).map
  let y := b a
  have hy : y ∈ b.target := b.map_source ha
  have hcc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source := by
    change E.toSphere (F.map (F.parametrization i (b.symm (b a)))) ∈ c.chart.source
    rw [b.left_inv ha]
    exact hc
  have hreg := (native_piece_chart_C1_rank_at E F i j y hy c hcc).1
  have hu : UniqueDiffOn ℝ b.target := by
    rw [((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain
  have hDc := hreg.continuousWithinAt_fderivWithin hu (by norm_num) hy
  have hqA := hqc _ ⟨mem_range_self a,haU⟩
  have hDc' : ContinuousWithinAt (fun z => fderivWithin ℝ
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      b.target z) b.target (q (F.parametrization i a)) := by
    rw [hqa]
    exact hDc
  exact hDc'.comp (f := q) hqA hqm

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
