import NativeClockC1Probe
import ArcClockTopologyProbe
import CircleClockProbe

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- A native compact seam component and an open embedded local parameter
range isolate the exact original clock image in the source surface. -/
theorem native_compact_clock_source_window
    {S : CompactOrientedSurface.{u}}
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (f : C(P, S)) (hf : IsEmbedding f)
    (W : Set ℝ) (parameter : W → P) (hpr : IsOpen (range parameter))
    (β : ℝ → S) (hβ : ∀ t : W, β t = f (parameter t))
    (s : W) (C : Set S)
    (U : Set S) (hU : IsOpen U) (hsU : β s ∈ U)
    (hUB : U ⊆ S.boundaryᶜ) (hcut : C ∩ U ⊆ range f) :
    ∃ V : Set S, IsOpen V ∧ β s ∈ V ∧ V ⊆ U ∧
      V ⊆ S.boundaryᶜ ∧ C ∩ V ⊆ range (fun t : W => β t) := by
  obtain ⟨V, hV, hpV, hpre⟩ := native_compact_parameter_window f hf
    (parameter s) (range parameter) hpr ⟨s, rfl⟩
  refine ⟨U ∩ V, hU.inter hV, ⟨hsU, by rw [hβ s]; exact hpV⟩,
    inter_subset_left, fun _ hv => hUB hv.1, ?_⟩
  rintro x ⟨hxC, hxU, hxV⟩
  obtain ⟨p, hp⟩ := hcut ⟨hxC, hxU⟩
  have hpV' : p ∈ f ⁻¹' V := by change f p ∈ V; rw [hp]; exact hxV
  obtain ⟨t, ht⟩ := hpre hpV'
  refine ⟨t, ?_⟩
  change β t = x
  rw [hβ t, ht, hp]

/-- A common open interval in the SAME exact source clock has native
boundary lifts in selected charts of every incident whole piece. The
selection and all lifts come from the literal finite native cover. -/
theorem native_finite_incident_boundary_clock_lifts
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (W : Set ℝ) (β : ℝ → S) (he : IsEmbedding (fun t : W => β t))
    (s : ℝ) (hsW : s ∈ W)
    (U : Set S) (hU : IsOpen U) (hsU : β s ∈ U)
    (hUB : U ⊆ S.boundaryᶜ)
    (hcut : F.seam.carrier ∩ U ⊆ range (fun t : W => β t))
    (hs : β s ∈ F.seam.carrier) :
    ∃ Q : Set ℝ, IsOpen Q ∧ Q ⊆ W ∧ s ∈ Q ∧
      ∀ i : Fin F.pieceCount, β s ∈ range (F.parametrization i) →
        ∃ j : Fin (F.domain i).count, ∃ q : ℝ → Euc 2,
          MapsTo q Q (((F.domain i).chart j).map.target ∩
            frontier ((F.domain i).chart j).map.target) ∧
          ∀ t ∈ Q, F.parametrization i (((F.domain i).chart j).map.symm (q t)) = β t := by
  classical
  let I := {i : Fin F.pieceCount // β s ∈ range (F.parametrization i)}
  have hchoice (i : I) : ∃ Q : Set ℝ, IsOpen Q ∧ Q ⊆ W ∧ s ∈ Q ∧
      ∃ j : Fin (F.domain i.val).count, ∃ q : ℝ → Euc 2,
        MapsTo q Q (((F.domain i.val).chart j).map.target ∩
          frontier ((F.domain i.val).chart j).map.target) ∧
        ∀ t ∈ Q, F.parametrization i.val (((F.domain i.val).chart j).map.symm (q t)) = β t := by
    obtain ⟨p, hp⟩ := i.property
    have hcover : p ∈ ⋃ j, ((F.domain i.val).chart j).map.source := by
      rw [(F.domain i.val).covers]
      trivial
    obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
    obtain ⟨Q, hQ, hQW, hsQ, q, hqm, hqi⟩ :=
      native_incident_boundary_coordinate_lift E F W β he s hsW U hU hsU hUB hcut hs
        i.val j p hj hp
    exact ⟨Q, hQ, hQW, hsQ, j, q, hqm, hqi⟩
  choose Q hQ hQW hsQ j q hqm hqi using hchoice
  let V := W ∩ ⋂ i : I, Q i
  have hI : Nonempty I := by
    obtain ⟨i, hi⟩ := native_piece_incidence_nonempty E F (β s)
    exact ⟨⟨i, hi⟩⟩
  obtain ⟨i₀⟩ := hI
  have hVW : V ⊆ Q i₀ := fun _ hv => mem_iInter.mp hv.2 i₀
  have hVeq : V = ⋂ i : I, Q i := by
    apply inter_eq_right.mpr
    exact (iInter_subset Q i₀).trans (hQW i₀)
  refine ⟨V, by rw [hVeq]; exact isOpen_iInter_of_finite hQ,
    inter_subset_left, ⟨hsW, mem_iInter.mpr hsQ⟩, ?_⟩
  intro i hi
  let k : I := ⟨i, hi⟩
  have hVk : V ⊆ Q k := fun _ hv => mem_iInter.mp hv.2 k
  exact ⟨j k, q k, fun _ ht => hqm k (hVk ht), fun t ht => hqi k t (hVk ht)⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
