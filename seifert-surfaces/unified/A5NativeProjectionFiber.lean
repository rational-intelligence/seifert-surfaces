import A5ManifoldSectorGraph
import A5CommonProjection
import A5NativeLocalCover
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u

/-- Ambient coordinates preserve the whole native C1/rank data at every
point of a sector chart, not only at the polar origin. -/
theorem native_piece_chart_C1_rank_at
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (y : Euc 2) (hy : y ∈ ((F.domain i).chart j).map.target)
    (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i) j y) ∈ c.chart.source) :
    let g := c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j
    ContDiffWithinAt ℝ 1 g ((F.domain i).chart j).map.target y ∧
      Function.Injective (fderivWithin ℝ g ((F.domain i).chart j).map.target y) := by
  dsimp only
  obtain ⟨hC, hR⟩ := native_piece_sphere_C1_rank E F i j
  have hca := (c.smooth _ hc).contMDiffAt (c.chart.open_source.mem_nhds hc)
  have hcompC := (hca.of_le (by simp)).comp_contMDiffWithinAt y (hC y hy)
  refine ⟨hcompC.contDiffWithinAt, ?_⟩
  have huniq : UniqueDiffOn ℝ ((F.domain i).chart j).map.target := by
    rw [((F.domain i).chart j).target_eq]
    exact ((F.domain i).chart j).model.uniqueDiffOn_domain
  have hcDiff : c.chart.MDifferentiable (𝓡 3) 𝓘(ℝ, Euc 3) :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hd := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, Euc 2))
    (I' := 𝓡 3) (I'' := 𝓘(ℝ, Euc 3)) y (hca.mdifferentiableAt (by simp))
    ((hC y hy).mdifferentiableWithinAt (by norm_num)) (huniq y hy).uniqueMDiffWithinAt
  have hi : Function.Injective (mfderivWithin 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 3)
      (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
      ((F.domain i).chart j).map.target y) := by
    rw [hd]
    exact (hcDiff.mfderiv_injective hc).comp (hR y hy)
  rw [mfderivWithin_eq_fderivWithin] at hi
  intro v w hvw
  have he := hi
    (a₁ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm v)
    (a₂ := (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm w) (by simpa using hvw)
  exact (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.injective he

/-- Within differentiability with invertible derivative already isolates the
center fiber. A centered chart or convexity of the domain is unnecessary. -/
theorem invertible_within_derivative_isolates_fiber
    (f : Euc 2 → Euc 2) (A : Set (Euc 2)) (x : Euc 2)
    (D : Euc 2 →L[ℝ] Euc 2) (hD : Function.Bijective D)
    (hf : HasFDerivWithinAt f D A x) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r ∩ A, f y = f x → y = x := by
  let L := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hD.1)
    (LinearMap.range_eq_top.mpr hD.2)
  have hne : ∀ᶠ y in 𝓝[A \ {x}] x, f y ≠ f x :=
    hf.eventually_ne ⟨‖L.symm.toContinuousLinearMap‖₊, L.antilipschitz⟩
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hne
  refine ⟨r, hr, ?_⟩
  intro y hy he
  by_contra hn
  exact hsub ⟨hy.1, hy.2, hn⟩ he

/-- The actual finite collection of whole native pieces supplies a projection
and height, an open source neighborhood, and a unique center fiber. This
construction uses the literal chart point of each piece, including nonzero
points on radial edges and reflex sectors. -/
theorem native_projection_isolated_fiber
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (c : SmoothAmbientChart ThreeSphere)
    (hc : E.toSphere (F.map x) ∈ c.chart.source) :
    ∃ P : Euc 3 →L[ℝ] Euc 2, ∃ height : Euc 3 →L[ℝ] ℝ,
      Function.Injective (fun z => (P z, height z)) ∧
      ∃ U : Set S, IsOpen U ∧ x ∈ U ∧
        MapsTo (E.toSphere ∘ F.map) U c.chart.source ∧
        ContinuousOn (P ∘ c.chart ∘ E.toSphere ∘ F.map) U ∧
        ContinuousOn (height ∘ c.chart ∘ E.toSphere ∘ F.map) U ∧
        InjOn (fun z => (P (c.chart (E.toSphere (F.map z))),
          height (c.chart (E.toSphere (F.map z))))) U ∧
        (∀ i z, z ∈ range (F.parametrization i) ∩ U →
          ∃ j : Fin (F.domain i).count, ∃ y ∈ ((F.domain i).chart j).map.target,
            sectorCoordinateMap (F.map ∘ F.parametrization i) j y = F.map z ∧
            Function.Bijective (P.comp (fderivWithin ℝ
              (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
              ((F.domain i).chart j).map.target y))) ∧
        ∀ z ∈ U, P (c.chart (E.toSphere (F.map z))) =
          P (c.chart (E.toSphere (F.map x))) → z = x := by
  classical
  let I := {i : Fin F.pieceCount // x ∈ range (F.parametrization i)}
  choose q hq using fun i : I => i.property
  have hjex (i : I) : ∃ j, q i ∈ ((F.domain i.val).chart j).map.source := by
    have hz : q i ∈ ⋃ j, ((F.domain i.val).chart j).map.source := by
      rw [(F.domain i.val).covers]
      trivial
    exact mem_iUnion.mp hz
  choose j hj using hjex
  let y (i : I) := ((F.domain i.val).chart (j i)).map (q i)
  let g (i : I) := c.chart ∘ E.toSphere ∘
    sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i)
  let A (i : I) := ((F.domain i.val).chart (j i)).map.target
  have hy (i : I) : y i ∈ A i := ((F.domain i.val).chart (j i)).map.map_source (hj i)
  have hyF (i : I) :
      sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i) (y i) = F.map x := by
    dsimp [sectorCoordinateMap, y]
    rw [((F.domain i.val).chart (j i)).map.left_inv (hj i), hq i]
  have hg (i : I) : ContDiffWithinAt ℝ 1 (g i) (A i) (y i) ∧
      Function.Injective (fderivWithin ℝ (g i) (A i) (y i)) :=
    native_piece_chart_C1_rank_at E F i.val (j i) (y i) (hy i) c (by rw [hyF]; exact hc)
  let D (i : I) := fderivWithin ℝ (g i) (A i) (y i)
  obtain ⟨P, height, hsep, hPD⟩ := finite_rank_two_common_projection_with_height D (fun i => (hg i).2)
  have hsmall (i : I) : ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.ball (y i) r ∩ A i, (P ∘ g i) z = (P ∘ g i) (y i) → z = y i) ∧
      ∀ z ∈ Metric.ball (y i) r ∩ A i,
        Function.Bijective (P.comp (fderivWithin ℝ (g i) (A i) z)) := by
    obtain ⟨r₀, hr₀, hfiber⟩ := invertible_within_derivative_isolates_fiber (P ∘ g i) (A i) (y i)
      (P.comp (D i)) (hPD i)
      (P.hasFDerivAt.comp_hasFDerivWithinAt (y i)
        ((hg i).1.differentiableWithinAt (by norm_num)).hasFDerivWithinAt)
    have hA : UniqueDiffOn ℝ (A i) := by
      dsimp [A]
      rw [((F.domain i.val).chart (j i)).target_eq]
      exact ((F.domain i.val).chart (j i)).model.uniqueDiffOn_domain
    have hdc := (hg i).1.continuousWithinAt_fderivWithin hA (by norm_num) (hy i)
    have hpc := continuousWithinAt_const.clm_comp (g := fun _ => P) hdc
    have hu : ∀ᶠ z in 𝓝[A i] (y i),
        IsUnit (P.comp (fderivWithin ℝ (g i) (A i) z)) :=
      hpc.tendsto.eventually (Units.isOpen.mem_nhds
        (ContinuousLinearMap.isUnit_iff_bijective.mpr (hPD i)))
    obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhdsWithin_iff.mp hu
    refine ⟨min r₀ δ, lt_min hr₀ hδ, ?_, ?_⟩
    · intro z hz
      exact hfiber z ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
    · intro z hz
      exact ContinuousLinearMap.isUnit_iff_bijective.mp
        (hδu ⟨Metric.ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩)
  choose r hr hri using hsmall
  have hVi (i : I) : ∃ V : Set S, IsOpen V ∧ x ∈ V ∧
      (∀ z ∈ range (F.parametrization i.val) ∩ V,
        P (c.chart (E.toSphere (F.map z))) = P (c.chart (E.toSphere (F.map x))) → z = x) ∧
      ∀ z ∈ range (F.parametrization i.val) ∩ V,
        ∃ y ∈ A i, sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i) y = F.map z ∧
          Function.Bijective (P.comp (fderivWithin ℝ (g i) (A i) y)) := by
    let B := ((F.domain i.val).chart (j i)).map.source ∩
      ((F.domain i.val).chart (j i)).map ⁻¹' Metric.ball (y i) (r i)
    have hB : IsOpen B := ((F.domain i.val).chart (j i)).map.continuousOn.isOpen_inter_preimage
      ((F.domain i.val).chart (j i)).source_open Metric.isOpen_ball
    have hqB : q i ∈ B := ⟨hj i, Metric.mem_ball_self (hr i)⟩
    obtain ⟨V, hV, hxV, _, hpre, _⟩ := A3GraphLower.embedding_ambient_open_source_isolation
      (F.parametrization i.val) (F.parametrization_embedding i.val) (q i)
      B hB hqB univ isOpen_univ (mem_univ _)
    refine ⟨V, hV, hq i ▸ hxV, ?_, ?_⟩
    · rintro z ⟨⟨a, rfl⟩, haV⟩ he
      have haB := hpre haV
      have haA := ((F.domain i.val).chart (j i)).map.map_source haB.1
      have hproj : (P ∘ g i) (((F.domain i.val).chart (j i)).map a) = (P ∘ g i) (y i) := by
        dsimp [g, sectorCoordinateMap]
        rw [((F.domain i.val).chart (j i)).map.left_inv haB.1]
        change P (c.chart (E.toSphere (F.map (F.parametrization i.val a)))) =
          P (c.chart (E.toSphere (sectorCoordinateMap (F.map ∘ F.parametrization i.val) (j i) (y i))))
        rw [hyF]
        exact he
      have hay := (hri i).1 _ ⟨haB.2, haA⟩ hproj
      have haq : a = q i := ((F.domain i.val).chart (j i)).map.injOn haB.1 (hj i) hay
      rw [haq, hq]
    · rintro z ⟨⟨a, rfl⟩, haV⟩
      have haB := hpre haV
      have haA := ((F.domain i.val).chart (j i)).map.map_source haB.1
      refine ⟨((F.domain i.val).chart (j i)).map a, haA, ?_,
        (hri i).2 _ ⟨haB.2, haA⟩⟩
      dsimp [sectorCoordinateMap]
      rw [((F.domain i.val).chart (j i)).map.left_inv haB.1]
  choose V hV hxV hVfiber using hVi
  obtain ⟨U₀, hU₀, hxU₀, havoid, _, _⟩ := native_incident_sector_chart_neighborhood F x
  have hsphere : Continuous (E.toSphere ∘ F.map) := continuous_subtype_val.comp F.map.continuous
  let U := U₀ ∩ (E.toSphere ∘ F.map) ⁻¹' c.chart.source ∩ ⋂ i, V i
  have hU : IsOpen U := (hU₀.inter (c.chart.open_source.preimage hsphere)).inter
    (isOpen_iInter_of_finite hV)
  have hxU : x ∈ U := ⟨⟨hxU₀, hc⟩, mem_iInter.mpr hxV⟩
  have hmap : MapsTo (E.toSphere ∘ F.map) U c.chart.source := fun _ hz => hz.1.2
  have hcoords : ContinuousOn (c.chart ∘ E.toSphere ∘ F.map) U :=
    c.chart.continuousOn.comp hsphere.continuousOn hmap
  refine ⟨P, height, hsep, U, hU, hxU, hmap,
    P.continuous.comp_continuousOn hcoords, height.continuous.comp_continuousOn hcoords, ?_, ?_, ?_⟩
  · intro a ha b hb he
    apply F.embedding.injective
    apply Subtype.val_injective
    exact c.chart.injOn (hmap ha) (hmap hb) (hsep he)
  · intro i z hz
    have hix : x ∈ range (F.parametrization i) := by
      by_contra hn
      have hem : z ∈ (∅ : Set S) := havoid i hn ▸ ⟨hz.1, hz.2.1.1⟩
      exact hem
    obtain ⟨y', hy', he', hr'⟩ := (hVfiber ⟨i, hix⟩).2 z
      ⟨hz.1, mem_iInter.mp hz.2.2 ⟨i, hix⟩⟩
    exact ⟨j ⟨i, hix⟩, y', hy', he', hr'⟩
  · intro z hz he
    have hcover : z ∈ ⋃ i, range (F.parametrization i) := by rw [F.covers]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
    have hix : x ∈ range (F.parametrization i) := by
      by_contra hn
      have hem : z ∈ (∅ : Set S) := havoid i hn ▸ ⟨hi, hz.1.1⟩
      exact hem
    exact (hVfiber ⟨i, hix⟩).1 z ⟨hi, mem_iInter.mp hz.2 ⟨i, hix⟩⟩ he

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
