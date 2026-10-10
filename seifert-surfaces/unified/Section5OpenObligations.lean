import Section5NeatImageAtlasV481
import Section5GeometricDefinitions
import OriginalSection4Whole
import OriginalB2B5V480
import Section5ConfigurationV480
import Section5AreaAssemblyV480
import Section5NativeStrictConvexityV481
import Section5NativeAreaReplayV488
import Section5CommonLeafNativeReplayV489

set_option autoImplicit false
noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators ENNReal

namespace SeifertSurfaces.OriginalEndpoints.Section5.Obligations
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.Section5

/- Finite lower-obligation interface. None is a hypothesis of a six-result
root. Active A6/B1/B2--B5/compression owners retain their proof ownership. -/

theorem pair_sector_controls {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (g : SmoothMetric M)
    {SA SB : CompactOrientedSurface.{0}} (A : NeatEmbedding SA M) (B : NeatEmbedding SB M)
    (C : PairRoundingControl g A B) (k : Fin 4) :
    ∃ D : RoundingBounds (C.sector k),
      D.etaMax = C.etaMax ∧ D.kappa = C.kappa ∧ D.g0 = C.gain := by
  exact ⟨C.sectorBounds k, C.sector_caps k⟩

theorem image_area_chart_independence {M : Type} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (g : SmoothMetric M) (F : Set M) (A B : ImageAreaAtlas F)
    (hA : A.Valid g) (hB : B.Valid g) :
    A.area g = B.area g := by
  exact NativeAreaV487.image_area_chart_independence g A B hA hB

theorem image_area_neat_bridge {M : Type} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] (g : SmoothMetric M)
    {S : CompactOrientedSurface.{0}} (F : NeatEmbedding S M) :
    imageArea g F.image = area g F.toFun := by
  exact WholeAssemblyV480.image_area_neat_bridge_assembly g F
    (fun A B hA hB => image_area_chart_independence g F.image A B hA hB)

theorem positive_admissible_width {M : Type} [TopologicalSpace M]
    [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (g : SmoothMetric M) (F : SourceCornerSurface g) (C : RoundingBounds F) :
    ∃ eta : M → ℝ, WidthAdmissible g F.seams C.etaMax C.kappa eta := by
  classical
  have hcompact : IsCompact F.seams.carrier := by
    apply isCompact_iUnion
    intro i
    exact isCompact_range (F.seams.curve i).regular.isEmbedding.continuous
  obtain ⟨c, hc, hcap⟩ : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ F.seams.carrier, c ≤ C.etaMax p := by
    by_cases hne : F.seams.carrier.Nonempty
    · obtain ⟨p, hp, hmin⟩ := hcompact.exists_isMinOn hne C.continuous.1
      exact ⟨C.etaMax p, (C.positive p hp).1, hmin⟩
    · exact ⟨1, zero_lt_one, fun p hp => False.elim (hne ⟨p, hp⟩)⟩
  refine ⟨fun _ => c, ?_, ?_⟩
  · exact fun p hp => ⟨hc, hcap p hp⟩
  · intro i
    constructor
    · exact contDiff_const
    · intro t
      have hmem : (F.seams.curve i).at t ∈ F.seams.carrier := by
        exact mem_iUnion.mpr ⟨i, ⟨Circle.exp (2 * Real.pi * t), rfl⟩⟩
      have hk := (C.positive _ hmem).2.le
      simp only [Function.comp_def, deriv_const, abs_zero, C2ClosedCurve.speed]
      exact mul_nonneg hk (Real.sqrt_nonneg _)

/- This is the expressly named topological variant, not the original smooth
5.4 claim. Near-boundary neatness is stated here as a repair condition and
appears only in this alternate lower task. -/
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

private theorem tangentPlane_sum_transport
    {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (p q : E.Carrier) (h : p = q)
    (L : U →ₗ[ℝ] TangentSpace (𝓡∂ 3) p)
    (R : V →ₗ[ℝ] TangentSpace (𝓡∂ 3) q) :
    ((h ▸ LinearMap.range L) ⊔ LinearMap.range R = ⊤) ↔
      (LinearMap.range L ⊔ LinearMap.range (h.symm ▸ R) = ⊤) := by
  subst q
  rfl

theorem three_configurations_exhaust (H : Section4.SourceGeometry E)
    (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B) :
    ConfigurationT0 E A B ∨ ConfigurationT1 E A B ∨ ConfigurationT2 E A B := by
  classical
  rcases Section5.WholeAssemblyV480.leaf_boundary_dichotomy E H A B hA.1 hB.1 with hd | heq
  · by_cases ht : Section4.Transverse (spanningAsNeat A.1) (spanningAsNeat B.1)
    · exact Or.inl ⟨hd, ht⟩
    · right; left
      refine ⟨hd, Section5.WholeAssemblyV480.nontansverse_has_interior_tangency E A B hd ?_⟩
      intro hb
      apply ht
      intro a b hab
      exact (tangentPlane_sum_transport E _ _ hab _ _).mp (hb a b hab)
  · exact Or.inr (Or.inr heq)

/- Every certificate ties the final vertices to actual retained outputs of
the native cover frontier and actual finite compression histories. The
frontier geometry and equality-case area estimate are conclusions here. -/
class NativeCoverGeometry (H : Section4.SourceGeometry E)
    {Q : LinkCoordinates K} {S A B : SeifertSurface.{0} E}
    (C : FrontierConfiguration E Q S A B) where
  [charted : ChartedSpace (EuclideanHalfSpace 3) C.cover]
  [manifold : IsManifold (𝓡∂ 3) ∞ C.cover]
  projection_smooth : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞ C.cover.projection
  metric : SmoothMetric C.cover

attribute [instance] NativeCoverGeometry.charted NativeCoverGeometry.manifold

structure RoundoffPushOffWitness (H : Section4.SourceGeometry E)
    {Q : LinkCoordinates K} {S A B : SeifertSurface.{0} E}
    (C : FrontierConfiguration E Q S A B) (upper : Bool)
    (Out : FrontierOutput E C upper) [G : NativeCoverGeometry E H C] where
  projection_rank : ∀ p, Function.Bijective
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) C.cover.projection p)
  boundary_preimage : C.cover.projection ⁻¹' (𝓡∂ 3).boundary E.Carrier =
    (𝓡∂ 3).boundary C.cover
  metric_pullback : ∀ p v w, G.metric.inner p v w = H.metric.inner (C.cover.projection p)
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) C.cover.projection p v)
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) C.cover.projection p w)
  corner : AppendixBOriginalV480.CorneredSurface G.metric
  rawIdentification : Out.total.surface ≃ₜ corner.source
  raw_boundary : rawIdentification '' Out.total.surface.boundary = corner.source.boundary
  raw_exact : ∀ x, corner.surface.map (rawIdentification x) = Out.rawLift x
  projected_raw_area : geometricArea G.metric corner.surface = geometricArea H.metric Out.raw
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  controls : AppendixBOriginalV480.CornerControl G.metric corner cutoff
  localization : AppendixBOriginalV480.CompactCornerLocalization corner controls
  localization_in_domain : closure localization.neighborhood.source ⊆ C.domain
  eta : C.cover → ℝ
  admissible : AppendixBOriginalV480.AdmissibleWidth (Γ := corner.seams)
    G.metric controls.etaMax controls.kappa eta
  rounded : AppendixBOriginalV480.RoundedSurface corner controls eta
  rounding_transport : AppendixBOriginalV480.LocalizedRoundingTransport localization eta rounded
  region : Set C.cover
  region_exact : region = if upper then C.upperRegion else C.lowerRegion
  selected : AppendixBOriginalV480.SelectedCornerRegion corner region
  rounded_collar : AppendixBOriginalV480.OneSidedCollar rounded.embedding region
  rounded_in_domain : rounded.embedding.image ⊆ C.domain
  rounding_in_domain : ∀ t p, p ∈ C.domain → rounded.isotopy.stage t p ∈ C.domain
  seamCount : ℕ
  seamCurve : Fin seamCount → AppendixBOriginalV480.ClosedIntersectionComponent corner.seams
  seam_disjoint : Pairwise (fun i j => Disjoint (range (seamCurve i).parameter)
    (range (seamCurve j).parameter))
  seams_cover : (⋃ i, range (seamCurve i).parameter) = corner.seams
  gain : ℝ
  gain_positive : 0 < gain
  gain_exact : gain = ∑ i, AppendixBOriginalV480.curveIntegral G.metric (seamCurve i)
    (fun p => SeifertSurfaces.AppendixB.angleGain cutoff
      (AppendixBOriginalV480.cornerAngle corner p) * eta p)
  projectedRounded : NeatEmbedding corner.source E.Carrier
  projected_rounded : ∀ x, projectedRounded.toFun x = C.cover.projection (rounded.embedding.toFun x)
  rounded_area_transport : area H.metric projectedRounded.toFun = area G.metric rounded.embedding.toFun
  rounded_leaf : H.foliation.BoundaryIn projectedRounded.toFun
  sigma0 : ℝ
  sigma0_positive : 0 < sigma0
  cost : ℝ
  cost_nonnegative : 0 ≤ cost
  pushed : ℝ → NeatEmbedding corner.source C.cover
  projectedPush : ℝ → NeatEmbedding corner.source E.Carrier
  projection_push : ∀ sigma x, (projectedPush sigma).toFun x =
    C.cover.projection ((pushed sigma).toFun x)
  push_isotopy : ℝ → SmoothAmbientIsotopy C.cover
  push_projected_isotopy : ℝ → SmoothAmbientIsotopy E.Carrier
  push_isotopy_image : ∀ sigma, 0 < sigma → sigma ≤ sigma0 →
    (push_isotopy sigma).stage 1 '' rounded.embedding.image = (pushed sigma).image
  push_isotopy_domain : ∀ sigma, 0 < sigma → sigma ≤ sigma0 →
    ∀ t p, p ∈ C.domain → (push_isotopy sigma).stage t p ∈ C.domain
  push_isotopy_projection : ∀ sigma, 0 < sigma → sigma ≤ sigma0 →
    ∀ t p, p ∈ C.domain →
      C.cover.projection ((push_isotopy sigma).stage t p) =
        (push_projected_isotopy sigma).stage t (C.cover.projection p)
  push_localization : ∀ sigma, 0 < sigma → sigma ≤ sigma0 →
    (pushed sigma).image ⊆ localization.neighborhood.source
  push_clauses : ∀ sigma, 0 < sigma → sigma ≤ sigma0 →
    (pushed sigma).image ⊆ region ∩ C.domain ∧
    H.foliation.BoundaryIn (projectedPush sigma).toFun ∧
    SmoothAmbientIsotopy.Rel rounded.embedding.image (pushed sigma).image ∧
    SmoothAmbientIsotopy.Rel projectedRounded.image (projectedPush sigma).image ∧
    area G.metric (pushed sigma).toFun - area G.metric rounded.embedding.toFun ≤ cost * sigma ∧
    area H.metric (projectedPush sigma).toFun = area G.metric (pushed sigma).toFun
  push_same_class : ∀ sigma sigma', 0 < sigma → sigma ≤ sigma0 →
    0 < sigma' → sigma' ≤ sigma0 →
    SmoothAmbientIsotopy.Rel (projectedPush sigma).image (projectedPush sigma').image
  sigma : ℝ
  sigma_positive : 0 < sigma
  sigma_small : sigma ≤ sigma0
  cost_margin : cost * sigma < gain / 2
  target_exact : ∀ x, (projectedPush sigma).toFun (rawIdentification x) = Out.total.embedding.toFun x

structure ActualExchangeConstruction (H : Section4.SourceGeometry E)
    (x u w up down : Vertices E) where
  coordinates : LinkCoordinates K
  S : IncompressibleSpanningSurface.{0} E
  A0 : IncompressibleSpanningSurface.{0} E
  B0 : IncompressibleSpanningSurface.{0} E
  S_class : SurfaceVertex E S = x
  A0_class : SurfaceVertex E A0 = u
  B0_class : SurfaceVertex E B0 = w
  S_minimum : IsRelativeAreaMinimizer H.metric H.foliation S
  A0_minimum : IsRelativeAreaMinimizer H.metric H.foliation A0
  B0_minimum : IsRelativeAreaMinimizer H.metric H.foliation B0
  central : SeifertSurface.{0} E
  left : SeifertSurface.{0} E
  right : SeifertSurface.{0} E
  central_image : central.image = S.1.image
  left_image : left.image = A0.1.image
  right_isotopy : SmoothAmbientIsotopy.Rel right.image B0.1.image
  input_avoids : Disjoint central.image (left.image ∪ right.image)
  meeting : (left.image ∩ right.image).Nonempty
  transverse : Section4.Transverse (seifertAsNeat left) (seifertAsNeat right)
  boundaries : Disjoint (left.embedding.toFun '' left.surface.boundary)
    (right.embedding.toFun '' right.surface.boundary)
  no_disc : NoDiscPatch (seifertAsNeat left) (seifertAsNeat right)
  frontier : FrontierConfiguration E coordinates central left right
  [coverGeometry : NativeCoverGeometry E H frontier]
  upper : FrontierOutput E frontier true
  lower : FrontierOutput E frontier false
  upper_roundoff : RoundoffPushOffWitness E H frontier true upper
  lower_roundoff : RoundoffPushOffWitness E H frontier false lower
  upperFinal : LinkSpanningSurface.{0} E
  lowerFinal : LinkSpanningSurface.{0} E
  upper_history : KnotCompressionHistory E upper.retained.toLinkSpanningSurface upperFinal
  lower_history : KnotCompressionHistory E lower.retained.toLinkSpanningSurface lowerFinal
  upper_incompressible : upperFinal.Incompressible
  lower_incompressible : lowerFinal.Incompressible
  upper_class : SurfaceVertex E ⟨upperFinal, upper_incompressible⟩ = up
  lower_class : SurfaceVertex E ⟨lowerFinal, lower_incompressible⟩ = down
  genus_bound : vertexGenus E up + vertexGenus E down ≤ vertexGenus E u + vertexGenus E w
  equality_no_compression : vertexGenus E up + vertexGenus E down =
      vertexGenus E u + vertexGenus E w →
    upperFinal = upper.retained.toLinkSpanningSurface ∧
    lowerFinal = lower.retained.toLinkSpanningSurface
  strict_area : vertexGenus E up + vertexGenus E down = vertexGenus E u + vertexGenus E w →
    areaInfimum E H up + areaInfimum E H down < areaInfimum E H u + areaInfimum E H w
  fixed_neighbor_classes : ∀ z : Vertices E,
    EqualOrAdjacent E z u → EqualOrAdjacent E z w →
      EqualOrAdjacent E z up ∧ EqualOrAdjacent E z down

theorem minimizer_common_leaf_graph (H : Section4.SourceGeometry E)
    (hK : KnotIsNontrivial K) (A B : IncompressibleSpanningSurface.{0} E)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2)
    (hT2 : ConfigurationT2 E A B) :
    ∃ D : B1OriginalData H.metric H.foliation, D.A = A ∧ D.B = B := by
  exact CommonLeafGeometryV488.original_minimizer_common_leaf_data H A B hA hB hAB hT2

theorem appendix_b_transverse_bridge (A B : IncompressibleSpanningSurface.{0} E) :
    AppendixBOriginalV479.Transverse A.1.embedding B.1.embedding ↔
      Section4.Transverse (spanningAsNeat A.1) (spanningAsNeat B.1) := by
  unfold AppendixBOriginalV479.Transverse Section4.Transverse
  constructor
  · intro h a b hab
    exact (tangentPlane_sum_transport E _ _ hab _ _).mp (h a b hab)
  · intro h a b hab
    exact (tangentPlane_sum_transport E _ _ hab _ _).mpr (h a b hab)

theorem exchange_pair_native_graph_bridge (H : Section4.SourceGeometry E)
    (x u w up down : Vertices E) :
    ExchangePair E H x u w up down ↔
      ((EqualOrAdjacent E up x ∧ EqualOrAdjacent E up u ∧ EqualOrAdjacent E up w) ∧
       (EqualOrAdjacent E down x ∧ EqualOrAdjacent E down u ∧ EqualOrAdjacent E down w) ∧
       (∀ z : Vertices E, EqualOrAdjacent E z u → EqualOrAdjacent E z w →
         EqualOrAdjacent E z up ∧ EqualOrAdjacent E z down) ∧
       vertexGenus E up + vertexGenus E down ≤ vertexGenus E u + vertexGenus E w ∧
       (vertexGenus E up + vertexGenus E down = vertexGenus E u + vertexGenus E w →
         areaInfimum E H up + areaInfimum E H down < areaInfimum E H u + areaInfimum E H w)) := by
  rfl

end SeifertSurfaces.OriginalEndpoints.Section5.Obligations
