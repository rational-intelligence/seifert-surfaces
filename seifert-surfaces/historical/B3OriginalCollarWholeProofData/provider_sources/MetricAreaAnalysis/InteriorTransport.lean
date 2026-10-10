import MetricAreaAnalysis.RefinementPositivity

open scoped Manifold ContDiff ENNReal
open Set Topology MeasureTheory Bundle

noncomputable section
namespace SeifertSurfaces.MetricFoundations.AreaAnalysis
open Foundations
universe u v

/-- H19: the boundary equation is a structural premise supplied at both root calls. -/
theorem homeomorph_boundary_iff {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (x : R) :
    a x ∈ S.boundary ↔ x ∈ R.boundary := by 
  change x ∈ a ⁻¹' S.boundary ↔ x ∈ R.boundary
  rw [hboundary]

theorem homeomorph_interior_iff {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (x : R) :
    a x ∈ (S.boundary)ᶜ ↔ x ∈ (R.boundary)ᶜ := by 
  exact not_congr (homeomorph_boundary_iff a hboundary x)

theorem homeomorph_surface_measurable {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S) :
    (∀ s : Set S, MeasurableSet s → MeasurableSet (a ⁻¹' s)) ∧
    (∀ t : Set R, MeasurableSet t → MeasurableSet (a '' t)) := by 
  letI : BorelSpace S := ⟨rfl⟩
  letI : BorelSpace R := ⟨rfl⟩
  exact ⟨fun _ hs => a.continuous.measurable hs,
    fun _ ht => a.measurableEmbedding.measurableSet_image.mpr ht⟩

theorem interiorCoordinateDomain_open {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (r : R) (p : S) :
    IsOpen (interiorCoordinateDomain a r p) := by 
  have hdom : interiorCoordinateDomain a r p =
      interior (surfaceChart r).target ∩
        (surfaceChart r).symm ⁻¹' (a ⁻¹' (surfaceChart p).source) := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, hy.2.2⟩
      have hinterior : (𝓡∂ 2).IsInteriorPoint ((surfaceChart r).symm y) :=
        ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mpr hy.2.1
      have hc := ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞)
        (by simp) (chart_mem_atlas (EuclideanHalfSpace 2) r)
        (by simpa only [extChartAt_source] using
          ((surfaceChart r).map_target hy.1))).mp hinterior
      change surfaceChart r ((surfaceChart r).symm y) ∈
        interior (surfaceChart r).target at hc
      simpa only [(surfaceChart r).right_inv hy.1] using hc
    · intro hy
      have hyt : y ∈ (surfaceChart r).target := interior_subset hy.1
      refine ⟨hyt, ?_, hy.2⟩
      apply ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mp
      apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞)
        (by simp) (chart_mem_atlas (EuclideanHalfSpace 2) r)
        (by simpa only [extChartAt_source] using
          ((surfaceChart r).map_target hyt))).mpr
      change surfaceChart r ((surfaceChart r).symm y) ∈
        interior (surfaceChart r).target
      simpa only [(surfaceChart r).right_inv hyt] using hy.1
  rw [hdom]
  exact ((continuousOn_extChartAt_symm r).mono interior_subset).isOpen_inter_preimage
    isOpen_interior ((isOpen_extChartAt_source p).preimage a.continuous)

theorem interiorCoordinateDomain_measurable {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (r : R) (p : S) :
    MeasurableSet (interiorCoordinateDomain a r p) := by 
  exact (interiorCoordinateDomain_open a hboundary r p).measurableSet

theorem interiorCoordinateMap_injOn {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (r : R) (p : S) :
    InjOn (interiorCoordinateMap a r p) (interiorCoordinateDomain a r p) := by 
  intro x hx y hy hxy
  apply (surfaceChart r).symm.injOn hx.1 hy.1
  apply a.injective
  exact (surfaceChart p).injOn hx.2.2 hy.2.2 hxy

theorem interiorCoordinateMap_target_interior {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (r : R) (p : S) :
    interiorCoordinateMap a r p '' interiorCoordinateDomain a r p ⊆
      interior (surfaceChart p).target := by 
  rintro _ ⟨y, hy, rfl⟩
  have hi : a ((surfaceChart r).symm y) ∈ (S.boundary)ᶜ :=
    (homeomorph_interior_iff a hboundary _).mpr hy.2.1
  exact ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞)
    (by simp) (chart_mem_atlas (EuclideanHalfSpace 2) p)
    (by simpa only [extChartAt_source, Set.mem_preimage, Function.comp_apply]
      using hy.2.2)).mp
      (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mpr hi)

theorem interiorCoordinateMap_image {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary) (r : R) (p : S) (t : Set R)
    (hsub : t ⊆ (surfaceChart r).source ∩ (R.boundary)ᶜ ∩ a ⁻¹' (surfaceChart p).source) :
    (surfaceChart r) '' t ⊆ interiorCoordinateDomain a r p ∧
      interiorCoordinateMap a r p '' ((surfaceChart r) '' t) =
        (surfaceChart p) '' (a '' t) := by 
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hs := hsub hx
    refine ⟨(surfaceChart r).map_source hs.1.1, ?_⟩
    change (surfaceChart r).symm (surfaceChart r x) ∈
      (R.boundary)ᶜ ∩ a ⁻¹' (surfaceChart p).source
    rw [(surfaceChart r).left_inv hs.1.1]
    exact ⟨hs.1.2, hs.2⟩
  · ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨a x, ⟨x, hx, rfl⟩, ?_⟩
      simp only [interiorCoordinateMap, Function.comp_apply,
        (surfaceChart r).left_inv (hsub hx).1.1]
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨surfaceChart r x, ⟨x, hx, rfl⟩, ?_⟩
      simp only [interiorCoordinateMap, Function.comp_apply,
        (surfaceChart r).left_inv (hsub hx).1.1]

/-- H20a: ordinary derivatives are used only after removal of boundary points. -/
theorem interiorSourceMap_coordinate_derivative {S R : CompactOrientedSurface.{u}}
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (r : R) (p : S) {y : Euc 2} (hy : y ∈ interiorCoordinateDomain a r p) :
    HasFDerivAt (interiorCoordinateMap a r p) (interiorCoordinateDerivative a r p y) y := by 
  have ha' : ContMDiffAt (𝓡∂ 2) (𝓡∂ 2) ∞ a ((surfaceChart r).symm y) :=
    (ha _ hy.2.1).contMDiffAt
      (((𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by simp)).isOpen_compl.mem_nhds hy.2.1)
  have hc := (contMDiffAt_iff_of_mem_source
    (by simpa only [extChartAt_source] using (surfaceChart r).map_target hy.1)
    (by simpa only [extChartAt_source, Set.mem_preimage] using hy.2.2)).mp ha'
  change ContinuousAt a ((surfaceChart r).symm y) ∧
    ContDiffWithinAt ℝ ∞ (interiorCoordinateMap a r p) (range (𝓡∂ 2))
      (surfaceChart r ((surfaceChart r).symm y)) at hc
  rw [(surfaceChart r).right_inv hy.1] at hc
  have hi : y ∈ interior (surfaceChart r).target := by
    have h := ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) r)
      (by simpa only [extChartAt_source] using (surfaceChart r).map_target hy.1)).mp
        (((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint _).mpr hy.2.1)
    change surfaceChart r ((surfaceChart r).symm y) ∈
      interior (surfaceChart r).target at h
    simpa only [(surfaceChart r).right_inv hy.1] using h
  have hrange : range (𝓡∂ 2) ∈ 𝓝 y :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
      (fun z hz => extChartAt_target_subset_range r (interior_subset hz))
  exact ((hc.2.contDiffAt hrange).differentiableAt (by simp)).hasFDerivAt

theorem interiorSourceMap_coordinate_derivative_restrict {S R : CompactOrientedSurface.{u}}
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (r : R) (p : S) (b : Set (Euc 2)) (hb : b ⊆ interiorCoordinateDomain a r p)
    {y : Euc 2} (hy : y ∈ b) :
    HasFDerivWithinAt (interiorCoordinateMap a r p)
      (interiorCoordinateDerivative a r p y) b y := by 
  exact (interiorSourceMap_coordinate_derivative a hboundary ha r p (hb hy)).hasFDerivWithinAt

/-- H21: finite mixed pieces bind the two literal original chart partitions. -/
theorem mixedInteriorPiece_measurable {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S) (i : Fin P.count) (j : Fin Q.count) :
    MeasurableSet (mixedInteriorPiece a P Q i j) := by 
  letI : BorelSpace R := ⟨rfl⟩
  exact ((P.measurable i).inter ((homeomorph_surface_measurable a).1 _ (Q.measurable j))).inter
    ((𝓡∂ 2).isClosed_boundary (M := R) (n := ∞) (by simp)).measurableSet.compl

theorem mixedInteriorPiece_subordinate {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S) (i : Fin P.count) (j : Fin Q.count) :
    mixedInteriorPiece a P Q i j ⊆
      (surfaceChart (P.center i)).source ∩ (R.boundary)ᶜ ∩
        a ⁻¹' (surfaceChart (Q.center j)).source := by 
  intro x hx
  exact ⟨⟨P.subordinate i hx.1.1, hx.2⟩, Q.subordinate j hx.1.2⟩

theorem mixedInteriorPiece_disjoint {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S) :
    Pairwise (fun b c : Fin P.count × Fin Q.count =>
      Disjoint (mixedInteriorPiece a P Q b.1 b.2) (mixedInteriorPiece a P Q c.1 c.2)) := by 
  intro b c hbc
  by_cases hfirst : b.1 = c.1
  · have hsecond : b.2 ≠ c.2 := fun he => hbc (Prod.ext hfirst he)
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (Q.disjoint hsecond) hx.1.2 hy.1.2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (P.disjoint hfirst) hx.1.1 hy.1.1

theorem mixedInteriorPiece_source_cover {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S) (i : Fin P.count) :
    (⋃ j, mixedInteriorPiece a P Q i j) = P.piece i \ R.boundary := by 
  ext x
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, hx⟩
    exact ⟨hx.1.1, hx.2⟩
  · intro hx
    have ha : a x ∈ ⋃ j, Q.piece j := by rw [Q.covers]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨j, ⟨⟨hx.1, hj⟩, hx.2⟩⟩

theorem mixedInteriorPiece_target_cover {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary)
    (P : ChartPartition R) (Q : ChartPartition S) (j : Fin Q.count) :
    (⋃ i, a '' mixedInteriorPiece a P Q i j) = Q.piece j \ S.boundary := by 
  ext x
  constructor
  · intro hx
    obtain ⟨i, r, hr, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨hr.1.2, (homeomorph_interior_iff a hboundary r).mpr hr.2⟩
  · intro hx
    have ha : a.symm x ∈ ⋃ i, P.piece i := by rw [P.covers]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    refine Set.mem_iUnion.mpr ⟨i, a.symm x, ?_, a.apply_symm_apply x⟩
    refine ⟨⟨hi, ?_⟩, ?_⟩
    · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using hx.1
    · apply (homeomorph_interior_iff a hboundary (a.symm x)).mp
      change a (a.symm x) ∉ S.boundary
      rw [a.apply_symm_apply]
      exact hx.2

theorem mixedInteriorPiece_image_disjoint {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (P : ChartPartition R) (Q : ChartPartition S) (j : Fin Q.count) :
    Pairwise (fun i k => Disjoint (a '' mixedInteriorPiece a P Q i j)
      (a '' mixedInteriorPiece a P Q k j)) := by 
  intro i k hik
  apply Set.disjoint_left.mpr
  rintro x ⟨r, hr, he⟩ ⟨s, hs, hsx⟩
  have hrs : r = s := a.injective (he.trans hsx.symm)
  subst s
  exact Set.disjoint_left.mp (P.disjoint hik) hr.1.1 hs.1.1

theorem mixedInteriorPiece_coordinate_domain {S R : CompactOrientedSurface.{u}} (a : R ≃ₜ S)
    (hboundary : a ⁻¹' S.boundary = R.boundary)
    (P : ChartPartition R) (Q : ChartPartition S) (i : Fin P.count) (j : Fin Q.count) :
    (surfaceChart (P.center i)) '' mixedInteriorPiece a P Q i j ⊆
      interiorCoordinateDomain a (P.center i) (Q.center j) := by 
  exact (interiorCoordinateMap_image a hboundary (P.center i) (Q.center j)
    (mixedInteriorPiece a P Q i j) (mixedInteriorPiece_subordinate a P Q i j)).1

variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/-- H20b: scalar Jacobian covariance of the exact approved density. -/
theorem interiorSourceMap_coordinate_density (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (F : S → M) (H : R → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (heq : ∀ x, H x = F (a x)) (r : R) (p : S) {y : Euc 2}
    (hy : y ∈ interiorCoordinateDomain a r p) :
    coordinateAreaDensity g H r y = |(interiorCoordinateDerivative a r p y).det| *
      coordinateAreaDensity g F p (interiorCoordinateMap a r p y) := by 
  let D := interiorCoordinateDomain a r p
  let c := interiorCoordinateMap a r p
  have hp : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (H ∘ (surfaceChart r).symm) (surfaceChart r).target y :=
    (hH.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt y
      (mdifferentiableOn_extChartAt_symm y hy.1)
  have hm : MapsTo c D (surfaceChart p).target := fun z hz =>
    interior_subset (interiorCoordinateMap_target_interior a hboundary r p ⟨z, hz, rfl⟩)
  have hq : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) (𝓡∂ 3)
      (F ∘ (surfaceChart p).symm) (surfaceChart p).target (c y) :=
    (hF.mdifferentiable (by simp) _).comp_mdifferentiableWithinAt _
      (mdifferentiableOn_extChartAt_symm _ (hm hy))
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, Euc 2) D y :=
    ((interiorCoordinateDomain_open a hboundary r p).uniqueDiffOn y hy).uniqueMDiffWithinAt
  have hd : MDifferentiableWithinAt 𝓘(ℝ, Euc 2) 𝓘(ℝ, Euc 2) c D y :=
    (interiorSourceMap_coordinate_derivative a hboundary ha r p hy).hasFDerivWithinAt
      |>.differentiableWithinAt |>.mdifferentiableWithinAt
  have hc := mfderivWithin_comp y hq hd hm hu
  have he : ∀ z ∈ D, ((F ∘ (surfaceChart p).symm) ∘ c) z =
      (H ∘ (surfaceChart r).symm) z := by
    intro z hz
    change F ((surfaceChart p).symm (surfaceChart p (a ((surfaceChart r).symm z)))) =
      H ((surfaceChart r).symm z)
    rw [(surfaceChart p).left_inv hz.2.2]
    exact (heq _).symm
  have hg := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, Euc 2)) (I' := 𝓡∂ 3) he hy
  rw [hc, hp.mfderivWithin_mono hu (fun _ hz => hz.1)] at hg
  have hcast : ∀ (x z : M) (h : x = z) (v : TangentSpace (𝓡∂ 3) x),
      tangentTransport h v = (tangentSpaceCast (𝓡∂ 3) x z) v := by
    intro x z h v
    subst z
    rfl
  have hdiff (w : Euc 2) : coordinateDifferential H r y w =
      tangentTransport (he y hy)
        (coordinateDifferential F p (c y) (interiorCoordinateDerivative a r p y w)) := by
    rw [hcast]
    have hv := congrArg (fun d => d ((tangentSpaceCastModel 𝓘(ℝ, Euc 2) y).symm w)) hg
    rw [mfderivWithin_eq_fderivWithin,
      fderivWithin_of_mem_nhds ((interiorCoordinateDomain_open a hboundary r p).mem_nhds hy)] at hv
    exact hv.symm
  letI : RiemannianBundle (fun x : M => TangentSpace (𝓡∂ 3) x) :=
    ⟨g.toRiemannianMetric⟩
  have hinner {x z : M} (h : x = z) (v w : TangentSpace (𝓡∂ 3) x) :
      g.inner z (tangentTransport h v) (tangentTransport h w) = g.inner x v w := by
    subst z
    rfl
  have hgram : coordinateGram g H r y = Matrix.gram ℝ (fun i : Fin 2 =>
      coordinateDifferential F p (c y)
        (interiorCoordinateDerivative a r p y (EuclideanSpace.single i 1))) := by
    ext i j
    change g.inner (H ((surfaceChart r).symm y))
      (coordinateDifferential H r y (EuclideanSpace.single i 1))
      (coordinateDifferential H r y (EuclideanSpace.single j 1)) = _
    rw [hdiff, hdiff, hinner]
    rfl
  unfold coordinateAreaDensity
  rw [hgram]
  exact linearMapGramDensity_comp (coordinateDifferential F p (c y))
    (interiorCoordinateDerivative a r p y).toLinearMap

/-- H22: the same interior transport theorem serves both final callers. -/
theorem interiorSourceMap_coordinateIntegral_transport (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (F : S → M) (H : R → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (heq : ∀ x, H x = F (a x)) (r : R) (p : S) (t : Set R)
    (ht : MeasurableSet t)
    (hsub : t ⊆ (surfaceChart r).source ∩ (R.boundary)ᶜ ∩ a ⁻¹' (surfaceChart p).source) :
    coordinateIntegral g H r t = coordinateIntegral g F p (a '' t) := by 
  have hi := interiorCoordinateMap_image a hboundary r p t hsub
  have hderiv : ∀ y ∈ (surfaceChart r) '' t,
      HasFDerivWithinAt (interiorCoordinateMap a r p) (interiorCoordinateDerivative a r p y)
        ((surfaceChart r) '' t) y := fun y hy =>
    (interiorSourceMap_coordinate_derivative a hboundary ha r p (hi.1 hy)).hasFDerivWithinAt
  have hm := extChart_image_measurable r t ht (fun _ hx => (hsub hx).1.1)
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume hm hderiv
    ((interiorCoordinateMap_injOn a hboundary r p).mono hi.1) (coordinateAreaDensity g F p)
  unfold coordinateIntegral
  rw [hi.2] at hcov
  rw [hcov]
  apply setIntegral_congr_fun hm
  intro y hy
  exact interiorSourceMap_coordinate_density g F H hF hH a hboundary ha heq r p (hi.1 hy)

theorem interiorSourceMap_coordinateIntegrable_transport (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (F : S → M) (H : R → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (heq : ∀ x, H x = F (a x)) (r : R) (p : S) (t : Set R)
    (ht : MeasurableSet t)
    (hsub : t ⊆ (surfaceChart r).source ∩ (R.boundary)ᶜ ∩ a ⁻¹' (surfaceChart p).source) :
    IntegrableOn (coordinateAreaDensity g H r) ((surfaceChart r) '' t) ∧
      IntegrableOn (coordinateAreaDensity g F p) ((surfaceChart p) '' (a '' t)) := by 
  constructor
  · exact coordinateDensity_integrable_measurableChartSubset g H hH r t ht
      (fun _ hx => (hsub hx).1.1)
  · apply coordinateDensity_integrable_measurableChartSubset g F hF p (a '' t)
      ((homeomorph_surface_measurable a).2 t ht)
    rintro _ ⟨x, hx, rfl⟩
    exact (hsub hx).2

/-- H23: a consumer whose structural premises are concretely produced at both endpoints. -/
theorem interiorSourceMap_finite_sum_transport (g : SmoothMetric M)
    {S R : CompactOrientedSurface.{u}} (F : S → M) (H : R → M)
    (hF : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ F) (hH : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ H)
    (a : R ≃ₜ S) (hboundary : a ⁻¹' S.boundary = R.boundary)
    (ha : ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ a ((R.boundary)ᶜ))
    (heq : ∀ x, H x = F (a x)) (P : ChartPartition R) (Q : ChartPartition S) :
    partitionArea g H P = partitionArea g F Q := by 
  have hsource (i : Fin P.count) :
      coordinateIntegral g H (P.center i) (P.piece i) =
        ∑ j : Fin Q.count, coordinateIntegral g H (P.center i) (mixedInteriorPiece a P Q i j) := by
    rw [coordinateDensity_integral_remove_boundary g H hH (P.center i) (P.piece i)
      (P.measurable i) (P.subordinate i), ← mixedInteriorPiece_source_cover a P Q i]
    unfold coordinateIntegral
    rw [image_iUnion]
    apply integral_iUnion_fintype
    · intro j
      exact extChart_image_measurable (P.center i) _ (mixedInteriorPiece_measurable a P Q i j)
        (fun _ hx => (mixedInteriorPiece_subordinate a P Q i j hx).1.1)
    · intro j k hjk
      change Disjoint ((surfaceChart (P.center i)) '' mixedInteriorPiece a P Q i j)
        ((surfaceChart (P.center i)) '' mixedInteriorPiece a P Q i k)
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have hxz := (surfaceChart (P.center i)).injOn
        (P.subordinate i hx.1.1) (P.subordinate i hz.1.1) (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (Q.disjoint hjk) hx.1.2 hz.1.2
    · intro j
      exact coordinateDensity_integrable_measurableChartSubset g H hH (P.center i) _
        (mixedInteriorPiece_measurable a P Q i j)
        (fun _ hx => (mixedInteriorPiece_subordinate a P Q i j hx).1.1)
  have htarget (j : Fin Q.count) :
      coordinateIntegral g F (Q.center j) (Q.piece j) =
        ∑ i : Fin P.count, coordinateIntegral g F (Q.center j) (a '' mixedInteriorPiece a P Q i j) := by
    rw [coordinateDensity_integral_remove_boundary g F hF (Q.center j) (Q.piece j)
      (Q.measurable j) (Q.subordinate j), ← mixedInteriorPiece_target_cover a hboundary P Q j]
    unfold coordinateIntegral
    rw [image_iUnion]
    apply integral_iUnion_fintype
    · intro i
      apply extChart_image_measurable (Q.center j) _
        ((homeomorph_surface_measurable a).2 _ (mixedInteriorPiece_measurable a P Q i j))
      rintro _ ⟨x, hx, rfl⟩
      exact Q.subordinate j hx.1.2
    · intro i k hik
      change Disjoint ((surfaceChart (Q.center j)) '' (a '' mixedInteriorPiece a P Q i j))
        ((surfaceChart (Q.center j)) '' (a '' mixedInteriorPiece a P Q k j))
      rw [Set.disjoint_left]
      rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
      have hxs : x ∈ (surfaceChart (Q.center j)).source := by
        rcases hx with ⟨x', hx', rfl⟩
        exact Q.subordinate j hx'.1.2
      have hzs : z ∈ (surfaceChart (Q.center j)).source := by
        rcases hz with ⟨z', hz', rfl⟩
        exact Q.subordinate j hz'.1.2
      have hxz := (surfaceChart (Q.center j)).injOn hxs hzs (hxy.trans hzy.symm)
      subst z
      exact Set.disjoint_left.mp (mixedInteriorPiece_image_disjoint a P Q j hik) hx hz
    · intro i
      apply coordinateDensity_integrable_measurableChartSubset g F hF (Q.center j) _
        ((homeomorph_surface_measurable a).2 _ (mixedInteriorPiece_measurable a P Q i j))
      rintro _ ⟨x, hx, rfl⟩
      exact Q.subordinate j hx.1.2
  calc
    partitionArea g H P = ∑ i : Fin P.count, ∑ j : Fin Q.count,
        coordinateIntegral g H (P.center i) (mixedInteriorPiece a P Q i j) :=
      Finset.sum_congr rfl (fun i _ => hsource i)
    _ = ∑ i : Fin P.count, ∑ j : Fin Q.count,
        coordinateIntegral g F (Q.center j) (a '' mixedInteriorPiece a P Q i j) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact interiorSourceMap_coordinateIntegral_transport g F H hF hH a hboundary ha heq
        (P.center i) (Q.center j) (mixedInteriorPiece a P Q i j)
        (mixedInteriorPiece_measurable a P Q i j) (mixedInteriorPiece_subordinate a P Q i j)
    _ = ∑ j : Fin Q.count, ∑ i : Fin P.count,
        coordinateIntegral g F (Q.center j) (a '' mixedInteriorPiece a P Q i j) :=
      Finset.sum_comm
    _ = partitionArea g F Q :=
      (Finset.sum_congr rfl (fun j _ => htarget j)).symm

end SeifertSurfaces.MetricFoundations.AreaAnalysis
