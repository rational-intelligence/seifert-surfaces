import Section4GeneralCompression
import OriginalB2B5V479
import Section5Analysis
import Section5Arithmetic
import Section5Combinatorics

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology Function MeasureTheory Bundle
open scoped Manifold ContDiff BigOperators ENNReal

namespace SeifertSurfaces.OriginalEndpoints.Section5
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.AppendixACoordinates

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]

/- A literal C² closed curve; unlike the smooth Appendix B consumer type,
this does not strengthen the standalone Lemma 5.4 input to C∞. -/
structure C2ClosedCurve (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] where
  map : Circle → M
  regular : Manifold.IsSmoothEmbedding (𝓡 1) (𝓡∂ 3) 2 map

def C2ClosedCurve.at (c : C2ClosedCurve M) (s : ℝ) : M :=
  c.map (Circle.exp (2 * Real.pi * s))

def curveVelocity (c : ℝ → M) (s : ℝ) : TangentSpace (𝓡∂ 3) (c s) :=
  mfderiv 𝓘(ℝ) (𝓡∂ 3) c s ((NormedSpace.fromTangentSpace s).symm 1)

def C2ClosedCurve.speed (g : SmoothMetric M) (c : C2ClosedCurve M) (s : ℝ) : ℝ :=
  Real.sqrt (g.inner (c.at s) (curveVelocity c.at s) (curveVelocity c.at s))

def C2ClosedCurve.integral (g : SmoothMetric M) (c : C2ClosedCurve M) (h : M → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, h (c.at s) * c.speed g s

structure C2Seams (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] where
  count : ℕ
  curve : Fin count → C2ClosedCurve M
  disjoint : Pairwise (fun i j => Disjoint (range (curve i).map) (range (curve j).map))

def C2Seams.carrier (Γ : C2Seams M) : Set M := ⋃ i, range (Γ.curve i).map
def C2Seams.integral (g : SmoothMetric M) (Γ : C2Seams M) (h : M → ℝ) : ℝ :=
  ∑ i, (Γ.curve i).integral g h

/- Real image area from countably many measurable disjoint coordinate pieces. The
maps are actual regular surface charts. Neither orientation nor a neatness
condition is added to the standalone source surface. Independence of charts
and existence of the atlas are separately named theorem obligations. -/
structure ImageAreaAtlas (F : Set M) where
  map : ℕ → E2 → M
  chartDomain : ℕ → Set E2
  piece : ℕ → Set E2
  piece_measurable : ∀ i, MeasurableSet (piece i)
  subordinate : ∀ i, piece i ⊆ chartDomain i
  c2 : ∀ i, ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) 2 (map i) (chartDomain i)
  chart_embedding : ∀ i, IsEmbedding (fun x : chartDomain i => map i x)
  immersion : ∀ i x, x ∈ chartDomain i →
    Function.Injective (mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (map i) (chartDomain i) x)
  partition : Pairwise (fun i j => Disjoint ((map i) '' piece i) ((map j) '' piece j))
  covers : (⋃ i, (map i) '' piece i) = F

def ImageAreaAtlas.gram {F : Set M} (g : SmoothMetric M) (A : ImageAreaAtlas F)
    (i : ℕ) (x : E2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let d := mfderivWithin 𝓘(ℝ, E2) (𝓡∂ 3) (A.map i) (A.chartDomain i) x
  fun j k => g.inner (A.map i x)
    (d ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 j)))
    (d ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 k)))

def ImageAreaAtlas.area {F : Set M} (g : SmoothMetric M) (A : ImageAreaAtlas F) : ℝ≥0∞ :=
  ∑' i : ℕ, ∫⁻ x in A.piece i, ENNReal.ofReal (Real.sqrt (Matrix.det (A.gram g i x)))

def ImageAreaAtlas.Valid {F : Set M} (g : SmoothMetric M) (A : ImageAreaAtlas F) : Prop :=
  ∀ i, AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt (Matrix.det (A.gram g i x))))
    (volume.restrict (A.piece i))

/-- Empty images have geometric extended area zero even when the ambient type
has no point and hence admits no Nat-total atlas. On a nonempty image the
original chart integral infimum is retained. Atlas existence and independence
remain obligations; this branch does not supply either one. -/
def extendedImageArea (g : SmoothMetric M) (F : Set M) : ℝ≥0∞ :=
  if F = ∅ then 0 else
    sInf {a : ℝ≥0∞ | ∃ A : ImageAreaAtlas F, A.Valid g ∧ a = A.area g}

def imageArea (g : SmoothMetric M) (F : Set M) : ℝ :=
  (extendedImageArea g F).toReal

/- The smooth image away from Γ is expressed without imposing smoothness on
an arbitrary topological parametrization of the whole cornered source. -/
structure SmoothSurfaceImageChart (F : Set M) (p : M) where
  domain : Set (EuclideanHalfSpace 2)
  domain_open : IsOpen domain
  ambient : Set M
  ambient_open : IsOpen ambient
  point : EuclideanHalfSpace 2
  point_mem : point ∈ domain
  map : EuclideanHalfSpace 2 → M
  smooth : ContMDiffOn (𝓡∂ 2) (𝓡∂ 3) ∞ map domain
  embedding : IsEmbedding (fun x : domain => map x)
  rank : ∀ x ∈ domain, Function.Injective (mfderivWithin (𝓡∂ 2) (𝓡∂ 3) map domain x)
  base : map point = p
  exact_image : map '' domain = F ∩ ambient

def wedgePoint (alpha s r : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![s, Real.cot (alpha / 2) * |r|, r]

structure CornerSlice (g : SmoothMetric M) (F Γ : Set M) (p : M) where
  coordinates : OpenPartialHomeomorph M E3
  point_mem : p ∈ coordinates.source
  source_interior : coordinates.source ⊆ (𝓡∂ 3).interior M
  c2 : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, E3) 2 coordinates coordinates.source
  inverse_c2 : ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 3) 2 coordinates.symm coordinates.target
  angle : ℝ → ℝ
  angle_c1 : ContDiff ℝ 1 angle
  angle_range : ∀ y ∈ coordinates.target, angle (y 0) ∈ Ioo (0 : ℝ) Real.pi
  seam_exact : coordinates '' (Γ ∩ coordinates.source) =
    {y ∈ coordinates.target | y 1 = 0 ∧ y 2 = 0}
  wedge_exact : coordinates '' (F ∩ coordinates.source) =
    {y ∈ coordinates.target | y 1 = Real.cot (angle (y 0) / 2) * |y 2|}
  plusSheet : E2 → M
  minusSheet : E2 → M
  plusDomain : Set E2
  minusDomain : Set E2
  plus_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ plusSheet plusDomain
  minus_smooth : ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ minusSheet minusDomain
  sheets_exact : ∀ z : E2,
    (z 1 ≥ 0 → wedgePoint (angle (z 0)) (z 0) (z 1) ∈ coordinates.target →
      z ∈ plusDomain ∧ plusSheet z = coordinates.symm (wedgePoint (angle (z 0)) (z 0) (z 1))) ∧
    (z 1 ≤ 0 → wedgePoint (angle (z 0)) (z 0) (z 1) ∈ coordinates.target →
      z ∈ minusDomain ∧ minusSheet z = coordinates.symm (wedgePoint (angle (z 0)) (z 0) (z 1)))
  orthonormal_on_seam : ∀ y ∈ coordinates.target, y 1 = 0 → y 2 = 0 →
    ∀ i j : Fin 3, g.inner (coordinates.symm y)
      (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) coordinates.symm coordinates.target y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
      (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) coordinates.symm coordinates.target y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j))) = if i = j then 1 else 0

structure SourceSmoothSurface where
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charted : ChartedSpace (EuclideanHalfSpace 2) carrier]
  [smooth : IsManifold (𝓡∂ 2) ∞ carrier]
  [hausdorff : T2Space carrier]
  [secondCountable : SecondCountableTopology carrier]

attribute [instance] SourceSmoothSurface.topology SourceSmoothSurface.charted
  SourceSmoothSurface.smooth SourceSmoothSurface.hausdorff SourceSmoothSurface.secondCountable
instance : CoeSort SourceSmoothSurface Type := ⟨SourceSmoothSurface.carrier⟩
def SourceSmoothSurface.boundary (S : SourceSmoothSurface) : Set S := (𝓡∂ 2).boundary S

structure SourceCornerSurface (g : SmoothMetric M) where
  source : SourceSmoothSurface
  map : C(source, M)
  embedded : IsEmbedding map
  seams : C2Seams M
  seams_on_surface : seams.carrier ⊆ range map
  boundary_disjoint : Disjoint seams.carrier (map '' source.boundary)
  smooth_off_seam : ∀ p ∈ range map \ seams.carrier,
    Nonempty (SmoothSurfaceImageChart (range map) p)
  slice : ∀ p, p ∈ seams.carrier → CornerSlice g (range map) seams.carrier p

def SourceCornerSurface.image {g : SmoothMetric M} (F : SourceCornerSurface g) : Set M := range F.map
def SourceCornerSurface.boundary {g : SmoothMetric M} (F : SourceCornerSurface g) : Set M :=
  F.map '' F.source.boundary
def SourceCornerSurface.theta {g : SmoothMetric M} (F : SourceCornerSurface g) (p : M) : ℝ :=
  if h : p ∈ F.seams.carrier then
    let c := F.slice p h
    let alpha := c.angle ((c.coordinates p) 0)
    min alpha (Real.pi - alpha)
  else 0

def seamDistance (g : SmoothMetric M) (Γ : Set M) (p q : M) : ℝ≥0∞ :=
  ⨅ c : {c : ℝ → M // ContMDiffOn 𝓘(ℝ) (𝓡∂ 3) 1 c (Icc (0 : ℝ) 1) ∧
    c '' Icc (0 : ℝ) 1 ⊆ Γ ∧ c 0 = p ∧ c 1 = q},
    ENNReal.ofReal (∫ s in (0 : ℝ)..1,
      Real.sqrt (g.inner (c.1 s) (curveVelocity c.1 s) (curveVelocity c.1 s)))

def NormalToSeams (g : SmoothMetric M) (Γ : C2Seams M)
    (p : M) (v : TangentSpace (𝓡∂ 3) p) : Prop :=
  ∀ i : Fin Γ.count, ∀ s : ℝ, ∀ h : (Γ.curve i).at s = p,
    g.inner p v (h ▸ curveVelocity (Γ.curve i).at s) = 0

/- Actual geodesic exponential characterization, not a freely supplied reach
function. Constructing this geometry is an output obligation of Lemma 5.4. -/
structure SourceNormalExponential (g : SmoothMetric M) (Γ : C2Seams M) where
  domain : Set (Σ x : Γ.carrier, TangentSpace (𝓡∂ 3) x.1)
  exp : (Σ x : Γ.carrier, TangentSpace (𝓡∂ 3) x.1) → M
  domain_exact : ∀ v, v ∈ domain ↔
    ∃ c : ℝ → M, ∃ h : c 0 = v.1.1,
      SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.IsMetricGeodesic g c ∧ (h ▸ curveVelocity c 0) = v.2
  geodesic : ∀ v ∈ domain, ∃ c : ℝ → M, ∃ h : c 0 = v.1.1,
    SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.IsMetricGeodesic g c ∧ (h ▸ curveVelocity c 0) = v.2 ∧ c 1 = exp v

def normalReachDomain {g : SmoothMetric M} {Γ : C2Seams M}
    (N : SourceNormalExponential g Γ) (p : M) (rho : ℝ) :
    Set (Σ x : Γ.carrier, TangentSpace (𝓡∂ 3) x.1) :=
  {v | NormalToSeams g Γ v.1.1 v.2 ∧
    Real.sqrt (g.inner v.1.1 v.2 v.2) < rho ∧
    seamDistance g Γ.carrier v.1.1 p < ENNReal.ofReal rho}

def localReach {g : SmoothMetric M} {Γ : C2Seams M}
    (N : SourceNormalExponential g Γ) (p : M) : ℝ≥0∞ :=
  ⨆ rho : {rho : ℝ // 0 < rho ∧ normalReachDomain N p rho ⊆ N.domain ∧
    Set.InjOn N.exp (normalReachDomain N p rho) ∧
    IsPreconnected (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.metricBall g p rho ∩ Γ.carrier)}, ENNReal.ofReal rho.1

def boundaryDistance {g : SmoothMetric M} (F : SourceCornerSurface g) (p : M) : ℝ≥0∞ :=
  ⨅ q : F.boundary, SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.metricEDist g p q.1

def widthTube (g : SmoothMetric M) (Γ : Set M) (eta : M → ℝ) : Set M :=
  {p | ∃ x ∈ Γ, SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.metricEDist g p x < ENNReal.ofReal (eta x)}

def WidthAdmissible (g : SmoothMetric M) (Γ : C2Seams M)
    (etaMax kappa eta : M → ℝ) : Prop :=
  (∀ p ∈ Γ.carrier, 0 < eta p ∧ eta p ≤ etaMax p) ∧
  ∀ i : Fin Γ.count, ContDiff ℝ 1 (eta ∘ (Γ.curve i).at) ∧
    ∀ s : ℝ, |deriv (eta ∘ (Γ.curve i).at) s| ≤
      kappa ((Γ.curve i).at s) * (Γ.curve i).speed g s

structure RoundingBounds {g : SmoothMetric M} (F : SourceCornerSurface g) where
  normal : SourceNormalExponential g F.seams
  etaMax : M → ℝ
  kappa : M → ℝ
  positive : ∀ p ∈ F.seams.carrier, 0 < etaMax p ∧ 0 < kappa p
  continuous : ContinuousOn etaMax F.seams.carrier ∧ ContinuousOn kappa F.seams.carrier
  g0 : ℝ → ℝ
  gain_positive : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < g0 theta
  gain_continuous : ContinuousOn g0 (Ioc (0 : ℝ) (Real.pi / 2))
  gain_monotone : MonotoneOn g0 (Ioc (0 : ℝ) (Real.pi / 2))
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  gain_exact : g0 = SeifertSurfaces.AppendixB.angleGain cutoff
  C2Bound : ℝ
  slopeDerivativeBound : ℝ
  metricBound : ℝ
  bounds_positive : 0 < C2Bound ∧ 0 < slopeDerivativeBound ∧ 0 < metricBound
  localTarget : ∀ p, p ∈ F.seams.carrier → Set E3
  target_open : ∀ p hp, IsOpen (localTarget p hp)
  target_contains : ∀ p hp, (F.slice p hp).coordinates p ∈ localTarget p hp
  target_inside : ∀ p hp, localTarget p hp ⊆ (F.slice p hp).coordinates.target
  metric_estimates : ∀ p hp, ∀ y ∈ localTarget p hp, ∀ i j : Fin 3,
    |g.inner ((F.slice p hp).coordinates.symm y)
      (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (F.slice p hp).coordinates.symm
        (F.slice p hp).coordinates.target y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
      (mfderivWithin 𝓘(ℝ, E3) (𝓡∂ 3) (F.slice p hp).coordinates.symm
        (F.slice p hp).coordinates.target y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j))) -
        (if i = j then 1 else 0)| ≤ metricBound * Real.sqrt ((y 1) ^ 2 + (y 2) ^ 2)
  sheet_bounds : ∀ p hp, ∀ n : ℕ, n ≤ 2 → ∀ z : E2,
    ((z ∈ (F.slice p hp).plusDomain ∧
      (F.slice p hp).coordinates ((F.slice p hp).plusSheet z) ∈ localTarget p hp) →
      ‖iteratedFDerivWithin ℝ n ((F.slice p hp).coordinates ∘ (F.slice p hp).plusSheet)
        (F.slice p hp).plusDomain z‖ ≤ C2Bound) ∧
    ((z ∈ (F.slice p hp).minusDomain ∧
      (F.slice p hp).coordinates ((F.slice p hp).minusSheet z) ∈ localTarget p hp) →
      ‖iteratedFDerivWithin ℝ n ((F.slice p hp).coordinates ∘ (F.slice p hp).minusSheet)
        (F.slice p hp).minusDomain z‖ ≤ C2Bound)
  slope_bounds : ∀ p hp, ∀ s : ℝ,
    (EuclideanSpace.equiv (Fin 3) ℝ).symm ![s, 0, 0] ∈ localTarget p hp →
      |deriv (fun u => Real.cot ((F.slice p hp).angle u / 2)) s| ≤ slopeDerivativeBound
  upper_bounds : ∀ p hp,
    let alpha := (F.slice p hp).angle (((F.slice p hp).coordinates p) 0)
    let m := Real.cot (alpha / 2)
    8 * etaMax p ^ 2 * slopeDerivativeBound ^ 2 ≤ g0 (F.theta p) ∧
    36 * m ^ 2 * kappa p ^ 2 ≤ g0 (F.theta p) ∧
    4 * C2Bound * etaMax p ≤ g0 (F.theta p) ∧
    24 * metricBound * etaMax p * (1 + m ^ 2) ≤ g0 (F.theta p) ∧
    ENNReal.ofReal (2 * etaMax p * Real.sqrt (1 + m ^ 2)) ≤ localReach normal p ∧
    ENNReal.ofReal (2 * etaMax p) ≤ boundaryDistance F p
  etaLower : ℝ → ℝ → ℝ → ℝ
  kappaLower : ℝ → ℝ → ℝ → ℝ
  lower_positive : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho b,
    0 < rho → 0 < b → 0 < etaLower theta rho b ∧ 0 < kappaLower theta rho b
  lower_monotone : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2),
    ∀ theta' ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rho' b b',
    0 < rho → 0 < rho' → 0 < b → 0 < b' →
    theta ≤ theta' → rho ≤ rho' → b ≤ b' →
    etaLower theta rho b ≤ etaLower theta' rho' b' ∧
    kappaLower theta rho b ≤ kappaLower theta' rho' b'
  lower_bounds : ∀ p ∈ F.seams.carrier, ∀ rho b : ℝ, 0 < rho → 0 < b →
    ENNReal.ofReal rho ≤ localReach normal p → ENNReal.ofReal b ≤ boundaryDistance F p →
    etaLower (F.theta p) rho b ≤ etaMax p ∧ kappaLower (F.theta p) rho b ≤ kappa p
  etaLower_exact : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho b,
    etaLower theta rho b =
      min (rho / (2 * Real.sqrt (1 + Real.cot (theta / 2) ^ 2)))
        (min (Real.sqrt (g0 theta / (8 * slopeDerivativeBound ^ 2)))
          (min (g0 theta / (4 * C2Bound))
            (min (g0 theta / (24 * metricBound * (1 + Real.cot (theta / 2) ^ 2))) (b / 2))))
  kappaLower_exact : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho b,
    kappaLower theta rho b = Real.sqrt (g0 theta) / (6 * Real.cot (theta / 2))

structure GeneralNeatImage (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] where
  surface : CompactSmoothSurface
  map : surface → M
  smooth : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ map
  proper : map ⁻¹' (𝓡∂ 3).boundary M = surface.boundary
  transverse : ∀ x ∈ surface.boundary, ∃ v : TangentSpace (𝓡∂ 2) x,
    inwardCoordinate (map x) (mfderiv (𝓡∂ 2) (𝓡∂ 3) map x v) ≠ 0

def GeneralNeatImage.image (F : GeneralNeatImage M) : Set M := range F.map
def GeneralNeatImage.boundary (F : GeneralNeatImage M) : Set M := F.map '' F.surface.boundary

structure GeneralOneSidedCollar (F : GeneralNeatImage M) (U : Set M) where
  epsilon : ℝ
  positive : 0 < epsilon
  map : F.surface × ℝ → M
  initial : ∀ x, map (x, 0) = F.map x
  smooth : ContMDiffOn ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3) ∞ map (univ ×ˢ Ico 0 epsilon)
  embedded : IsEmbedding (fun x : univ ×ˢ Ico (0 : ℝ) epsilon => map x.1)
  closed_side : F.image ⊆ closure U
  open_side : ∀ x t, 0 < t → t < epsilon → map (x, t) ∈ U
  boundary_strata : ∀ x t, t ∈ Ico (0 : ℝ) epsilon →
    (map (x, t) ∈ (𝓡∂ 3).boundary M ↔ x ∈ F.surface.boundary)
  immersion : ∀ x ∈ univ ×ˢ Ico (0 : ℝ) epsilon,
    Function.Injective (mfderivWithin ((𝓡∂ 2).prod 𝓘(ℝ)) (𝓡∂ 3)
      map (univ ×ˢ Ico (0 : ℝ) epsilon) x)

def SelectedRegion {g : SmoothMetric M} (F : SourceCornerSurface g) (U : Set M) : Prop :=
  IsOpen U ∧ F.image = frontier U ∧ ∀ p hp,
    let c := F.slice p hp
    c.coordinates '' (U ∩ c.coordinates.source) =
      {y ∈ c.coordinates.target | Real.cot (c.angle (y 0) / 2) * |y 2| < y 1}

def Separates (F : Set M) : Prop :=
  ∃ x ∈ Fᶜ, ∃ y ∈ Fᶜ, y ∉ connectedComponentIn Fᶜ x

/- Slice nonnegativity is an integral of the actual Gram determinants of
two actual surface parametrizations, rather than a freely assigned gain. -/
structure SliceComparison {g : SmoothMetric M} (F : SourceCornerSurface g)
    (C : RoundingBounds F) (eta : M → ℝ) (B : GeneralNeatImage M) where
  oldMap : ∀ p, p ∈ F.seams.carrier → E2 → M
  newMap : ∀ p, p ∈ F.seams.carrier → E2 → M
  interval : ∀ p, p ∈ F.seams.carrier → Set ℝ
  center : ∀ p hp, ((F.slice p hp).coordinates p) 0 ∈ interval p hp
  interval_open : ∀ p hp, IsOpen (interval p hp)
  base : ∀ p, p ∈ F.seams.carrier → ℝ → F.seams.carrier
  base_exact : ∀ p hp, ∀ s ∈ interval p hp,
    (base p hp s).1 = (F.slice p hp).coordinates.symm
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![s, 0, 0])
  base_unit_speed : ∀ p hp, ∀ s ∈ interval p hp,
    g.inner (base p hp s).1
      (curveVelocity (fun u => (base p hp u).1) s)
      (curveVelocity (fun u => (base p hp u).1) s) = 1
  old_exact : ∀ p hp, ∀ s ∈ interval p hp, ∀ r,
    |r| ≤ eta ((F.slice p hp).coordinates.symm
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![s, 0, 0])) →
    oldMap p hp ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, r]) =
      (F.slice p hp).coordinates.symm (wedgePoint ((F.slice p hp).angle s) s r)
  new_fiber : ∀ p hp, ∀ s ∈ interval p hp,
    (newMap p hp) '' {z : E2 | z 0 = s ∧ |z 1| ≤ eta (base p hp s).1} =
      B.image ∩ (F.slice p hp).coordinates.source ∩
        {q | ((F.slice p hp).coordinates q) 0 = s ∧
          |((F.slice p hp).coordinates q) 2| ≤ eta (base p hp s).1}
  base_smooth : ∀ p hp, ContMDiffOn 𝓘(ℝ) (𝓡∂ 3) 2 (fun s => (base p hp s).1) (interval p hp)
  base_source : ∀ p hp, ∀ s ∈ interval p hp,
    (base p hp s).1 ∈ (F.slice p hp).coordinates.source
  old_strip_target : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    |z 1| ≤ eta (base p hp (z 0)).1 →
    wedgePoint ((F.slice p hp).angle (z 0)) (z 0) (z 1) ∈ (F.slice p hp).coordinates.target
  old_chart_source : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    |z 1| ≤ eta (base p hp (z 0)).1 →
    oldMap p hp z ∈ (F.slice p hp).coordinates.source
  new_chart_source : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    |z 1| ≤ eta (base p hp (z 0)).1 →
    newMap p hp z ∈ (F.slice p hp).coordinates.source
  new_coordinates : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    |z 1| ≤ eta (base p hp (z 0)).1 →
    ((F.slice p hp).coordinates (newMap p hp z)) 0 = z 0 ∧
    ((F.slice p hp).coordinates (newMap p hp z)) 2 = z 1
  old_continuous : ∀ p hp, ContinuousOn (oldMap p hp)
    {z | z 0 ∈ interval p hp ∧ |z 1| ≤ eta (base p hp (z 0)).1}
  old_regular_plus : ∀ p hp, ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) 2 (oldMap p hp)
    {z | z 0 ∈ interval p hp ∧ 0 < z 1 ∧ z 1 < eta (base p hp (z 0)).1}
  old_regular_minus : ∀ p hp, ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) 2 (oldMap p hp)
    {z | z 0 ∈ interval p hp ∧ -eta (base p hp (z 0)).1 < z 1 ∧ z 1 < 0}
  new_regular : ∀ p hp, ContMDiffOn 𝓘(ℝ, E2) (𝓡∂ 3) ∞ (newMap p hp)
    {z | z 0 ∈ interval p hp ∧ |z 1| < eta (base p hp (z 0)).1}
  old_embedded : ∀ p hp, IsEmbedding (fun z :
    {z | z 0 ∈ interval p hp ∧ |z 1| ≤ eta (base p hp (z 0)).1} => oldMap p hp z.1)
  new_embedded : ∀ p hp, IsEmbedding (fun z :
    {z | z 0 ∈ interval p hp ∧ |z 1| ≤ eta (base p hp (z 0)).1} => newMap p hp z.1)
  old_rank : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    0 < |z 1| → |z 1| < eta (base p hp (z 0)).1 →
    Function.Injective (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (oldMap p hp) z)
  new_rank : ∀ p hp, ∀ z : E2, z 0 ∈ interval p hp →
    |z 1| < eta (base p hp (z 0)).1 →
    Function.Injective (mfderiv 𝓘(ℝ, E2) (𝓡∂ 3) (newMap p hp) z)
  old_fiber : ∀ p hp, ∀ s ∈ interval p hp,
    (oldMap p hp) '' {z : E2 | z 0 = s ∧ |z 1| ≤ eta (base p hp s).1} =
      F.image ∩ (F.slice p hp).coordinates.source ∩
        {q | ((F.slice p hp).coordinates q) 0 = s ∧
          |((F.slice p hp).coordinates q) 2| ≤ eta (base p hp s).1}
  width_positive : ∀ p hp, ∀ s ∈ interval p hp, 0 < eta (base p hp s).1
  width_c1 : ∀ p hp, ContDiffOn ℝ 1 (fun s => eta (base p hp s).1) (interval p hp)
  strip_area_identification : ∀ p hp, ∀ a b : ℝ, a ≤ b → Icc a b ⊆ interval p hp →
    let D : Set E2 := {z | z 0 ∈ Icc a b ∧ |z 1| ≤ eta (base p hp (z 0)).1}
    extendedImageArea g ((oldMap p hp) '' D) =
      ∫⁻ z in D, ENNReal.ofReal (Real.sqrt (Matrix.det
        (AppendixBOriginalV479.actualSurfaceGram g (oldMap p hp) z))) ∧
    extendedImageArea g ((newMap p hp) '' D) =
      ∫⁻ z in D, ENNReal.ofReal (Real.sqrt (Matrix.det
        (AppendixBOriginalV479.actualSurfaceGram g (newMap p hp) z)))
  density_integrable : ∀ p hp, ∀ s ∈ interval p hp,
    IntervalIntegrable (fun r => Real.sqrt (Matrix.det
      (AppendixBOriginalV479.actualSurfaceGram g (oldMap p hp)
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, r])))) volume
      (-eta (base p hp s).1) (eta (base p hp s).1) ∧
    IntervalIntegrable (fun r => Real.sqrt (Matrix.det
      (AppendixBOriginalV479.actualSurfaceGram g (newMap p hp)
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, r])))) volume
      (-eta (base p hp s).1) (eta (base p hp s).1)
  nonnegative : ∀ p hp, ∀ s ∈ interval p hp,
    0 ≤ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.actualSliceDensity g (oldMap p hp) s
      (eta (base p hp s).1) -
      SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.actualSliceDensity g (newMap p hp) s
        (eta (base p hp s).1)

structure RoundedGeometry {g : SmoothMetric M} (F : SourceCornerSurface g)
    (C : RoundingBounds F) (eta : M → ℝ) where
  surface : GeneralNeatImage M
  agrees : surface.image \ widthTube g F.seams.carrier eta =
    F.image \ widthTube g F.seams.carrier eta
  boundary : surface.boundary = F.boundary
  closed_wedge : ∀ p hp,
    let c := F.slice p hp
    c.coordinates '' (surface.image ∩ widthTube g F.seams.carrier eta ∩ c.coordinates.source) ⊆
      {y ∈ c.coordinates.target | Real.cot (c.angle (y 0) / 2) * |y 2| ≤ y 1}
  collar : ∀ U, SelectedRegion F U →
    surface.image ⊆ closure U ∧ Nonempty (GeneralOneSidedCollar surface U)
  slices : SliceComparison F C eta surface
  area : extendedImageArea g surface.image +
    ENNReal.ofReal (F.seams.integral g (fun p => C.g0 (F.theta p) * eta p)) ≤ extendedImageArea g F.image
  restricted_gain : ∀ Z : Set M, @MeasurableSet M (borel M) Z →
    extendedImageArea g surface.image +
      ENNReal.ofReal (F.seams.integral g (fun p => if p ∈ Z then C.g0 (F.theta p) * eta p else 0)) ≤
        extendedImageArea g F.image
  separates : F.boundary = ∅ → Separates F.image → surface.boundary = ∅ ∧ Separates surface.image

/- The literal printed smooth category is retained as the original claim.
SF-09 is recorded in SOURCE_MAP and REVIEW_REQUEST; no proof is authorized. -/
structure OriginalRoundedSurface {g : SmoothMetric M} (F : SourceCornerSurface g)
    (C : RoundingBounds F) (eta : M → ℝ) extends RoundedGeometry F C eta where
  isotopy : SmoothAmbientIsotopy M
  image : (isotopy.stage 1) '' surface.image = F.image
  supported : ∀ t p, p ∉ widthTube g F.seams.carrier eta → isotopy.stage t p = p
  regions : ∀ p, p ∉ surface.image →
    let Rnew := connectedComponentIn surface.imageᶜ p
    let Rold := connectedComponentIn F.imageᶜ (isotopy.stage 1 p)
    (isotopy.stage 1) '' Rnew = Rold ∧
      Rnew \ widthTube g F.seams.carrier eta = Rold \ widthTube g F.seams.carrier eta

/- Explicit alternate category, never labelled the original statement. -/
structure TopologicallyRoundedSurface {g : SmoothMetric M} (F : SourceCornerSurface g)
    (C : RoundingBounds F) (eta : M → ℝ) extends RoundedGeometry F C eta where
  isotopy : TopologicalAmbientIsotopy M
  image : (isotopy.stage 1) '' F.image = surface.image
  supported : ∀ t p, p ∉ widthTube g F.seams.carrier eta → isotopy.stage t p = p
  regions : ∀ p, p ∉ F.image →
    let Rold := connectedComponentIn F.imageᶜ p
    let Rnew := connectedComponentIn surface.imageᶜ (isotopy.stage 1 p)
    (isotopy.stage 1) '' Rold = Rnew ∧
      Rnew \ widthTube g F.seams.carrier eta = Rold \ widthTube g F.seams.carrier eta

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

def EqualOrAdjacent (v w : Vertices E) : Prop := v = w ∨ Adjacent E v w
def Apex (u w x : Vertices E) : Prop :=
  x ∈ commonNeighbors E u w ∧ ∀ z ∈ commonNeighbors E u w, EqualOrAdjacent E x z
def ExchangePair (H : Section4.SourceGeometry E) (x u w up down : Vertices E) : Prop :=
  SeifertSurfaces.Section5.Combinatorics.IsExchangePair (oneSkeleton E)
    (vertexGenus E) (areaInfimum E H) x u w up down
def ExchangeComplex (H : Section4.SourceGeometry E) : Prop :=
  Nonempty (Vertices E) ∧ (oneSkeleton.{0} E).Connected ∧ Flag E (complexFaces E) ∧
    IsWellOrder (attainedValues E H) (· < ·) ∧
    (∀ u w, graphDistance E u w = 2 → ∃ x, Apex E u w x) ∧
    (∀ u w, graphDistance E u w = 2 → ∃ x, Apex E u w x ∧
      Section4.complexity E H x < max (Section4.complexity E H u) (Section4.complexity E H w))

def SurfaceVertex (F : IncompressibleSpanningSurface.{0} E) : Vertices E :=
  classOf E (surfaceImageOf E F)
def SurfaceBoundary (F : IncompressibleSpanningSurface.{0} E) : Set E.Carrier :=
  F.1.embedding.toFun '' F.1.surface.boundary

/- No minimizer/production fields occur in this classification. -/
def ConfigurationT0 (A B : IncompressibleSpanningSurface.{0} E) : Prop :=
  Disjoint (SurfaceBoundary E A) (SurfaceBoundary E B) ∧
    Section4.Transverse (spanningAsNeat A.1) (spanningAsNeat B.1)
def ConfigurationT1 (A B : IncompressibleSpanningSurface.{0} E) : Prop :=
  Disjoint (SurfaceBoundary E A) (SurfaceBoundary E B) ∧
    (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.interiorTangencies A.1.embedding B.1.embedding).Nonempty
def ConfigurationT2 (A B : IncompressibleSpanningSurface.{0} E) : Prop :=
  SurfaceBoundary E A = SurfaceBoundary E B

/- Calibrated common control for all four local sectors. Each sector carries
the full RoundingBounds with the same caps and source gain, and its chart
is attached to the actual complementary wedge. Production remains an output. -/
structure PairRoundingControl (g : SmoothMetric M)
    {SA SB : CompactOrientedSurface.{0}} (A : NeatEmbedding SA M) (B : NeatEmbedding SB M) where
  seams : C2Seams M
  seam_exact : seams.carrier = A.image ∩ B.image
  normal : SourceNormalExponential g seams
  etaMax : M → ℝ
  kappa : M → ℝ
  caps_positive : ∀ p ∈ seams.carrier, 0 < etaMax p ∧ 0 < kappa p
  caps_continuous : ContinuousOn etaMax seams.carrier ∧ ContinuousOn kappa seams.carrier
  gain : ℝ → ℝ
  gain_positive : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), 0 < gain theta
  gain_continuous : ContinuousOn gain (Ioc (0 : ℝ) (Real.pi / 2))
  gain_monotone : MonotoneOn gain (Ioc (0 : ℝ) (Real.pi / 2))
  cutoff : SeifertSurfaces.AppendixB.RoundingCutoff
  gain_exact : gain = SeifertSurfaces.AppendixB.angleGain cutoff
  etaLower : ℝ → ℝ → ℝ → ℝ
  kappaLower : ℝ → ℝ → ℝ → ℝ
  lower_positive : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho b,
    0 < rho → 0 < b → 0 < etaLower theta rho b ∧ 0 < kappaLower theta rho b
  lower_monotone : ∀ theta ∈ Ioc (0 : ℝ) (Real.pi / 2),
    ∀ theta' ∈ Ioc (0 : ℝ) (Real.pi / 2), ∀ rho rho' b b',
    0 < rho → 0 < rho' → 0 < b → 0 < b' →
    theta ≤ theta' → rho ≤ rho' → b ≤ b' →
    etaLower theta rho b ≤ etaLower theta' rho' b' ∧
    kappaLower theta rho b ≤ kappaLower theta' rho' b'
  lower_bounds : ∀ p ∈ seams.carrier, ∀ rho b : ℝ, 0 < rho → 0 < b →
    ENNReal.ofReal rho ≤ localReach normal p →
    ENNReal.ofReal b ≤ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.boundaryEDist g p →
    etaLower (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.twoSidedAngle g A B p)
      rho b ≤ etaMax p ∧
    kappaLower (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.twoSidedAngle g A B p)
      rho b ≤ kappa p

  sector : Fin 4 → SourceCornerSurface g
  sector_seams : ∀ k, (sector k).seams.carrier = seams.carrier
  sector_sheets : ∀ k, (sector k).image ⊆ A.image ∪ B.image
  sector_angle : ∀ k p, p ∈ seams.carrier →
    (sector k).theta p = AppendixBOriginalV479.twoSidedAngle g A B p
  sectorBounds : ∀ k, RoundingBounds (sector k)
  sector_caps : ∀ k, (sectorBounds k).etaMax = etaMax ∧
    (sectorBounds k).kappa = kappa ∧ (sectorBounds k).g0 = gain
  boundary_cap : ∀ p ∈ seams.carrier,
    ENNReal.ofReal (2 * etaMax p) ≤ AppendixBOriginalV479.boundaryEDist g p
  sector_neighborhood : ∀ p, p ∈ seams.carrier → Set M
  sector_neighborhood_open : ∀ p hp, IsOpen (sector_neighborhood p hp)
  sector_neighborhood_contains : ∀ p hp, p ∈ sector_neighborhood p hp
  sectorRegion : ∀ p, p ∈ seams.carrier → Fin 4 → Set M
  sector_regions_open : ∀ p hp k, IsOpen (sectorRegion p hp k)
  sector_regions_inside : ∀ p hp k, sectorRegion p hp k ⊆ sector_neighborhood p hp
  sector_regions_disjoint : ∀ p hp, Pairwise (fun i j => Disjoint (sectorRegion p hp i) (sectorRegion p hp j))
  sector_regions_cover : ∀ p hp, (⋃ k, sectorRegion p hp k) =
    sector_neighborhood p hp \ (A.image ∪ B.image)
  sector_frontiers : ∀ p hp k, frontier (sectorRegion p hp k) ∩ sector_neighborhood p hp =
    (sector k).image ∩ sector_neighborhood p hp
  sector_chart_side : ∀ p hp k, ∀ hk : p ∈ (sector k).seams.carrier,
    let W := (sector k).slice p hk
    sector_neighborhood p hp ⊆ W.coordinates.source ∧
    W.coordinates '' sectorRegion p hp k =
      {y ∈ W.coordinates '' sector_neighborhood p hp |
        Real.cot (W.angle (y 0) / 2) * |y 2| < y 1}

def pairGain {g : SmoothMetric M} {SA SB : CompactOrientedSurface.{0}}
    {A : NeatEmbedding SA M} {B : NeatEmbedding SB M} (C : PairRoundingControl g A B)
    (eta : M → ℝ) (γ : SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.ClosedIntersectionComponent
      (A.image ∩ B.image)) : ℝ :=
  SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.curveIntegral g γ
    (fun p => C.gain (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.twoSidedAngle g A B p) * eta p)

def partialDerivative (f : E2 → ℝ) (i : Fin 2) (x : E2) : ℝ :=
  fderiv ℝ f x (coordinateVector 2 i)

structure LinearGraphEquation (f : E2 → ℝ) (domain : Set E2) where
  principal : Fin 2 → Fin 2 → E2 → ℝ
  drift : Fin 2 → E2 → ℝ
  zeroth : E2 → ℝ
  principal_smooth : ∀ i j, ContDiffOn ℝ ∞ (principal i j) domain
  drift_smooth : ∀ i, ContDiffOn ℝ ∞ (drift i) domain
  zeroth_smooth : ContDiffOn ℝ ∞ zeroth domain
  symmetric : ∀ i j x, x ∈ domain → principal i j x = principal j i x
  ellipticity : ℝ
  ellipticity_pos : 0 < ellipticity
  elliptic : ∀ x ∈ domain, ∀ v : E2,
    ellipticity * ‖v‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, principal i j x * v i * v j
  equation : ∀ x ∈ domain,
    (∑ i : Fin 2, ∑ j : Fin 2,
      partialDerivative (fun y => principal i j y * partialDerivative f j y) i x) +
      (∑ i : Fin 2, drift i x * partialDerivative f i x) + zeroth x * f x = 0

def InteriorTangencyResult (A B : IncompressibleSpanningSurface.{0} E) : Prop :=
  ∀ p ∈ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.interiorTangencies
    A.1.embedding B.1.embedding,
    (∃ U : Set E.Carrier, IsOpen U ∧ p ∈ U ∧
      U ∩ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.interiorTangencies
        A.1.embedding B.1.embedding = {p}) ∧
    ∃ c : SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.InteriorGraph A B p,
      Nonempty (LinearGraphEquation
        (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.graphDifference c)
        (Metric.ball 0 c.R)) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ c1 c2 R : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < R ∧ R ≤ c.R ∧
      (∀ x : E2, 0 < ‖x‖ → ‖x‖ < R →
        c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1) ≤
          ‖fderiv ℝ (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.graphDifference c) x‖ ∧
        0 < c1 * ‖x‖ ^ m - c2 * ‖x‖ ^ (m + 1)) ∧
      (∀ x ∈ Metric.ball (0 : E2) R,
        fderiv ℝ (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.graphDifference c) x = 0 ↔ x = 0) ∧
      (∀ V : Set E2, V ∈ 𝓝 (0 : E2) →
        (∃ x ∈ V ∩ Metric.ball 0 R,
          0 < SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.graphDifference c x) ∧
        (∃ x ∈ V ∩ Metric.ball 0 R,
          SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.graphDifference c x < 0))

def CollarTangencyResult {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (D : B1OriginalData g J) : Prop :=
  ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ D.r0 ∧
    (∀ s : Circle, ∀ r : ℝ, 0 < r → r < r0 →
      mfderiv ((𝓡 1).prod 𝓘(ℝ)) 𝓘(ℝ) (fun q : Circle × ℝ => D.f q.1 q.2) (s, r) ≠ 0) ∧
    (SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.collarCriticalPoints D).Finite ∧
    (∀ s ∈ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.collarCriticalPoints D, D.f s 0 = 0) ∧
    (∀ p ∈ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.interiorTangencies
      D.A.1.embedding D.B.1.embedding,
      r0 ≤ SeifertSurfaces.OriginalEndpoints.AppendixBOriginalV479.extendedRadial D r0 p)

end SeifertSurfaces.OriginalEndpoints.Section5
