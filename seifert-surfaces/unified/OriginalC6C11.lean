import NativeWarpedHessian
import DifferentialGeometry.Analysis.Schauder.Holder.Bilinear
import MetricAreaAnalysis.ChartCalculus
import EllipticPdes.Existence.StrongMaximum
import BoundaryFoliation
import C2Analytic
import C12Topology
import GeometricArea

noncomputable section
open Bundle Set Topology MeasureTheory
open scoped Manifold ContDiff BigOperators ENNReal NNReal
namespace SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations

variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel ∞ N]

abbrev Differential (f : S → N) :=
  ∀ p : S, TangentSpace SurfaceModel p →L[ℝ] TangentSpace AmbientModel (f p)

def coordinateDifferential (f : S → N) (D : Differential S f)
    (p : S) (q : N) (x : RVec 2) : RVec 2 →L[ℝ] RVec 3 :=
  (mfderiv AmbientModel 𝓘(ℝ, RVec 3) (extChartAt AmbientModel q)
    (f ((extChartAt SurfaceModel p).symm x))).comp
    ((D ((extChartAt SurfaceModel p).symm x)).comp
      (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel
        (extChartAt SurfaceModel p).symm (range SurfaceModel) x))

def localMapDomain (f : S → N) (p : S) (q : N) : Set (RVec 2) :=
  interior (extChartAt SurfaceModel p).target ∩
    (f ∘ (extChartAt SurfaceModel p).symm) ⁻¹' (extChartAt AmbientModel q).source

/-- Distributional derivative in every source/target chart, with the actual
coordinate expression of the same continuous map and differential. -/
def IsWeakDifferential (f : C(S, N)) (D : Differential S f) : Prop :=
  ∀ (p : S) (q : N), let U := localMapDomain S f p q
    let F := (extChartAt AmbientModel q) ∘ f ∘ (extChartAt SurfaceModel p).symm
    (∀ a : Fin 3, LocallyIntegrableOn (fun x => F x a) U) ∧
    (∀ (a : Fin 3) (i : Fin 2),
      LocallyIntegrableOn (fun x => coordinateDifferential S f D p q x
        (EuclideanSpace.single i 1) a) U) ∧
    ∀ (φ : RVec 2 → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ (a : Fin 3) (i : Fin 2),
      (∫ x in U, F x a * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      -(∫ x in U, coordinateDifferential S f D p q x
        (EuclideanSpace.single i 1) a * φ x)

def weakGram (h : AmbientMetric N) (f : S → N) (D : Differential S f)
    (p : S) (x : RVec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let y := (extChartAt SurfaceModel p).symm x
  let A := (D y).comp (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel
    (extChartAt SurfaceModel p).symm (range SurfaceModel) x)
  fun i j => h.inner (f y) (A (EuclideanSpace.single i 1))
    (A (EuclideanSpace.single j 1))

def weakArea (h : AmbientMetric N) (f : S → N) (D : Differential S f) : ℝ≥0∞ :=
  let P := canonicalPartition S
  ∑ i, ∫⁻ x in (extChartAt SurfaceModel (P.center i)) '' P.piece i,
    ENNReal.ofReal (Real.sqrt (Matrix.det (weakGram S h f D (P.center i) x)))

def weakEnergy (g : SurfaceMetric S) (h : AmbientMetric N)
    (f : S → N) (D : Differential S f) : ℝ≥0∞ :=
  let P := canonicalPartition S
  ∑ i, ∫⁻ x in (extChartAt SurfaceModel (P.center i)) '' P.piece i,
    ENNReal.ofReal ((1 / 2 : ℝ) *
      (∑ a : Fin 2, ∑ b : Fin 2,
        (MetricInChart SurfaceModel g (P.center i) x)⁻¹ a b *
          weakGram S h f D (P.center i) x a b) *
      Real.sqrt (Matrix.det (MetricInChart SurfaceModel g (P.center i) x)))

/-- Finite-energy continuous maps: the weak derivative is real distributional
chart data, and area/energy are actual Gram/Jacobian integrals. -/
structure FiniteEnergyMap (g : SurfaceMetric S) (h : AmbientMetric N) where
  map : C(S, N)
  differential : Differential S map
  weak : IsWeakDifferential S map differential
  finite_energy : weakEnergy S g h map differential < ⊤

/-- Definition C.2 in full, including L1's relative-class area minimality.
L2's chosen metric is explicit, as required in Lemma C.6. -/
structure LemaireMinimizer (g : SurfaceMetric S) (h : AmbientMetric N)
    (f : C(S, N)) (curve : Set N) : Prop where
  boundary : L1BoundaryMonotone f curve
  finite_energy : ∃ D : Differential S f,
    IsWeakDifferential S f D ∧ weakEnergy S g h f D < ⊤ ∧
    D = fun p => mfderiv SurfaceModel AmbientModel f p
  minimizing : ∀ k : FiniteEnergyMap S g h,
    LemaireRelativeHomotopic f k.map curve →
      weakArea S h f (fun p => mfderiv SurfaceModel AmbientModel f p) ≤
        weakArea S h k.map k.differential
  harmonic : HarmonicInterior g h f
  conformal : WeakConformalInterior g h f
  regularity : C2HolderUpToBoundary f

/-- Genuine collar metric charts. The first coordinate is r, and the metric
is dr²+(1-r)² k, with k independent of r. This specifies the ambient metric,
not its Hessian, Christoffel symbols, or their desired consequences. -/
structure WarpedCollar (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ) : Prop where
  epsilon_pos : 0 < ε
  epsilon_lt_one : ε < 1
  smooth_height : ContMDiff AmbientModel 𝓘(ℝ, ℝ) ∞ r
  charts : ∀ q : N, r q < ε →
    ∃ (c : OpenPartialHomeomorph N (RVec 3))
      (K : RVec 2 → Matrix (Fin 2) (Fin 2) ℝ),
      q ∈ c.source ∧ c.source ⊆ {z | r z < ε} ∧
      ContMDiffOn AmbientModel 𝓘(ℝ, RVec 3) ∞ c c.source ∧
      ContMDiffOn 𝓘(ℝ, RVec 3) AmbientModel ∞ c.symm c.target ∧
      (∀ z ∈ c.source, r z = c z 0) ∧
      (∀ z ∈ c.target, ∀ v w : RVec 3,
        let y : RVec 2 := WithLp.toLp 2 (fun i : Fin 2 => z i.succ)
        h.inner (c.symm z)
          (mfderiv 𝓘(ℝ, RVec 3) AmbientModel c.symm z v)
          (mfderiv 𝓘(ℝ, RVec 3) AmbientModel c.symm z w) =
          v 0 * w 0 + (1 - z 0)^2 *
            ∑ i : Fin 2, ∑ j : Fin 2, K y i j * v i.succ * w j.succ) ∧
      (∀ y : RVec 2, ∀ i j : Fin 2, K y i j = K y j i) ∧
      (∀ y : RVec 2, ∀ ξ : Fin 2 → ℝ,
        0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, K y i j * ξ i * ξ j)

/-- Radial means proportional to grad r, specified by its metric-dual
identity. The zero tangent vector is included. -/
def IsRadial (h : AmbientMetric N) (r : N → ℝ) (q : N)
    (v : TangentSpace AmbientModel q) : Prop :=
  ∃ a : ℝ, ∀ w : TangentSpace AmbientModel q,
    h.inner q v w = a * tangentSpaceCastModel 𝓘(ℝ, ℝ) (r q) (mfderiv AmbientModel 𝓘(ℝ, ℝ) r q w)

def covariantHessian (h : AmbientMetric N) (r : N → ℝ) (q : N)
    (v w : TangentSpace AmbientModel q) : ℝ :=
  let c := extChartAt AmbientModel q
  let R := r ∘ c.symm
  let x := c q
  let V := tangentSpaceCastModel 𝓘(ℝ, RVec 3) (c q) (mfderiv AmbientModel 𝓘(ℝ, RVec 3) c q v)
  let W := tangentSpaceCastModel 𝓘(ℝ, RVec 3) (c q) (mfderiv AmbientModel 𝓘(ℝ, RVec 3) c q w)
  fderiv ℝ (fderiv ℝ R) x V W -
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3,
      ChristoffelCoordinate (MetricInChart AmbientModel h q) x k a b *
        fderiv ℝ R x (EuclideanSpace.single k 1) * V a * W b

def sourceChristoffel (g : SurfaceMetric S) (p : S) (x : RVec 2)
    (k i j : Fin 2) : ℝ :=
  let G := MetricInChart SurfaceModel g p
  let U := (extChartAt SurfaceModel p).target
  (1 / 2 : ℝ) * ∑ l : Fin 2, (G x)⁻¹ k l *
    (fderivWithin ℝ (fun y => G y j l) U x (EuclideanSpace.single i 1) +
     fderivWithin ℝ (fun y => G y i l) U x (EuclideanSpace.single j 1) -
     fderivWithin ℝ (fun y => G y i j) U x (EuclideanSpace.single l 1))

def chartLaplacian (g : SurfaceMetric S) (p : S) (v : RVec 2 → ℝ)
    (x : RVec 2) : ℝ :=
  let U := (extChartAt SurfaceModel p).target
  ∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p x)⁻¹ i j *
    (fderivWithin ℝ (fun y => fderivWithin ℝ v U y) U x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      ∑ k : Fin 2, sourceChristoffel S g p x k i j *
        fderivWithin ℝ v U x (EuclideanSpace.single k 1))

def laplacian (g : SurfaceMetric S) (u : S → ℝ) (p : S) : ℝ :=
  chartLaplacian S g p (u ∘ (extChartAt SurfaceModel p).symm)
    (extChartAt SurfaceModel p p)

def pulledHessianTrace (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (f : S → N) (p : S) : ℝ :=
  let x := extChartAt SurfaceModel p p
  let A := mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel
    (extChartAt SurfaceModel p).symm (range SurfaceModel) x
  ∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p x)⁻¹ i j *
    covariantHessian h r (f p)
      (mfderiv SurfaceModel AmbientModel f p (A (EuclideanSpace.single i 1)))
      (mfderiv SurfaceModel AmbientModel f p (A (EuclideanSpace.single j 1)))

structure ScalarC2HolderUpToBoundary (u : S → ℝ) : Prop where
  regular : ContMDiff SurfaceModel 𝓘(ℝ, ℝ) 2 u
  holder_extensions : ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧
    ∀ p : S, ∃ (U : Set (RVec 2)) (F : RVec 2 → ℝ) (K : ℝ≥0),
      IsOpen U ∧ extChartAt SurfaceModel p p ∈ U ∧
      U ∩ range SurfaceModel ⊆ (extChartAt SurfaceModel p).target ∧
      ContDiffOn ℝ 2 F U ∧ HolderOnWith K α (iteratedFDeriv ℝ 2 F) U ∧
      ∀ x ∈ U ∩ range SurfaceModel, F x = u ((extChartAt SurfaceModel p).symm x)

def extendedCoordinates (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2)) :=
  c.toPartialEquiv.trans SurfaceModel.toPartialEquiv

def metricInCoordinates (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (x : RVec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  let E := extendedCoordinates S c
  fun i j => g.inner (E.symm x)
    (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x (EuclideanSpace.single i 1))
    (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x (EuclideanSpace.single j 1))

def christoffelInCoordinates (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (x : RVec 2) (k i j : Fin 2) : ℝ :=
  let G := metricInCoordinates S g c
  let U := (extendedCoordinates S c).target
  (1 / 2 : ℝ) * ∑ l : Fin 2, (G x)⁻¹ k l *
    (fderivWithin ℝ (fun y => G y j l) U x (EuclideanSpace.single i 1) +
     fderivWithin ℝ (fun y => G y i l) U x (EuclideanSpace.single j 1) -
     fderivWithin ℝ (fun y => G y i j) U x (EuclideanSpace.single l 1))

def laplacianInCoordinates (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (v : RVec 2 → ℝ) (x : RVec 2) : ℝ :=
  let U := (extendedCoordinates S c).target
  ∑ i : Fin 2, ∑ j : Fin 2, (metricInCoordinates S g c x)⁻¹ i j *
    (fderivWithin ℝ (fun y => fderivWithin ℝ v U y) U x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      ∑ k : Fin 2, christoffelInCoordinates S g c x k i j *
        fderivWithin ℝ v U x (EuclideanSpace.single k 1))

/-- Every smooth chart in the maximal atlas has smooth locally uniformly
elliptic coefficients and an exact operator identity with no zeroth term. -/
def SmoothLocallyUniformElliptic (g : SurfaceMetric S) : Prop :=
  ∀ c : OpenPartialHomeomorph S (EuclideanHalfSpace 2),
    c ∈ IsManifold.maximalAtlas SurfaceModel ∞ S →
    ∀ p ∈ c.source,
    ∃ (V : Set (RVec 2)) (a : RVec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (b : RVec 2 → Fin 2 → ℝ) (θ A B : ℝ),
      let E := extendedCoordinates S c
      IsOpen V ∧ E p ∈ V ∧ 0 < θ ∧
      (∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) (V ∩ E.target)) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun x => b x i) (V ∩ E.target)) ∧
      (∀ x ∈ V ∩ E.target,
        (∀ i j, a x i j = a x j i ∧ |a x i j| ≤ A) ∧
        (∀ i, |b x i| ≤ B) ∧
        (∀ ξ : Fin 2 → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) ∧
        ∀ v : RVec 2 → ℝ,
          laplacianInCoordinates S g c v x =
            (∑ i, ∑ j, a x i j * fderivWithin ℝ (fun y =>
              fderivWithin ℝ v E.target y) E.target x
              (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
            ∑ i, b x i * fderivWithin ℝ v E.target x (EuclideanSpace.single i 1))


end SeifertSurfaces.AppendixC.OriginalEndpoints

-- Paid private support: NativeC6Bridge
noncomputable section
open Set Topology
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates
universe u
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold AmbientModel (∞ : ℕ∞ω) N]
def ambientNativeChart (q : N) : SmoothAmbientChart N where
  chart := chartAt E3 q
  smooth := contMDiffOn_chart
  inverse_smooth := contMDiffOn_chart_symm

theorem ambientNativeChart_eq (q : N) : (ambientNativeChart q).chart.toPartialEquiv = extChartAt AmbientModel q := by
  simp [ambientNativeChart, extChartAt, OpenPartialHomeomorph.extend]

theorem ambient_native_metric (h : AmbientMetric N) (q : N) :
    actualChartTensor h (ambientNativeChart q) = MetricInChart AmbientModel h q := by
  funext x i j
  simp [actualChartTensor, ambientNativeChart, inverseChartDifferential,
    MetricInChart, coordinateVector, extChartAt, OpenPartialHomeomorph.extend,
    NormedSpace.fromTangentSpace, tangentSpaceCastModel, ContinuousLinearMap.comp_apply]
  rfl

theorem native_christoffel (g : MetricTensor) (x : E3) (a b k : Fin 3)
    (hs : ∀ z i j, g z i j = g z j i) :
    christoffel g x a b k = ChristoffelCoordinate g x k a b := by
  simp only [christoffel, ChristoffelCoordinate, partial3, coordinateVector, hs]



theorem covariant_hessian_chart_quadratic
    (h : AmbientMetric N) (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r)
    (q : N) (v : TangentSpace AmbientModel q) :
    covariantHessian h r q v v =
      hessianQuadratic (actualChartTensor h (ambientNativeChart q))
        (r ∘ (ambientNativeChart q).chart.symm) ((ambientNativeChart q).chart q)
        (chartDifferential (ambientNativeChart q) q v) := by
  have hq : q ∈ (ambientNativeChart q).chart.source := mem_chart_source E3 q
  have hx : (ambientNativeChart q).chart q ∈ (ambientNativeChart q).chart.target :=
    (ambientNativeChart q).chart.map_source hq
  have hR : ContDiffAt ℝ 2 (r ∘ (ambientNativeChart q).chart.symm)
      ((ambientNativeChart q).chart q) := by
    have hi := (ambientNativeChart q).inverse_smooth.contMDiffAt
      ((ambientNativeChart q).chart.open_target.mem_nhds hx)
    exact ((hr.of_le (by norm_num)).contMDiffAt.comp _ (hi.of_le (by norm_num))).contDiffAt
  have hs : ∀ z i j, MetricInChart AmbientModel h q z i j =
      MetricInChart AmbientModel h q z j i := fun _ _ _ => h.symm _ _ _
  have hh := hessian_quadratic_frechet (MetricInChart AmbientModel h q)
    (r ∘ (ambientNativeChart q).chart.symm) ((ambientNativeChart q).chart q)
    (chartDifferential (ambientNativeChart q) q v) hs hR
  rw [ambient_native_metric] at ⊢
  rw [hh]
  simp [covariantHessian, ambientNativeChart, chartDifferential, coordinateVector,
    extChartAt, OpenPartialHomeomorph.extend, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel]
  rfl



theorem native_collar_hessian_formula
    (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (q : N) (hq : r q < ε) :
    ∃ (d : SmoothAmbientChart N) (K : E2 → Matrix (Fin 2) (Fin 2) ℝ),
      q ∈ d.chart.source ∧
      (∀ z ∈ d.chart.source, r z = d.chart z 0) ∧
      (∀ z ∈ d.chart.target, ∀ v w : E3,
        coordinateInner (actualChartTensor h d) z v w =
          v 0 * w 0 + (1 - z 0)^2 *
            ∑ i : Fin 2, ∑ j : Fin 2,
              K (levelCoordinates z) i j * v i.succ * w j.succ) ∧
      ∀ v : TangentSpace AmbientModel q,
        covariantHessian h r q v v =
          (r q - 1) * ∑ i : Fin 2, ∑ j : Fin 2,
            K (levelCoordinates (d.chart q)) i j *
              (chartDifferential d q v) i.succ * (chartDifferential d q v) j.succ := by
  obtain ⟨c, K, hqc, hsrc, hc, hci, hrc, hm, hs, hp⟩ := collar.charts q hq
  let d : SmoothAmbientChart N := ⟨c, hc, hci⟩
  have hl (z : E3) : levelCoordinates z = WithLp.toLp 2 (fun i : Fin 2 => z i.succ) := by
    ext i
    fin_cases i <;> simp [levelCoordinates, coordinateVector, EuclideanSpace.single,
      PiLp.single_apply, PiLp.add_apply, PiLp.smul_apply]
  have hmetric : ∀ z ∈ d.chart.target, ∀ v w : E3,
      coordinateInner (actualChartTensor h d) z v w =
        v 0 * w 0 + (1 - z 0)^2 *
          ∑ i : Fin 2, ∑ j : Fin 2,
            K (levelCoordinates z) i j * v i.succ * w j.succ := by
    intro z hz v w
    rw [actual_coordinate_inner]
    have hh := hm z hz v w
    rw [← hl] at hh
    exact hh
  refine ⟨d, K, hqc, hrc, hmetric, ?_⟩
  intro v
  let e := ambientNativeChart q
  have hqe : q ∈ e.chart.source := mem_chart_source E3 q
  have hye : e.chart q ∈ e.chart.target := e.chart.map_source hqe
  have heinv : e.chart.symm (e.chart q) = q := e.chart.left_inv hqe
  rw [covariant_hessian_chart_quadratic h r collar.smooth_height]
  rw [radial_hessian_chart_transport r d e hrc (e.chart q) hye (by rw [heinv]; exact hqc)]
  have hcoord : r ∘ d.chart.symm =ᶠ[𝓝 (d.chart q)] (fun z : E3 => z 0) := by
    filter_upwards [d.chart.open_target.mem_nhds (d.chart.map_source hqc)] with z hz
    rw [Function.comp_apply, hrc _ (d.chart.map_target hz), d.chart.right_inv hz]
  have hgerm (G : MetricTensor) (R T : E3 → ℝ) (x v : E3)
      (heq : R =ᶠ[𝓝 x] T) : hessianQuadratic G R x v = hessianQuadratic G T x v := by
    have hfirst (a : Fin 3) : partial3 R x a = partial3 T x a :=
      congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) heq.fderiv_eq
    have hsecond (a b : Fin 3) : partial3 (fun z => partial3 R z b) x a =
        partial3 (fun z => partial3 T z b) x a := by
      have hn : (fun z => partial3 R z b) =ᶠ[𝓝 x] (fun z => partial3 T z b) :=
        heq.fderiv.mono (fun z hz => congrArg
        (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 b)) hz)
      exact congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hn.fderiv_eq
    simp only [hessianQuadratic, hessianCoefficient, hfirst, hsecond]
  rw [heinv]
  rw [hgerm _ _ _ _ _ hcoord, linear_warped_coordinate_hessian d K hmetric
    (d.chart q) (d.chart.map_source hqc)]
  have hMD (c : SmoothAmbientChart N) : c.chart.MDifferentiable AmbientModel AmbientModel :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have ht : fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart q)
      (chartDifferential e q v) = chartDifferential d q v := by
    have hh := mfderiv_comp (e.chart q)
      ((hMD d).mdifferentiableAt (by rw [heinv]; exact hqc))
      ((hMD e).mdifferentiableAt_symm hye)
    rw [mfderiv_eq_fderiv] at hh
    change fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart q) =
      (mfderiv AmbientModel AmbientModel d.chart (e.chart.symm (e.chart q))).comp
        (mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q)) at hh
    rw [hh]
    have hInv := congrArg (fun L : E3 →L[ℝ] E3 => L v) ((hMD e).symm_comp_deriv hqe)
    change (mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q))
      ((mfderiv AmbientModel AmbientModel e.chart q) v) = v at hInv
    change (mfderiv AmbientModel AmbientModel d.chart (e.chart.symm (e.chart q)))
      ((mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q))
        ((mfderiv AmbientModel AmbientModel e.chart q) v)) =
      (mfderiv AmbientModel AmbientModel d.chart q) v
    rw [hInv, heinv]
  rw [ht, ← hrc q hqc]



theorem radial_iff_collar_coordinates
    (h : AmbientMetric N) (r : N → ℝ)
    (d : SmoothAmbientChart N) (K : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ z ∈ d.chart.source, r z = d.chart z 0)
    (hmetric : ∀ z ∈ d.chart.target, ∀ v w : E3,
      coordinateInner (actualChartTensor h d) z v w =
        v 0 * w 0 + (1 - z 0)^2 *
          ∑ i : Fin 2, ∑ j : Fin 2,
            K (levelCoordinates z) i j * v i.succ * w j.succ)
    (q : N) (hq : q ∈ d.chart.source) (v : TangentSpace AmbientModel q) :
    IsRadial h r q v ↔ ∀ i : Fin 2, (chartDifferential d q v) i.succ = 0 := by
  classical
  have hMD : d.chart.MDifferentiable AmbientModel AmbientModel :=
    ⟨d.smooth.mdifferentiableOn (by simp), d.inverse_smooth.mdifferentiableOn (by simp)⟩
  have hy := d.chart.map_source hq
  have hInv (w : TangentSpace AmbientModel q) :
      inverseChartDifferential d (d.chart q) (chartDifferential d q w) = w := by
    exact congrArg (fun L : E3 →L[ℝ] E3 => L w) (hMD.symm_comp_deriv hq)
  have hComp (w : E3) : chartDifferential d q (inverseChartDifferential d (d.chart q) w) = w := by
    have hh := hMD.comp_symm_deriv hy
    rw [d.chart.left_inv hq] at hh
    exact congrArg (fun L : E3 →L[ℝ] E3 => L w) hh
  have hinner (v w : TangentSpace AmbientModel q) :
      h.inner q v w = coordinateInner (actualChartTensor h d) (d.chart q)
        (chartDifferential d q v) (chartDifferential d q w) := by
    rw [actual_coordinate_inner, hInv, hInv, d.chart.left_inv hq]
  have hheight (w : TangentSpace AmbientModel q) :
      tangentSpaceCastModel 𝓘(ℝ, ℝ) (r q) (mfderiv AmbientModel 𝓘(ℝ, ℝ) r q w) =
        (chartDifferential d q w) 0 := by
    let P : E3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
    have heq : r =ᶠ[𝓝 q] P ∘ d.chart := by
      filter_upwards [d.chart.open_source.mem_nhds hq] with z hz
      exact hr z hz
    rw [heq.mfderiv_eq, mfderiv_comp q P.differentiableAt.mdifferentiableAt
      (hMD.mdifferentiableAt hq), mfderiv_eq_fderiv, P.fderiv]
    rfl
  constructor
  · rintro ⟨a, ha⟩
    let V := chartDifferential d q v
    let W : E3 := V - V 0 • coordinateVector 3 0
    have hW0 : W 0 = 0 := by
      simp [W, coordinateVector, EuclideanSpace.single, PiLp.single_apply,
        PiLp.sub_apply, PiLp.smul_apply]
    have hWi (i : Fin 2) : W i.succ = V i.succ := by
      fin_cases i <;> simp [W, coordinateVector, EuclideanSpace.single,
        PiLp.single_apply, PiLp.sub_apply, PiLp.smul_apply]
    have hvw : coordinateInner (actualChartTensor h d) (d.chart q) V W = 0 := by
      have hh := ha (inverseChartDifferential d (d.chart q) W)
      rw [hinner v (inverseChartDifferential d (d.chart q) W),
        hheight (inverseChartDifferential d (d.chart q) W), hComp W] at hh
      simpa [V, hW0] using hh
    have hww : coordinateInner (actualChartTensor h d) (d.chart q) W W = 0 := by
      rw [hmetric _ hy, hW0]
      rw [hmetric _ hy, hW0] at hvw
      simp only [hWi, mul_zero, zero_add] at hvw ⊢
      exact hvw
    have hW : W = 0 := by
      by_contra hne
      exact (ne_of_gt ((SeifertSurfaces.OriginalEndpoints.A4GeometryBridges.actual_chart_tensor_metric_properties h d).2.2 _ hy W hne)) hww
    intro i
    rw [← hWi i, hW]
    rfl
  · intro hv
    refine ⟨(chartDifferential d q v) 0, ?_⟩
    intro w
    rw [hinner, hmetric _ hy, hheight]
    simp [hv]



theorem native_collar_hessian_sign_radial
    (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (q : N) (hq : r q < ε) (v : TangentSpace AmbientModel q) :
    covariantHessian h r q v v ≤ 0 ∧
      (covariantHessian h r q v v = 0 ↔ IsRadial h r q v) := by
  classical
  obtain ⟨d, K, hqd, hr, hmetric, hformula⟩ := native_collar_hessian_formula h r ε collar q hq
  have hrad := radial_iff_collar_coordinates h r d K hr hmetric q hqd v
  let V := chartDifferential d q v
  have hless : r q < 1 := hq.trans collar.epsilon_lt_one
  by_cases hv : ∀ i : Fin 2, V i.succ = 0
  · have hzero : covariantHessian h r q v v = 0 := by
      rw [hformula v]
      change (r q - 1) * (∑ i : Fin 2, ∑ j : Fin 2,
        K (levelCoordinates (d.chart q)) i j * V i.succ * V j.succ) = 0
      simp [hv]
    exact ⟨hzero.le, by rw [hzero]; exact iff_of_true rfl (hrad.mpr hv)⟩
  · let W : E3 := V - V 0 • coordinateVector 3 0
    have hW0 : W 0 = 0 := by
      simp [W, coordinateVector, EuclideanSpace.single, PiLp.single_apply,
        PiLp.sub_apply, PiLp.smul_apply]
    have hWi (i : Fin 2) : W i.succ = V i.succ := by
      fin_cases i <;> simp [W, coordinateVector, EuclideanSpace.single,
        PiLp.single_apply, PiLp.sub_apply, PiLp.smul_apply]
    have hWne : W ≠ 0 := by
      intro hW
      apply hv
      intro i
      rw [← hWi i, hW]
      rfl
    have hpositive := (SeifertSurfaces.OriginalEndpoints.A4GeometryBridges.actual_chart_tensor_metric_properties h d).2.2
      (d.chart q) (d.chart.map_source hqd) W hWne
    rw [hmetric _ (d.chart.map_source hqd), hW0] at hpositive
    simp only [hWi, zero_mul, zero_add] at hpositive
    have hQ : 0 < ∑ i : Fin 2, ∑ j : Fin 2,
        K (levelCoordinates (d.chart q)) i j * V i.succ * V j.succ := by
      apply pos_of_mul_pos_right hpositive
      exact sq_nonneg _
    have hnegative : covariantHessian h r q v v < 0 := by
      rw [hformula v]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hless) hQ
    refine ⟨hnegative.le, iff_of_false (ne_of_lt hnegative) ?_⟩
    exact fun ha => hv (hrad.mp ha)

end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: OperatorAlgebra
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface)
/-- The no-zeroth-order decomposition uses the actual inverse metric and its
actual Christoffel coefficients; no coefficient certificate is an input. -/
theorem actual_operator_decomposition (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (v : RVec 2 → ℝ) (x : RVec 2) :
    laplacianInCoordinates S g c v x =
      (∑ i : Fin 2, ∑ j : Fin 2, (metricInCoordinates S g c x)⁻¹ i j *
        fderivWithin ℝ (fun y => fderivWithin ℝ v (extendedCoordinates S c).target y)
          (extendedCoordinates S c).target x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
      ∑ k : Fin 2, (-(∑ i : Fin 2, ∑ j : Fin 2,
        (metricInCoordinates S g c x)⁻¹ i j * christoffelInCoordinates S g c x k i j)) *
          fderivWithin ℝ v (extendedCoordinates S c).target x (EuclideanSpace.single k 1) := by
  classical
  unfold laplacianInCoordinates
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring


theorem actual_surface_metric_properties (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hc : c ∈ IsManifold.maximalAtlas SurfaceModel (∞ : ℕ∞ω) S) :
    (∀ i j, ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => metricInCoordinates S g c x i j)
      (extendedCoordinates S c).target) ∧
    (∀ x i j, metricInCoordinates S g c x i j = metricInCoordinates S g c x j i) ∧
    ∀ x ∈ (extendedCoordinates S c).target, (metricInCoordinates S g c x).PosDef := by
  classical
  let E := extendedCoordinates S c
  have hE : E = c.extend SurfaceModel := rfl
  have hU : UniqueDiffOn ℝ E.target := by
    rw [hE, c.extend_target]
    exact SurfaceModel.uniqueDiffOn_preimage c.open_target
  have hUM : UniqueMDiffOn 𝓘(ℝ, RVec 2) E.target := hU.uniqueMDiffOn
  have hi : ContMDiffOn 𝓘(ℝ, RVec 2) SurfaceModel (∞ : ℕ∞ω) E.symm E.target := by
    rw [hE, c.extend_target']
    exact contMDiffOn_extend_symm hc
  have hvector (v : RVec 2) :
      ContMDiffOn 𝓘(ℝ, RVec 2) SurfaceModel.tangent (∞ : ℕ∞ω)
        (fun x => Bundle.TotalSpace.mk' (RVec 2) (E.symm x)
          (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x v)) E.target := by
    have hconst : ContMDiff 𝓘(ℝ, RVec 2) (𝓘(ℝ, RVec 2).tangent) (∞ : ℕ∞ω)
        (fun x : RVec 2 => Bundle.TotalSpace.mk' (RVec 2) x
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v)) := by
      apply (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (E := RVec 2)
        (V := fun x : RVec 2 => (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v)).mpr
      change ContDiff ℝ (∞ : ℕ∞ω) (fun _ : RVec 2 => v)
      exact contDiff_const
    have hv := (hi.contMDiffOn_tangentMapWithin (m := (∞ : ℕ∞ω)) (by simp) hUM).comp
      hconst.contMDiffOn (s := E.target) (fun _ hx => hx)
    exact hv
  refine ⟨?_, ?_, ?_⟩
  · intro i j x hx
    have hh : ContMDiffWithinAt 𝓘(ℝ, RVec 2) (SurfaceModel.prod 𝓘(ℝ, ℝ)) (∞ : ℕ∞ω)
        (fun x => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial S ℝ) (E.symm x)
          (metricInCoordinates S g c x i j)) E.target x := by
      apply ContMDiffWithinAt.clm_bundle_apply₂ (F₁ := RVec 2) (F₂ := RVec 2)
      · exact g.contMDiff.contMDiffAt.comp_contMDiffWithinAt x (hi x hx)
      · exact hvector (EuclideanSpace.single i 1) x hx
      · exact hvector (EuclideanSpace.single j 1) x hx
    exact (Bundle.contMDiffWithinAt_totalSpace.mp hh).2.contDiffWithinAt
  · intro x i j
    exact g.symm _ _ _
  · intro x hx
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j
      change star (metricInCoordinates S g c x j i) = metricInCoordinates S g c x i j
      simpa only [star_trivial, metricInCoordinates] using
        g.symm (E.symm x)
          (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x (EuclideanSpace.single j 1))
          (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x (EuclideanSpace.single i 1))
    · intro ξ hξ
      let v : RVec 2 := WithLp.toLp 2 ξ
      have hv : v ≠ 0 := fun hv => hξ (WithLp.toLp_injective 2 hv)
      let A : RVec 2 →L[ℝ] TangentSpace SurfaceModel (E.symm x) :=
        mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm E.target x
      have hsame : A = mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel E.symm (range SurfaceModel) x := by
        have hq : E.symm x ∈ c.source := by
          have hh := E.map_target hx
          simpa [hE, c.extend_source] using hh
        have hn := c.extend_target_eventuallyEqSet (I := SurfaceModel) hq
        rw [← hE, E.right_inv hx] at hn
        exact mfderivWithin_congr_set hn
      have hinv : A.IsInvertible := by
        rw [hsame]
        exact isInvertible_mfderivWithin_extend_symm
          (IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp) hc) (by rw [← hE]; exact hx)
      have hAv : A v ≠ 0 := fun hz => hv (hinv.injective (hz.trans (map_zero _).symm))
      have hp := g.pos (E.symm x) (A v) hAv
      have hsum : (∑ i : Fin 2, ξ i • EuclideanSpace.single i 1) = v := by
        ext i
        fin_cases i <;> simp [v, EuclideanSpace.single, Pi.single_apply, Fin.sum_univ_succ]
      have hA : A v = ∑ i : Fin 2, ξ i • A (EuclideanSpace.single i 1) := by
        rw [← hsum]
        simp only [map_sum, map_smul]
      have hquad : star ξ ⬝ᵥ ((metricInCoordinates S g c x) *ᵥ ξ) =
          g.inner (E.symm x) (A v) (A v) := by
        rw [hA, map_sum]
        simp only [map_smul, sum_apply, smul_apply, map_sum, smul_eq_mul]
        simp only [Finset.mul_sum]
        unfold Matrix.mulVec dotProduct
        simp only [Pi.star_apply, star_trivial, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        change ξ i * (metricInCoordinates S g c x i j * ξ j) =
          ξ j * (ξ i * g.inner (E.symm x) (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single j 1)))
        change ξ i * ((g.inner (E.symm x) (A (EuclideanSpace.single i 1))
          (A (EuclideanSpace.single j 1))) * ξ j) =
          ξ j * (ξ i * (g.inner (E.symm x) (A (EuclideanSpace.single i 1))
            (A (EuclideanSpace.single j 1))))
        ring
      rw [hquad]
      exact hp



theorem actual_inverse_metric_smooth (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hc : c ∈ IsManifold.maximalAtlas SurfaceModel (∞ : ℕ∞ω) S) :
    ∀ i j, ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => (metricInCoordinates S g c x)⁻¹ i j)
      (extendedCoordinates S c).target := by
  classical
  obtain ⟨hG, hs, hp⟩ := actual_surface_metric_properties S g c hc
  have hdet : ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => (metricInCoordinates S g c x).det)
      (extendedCoordinates S c).target := by
    simpa only [Matrix.det_fin_two] using ((hG 0 0).mul (hG 1 1)).sub
      ((hG 0 1).mul (hG 1 0))
  have hdi := hdet.inv (fun x hx => ne_of_gt (hp x hx).det_pos)
  intro i j
  have heq : (fun x => (metricInCoordinates S g c x)⁻¹ i j) =
      (fun x => (metricInCoordinates S g c x).det⁻¹ *
        (metricInCoordinates S g c x).adjugate i j) := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  rw [heq]
  apply hdi.mul
  simp_rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · simpa using hG 1 1
  · simpa using (hG 0 1).neg
  · simpa using (hG 1 0).neg
  · simpa using hG 0 0

theorem actual_christoffel_smooth (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hc : c ∈ IsManifold.maximalAtlas SurfaceModel (∞ : ℕ∞ω) S) :
    ∀ k i j, ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => christoffelInCoordinates S g c x k i j)
      (extendedCoordinates S c).target := by
  classical
  have hG := (actual_surface_metric_properties S g c hc).1
  have hInv := actual_inverse_metric_smooth S g c hc
  have hU : UniqueDiffOn ℝ (extendedCoordinates S c).target := by
    change UniqueDiffOn ℝ (c.extend SurfaceModel).target
    rw [c.extend_target]
    exact SurfaceModel.uniqueDiffOn_preimage c.open_target
  intro k i j
  unfold christoffelInCoordinates
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro l hl
  apply (hInv k l).mul
  apply ContDiffOn.sub
  · apply ContDiffOn.add
    · exact ((hG j l).fderivWithin hU (by simp)).clm_apply contDiffOn_const
    · exact ((hG i l).fderivWithin hU (by simp)).clm_apply contDiffOn_const
  · exact ((hG i j).fderivWithin hU (by simp)).clm_apply contDiffOn_const

theorem actual_drift_smooth (g : SurfaceMetric S)
    (c : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hc : c ∈ IsManifold.maximalAtlas SurfaceModel (∞ : ℕ∞ω) S) :
    ∀ k, ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => -(∑ i : Fin 2, ∑ j : Fin 2,
      (metricInCoordinates S g c x)⁻¹ i j * christoffelInCoordinates S g c x k i j))
        (extendedCoordinates S c).target := by
  classical
  intro k
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact (actual_inverse_metric_smooth S g c hc i j).mul
    (actual_christoffel_smooth S g c hc k i j)



theorem positive_matrix_two_elliptic_bound
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.PosDef)
    (δ T : ℝ) (hT : 0 < T) (hdet : δ ≤ A.det) (htrace : A.trace ≤ T)
    (ξ : Fin 2 → ℝ) :
    (δ / T) * ∑ i : Fin 2, ξ i ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      A i j * ξ i * ξ j := by
  classical
  let Q := ∑ i : Fin 2, ∑ j : Fin 2, A i j * ξ i * ξ j
  have hQ : 0 ≤ Q := by
    by_cases hz : ξ = 0
    · simp [Q, hz]
    · have hp := hA.dotProduct_mulVec_pos hz
      convert hp.le using 1
      simp only [Q, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      ring
  have hs : A 0 1 = A 1 0 := by
    have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 1 0) hA.isHermitian
    simpa [Matrix.conjTranspose_apply] using hh
  have hidentity : A.det * (∑ i : Fin 2, ξ i ^ 2) ≤ A.trace * Q := by
    simp only [Q, Matrix.trace, Matrix.diag, Matrix.det_fin_two,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one, hs]
    nlinarith [sq_nonneg (A 0 0 * ξ 0 + A 1 0 * ξ 1),
      sq_nonneg (A 1 0 * ξ 0 + A 1 1 * ξ 1)]
  have hsum : 0 ≤ ∑ i : Fin 2, ξ i ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh : δ * (∑ i : Fin 2, ξ i ^ 2) ≤ T * Q :=
    (mul_le_mul_of_nonneg_right hdet hsum).trans
      (hidentity.trans (mul_le_mul_of_nonneg_right htrace hQ))
  have hcancel : T * ((δ / T) * (∑ i : Fin 2, ξ i ^ 2)) =
      δ * (∑ i : Fin 2, ξ i ^ 2) := by
    field_simp
  change (δ / T) * (∑ i : Fin 2, ξ i ^ 2) ≤ Q
  apply (mul_le_mul_iff_right₀ hT).mp
  nlinarith



theorem actual_metric_locally_uniform_elliptic (g : SurfaceMetric S) :
    SmoothLocallyUniformElliptic S g := by
  classical
  intro c hc p hp
  let E := extendedCoordinates S c
  let U := E.target
  let a : RVec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun x => (metricInCoordinates S g c x)⁻¹
  let b : RVec 2 → Fin 2 → ℝ := fun x k => -(∑ i : Fin 2, ∑ j : Fin 2,
    (metricInCoordinates S g c x)⁻¹ i j * christoffelInCoordinates S g c x k i j)
  let x₀ := E p
  have hsrc : p ∈ E.source := by
    change p ∈ (c.extend SurfaceModel).source
    simpa [c.extend_source] using hp
  have hx : x₀ ∈ U := E.map_source hsrc
  have ha := actual_inverse_metric_smooth S g c hc
  have hb := actual_drift_smooth S g c hc
  have hpd (x : RVec 2) (hx : x ∈ U) : (a x).PosDef :=
    ((actual_surface_metric_properties S g c hc).2.2 x hx).inv
  have hd : ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => (a x).det) U := by
    simpa only [Matrix.det_fin_two] using ((ha 0 0).mul (ha 1 1)).sub ((ha 0 1).mul (ha 1 0))
  have ht : ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => (a x).trace) U := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_succ] using (ha 0 0).add (ha 1 1)
  let δ := (a x₀).det / 2
  let T := (a x₀).trace + 1
  let A := |a x₀ 0 0| + |a x₀ 0 1| + |a x₀ 1 0| + |a x₀ 1 1| + 1
  let B := |b x₀ 0| + |b x₀ 1| + 1
  have hδ : 0 < δ := div_pos (hpd x₀ hx).det_pos (by norm_num)
  have hδlt : δ < (a x₀).det := by dsimp [δ]; linarith [(hpd x₀ hx).det_pos]
  have hT : 0 < T := by
    have h0 := (hpd x₀ hx).diag_pos (i := 0)
    have h1 := (hpd x₀ hx).diag_pos (i := 1)
    dsimp [T]
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_succ, Fin.sum_univ_zero,
      add_zero, Fin.succ_zero_eq_one]
    linarith
  have hA (i j : Fin 2) : |a x₀ i j| < A := by
    fin_cases i <;> fin_cases j <;> dsimp [A] <;>
      linarith [abs_nonneg (a x₀ 0 0), abs_nonneg (a x₀ 0 1),
        abs_nonneg (a x₀ 1 0), abs_nonneg (a x₀ 1 1)]
  have hB (k : Fin 2) : |b x₀ k| < B := by
    fin_cases k <;> dsimp [B] <;>
      linarith [abs_nonneg (b x₀ 0), abs_nonneg (b x₀ 1)]
  have hea : ∀ᶠ x in 𝓝[U] x₀, ∀ i j : Fin 2, |a x i j| < A := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_order.mp ((ha i j x₀ hx).continuousWithinAt.abs)).2 A (hA i j)
  have heb : ∀ᶠ x in 𝓝[U] x₀, ∀ k : Fin 2, |b x k| < B := by
    apply Filter.eventually_all.mpr
    intro k
    exact (tendsto_order.mp ((hb k x₀ hx).continuousWithinAt.abs)).2 B (hB k)
  have hed : ∀ᶠ x in 𝓝[U] x₀, δ < (a x).det :=
    (tendsto_order.mp (hd x₀ hx).continuousWithinAt).1 δ hδlt
  have het : ∀ᶠ x in 𝓝[U] x₀, (a x).trace < T :=
    (tendsto_order.mp (ht x₀ hx).continuousWithinAt).2 T (lt_add_one _)
  have hall : {x | (∀ i j : Fin 2, |a x i j| ≤ A) ∧
      (∀ k : Fin 2, |b x k| ≤ B) ∧ δ ≤ (a x).det ∧ (a x).trace ≤ T} ∈ 𝓝[U] x₀ := by
    filter_upwards [hea, heb, hed, het] with x hxA hxB hxd hxt
    exact ⟨fun i j => (hxA i j).le, fun k => (hxB k).le, hxd.le, hxt.le⟩
  obtain ⟨W, hW, hWU⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hall
  obtain ⟨V, hVW, hV, hxV⟩ := mem_nhds_iff.mp hW
  refine ⟨V, a, b, δ / T, A, B, hV, hxV, div_pos hδ hT,
    fun i j => (ha i j).mono inter_subset_right,
    fun k => (hb k).mono inter_subset_right, ?_⟩
  intro x hxV
  have hxU : x ∈ U := hxV.2
  obtain ⟨hxA, hxB, hxd, hxt⟩ := hWU ⟨hVW hxV.1, hxV.2⟩
  refine ⟨?_, hxB, ?_, ?_⟩
  · intro i j
    have hs := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M j i) (hpd x hxU).isHermitian
    refine ⟨?_, hxA i j⟩
    simpa [Matrix.conjTranspose_apply] using hs
  · intro ξ
    exact positive_matrix_two_elliptic_bound (a x) (hpd x hxU) δ T hT hxd hxt ξ
  · intro v
    exact actual_operator_decomposition S g c v x

end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: EuclideanHolderComposition
noncomputable section
open Set Topology Filter
open scoped ContDiff BigOperators ENNReal NNReal
namespace SeifertSurfaces.PrivateHelpers.C6Native
open DifferentialGeometry.Analysis.Schauder
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
theorem second_derivative_composition_apply (R : V → ℝ) (F : E → V) (x v w : E)
    (hF : ContDiffAt ℝ 2 F x) (hR : ContDiffAt ℝ 2 R (F x)) :
    fderiv ℝ (fderiv ℝ (R ∘ F)) x v w =
      fderiv ℝ (fderiv ℝ R) (F x) (fderiv ℝ F x v) (fderiv ℝ F x w) +
      fderiv ℝ R (F x) (fderiv ℝ (fderiv ℝ F) x v w) := by
  have hdF : DifferentiableAt ℝ F x := hF.differentiableAt (by norm_num)
  have hdr' : DifferentiableAt ℝ (fderiv ℝ R) (F x) :=
    (hR.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdF' : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfirst : (fun z => fderiv ℝ (R ∘ F) z w) =ᶠ[𝓝 x]
      (fun z => fderiv ℝ R (F z) (fderiv ℝ F z w)) := by
    filter_upwards [hF.eventually (by norm_num),
      hF.continuousAt.eventually (hR.eventually (by norm_num))] with z hFz hrz
    rw [fderiv_comp z (hrz.differentiableAt (by norm_num))
      (hFz.differentiableAt (by norm_num))]
    rfl
  have hleft := fderiv_clm_apply
    (((hR.comp x hF).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)) (differentiableAt_const w)
  have hright := fderiv_clm_apply (hdr'.comp x hdF)
    (hdF'.clm_apply (differentiableAt_const w))
  dsimp only [Function.comp_def] at hright
  have heq := hfirst.fderiv_eq (𝕜 := ℝ)
  have hchain := fderiv_comp x hdr' hdF
  dsimp only [Function.comp_def] at hchain
  rw [hleft, hright, hchain] at heq
  have heqv := congrArg (fun A : E →L[ℝ] ℝ => A v) heq
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at heqv
  have hFw := fderiv_clm_apply hdF' (differentiableAt_const w)
  rw [hFw] at heqv
  have hz : fderiv ℝ (fun _ : E => w) x = 0 := (hasFDerivAt_const w x).fderiv
  simp only [hz, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add] at heqv
  simpa only [add_comm] using heqv

theorem second_composition_component_contDiffAt (R : V → ℝ) (F : E → V) (x v w : E)
    (hF : ContDiffAt ℝ 2 F x) (hR : ContDiffAt ℝ 3 R (F x)) :
    ContDiffAt ℝ 1 (fun z => fderiv ℝ (fderiv ℝ R) (F z)
      (fderiv ℝ F z v) (fderiv ℝ F z w)) x := by
  have hB := (hR.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)
  have hD := hF.fderiv_right (m := 1) (by norm_num)
  exact ((hB.comp x (hF.of_le (by norm_num))).clm_apply
    (hD.clm_apply contDiffAt_const)).clm_apply (hD.clm_apply contDiffAt_const)
theorem holderOn_of_dist_bound {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (α K : ℝ≥0) (H : X → Y) (U : Set X)
    (h : ∀ y ∈ U, ∀ z ∈ U, dist (H y) (H z) ≤ (K : ℝ) * dist y z ^ (α : ℝ)) :
    HolderOnWith K α H U := by
  intro y hy z hz
  rw [edist_dist, edist_dist, ← (ENNReal.ofReal_coe_nnreal (p := K)),
    ENNReal.ofReal_rpow_of_nonneg (dist_nonneg) α.coe_nonneg,
    ← ENNReal.ofReal_mul K.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h y hy z hz)

theorem holder_second_composition_component
    (R : V → ℝ) (F : E → V) (U : Set E) (hU : IsOpen U)
    (x v w : E) (hx : x ∈ U) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hF : ContDiffOn ℝ 2 F U) (hR : ContDiffAt ℝ 3 R (F x))
    (α K : ℝ≥0) (hα : α ≤ 1)
    (hholder : HolderOnWith K α (iteratedFDeriv ℝ 2 F) U) :
    ∃ (W : Set E) (L : ℝ≥0), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      HolderOnWith L α (fun z => fderiv ℝ (fderiv ℝ (R ∘ F)) z v w) W := by
  have hFx := hF.contDiffAt (hU.mem_nhds hx)
  let A := fun z => fderiv ℝ (fderiv ℝ R) (F z) (fderiv ℝ F z v) (fderiv ℝ F z w)
  let B := fun z => fderiv ℝ R (F z)
  let C := fun z => fderiv ℝ (fderiv ℝ F) z v w
  have hA : ContDiffAt ℝ 1 A x := second_composition_component_contDiffAt R F x v w hFx hR
  have hB : ContDiffAt ℝ 1 B x :=
    ((hR.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).fderiv_right
      (m := 1) (by norm_num)).comp x (hFx.of_le (by norm_num))
  have hC : ContinuousAt C x :=
    ((((hFx.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).clm_apply contDiffAt_const).clm_apply contDiffAt_const).continuousAt
  obtain ⟨KA, UA, hUA, hLA⟩ := hA.exists_lipschitzOnWith
  obtain ⟨KB, UB, hUB, hLB⟩ := hB.exists_lipschitzOnWith
  let MB : ℝ≥0 := ‖B x‖₊ + 1
  let MC : ℝ≥0 := ‖C x‖₊ + 1
  have hBn : ∀ᶠ z in 𝓝 x, ‖B z‖ < MB :=
    hB.continuousAt.norm.eventually (gt_mem_nhds (show ‖B x‖ < (MB : ℝ) by simp [MB]))
  have hCn : ∀ᶠ z in 𝓝 x, ‖C z‖ < MC :=
    hC.norm.eventually (gt_mem_nhds (show ‖C x‖ < (MC : ℝ) by simp [MC]))
  have hRs : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 R (F z) :=
    hFx.continuousAt.eventually ((hR.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).eventually (by norm_num))
  have hall : U ∩ UA ∩ UB ∩ {z | ‖B z‖ < MB} ∩ {z | ‖C z‖ < MC} ∩
      {z | ContDiffAt ℝ 2 R (F z)} ∩ Metric.ball x (1 / 4) ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hx, hUA, hUB, hBn, hCn, hRs,
      Metric.ball_mem_nhds x (show (0 : ℝ) < 1 / 4 by norm_num)] with z h1 h2 h3 h4 h5 h6 h7
    exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp hall
  have hWU : W ⊆ U := fun z hz => (hWsub hz).1.1.1.1.1.1
  have hWA : W ⊆ UA := fun z hz => (hWsub hz).1.1.1.1.1.2
  have hWB : W ⊆ UB := fun z hz => (hWsub hz).1.1.1.1.2
  have hdist : ∀ y ∈ W, ∀ z ∈ W, edist y z ≤ (1 : ℝ≥0) := by
    intro y hy z hz
    rw [edist_dist]
    apply ENNReal.ofReal_le_one.2
    have h1 := Metric.mem_ball.mp ((hWsub hy).2)
    have h2 := Metric.mem_ball.mp ((hWsub hz).2)
    have hd := dist_triangle y x z
    rw [dist_comm x z] at hd
    exact (by linarith : dist y z ≤ 1)
  have hHA : HolderOnWith KA α A W := by
    simpa using HolderOnWith.of_le hdist ((hLA.mono hWA).holderOnWith) hα
  have hHB : HolderOnWith KB α B W := by
    simpa using HolderOnWith.of_le hdist ((hLB.mono hWB).holderOnWith) hα
  have heval (z : E) : iteratedFDeriv ℝ 2 F z ![v, w] = C z := by
    rw [iteratedFDeriv_two_apply]
    rfl
  have hHC : HolderOnWith K α C W := by
    apply holderOn_of_dist_bound
    intro y hy z hz
    rw [dist_eq_norm, ← heval y, ← heval z, ← sub_apply]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ *
          ∏ i : Fin 2, ‖(![v, w] : Fin 2 → E) i‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 F y - iteratedFDeriv ℝ 2 F z‖ := by simp [Fin.prod_univ_two, hv, hw]
      _ ≤ (K : ℝ) * dist y z ^ (α : ℝ) := by
        simpa only [dist_eq_norm] using hholder.dist_le (hWU hy) (hWU hz)
  have hbil : HolderWith (MB * K + MC * KB) α
      (fun z : W => B z (C z)) := by
    exact holderWith_bilinear_of_norm_le (Mf := MB) (Mg := MC)
      (ContinuousLinearMap.apply ℝ ℝ).flip
      (fun b c => b.le_opNorm c)
      hHB.holderWith hHC.holderWith
      (fun z => ((hWsub z.property).1.1.1.2).le)
      (fun z => ((hWsub z.property).1.1.2).le)
  have hsum := holderWith_add hHA.holderWith hbil
  refine ⟨W, KA + (MB * K + MC * KB), hWo, hxW, hWU, ?_⟩
  intro y hy z hz
  have hs := hsum ⟨y, hy⟩ ⟨z, hz⟩
  have heq (t : E) (ht : t ∈ W) :
      fderiv ℝ (fderiv ℝ (R ∘ F)) t v w = A t + B t (C t) :=
    second_derivative_composition_apply R F t v w
      (hF.contDiffAt (hU.mem_nhds (hWU ht))) ((hWsub ht).1.2)
  change edist (A y + B y (C y)) (A z + B z (C z)) ≤ _ at hs
  rw [← heq y hy, ← heq z hz] at hs
  exact hs
theorem holder_second_derivative_of_composition
    {E' V' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    [FiniteDimensional ℝ E'] [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (R : V' → ℝ) (F : E' → V') (U : Set E') (hU : IsOpen U)
    (x : E') (hx : x ∈ U) (hF : ContDiffOn ℝ 2 F U)
    (hR : ContDiffAt ℝ 3 R (F x)) (α K : ℝ≥0) (hα : α ≤ 1)
    (hholder : HolderOnWith K α (iteratedFDeriv ℝ 2 F) U) :
    ∃ (W : Set E') (L : ℝ≥0), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ContDiffOn ℝ 2 (R ∘ F) W ∧ HolderOnWith L α (iteratedFDeriv ℝ 2 (R ∘ F)) W := by
  classical
  let b := stdOrthonormalBasis ℝ E'
  have hlocal : ∀ β : Fin 2 → Fin (Module.finrank ℝ E'),
      ∃ (W : Set E') (L : ℝ≥0), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
        HolderOnWith L α (fun z => fderiv ℝ (fderiv ℝ (R ∘ F)) z (b (β 0)) (b (β 1))) W := by
    intro β
    exact holder_second_composition_component R F U hU x _ _ hx
      (b.orthonormal.norm_eq_one _) (b.orthonormal.norm_eq_one _)
      hF hR α K hα hholder
  choose W L hWo hxW hWU hH using hlocal
  have hRs : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 R (F z) :=
    (hF.contDiffAt (hU.mem_nhds hx)).continuousAt.eventually
      ((hR.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)).eventually (by norm_num))
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.mp hRs
  let Z := U ∩ (⋂ β, W β) ∩ T
  have hZo : IsOpen Z := (hU.inter (isOpen_iInter_of_finite hWo)).inter hTo
  have hxZ : x ∈ Z := ⟨⟨hx, mem_iInter.mpr hxW⟩, hxT⟩
  have hZU : Z ⊆ U := fun _ hz => hz.1.1
  have hZW (β) : Z ⊆ W β := fun _ hz => mem_iInter.mp hz.1.2 β
  have hreg : ContDiffOn ℝ 2 (R ∘ F) Z := by
    intro z hz
    have hRz : ContDiffAt ℝ 2 R (F z) := hTsub hz.2
    exact (hRz.comp z (hF.contDiffAt (hU.mem_nhds hz.1.1))).contDiffWithinAt
  have hAll := holderWith_continuousMultilinearMap_of_stdOrthonormalBasis
    (fun z : Z => iteratedFDeriv ℝ 2 (R ∘ F) z) L (fun β => by
      intro y z
      simpa only [iteratedFDeriv_two_apply, b, Subtype.edist_eq] using
        hH β y (hZW β y.property) z (hZW β z.property))
  refine ⟨Z, ∑ β, L β, hZo, hxZ, hZU, hreg, ?_⟩
  intro y hy z hz
  exact hAll ⟨y, hy⟩ ⟨z, hz⟩
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: ScalarComposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC
open SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem scalar_composition_regular (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r)
    (f : S → N) (hf : C2HolderUpToBoundary f) :
    ContMDiff SurfaceModel 𝓘(ℝ, ℝ) 2 (r ∘ f) :=
  (hr.of_le (by norm_num)).comp hf.regular
theorem scalar_composition_holder (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r)
    (f : C(S, N)) (hf : C2HolderUpToBoundary f) :
    ScalarC2HolderUpToBoundary S (r ∘ f) := by
  refine ⟨scalar_composition_regular S r hr f hf, ?_⟩
  obtain ⟨α, hα0, hα1, hcharts⟩ := hf.holder_extensions
  refine ⟨α, hα0, hα1, ?_⟩
  intro p
  obtain ⟨U, F, K, hUo, hxU, hsub, hF, hH, hmatch⟩ := hcharts p
  let x := extChartAt SurfaceModel p p
  let d := ambientNativeChart (f p)
  let R := r ∘ d.chart.symm
  have hxr : x ∈ range SurfaceModel :=
    extChartAt_target_subset_range p (mem_extChartAt_target p)
  have hF0 : F x = d.chart (f p) := by
    rw [hmatch x ⟨hxU, hxr⟩]
    simp only [writtenInExtChartAt, Function.comp_def]
    dsimp only [x]
    rw [extChartAt_to_inv]
    exact congrArg (fun c : PartialEquiv N (RVec 3) => c (f p))
      (ambientNativeChart_eq (f p)).symm
  have hR : ContDiffAt ℝ 3 R (F x) := by
    rw [hF0]
    have hd := d.chart.map_source (mem_chart_source (RVec 3) (f p))
    have hi := d.inverse_smooth.contMDiffAt (d.chart.open_target.mem_nhds hd)
    exact ((hr.of_le (by norm_num)).contMDiffAt.comp _ (hi.of_le (by norm_num))).contDiffAt
  obtain ⟨W, L, hWo, hxW, hWU, hreg, hholder⟩ :=
    holder_second_derivative_of_composition R F U hUo x hxU hF hR α K hα1.le hH
  let ψ : RVec 2 → N := fun z => f ((extChartAt SurfaceModel p).symm z)
  have hψ : ContinuousAt ψ x := by
    change ContinuousAt (f ∘ (extChartAt SurfaceModel p).symm) (extChartAt SurfaceModel p p)
    exact f.continuous.continuousAt.comp (continuousAt_extChartAt_symm (I := SurfaceModel) p)
  have hs : ψ ⁻¹' d.chart.source ∈ 𝓝 x := by
    apply hψ.preimage_mem_nhds
    apply d.chart.open_source.mem_nhds
    simpa only [ψ, x, d, ambientNativeChart, extChartAt_to_inv] using mem_chart_source (RVec 3) (f p)
  obtain ⟨T, hTsub, hTo, hxT⟩ := mem_nhds_iff.mp hs
  refine ⟨W ∩ T, R ∘ F, L, hWo.inter hTo, ⟨hxW, hxT⟩, ?_,
    hreg.mono inter_subset_left, hholder.mono inter_subset_left, ?_⟩
  · intro z hz
    exact hsub ⟨hWU hz.1.1, hz.2⟩
  · intro z hz
    have heq : F z = d.chart (ψ z) := by
      rw [hmatch z ⟨hWU hz.1.1, hz.2⟩]
      change (extChartAt AmbientModel (f p)) (ψ z) = d.chart (ψ z)
      exact congrArg (fun c : PartialEquiv N (RVec 3) => c (ψ z))
        (ambientNativeChart_eq (f p)).symm
    change r (d.chart.symm (F z)) = r (ψ z)
    rw [heq, d.chart.left_inv (hTsub hz.1.2)]
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: EuclideanTrace
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Filter
open scoped ContDiff BigOperators ENNReal NNReal
namespace SeifertSurfaces.PrivateHelpers.C6Native
abbrev TraceE2 := EuclideanSpace ℝ (Fin 2)
abbrev TraceE3 := EuclideanSpace ℝ (Fin 3)
theorem trace_second_composition_algebra
    (R : TraceE3 → ℝ) (F : TraceE2 → TraceE3) (x : TraceE2)
    (A : Matrix (Fin 2) (Fin 2) ℝ)
    (C : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hF : ContDiffAt ℝ 2 F x) (hR : ContDiffAt ℝ 2 R (F x))
    (htension : ∑ a : Fin 3, (∑ i : Fin 2, ∑ j : Fin 2, A i j *
      ((fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ))) a -
        (∑ k : Fin 2, C k i j * (fderiv ℝ F x (EuclideanSpace.single k (1 : ℝ))) a) +
        (∑ b : Fin 3, ∑ c : Fin 3, Γ a b c *
          (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ))) b *
          (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) c))) • EuclideanSpace.single a (1 : ℝ) = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, A i j *
      (fderiv ℝ (fderiv ℝ (R ∘ F)) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) -
        ∑ k : Fin 2, C k i j * fderiv ℝ (R ∘ F) x (EuclideanSpace.single k (1 : ℝ)))) =
    ∑ i : Fin 2, ∑ j : Fin 2, A i j *
      (fderiv ℝ (fderiv ℝ R) (F x) (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ)))
        (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) -
        ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
          Γ a b c * fderiv ℝ R (F x) (EuclideanSpace.single a (1 : ℝ)) *
            (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ))) b *
            (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) c) := by
  have hsum (v : TraceE3) : (∑ a : Fin 3, v a • EuclideanSpace.single a (1 : ℝ)) = v := by
    ext i
    simp [EuclideanSpace.single, Pi.single_apply]
  have hlinear (v : TraceE3) : fderiv ℝ R (F x) v =
      ∑ a : Fin 3, v a * fderiv ℝ R (F x) (EuclideanSpace.single a (1 : ℝ)) := by
    conv_lhs => rw [← hsum v]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hzero := congrArg (fderiv ℝ R (F x)) htension
  simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hzero
  have hfirst (i : Fin 2) : fderiv ℝ (R ∘ F) x (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ R (F x) (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ))) := by
    rw [fderiv_comp x (hR.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num))]
    rfl
  have hlinearfirst (i : Fin 2) := hlinear (fderiv ℝ F x (EuclideanSpace.single i (1 : ℝ)))
  have hlinearsecond (i j : Fin 2) := hlinear
    (fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))
  simp_rw [second_derivative_composition_apply R F x _ _ hF hR, hfirst,
    hlinearfirst, hlinearsecond]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hzero ⊢
  linear_combination hzero
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: NativeInterior
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem native_surface_metric (g : SurfaceMetric S) (p : S) (x : RVec 2)
    (hx : x ∈ (extChartAt SurfaceModel p).target) :
    MetricInChart SurfaceModel g p x =
      metricInCoordinates S g (chartAt (EuclideanHalfSpace 2) p) x := by
  have hn := extChartAt_target_eventuallyEqSet_of_mem (I := SurfaceModel) hx
  have hd := mfderivWithin_congr_set (I := 𝓘(ℝ, RVec 2))
    (I' := SurfaceModel) (f := (extChartAt SurfaceModel p).symm) hn
  unfold MetricInChart metricInCoordinates
  change (fun i j => g.inner ((extChartAt SurfaceModel p).symm x)
    (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
      (range SurfaceModel) x (EuclideanSpace.single i 1))
    (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
      (range SurfaceModel) x (EuclideanSpace.single j 1))) = _
  rw [← hd]
  rfl

theorem interior_coordinate_map (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (hp : p ∈ SurfaceModel.interior S) :
    ContDiffAt ℝ 2 (writtenInExtChartAt SurfaceModel AmbientModel p f)
      (extChartAt SurfaceModel p p) := by
  have hh := (contMDiffAt_iff.mp (hf p)).2
  apply hh.contDiffAt
  exact mem_interior_iff_mem_nhds.mp hp

theorem native_map_derivative (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (hp : p ∈ SurfaceModel.interior S) :
    mfderiv SurfaceModel AmbientModel f p =
      fderiv ℝ (writtenInExtChartAt SurfaceModel AmbientModel p f)
        (extChartAt SurfaceModel p p) := by
  rw [(hf.mdifferentiable (by norm_num) p).mfderiv_abuse]
  apply fderivWithin_eq_fderiv (SurfaceModel.uniqueDiffOn _ (by simp))
  exact (interior_coordinate_map S f hf p hp).differentiableAt (by norm_num)

theorem native_surface_center_metric (g : SurfaceMetric S) (p : S) :
    MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p) =
      fun i j => g.inner p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold MetricInChart
  rw [extChartAt_to_inv, mfderivWithin_range_extChartAt_symm]
  rfl
theorem interior_chart_laplacian (g : SurfaceMetric S) (p : S)
    (hp : p ∈ SurfaceModel.interior S) (v : RVec 2 → ℝ) :
    chartLaplacian S g p v (extChartAt SurfaceModel p p) =
      ∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p))⁻¹ i j *
        (fderiv ℝ (fderiv ℝ v) (extChartAt SurfaceModel p p)
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
          ∑ k : Fin 2, ChristoffelCoordinate (MetricInChart SurfaceModel g p)
            (extChartAt SurfaceModel p p) k i j *
            fderiv ℝ v (extChartAt SurfaceModel p p) (EuclideanSpace.single k 1)) := by
  let U := (extChartAt SurfaceModel p).target
  let x := extChartAt SurfaceModel p p
  have hx : x ∈ interior U := SurfaceModel.isInteriorPoint_iff.mp hp
  have hn : U ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  have hg (v : RVec 2 → ℝ) : (fun z => fderivWithin ℝ v U z) =ᶠ[𝓝 x] fderiv ℝ v := by
    filter_upwards [isOpen_interior.mem_nhds hx] with z hz
    exact fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  have hsecond : fderivWithin ℝ (fun z => fderivWithin ℝ v U z) U x =
      fderiv ℝ (fderiv ℝ v) x := by
    rw [(hg v).fderivWithin_eq_of_nhds, fderivWithin_of_mem_nhds hn]
  dsimp only [U, x] at hn hsecond
  unfold chartLaplacian sourceChristoffel ChristoffelCoordinate
  dsimp only
  rw [hsecond]
  simp only [fderivWithin_of_mem_nhds hn]

theorem native_chart_tangent_identity (q : N) (v : TangentSpace AmbientModel q) :
    tangentSpaceCastModel 𝓘(ℝ, RVec 3) (extChartAt AmbientModel q q)
      (mfderiv AmbientModel 𝓘(ℝ, RVec 3) (extChartAt AmbientModel q) q v) = v := by
  rw [mfderiv_extChartAt_self]
  rfl

theorem native_height_hessian_interior (h : AmbientMetric N) (r : N → ℝ)
    (f : S → N) (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (hp : p ∈ SurfaceModel.interior S) (v w : TangentSpace SurfaceModel p) :
    covariantHessian h r (f p) (mfderiv SurfaceModel AmbientModel f p v)
      (mfderiv SurfaceModel AmbientModel f p w) =
      fderiv ℝ (fderiv ℝ (r ∘ (extChartAt AmbientModel (f p)).symm))
        (extChartAt AmbientModel (f p) (f p))
        (fderiv ℝ (writtenInExtChartAt SurfaceModel AmbientModel p f)
          (extChartAt SurfaceModel p p) v)
        (fderiv ℝ (writtenInExtChartAt SurfaceModel AmbientModel p f)
          (extChartAt SurfaceModel p p) w) -
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3,
        ChristoffelCoordinate (MetricInChart AmbientModel h (f p))
          (extChartAt AmbientModel (f p) (f p)) k a b *
          fderiv ℝ (r ∘ (extChartAt AmbientModel (f p)).symm)
            (extChartAt AmbientModel (f p) (f p)) (EuclideanSpace.single k 1) *
          (fderiv ℝ (writtenInExtChartAt SurfaceModel AmbientModel p f)
            (extChartAt SurfaceModel p p) v) a *
          (fderiv ℝ (writtenInExtChartAt SurfaceModel AmbientModel p f)
            (extChartAt SurfaceModel p p) w) b := by
  unfold covariantHessian
  dsimp only
  simp_rw [native_chart_tangent_identity]
  rw [native_map_derivative S f hf p hp]
  rfl

theorem height_chart_composition_germ (r : N → ℝ) (f : C(S, N)) (p : S) :
    (r ∘ f ∘ (extChartAt SurfaceModel p).symm) =ᶠ[𝓝 (extChartAt SurfaceModel p p)]
      ((r ∘ (extChartAt AmbientModel (f p)).symm) ∘
        writtenInExtChartAt SurfaceModel AmbientModel p f) := by
  have hψ : ContinuousAt (f ∘ (extChartAt SurfaceModel p).symm) (extChartAt SurfaceModel p p) :=
    f.continuous.continuousAt.comp (continuousAt_extChartAt_symm (I := SurfaceModel) p)
  have hn : ∀ᶠ x in 𝓝 (extChartAt SurfaceModel p p),
      f ((extChartAt SurfaceModel p).symm x) ∈ (extChartAt AmbientModel (f p)).source := by
    apply hψ.preimage_mem_nhds
    simpa only [Function.comp_def, extChartAt_to_inv] using extChartAt_source_mem_nhds (I := AmbientModel) (f p)
  filter_upwards [hn] with x hx
  simp only [Function.comp_def, writtenInExtChartAt]
  rw [(extChartAt AmbientModel (f p)).left_inv hx]
theorem pulled_trace_native (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (f : S → N) (p : S) :
    pulledHessianTrace S g h r f p =
      ∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p))⁻¹ i j *
        covariantHessian h r (f p)
          (mfderiv SurfaceModel AmbientModel f p (EuclideanSpace.single i 1))
          (mfderiv SurfaceModel AmbientModel f p (EuclideanSpace.single j 1)) := by
  unfold pulledHessianTrace
  dsimp only
  rw [mfderivWithin_range_extChartAt_symm]
  rfl

theorem native_interior_harmonic_trace (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r)
    (f : C(S, N)) (hf : C2HolderUpToBoundary f)
    (hh : HarmonicInterior g h f) (p : S) (hp : p ∈ SurfaceModel.interior S) :
    laplacian S g (r ∘ f) p = pulledHessianTrace S g h r f p := by
  let F := writtenInExtChartAt SurfaceModel AmbientModel p f
  let R := r ∘ (extChartAt AmbientModel (f p)).symm
  let x := extChartAt SurfaceModel p p
  have hFx : ContDiffAt ℝ 2 F x := interior_coordinate_map S f hf.regular p hp
  have hF0 : F x = extChartAt AmbientModel (f p) (f p) := by
    simp only [F, x, writtenInExtChartAt, Function.comp_def, extChartAt_to_inv]
  have hRx : ContDiffAt ℝ 2 R (F x) := by
    rw [hF0]
    have hi := (ambientNativeChart (f p)).inverse_smooth.contMDiffAt
      ((ambientNativeChart (f p)).chart.open_target.mem_nhds
        ((ambientNativeChart (f p)).chart.map_source (mem_chart_source (RVec 3) (f p))))
    have hx := ((hr.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).contMDiffAt.comp _
      (hi.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))).contDiffAt
    change ContDiffAt ℝ 2 (r ∘ (chartAt (RVec 3) (f p)).symm)
      (chartAt (RVec 3) (f p) (f p))
    exact hx
  have htrace := trace_second_composition_algebra R F x
    ((MetricInChart SurfaceModel g p x)⁻¹)
    (ChristoffelCoordinate (MetricInChart SurfaceModel g p) x)
    (ChristoffelCoordinate (MetricInChart AmbientModel h (f p)) (F x)) hFx hRx
    (hh p hp)
  have hgerm := height_chart_composition_germ S r f p
  have hfirst := hgerm.fderiv_eq (𝕜 := ℝ)
  have hsecond := (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  unfold laplacian
  rw [interior_chart_laplacian S g p hp]
  rw [pulled_trace_native S g h r f p]
  simp_rw [native_height_hessian_interior S h r f hf.regular p hp]
  simp only [← hF0]
  change (∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p x)⁻¹ i j *
    (fderiv ℝ (fderiv ℝ (r ∘ f ∘ (extChartAt SurfaceModel p).symm)) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
      ∑ k : Fin 2, ChristoffelCoordinate (MetricInChart SurfaceModel g p) x k i j *
        fderiv ℝ (r ∘ f ∘ (extChartAt SurfaceModel p).symm) x (EuclideanSpace.single k 1))) = _
  rw [hfirst, hsecond, htrace]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  ring
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: FrameTrace
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
abbrev FrameE2 := EuclideanSpace ℝ (Fin 2)
theorem orthonormal_coordinate_matrix_inverse (G : Matrix (Fin 2) (Fin 2) ℝ)
    (D : Matrix (Fin 2) (Fin 2) ℝ) (hD : D.transpose * G * D = 1) :
    G⁻¹ = D * D.transpose := by
  have hu : IsUnit D.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hh := congrArg Matrix.det hD
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, hz, zero_mul, mul_zero] at hh
    exact zero_ne_one hh
  have hDT : IsUnit D.transpose.det := by simpa only [Matrix.det_transpose] using hu
  have hG : G = D.transpose⁻¹ * D⁻¹ := by
    calc
      G = (D.transpose⁻¹ * D.transpose) * G * (D * D⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hDT, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul, Matrix.mul_one]
      _ = D.transpose⁻¹ * (D.transpose * G * D) * D⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = D.transpose⁻¹ * D⁻¹ := by rw [hD, Matrix.mul_one]
  apply Matrix.inv_eq_right_inv
  rw [hG]
  calc
    (D.transpose⁻¹ * D⁻¹) * (D * D.transpose) =
        D.transpose⁻¹ * (D⁻¹ * D) * D.transpose := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul _ hDT]

theorem coordinate_orthonormal_trace (G : Matrix (Fin 2) (Fin 2) ℝ)
    (e : Fin 2 → FrameE2)
    (he : ∀ a b, (∑ i : Fin 2, ∑ j : Fin 2, G i j * e a i * e b j) =
      if a = b then 1 else 0)
    (H : FrameE2 →L[ℝ] FrameE2 →L[ℝ] ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, G⁻¹ i j * H (EuclideanSpace.single i 1)
      (EuclideanSpace.single j 1)) = ∑ a : Fin 2, H (e a) (e a) := by
  let D : Matrix (Fin 2) (Fin 2) ℝ := fun i a => e a i
  have hD : D.transpose * G * D = 1 := by
    ext a b
    change (∑ k : Fin 2, (∑ i : Fin 2, e a i * G i k) * e b k) =
      if a = b then 1 else 0
    have hh := he a b
    simp only [Fin.sum_univ_two] at hh ⊢
    linear_combination hh
  rw [orthonormal_coordinate_matrix_inverse G D hD]
  have hsum (v : FrameE2) : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single, Pi.single_apply]
  have hH (v : FrameE2) : H v v =
      ∑ i : Fin 2, ∑ j : Fin 2, v i * v j * H (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
    conv_lhs => rw [← hsum v]
    simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hH]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, D, Fin.sum_univ_succ,
    Fin.sum_univ_zero, add_zero]
  change ((e 0 0 * e 0 0 + e 1 0 * e 1 0) * H (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) +
    (e 0 0 * e 0 1 + e 1 0 * e 1 1) * H (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)) +
    ((e 0 1 * e 0 0 + e 1 1 * e 1 0) * H (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1) +
    (e 0 1 * e 0 1 + e 1 1 * e 1 1) * H (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)) = _
  simp only [Fin.succ_zero_eq_one]
  ring
variable {N : Type*} [TopologicalSpace N] [ChartedSpace (RVec 3) N]
  [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem covariant_hessian_bilinear (h : AmbientMetric N) (r : N → ℝ) (q : N) :
    ∃ B : RVec 3 →L[ℝ] RVec 3 →L[ℝ] ℝ,
      ∀ v w : TangentSpace AmbientModel q, covariantHessian h r q v w = B v w := by
  let R := r ∘ (extChartAt AmbientModel q).symm
  let x := extChartAt AmbientModel q q
  let B : RVec 3 →L[ℝ] RVec 3 →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ R) x -
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3,
        (ChristoffelCoordinate (MetricInChart AmbientModel h q) x k a b *
          fderiv ℝ R x (EuclideanSpace.single k 1)) •
        (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
          (EuclideanSpace.proj (𝕜 := ℝ) a) (EuclideanSpace.proj (𝕜 := ℝ) b)
  refine ⟨B, ?_⟩
  intro v w
  change RVec 3 at v w
  unfold covariantHessian
  dsimp only
  simp_rw [native_chart_tangent_identity]
  simp only [B, R, x, sub_apply, sum_apply, smul_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply,
    EuclideanSpace.coe_proj, smul_eq_mul]
  change _ - ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3,
      ChristoffelCoordinate (MetricInChart AmbientModel h q) x k a b *
        fderiv ℝ R x (EuclideanSpace.single k 1) * v a * w b =
    _ - ∑ a : Fin 3, ∑ b : Fin 3, ∑ k : Fin 3,
      (ChristoffelCoordinate (MetricInChart AmbientModel h q) x k a b *
        fderiv ℝ R x (EuclideanSpace.single k 1)) * (v a * w b)
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_frame_trace (S : CompactOrientedSurface) (g : SurfaceMetric S)
    (h : AmbientMetric N) (r : N → ℝ) (f : S → N) (p : S)
    (e : Fin 2 → TangentSpace SurfaceModel p)
    (he : ∀ i j, g.inner p (e i) (e j) = if i = j then 1 else 0) :
    pulledHessianTrace S g h r f p =
      ∑ i : Fin 2, covariantHessian h r (f p)
        (mfderiv SurfaceModel AmbientModel f p (e i))
        (mfderiv SurfaceModel AmbientModel f p (e i)) := by
  obtain ⟨B, hB⟩ := covariant_hessian_bilinear h r (f p)
  let D : RVec 2 →L[ℝ] RVec 3 := mfderiv SurfaceModel AmbientModel f p
  let H : RVec 2 →L[ℝ] RVec 2 →L[ℝ] ℝ := B.bilinearComp D D
  have hsum (v : RVec 2) : (∑ i : Fin 2, v i • EuclideanSpace.single i 1) = v := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single]
  have hg (v w : RVec 2) : g.inner p v w =
      ∑ i : Fin 2, ∑ j : Fin 2,
        g.inner p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * v i * w j := by
    conv_lhs => rw [← hsum v, ← hsum w]
    simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  let E : Fin 2 → RVec 2 := fun i => e i
  have hcoord : ∀ a b : Fin 2,
      (∑ i : Fin 2, ∑ j : Fin 2,
        MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p) i j * E a i * E b j) =
      if a = b then 1 else 0 := by
    intro a b
    rw [native_surface_center_metric S g p]
    rw [← hg (E a) (E b)]
    exact he a b
  have ht := coordinate_orthonormal_trace
    (MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p)) E hcoord H
  rw [pulled_trace_native S g h r f p]
  simp_rw [hB]
  exact ht

theorem frame_hessian_sign_radial (S : CompactOrientedSurface) (g : SurfaceMetric S)
    (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (f : S → N) (p : S) (hp : r (f p) < ε)
    (e : Fin 2 → TangentSpace SurfaceModel p) :
    (∑ i : Fin 2, covariantHessian h r (f p)
      (mfderiv SurfaceModel AmbientModel f p (e i))
      (mfderiv SurfaceModel AmbientModel f p (e i))) ≤ 0 ∧
    ((∑ i : Fin 2, covariantHessian h r (f p)
      (mfderiv SurfaceModel AmbientModel f p (e i))
      (mfderiv SurfaceModel AmbientModel f p (e i))) = 0 ↔
      ∀ i, IsRadial h r (f p) (mfderiv SurfaceModel AmbientModel f p (e i))) := by
  have hs (i : Fin 2) := native_collar_hessian_sign_radial h r ε collar (f p) hp
    (mfderiv SurfaceModel AmbientModel f p (e i))
  refine ⟨Finset.sum_nonpos (fun i _ => (hs i).1), ?_⟩
  constructor
  · intro hz i
    have heq : ∀ j : Fin 2, covariantHessian h r (f p)
        (mfderiv SurfaceModel AmbientModel f p (e j))
        (mfderiv SurfaceModel AmbientModel f p (e j)) = 0 := by
      intro j
      have h0 := (hs 0).1
      have h1 := (hs 1).1
      simp only [Fin.sum_univ_two] at hz
      have hzero0 : covariantHessian h r (f p)
          (mfderiv SurfaceModel AmbientModel f p (e 0))
          (mfderiv SurfaceModel AmbientModel f p (e 0)) = 0 := by linarith
      have hzero1 : covariantHessian h r (f p)
          (mfderiv SurfaceModel AmbientModel f p (e 1))
          (mfderiv SurfaceModel AmbientModel f p (e 1)) = 0 := by linarith
      fin_cases j
      · simpa using hzero0
      · simpa using hzero1
    exact (hs i).2.mp (heq i)
  · intro hh
    exact Finset.sum_eq_zero (fun i _ => (hs i).2.mpr (hh i))
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: EuclideanSourceTransport
set_option maxHeartbeats 0
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC
abbrev Metric2 := RVec 2 → Matrix (Fin 2) (Fin 2) ℝ
abbrev basis2 (i : Fin 2) : RVec 2 := EuclideanSpace.single i (1 : ℝ)
def partial2 (f : RVec 2 → ℝ) (x : RVec 2) (i : Fin 2) : ℝ :=
  fderiv ℝ f x (basis2 i)
def hessianCoefficient2 (g : Metric2) (u : RVec 2 → ℝ) (x : RVec 2)
    (a b : Fin 2) : ℝ :=
  fderiv ℝ (fderiv ℝ u) x (basis2 a) (basis2 b) -
    ∑ k : Fin 2, ChristoffelCoordinate g x k a b * fderiv ℝ u x (basis2 k)
def laplacian2 (g : Metric2) (u : RVec 2 → ℝ) (x : RVec 2) : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 2, (g x)⁻¹ a b * hessianCoefficient2 g u x a b

theorem euclidean_source_laplacian_transport
    (g G : Metric2) (T : RVec 2 → RVec 2) (u : RVec 2 → ℝ) (y : RVec 2)
    (hT : ContDiffAt ℝ (∞ : ℕ∞ω) T y) (hTbij : Function.Bijective (fderiv ℝ T y))
    (hu : ContDiffAt ℝ 2 u (T y))
    (hGdiff : ∀ i j, DifferentiableAt ℝ (fun z => G z i j) (T y))
    (hGsym : ∀ z i j, G z i j = G z j i)
    (hgsym : ∀ z i j, g z i j = g z j i)
    (hgdet : IsUnit (g y).det) (hGdet : IsUnit (G (T y)).det)
    (hEntry : ∀ i j, (fun z => g z i j) =ᶠ[𝓝 y]
      (fun z => ∑ n : Fin 2, ∑ p : Fin 2,
        G (T z) n p * (fderiv ℝ T z (basis2 i)) n * (fderiv ℝ T z (basis2 j)) p)) :
    laplacian2 g (u ∘ T) y = laplacian2 G u (T y) := by
    classical
    have hLowerAlg (G J : Matrix (Fin 2) (Fin 2) ℝ)
        (dG H dg : Fin 2 → Fin 2 → Fin 2 → ℝ)
        (hG : ∀ i j, G i j = G j i)
        (hdG : ∀ a i j, dG a i j = dG a j i)
        (hH : ∀ k a b, H k a b = H k b a)
        (hdg : ∀ a l b, dg a l b =
          (∑ m : Fin 2, ∑ n : Fin 2, ∑ p : Fin 2,
            dG m n p * J m a * J n l * J p b) +
          ∑ n : Fin 2, ∑ p : Fin 2, G n p *
            (H n a l * J p b + J n l * H p a b))
        (a b l : Fin 2) :
        dg a l b + dg b l a - dg l a b =
          2 * (∑ s : Fin 2, ∑ t : Fin 2, G s t * H s a b * J t l) +
          ∑ s : Fin 2, ∑ t : Fin 2, ∑ m : Fin 2,
            (dG s m t + dG t m s - dG m s t) * J s a * J t b * J m l := by
      simp only [hdg, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      simp only [hG,hdG,hH]
      ring
    have hGammaAlg (g G J : Matrix (Fin 2) (Fin 2) ℝ)
        (L lG H : Fin 2 → Fin 2 → Fin 2 → ℝ)
        (hg : IsUnit g.det) (hG : IsUnit G.det) (hJ : IsUnit J)
        (hmet : g = J.transpose * G * J)
        (hLower : ∀ a b l, L a b l =
          2 * (∑ s : Fin 2, ∑ t : Fin 2, G t s * H s a b * J t l) +
          ∑ s : Fin 2, ∑ t : Fin 2, ∑ m : Fin 2,
            lG s t m * J s a * J t b * J m l)
        (a b k : Fin 2) :
        (∑ i : Fin 2, J k i * ((1 / 2 : ℝ) * ∑ l : Fin 2, g⁻¹ i l * L a b l)) =
          H k a b + ∑ s : Fin 2, ∑ t : Fin 2,
            ((1 / 2 : ℝ) * ∑ m : Fin 2, G⁻¹ k m * lG s t m) * J s a * J t b := by
      classical
      let γ : Fin 2 → ℝ := (1 / 2 : ℝ) • (Matrix.mulVec g⁻¹ (L a b))
      let Γ (s t : Fin 2) : Fin 2 → ℝ := (1 / 2 : ℝ) • (Matrix.mulVec G⁻¹ (lG s t))
      let Z : Fin 2 → ℝ := (fun k => H k a b) +
        ∑ s : Fin 2, ∑ t : Fin 2, (J s a * J t b) • Γ s t
      have hγ : Matrix.mulVec g γ = (1 / 2 : ℝ) • L a b := by
        simp only [γ,Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hg,
          Matrix.one_mulVec]
      have hΓ (s t : Fin 2) : Matrix.mulVec G (Γ s t) = (1 / 2 : ℝ) • lG s t := by
        simp only [Γ,Matrix.mulVec_smul,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hG,
          Matrix.one_mulVec]
      have hZ : Matrix.mulVec (J.transpose * G) Z = (1 / 2 : ℝ) • L a b := by
        rw [← Matrix.mulVec_mulVec]
        simp only [Z,Matrix.mulVec_add,Matrix.mulVec_sum,Matrix.mulVec_smul,hΓ]
        ext l
        simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Pi.add_apply,
          Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hLower,
          Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
        ring
      have heq : Matrix.mulVec (J.transpose * G) (Matrix.mulVec J γ) = Matrix.mulVec (J.transpose * G) Z := by
        rw [Matrix.mulVec_mulVec,← hmet,hγ,hZ]
      have hJT : IsUnit J.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr (by
        simpa only [Matrix.det_transpose] using (Matrix.isUnit_iff_isUnit_det _).mp hJ)
      have hJG : IsUnit (J.transpose * G) := hJT.mul ((Matrix.isUnit_iff_isUnit_det _).mpr hG)
      have hh := Matrix.mulVec_injective_iff_isUnit.mpr hJG heq
      have hk := congrFun hh k
      simpa only [γ,Γ,Z,Matrix.mulVec,dotProduct,Pi.add_apply,Finset.sum_apply,
        Pi.smul_apply,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hk
    have hMetricDeriv (G q : Metric2) (T : RVec 2 → RVec 2) (y : RVec 2)
        (hG : ∀ n p, DifferentiableAt ℝ (fun z => G z n p) (T y))
        (hT : DifferentiableAt ℝ T y)
        (hq : ∀ n b, DifferentiableAt ℝ (fun z => q z n b) y)
        (a l b : Fin 2) :
        partial2 (fun z => ∑ n : Fin 2, ∑ p : Fin 2,
          G (T z) n p * q z n l * q z p b) y a =
        (∑ m : Fin 2, ∑ n : Fin 2, ∑ p : Fin 2,
          partial2 (fun z => G z n p) (T y) m *
            (fderiv ℝ T y (basis2 a)) m * q y n l * q y p b) +
        ∑ n : Fin 2, ∑ p : Fin 2, G (T y) n p *
          (partial2 (fun z => q z n l) y a * q y p b +
            q y n l * partial2 (fun z => q z p b) y a) := by
      classical
      have hsum (v : RVec 2) : (∑ i : Fin 2, v i • basis2 i) = v := by
        ext j
        fin_cases j <;> simp [basis2,EuclideanSpace.single,Pi.single_apply]
      have hexpand (f : RVec 2 → ℝ) (x v : RVec 2) :
          fderiv ℝ f x v = ∑ i : Fin 2, partial2 f x i * v i := by
        conv_lhs => rw [← hsum v]
        simp only [map_sum,map_smul,smul_eq_mul,partial2]
        congr 1
        ext i
        rw [mul_comm]
      have hterm (n p : Fin 2) :
          partial2 (fun z => G (T z) n p * q z n l * q z p b) y a =
          (∑ m : Fin 2, partial2 (fun z => G z n p) (T y) m *
            (fderiv ℝ T y (basis2 a)) m) * q y n l * q y p b +
          G (T y) n p * (partial2 (fun z => q z n l) y a * q y p b +
            q y n l * partial2 (fun z => q z p b) y a) := by
        have hh := (((hG n p).hasFDerivAt.comp y hT.hasFDerivAt).mul
          (hq n l).hasFDerivAt).mul (hq p b).hasFDerivAt
        change HasFDerivAt (fun z => G (T z) n p * q z n l * q z p b) _ y at hh
        have hv := congrArg (fun L : RVec 2 →L[ℝ] ℝ => L (basis2 a)) hh.fderiv
        simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply,smul_eq_mul] at hv
        change _ = _ at hv
        rw [hexpand (fun z => G z n p) (T y) (fderiv ℝ T y (basis2 a))] at hv
        change partial2 _ y a = _ at hv
        simp only [partial2,Function.comp_def,Pi.mul_apply] at hv ⊢
        rw [hv]
        ring
      have hd (n p : Fin 2) : DifferentiableAt ℝ
          (fun z => G (T z) n p * q z n l * q z p b) y :=
        (((hG n p).comp y hT).mul (hq n l)).mul (hq p b)
      unfold partial2 at *
      rw [fderiv_fun_sum (fun n _ => DifferentiableAt.fun_sum (fun p _ => hd n p))]
      simp only [ContinuousLinearMap.sum_apply]
      simp_rw [fderiv_fun_sum (fun p _ => hd _ p),ContinuousLinearMap.sum_apply,hterm]
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
      ring
    have hJacobian (T : RVec 2 → RVec 2) (y : RVec 2) (hT : ContDiffAt ℝ (∞ : ℕ∞ω) T y) :
        (∀ k b : Fin 2, ContDiffAt ℝ (∞ : ℕ∞ω)
          (fun z => (fderiv ℝ T z (basis2 b)) k) y) ∧
        (∀ k a b : Fin 2,
          partial2 (fun z => (fderiv ℝ T z (basis2 b)) k) y a =
            (fderiv ℝ (fderiv ℝ T) y (basis2 a) (basis2 b)) k) ∧
        (∀ k a b : Fin 2,
          partial2 (fun z => (fderiv ℝ T z (basis2 b)) k) y a =
            partial2 (fun z => (fderiv ℝ T z (basis2 a)) k) y b) := by
      have hF : ContDiffAt ℝ (∞ : ℕ∞ω) (fderiv ℝ T) y := hT.fderiv_right (by simp)
      have hj (k b : Fin 2) : ContDiffAt ℝ (∞ : ℕ∞ω)
          (fun z => (fderiv ℝ T z (basis2 b)) k) y :=
        (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp y
          (hF.clm_apply contDiffAt_const)
      have heq (k a b : Fin 2) :
          partial2 (fun z => (fderiv ℝ T z (basis2 b)) k) y a =
            (fderiv ℝ (fderiv ℝ T) y (basis2 a) (basis2 b)) k := by
        have hd := (hF.differentiableAt (by simp)).hasFDerivAt.clm_apply
          (hasFDerivAt_const (basis2 b) y)
        have hp := (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt.comp y hd
        have hv := congrArg (fun L : RVec 2 →L[ℝ] ℝ => L (basis2 a)) hp.fderiv
        simpa only [Function.comp_def,EuclideanSpace.coe_proj,partial2,ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,
          ContinuousLinearMap.zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply] using hv
      refine ⟨hj,heq,?_⟩
      intro k a b
      rw [heq,heq]
      exact congrArg (fun v : RVec 2 => v k) ((hT.isSymmSndFDerivAt (by norm_num)).eq _ _)
    let J : Metric2 := fun z k a => (fderiv ℝ T z (basis2 a)) k
    let H : Fin 2 → Fin 2 → Fin 2 → ℝ := fun k a b => partial2 (fun z => J z k b) y a
    let dG : Fin 2 → Fin 2 → Fin 2 → ℝ := fun a i j => partial2 (fun z => G z i j) (T y) a
    let dg : Fin 2 → Fin 2 → Fin 2 → ℝ := fun a i j => partial2 (fun z => g z i j) y a
    have hJdiff (k a : Fin 2) : DifferentiableAt ℝ (fun z => J z k a) y :=
      ((hJacobian T y hT).1 k a).differentiableAt (by simp)
    have hHsym (k a b : Fin 2) : H k a b = H k b a := (hJacobian T y hT).2.2 k a b
    have hdGsym (a i j : Fin 2) : dG a i j = dG a j i := by
      have he : (fun z => G z i j) = (fun z => G z j i) := funext (fun z => hGsym z i j)
      simp only [dG, he]
    have hdg (a l b : Fin 2) : dg a l b =
        (∑ m : Fin 2, ∑ n : Fin 2, ∑ p : Fin 2,
          dG m n p * J y m a * J y n l * J y p b) +
        ∑ n : Fin 2, ∑ p : Fin 2, G (T y) n p *
          (H n a l * J y p b + J y n l * H p a b) := by
      change fderiv ℝ (fun z => g z l b) y (basis2 a) = _
      rw [(hEntry l b).fderiv_eq]
      exact hMetricDeriv G J T y hGdiff (hT.differentiableAt (by simp)) hJdiff a l b
    have hmetric : g y = (J y).transpose * G (T y) * J y := by
      ext i j
      calc
        g y i j = ∑ n : Fin 2, ∑ p : Fin 2, G (T y) n p * J y n i * J y p j :=
          (hEntry i j).self_of_nhds
        _ = _ := by simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]; ring
    have hsum (v : RVec 2) : (∑ i : Fin 2, v i • basis2 i) = v := by
      ext j
      fin_cases j <;> simp [basis2, EuclideanSpace.single, Pi.single_apply]
    have hrepr (v : RVec 2) (k : Fin 2) : (fderiv ℝ T y v) k =
        ∑ i : Fin 2, J y k i * v i := by
      conv_lhs => rw [← hsum v]
      simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
        smul_eq_mul, J]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hJunit : IsUnit (J y) := by
      apply Matrix.mulVec_injective_iff_isUnit.mp
      intro v w hvw
      have hh : (WithLp.toLp 2 v : RVec 2) = WithLp.toLp 2 w := by
        apply hTbij.injective
        ext k
        rw [hrepr, hrepr]
        exact congrFun hvw k
      exact WithLp.toLp_injective 2 hh
    have hLower (a b l : Fin 2) : dg a l b + dg b l a - dg l a b =
        2 * (∑ s : Fin 2, ∑ t : Fin 2, G (T y) t s * H s a b * J y t l) +
        ∑ s : Fin 2, ∑ t : Fin 2, ∑ m : Fin 2,
          (dG s m t + dG t m s - dG m s t) * J y s a * J y t b * J y m l := by
      simpa only [hGsym (T y)] using hLowerAlg (G (T y)) (J y) dG H dg
        (hGsym (T y)) hdGsym hHsym hdg a b l
    have hGamma (a b k : Fin 2) :
        (∑ i : Fin 2, J y k i * ChristoffelCoordinate g y i a b) =
          H k a b + ∑ s : Fin 2, ∑ t : Fin 2,
            ChristoffelCoordinate G (T y) k s t * J y s a * J y t b := by
      simpa only [ChristoffelCoordinate, dg, dG, partial2, basis2, hgsym, hGsym] using
        hGammaAlg (g y) (G (T y)) (J y)
        (fun a b l => dg a l b + dg b l a - dg l a b)
        (fun s t m => dG s m t + dG t m s - dG m s t) H
        hgdet hGdet hJunit hmetric hLower a b k
    have hJdet : IsUnit (J y).det := (Matrix.isUnit_iff_isUnit_det _).mp hJunit
    have hJTdet : IsUnit (J y).transpose.det := by simpa only [Matrix.det_transpose] using hJdet
    have hinv : (g y)⁻¹ = (J y)⁻¹ * (G (T y))⁻¹ * (J y).transpose⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [hmetric]
      calc
        ((J y).transpose * G (T y) * J y) * ((J y)⁻¹ * (G (T y))⁻¹ * (J y).transpose⁻¹) =
            (J y).transpose * G (T y) * (J y * (J y)⁻¹) * (G (T y))⁻¹ * (J y).transpose⁻¹ := by
          simp only [Matrix.mul_assoc]
        _ = (J y).transpose * (G (T y) * (G (T y))⁻¹) * (J y).transpose⁻¹ := by
          rw [Matrix.mul_nonsing_inv _ hJdet, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
        _ = 1 := by rw [Matrix.mul_nonsing_inv _ hGdet, Matrix.mul_one,
          Matrix.mul_nonsing_inv _ hJTdet]
    have hc : ∀ a b, hessianCoefficient2 g (u ∘ T) y a b =
        ∑ s : Fin 2, ∑ t : Fin 2,
          hessianCoefficient2 G u (T y) s t * J y s a * J y t b := by
      intro a b
      have hchain := second_derivative_composition_apply u T y (basis2 a) (basis2 b)
        (hT.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))) hu
      have hfirst := fderiv_comp y (hu.differentiableAt (by norm_num))
        (hT.differentiableAt (by simp))
      have hlinear (L : RVec 2 →L[ℝ] ℝ) (v : RVec 2) : L v =
          ∑ k : Fin 2, L (basis2 k) * v k := by
        conv_lhs => rw [← hsum v]
        simp only [map_sum, map_smul, smul_eq_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      have hbilinear (B : RVec 2 →L[ℝ] RVec 2 →L[ℝ] ℝ) (v w : RVec 2) : B v w =
          ∑ s : Fin 2, ∑ t : Fin 2, B (basis2 s) (basis2 t) * v s * w t := by
        conv_lhs => rw [← hsum v, ← hsum w]
        simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
        ring
      have hsecond : ∀ k, (fderiv ℝ (fderiv ℝ T) y (basis2 a) (basis2 b)) k = H k a b :=
        fun k => ((hJacobian T y hT).2.1 k a b).symm
      unfold hessianCoefficient2
      rw [hchain, hfirst]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hbilinear, hlinear (fderiv ℝ u (T y))]
      simp_rw [hsecond]
      have hlf (k : Fin 2) := hlinear (fderiv ℝ u (T y)) (fderiv ℝ T y (basis2 k))
      simp_rw [hlf]
      change _ = ∑ s : Fin 2, ∑ t : Fin 2, _ * J y s a * J y t b
      have hg0 := hGamma a b 0
      have hg1 := hGamma a b 1
      simp only [Fin.sum_univ_two] at hg0 hg1 ⊢
      dsimp only [J] at hg0 hg1
      linear_combination
        -(fderiv ℝ u (T y) (basis2 0)) * hg0 -
        (fderiv ℝ u (T y) (basis2 1)) * hg1
    have ht : (J y) * (g y)⁻¹ * (J y).transpose = (G (T y))⁻¹ := by
      rw [hinv]
      calc
        J y * ((J y)⁻¹ * (G (T y))⁻¹ * (J y).transpose⁻¹) * (J y).transpose =
            (J y * (J y)⁻¹) * (G (T y))⁻¹ * ((J y).transpose⁻¹ * (J y).transpose) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [Matrix.mul_nonsing_inv _ hJdet,
          Matrix.nonsing_inv_mul _ hJTdet, Matrix.one_mul, Matrix.mul_one]
    unfold laplacian2
    simp_rw [hc]
    rw [← ht]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
    ring
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: SourceInteriorGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface)
def sourceOverlap (p q : S) : Set (RVec 2) :=
  (extChartAt SurfaceModel p).target ∩
    (extChartAt SurfaceModel p).symm ⁻¹' (extChartAt SurfaceModel q).source
def sourceTransition (p q : S) : RVec 2 → RVec 2 :=
  (extChartAt SurfaceModel q) ∘ (extChartAt SurfaceModel p).symm

theorem source_overlap_nhds (p q z : S) (hzp : z ∈ (extChartAt SurfaceModel p).source)
    (hzq : z ∈ (extChartAt SurfaceModel q).source)
    (hz : z ∈ SurfaceModel.interior S) :
    sourceOverlap S p q ∈ 𝓝 (extChartAt SurfaceModel p z) := by
  have hx : extChartAt SurfaceModel p z ∈ interior (extChartAt SurfaceModel p).target := by
    exact (SurfaceModel.isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p)
      (by simpa only [extChartAt_source] using hzp)).mp hz
  apply inter_mem (mem_interior_iff_mem_nhds.mp hx)
  apply ((continuousOn_extChartAt_symm p).continuousAt (mem_interior_iff_mem_nhds.mp hx)).preimage_mem_nhds
  simpa only [(extChartAt SurfaceModel p).left_inv hzp] using
    (isOpen_extChartAt_source q).mem_nhds hzq

theorem source_transition_smooth_invertible (p q z : S)
    (hzp : z ∈ (extChartAt SurfaceModel p).source)
    (hzq : z ∈ (extChartAt SurfaceModel q).source)
    (hz : z ∈ SurfaceModel.interior S) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceTransition S p q) (extChartAt SurfaceModel p z) ∧
    (fderiv ℝ (sourceTransition S p q) (extChartAt SurfaceModel p z)).IsInvertible := by
  have hn := source_overlap_nhds S p q z hzp hzq hz
  have hx : extChartAt SurfaceModel p z ∈ sourceOverlap S p q :=
    mem_of_mem_nhds hn
  have hs := ModelWithCorners.contDiffOn_extendCoordChange
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p)
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) q)
  have hb := ModelWithCorners.isInvertible_fderivWithin_extendCoordChange
    (I := SurfaceModel) (by simp : ((∞ : ℕ∞ω) : ℕ∞ω) ≠ 0)
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p)
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) q) hx
  change ContDiffOn ℝ (∞ : ℕ∞ω) (sourceTransition S p q) (sourceOverlap S p q) at hs
  change (fderivWithin ℝ (sourceTransition S p q) (sourceOverlap S p q)
    (extChartAt SurfaceModel p z)).IsInvertible at hb
  rw [fderivWithin_of_mem_nhds hn] at hb
  exact ⟨hs.contDiffAt hn, hb⟩

theorem source_inverse_differential_overlap (p q : S) (y : RVec 2)
    (hy : y ∈ sourceOverlap S p q) (w : RVec 2) :
    mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
      (range SurfaceModel) y w =
    mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel q).symm
      (range SurfaceModel) (sourceTransition S p q y)
      (fderivWithin ℝ (sourceTransition S p q) (sourceOverlap S p q) y w) := by
  let P := extChartAt SurfaceModel p
  let Q := extChartAt SurfaceModel q
  have hyQ : sourceTransition S p q y ∈ Q.target := Q.map_source hy.2
  have hP := mdifferentiableOn_extChartAt_symm (I := SurfaceModel) (x := p) y hy.1
  have hQ := mdifferentiableOn_extChartAt_symm (I := SurfaceModel) (x := q) _ hyQ
  have hu := (ModelWithCorners.uniqueDiffOn_extendCoordChange_source
    (I := SurfaceModel) (e := chartAt (EuclideanHalfSpace 2) p)
    (e' := chartAt (EuclideanHalfSpace 2) q) y hy).uniqueMDiffWithinAt
  have ht := ((ModelWithCorners.contDiffOn_extendCoordChange
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p)
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) q) y hy).differentiableWithinAt
    (by simp)).mdifferentiableWithinAt
  have hm : MapsTo (sourceTransition S p q) (sourceOverlap S p q) Q.target :=
    fun x hx => Q.map_source hx.2
  change UniqueMDiffWithinAt 𝓘(ℝ, RVec 2) (sourceOverlap S p q) y at hu
  change MDifferentiableWithinAt 𝓘(ℝ, RVec 2) 𝓘(ℝ, RVec 2)
    (sourceTransition S p q) (sourceOverlap S p q) y at ht
  change MDifferentiableWithinAt 𝓘(ℝ, RVec 2) SurfaceModel P.symm P.target y at hP
  change MDifferentiableWithinAt 𝓘(ℝ, RVec 2) SurfaceModel Q.symm Q.target
    (sourceTransition S p q y) at hQ
  have hc := mfderivWithin_comp y hQ ht hm hu
  have heq : ∀ x ∈ sourceOverlap S p q,
      (Q.symm ∘ sourceTransition S p q) x = P.symm x := by
    intro x hx
    exact Q.left_inv hx.2
  have hg := mfderivWithin_congr_of_mem (I := 𝓘(ℝ, RVec 2)) (I' := SurfaceModel) heq hy
  rw [hc, hP.mfderivWithin_mono hu inter_subset_left] at hg
  have hv := congrArg (fun d => d ((tangentSpaceCastModel 𝓘(ℝ, RVec 2) y).symm w)) hg
  rw [mfderivWithin_eq_fderivWithin] at hv
  have hPset := mfderivWithin_congr_set (I := 𝓘(ℝ, RVec 2)) (I' := SurfaceModel)
    (f := P.symm) (extChartAt_target_eventuallyEqSet_of_mem (I := SurfaceModel) hy.1)
  have hQset := mfderivWithin_congr_set (I := 𝓘(ℝ, RVec 2)) (I' := SurfaceModel)
    (f := Q.symm) (extChartAt_target_eventuallyEqSet_of_mem (I := SurfaceModel) hyQ)
  rw [hPset, hQset] at hv
  exact hv.symm

theorem native_metric_source_transport (g : SurfaceMetric S) (p q z : S)
    (hzp : z ∈ (extChartAt SurfaceModel p).source)
    (hzq : z ∈ (extChartAt SurfaceModel q).source)
    (hz : z ∈ SurfaceModel.interior S) :
    ∀ i j : Fin 2, (fun y => MetricInChart SurfaceModel g p y i j) =ᶠ[𝓝 (extChartAt SurfaceModel p z)]
      (fun y => ∑ a : Fin 2, ∑ b : Fin 2,
        MetricInChart SurfaceModel g q (sourceTransition S p q y) a b *
          (fderiv ℝ (sourceTransition S p q) y (basis2 i)) a *
          (fderiv ℝ (sourceTransition S p q) y (basis2 j)) b) := by
  have hn := source_overlap_nhds S p q z hzp hzq hz
  intro i j
  filter_upwards [eventually_mem_nhds_iff.mpr hn] with y hy
  have hyN : sourceOverlap S p q ∈ 𝓝 y := by
    exact hy
  have hmem : y ∈ sourceOverlap S p q := mem_of_mem_nhds hyN
  have hd (w : RVec 2) := source_inverse_differential_overlap S p q y hmem w
  rw [fderivWithin_of_mem_nhds hyN] at hd
  have heq : (extChartAt SurfaceModel q).symm (sourceTransition S p q y) =
      (extChartAt SurfaceModel p).symm y := (extChartAt SurfaceModel q).left_inv hmem.2
  have hsum (w : RVec 2) : (∑ a : Fin 2, w a • basis2 a) = w := by
    ext k
    fin_cases k <;> simp [basis2, EuclideanSpace.single]
  have hbilin (v w : RVec 2) :
      g.inner ((extChartAt SurfaceModel p).symm y)
        (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel q).symm
          (range SurfaceModel) (sourceTransition S p q y) v)
        (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel q).symm
          (range SurfaceModel) (sourceTransition S p q y) w) =
      ∑ a : Fin 2, ∑ b : Fin 2,
        MetricInChart SurfaceModel g q (sourceTransition S p q y) a b * v a * w b := by
    rw [← heq]
    conv_lhs => rw [← hsum v, ← hsum w]
    simp only [MetricInChart, basis2, Fin.sum_univ_two, map_add, map_smul,
      add_apply, smul_apply, smul_eq_mul]
    ring
  unfold MetricInChart
  rw [hd, hd]
  exact hbilin _ _
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: SourceLaplacianTransport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface)
theorem native_metric_properties (g : SurfaceMetric S) (p : S) :
    (∀ i j, ContDiffOn ℝ (∞ : ℕ∞ω) (fun x => MetricInChart SurfaceModel g p x i j)
      (extChartAt SurfaceModel p).target) ∧
    (∀ x i j, MetricInChart SurfaceModel g p x i j = MetricInChart SurfaceModel g p x j i) ∧
    ∀ x ∈ (extChartAt SurfaceModel p).target, (MetricInChart SurfaceModel g p x).PosDef := by
  have hh := actual_surface_metric_properties S g (chartAt (EuclideanHalfSpace 2) p)
    (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply (hh.1 i j).congr
    intro x hx
    exact congrFun (congrFun (native_surface_metric S g p x hx) i) j
  · intro x i j
    exact g.symm _ _ _
  · intro x hx
    rw [native_surface_metric S g p x hx]
    exact hh.2.2 x hx

theorem scalar_in_source_chart (u : S → ℝ)
    (hu : ContMDiff SurfaceModel 𝓘(ℝ, ℝ) 2 u) (p : S) :
    ContDiffOn ℝ 2 (u ∘ (extChartAt SurfaceModel p).symm)
      (extChartAt SurfaceModel p).target := by
  have hh := hu.comp_contMDiffOn
    ((contMDiffOn_extChartAt_symm (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p).of_le
      (by norm_num : (2 : ℕ∞ω) ≤ ((∞ : ℕ∞ω) : ℕ∞ω)))
  exact hh.contDiffOn

theorem chart_laplacian_of_interior_target (g : SurfaceMetric S) (p : S)
    (v : RVec 2 → ℝ) (x : RVec 2)
    (hx : x ∈ interior (extChartAt SurfaceModel p).target) :
    chartLaplacian S g p v x = laplacian2 (MetricInChart SurfaceModel g p) v x := by
  have hn : (extChartAt SurfaceModel p).target ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  have hg (v : RVec 2 → ℝ) :
      (fun z => fderivWithin ℝ v (extChartAt SurfaceModel p).target z) =ᶠ[𝓝 x] fderiv ℝ v := by
    filter_upwards [isOpen_interior.mem_nhds hx] with z hz
    exact fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
  have hsecond := (hg v).fderivWithin_eq_of_nhds (𝕜 := ℝ)
    (s := (extChartAt SurfaceModel p).target)
  unfold chartLaplacian sourceChristoffel laplacian2 hessianCoefficient2 ChristoffelCoordinate
  dsimp only
  rw [hsecond]
  simp only [fderivWithin_of_mem_nhds hn, basis2]

theorem native_fixed_chart_laplacian (g : SurfaceMetric S) (u : S → ℝ)
    (hu : ContMDiff SurfaceModel 𝓘(ℝ, ℝ) 2 u) (p q : S)
    (hqp : q ∈ (extChartAt SurfaceModel p).source)
    (hq : q ∈ SurfaceModel.interior S) :
    chartLaplacian S g p (u ∘ (extChartAt SurfaceModel p).symm)
      (extChartAt SurfaceModel p q) = laplacian S g u q := by
  have hqq := mem_extChartAt_source (I := SurfaceModel) q
  have hxp : extChartAt SurfaceModel p q ∈ interior (extChartAt SurfaceModel p).target := by
    exact (SurfaceModel.isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 2) p)
      (by simpa only [extChartAt_source] using hqp)).mp hq
  have hxq : extChartAt SurfaceModel q q ∈ interior (extChartAt SurfaceModel q).target :=
    SurfaceModel.isInteriorPoint_iff.mp hq
  let T := sourceTransition S p q
  let Gp := MetricInChart SurfaceModel g p
  let Gq := MetricInChart SurfaceModel g q
  let vq := u ∘ (extChartAt SurfaceModel q).symm
  let x := extChartAt SurfaceModel p q
  have hTx : T x = extChartAt SurfaceModel q q := by
    simp only [T, x, sourceTransition, Function.comp_def, (extChartAt SurfaceModel p).left_inv hqp]
  have ht := source_transition_smooth_invertible S p q q hqp hqq hq
  have hvq : ContDiffAt ℝ 2 vq (T x) := by
    rw [hTx]
    exact (scalar_in_source_chart S u hu q).contDiffAt (mem_interior_iff_mem_nhds.mp hxq)
  have hGqdiff (i j : Fin 2) : DifferentiableAt ℝ (fun y => Gq y i j) (T x) := by
    rw [hTx]
    exact (((native_metric_properties S g q).1 i j).contDiffAt
      (mem_interior_iff_mem_nhds.mp hxq)).differentiableAt (by simp)
  have hgerm : (u ∘ (extChartAt SurfaceModel p).symm) =ᶠ[𝓝 x] vq ∘ T := by
    filter_upwards [source_overlap_nhds S p q q hqp hqq hq] with y hy
    exact congrArg u ((extChartAt SurfaceModel q).left_inv hy.2).symm
  have hfirst := hgerm.fderiv_eq (𝕜 := ℝ)
  have hsecond := (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  have htransport := euclidean_source_laplacian_transport Gp Gq T vq x ht.1 ht.2.bijective hvq
    hGqdiff (native_metric_properties S g q).2.1 (native_metric_properties S g p).2.1
    (isUnit_iff_ne_zero.mpr (ne_of_gt (((native_metric_properties S g p).2.2 x (interior_subset hxp)).det_pos)))
    (by rw [hTx]; exact isUnit_iff_ne_zero.mpr (ne_of_gt (((native_metric_properties S g q).2.2 _ (interior_subset hxq)).det_pos)))
    (native_metric_source_transport S g p q q hqp hqq hq)
  unfold laplacian
  rw [chart_laplacian_of_interior_target S g p _ _ hxp,
    chart_laplacian_of_interior_target S g q _ _ hxq]
  change laplacian2 Gp _ x = laplacian2 Gq vq _
  unfold laplacian2 hessianCoefficient2 at htransport ⊢
  rw [hfirst, hsecond]
  rw [htransport, hTx]
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: SourceOperatorBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface)

theorem native_chart_laplacian_eq_coordinates (g : SurfaceMetric S) (p : S)
    (v : RVec 2 → ℝ) (x : RVec 2) (hx : x ∈ (extChartAt SurfaceModel p).target) :
    chartLaplacian S g p v x =
      laplacianInCoordinates S g (chartAt (EuclideanHalfSpace 2) p) v x := by
  have hG := native_surface_metric S g p x hx
  have hd (i j : Fin 2) : fderivWithin ℝ (fun y => MetricInChart SurfaceModel g p y i j)
      (extChartAt SurfaceModel p).target x =
      fderivWithin ℝ (fun y => metricInCoordinates S g (chartAt (EuclideanHalfSpace 2) p) y i j)
      (extChartAt SurfaceModel p).target x := by
    apply fderivWithin_congr' _ hx
    intro y hy
    exact congrFun (congrFun (native_surface_metric S g p y hy) i) j
  unfold chartLaplacian sourceChristoffel laplacianInCoordinates christoffelInCoordinates
  dsimp only
  simp only [hG, hd]
  rfl
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: C6TraceSign
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem pulled_trace_nonpos (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (f : S → N) (p : S) (hp : r (f p) < ε) :
    pulledHessianTrace S g h r f p ≤ 0 := by
  obtain ⟨B, hB⟩ := covariant_hessian_bilinear h r (f p)
  let D : RVec 2 →L[ℝ] RVec 3 := mfderiv SurfaceModel AmbientModel f p
  let H : RVec 2 →L[ℝ] RVec 2 →L[ℝ] ℝ := B.bilinearComp D D
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j => (H (basis2 i) (basis2 j) + H (basis2 j) (basis2 i)) / 2
  have hquad (v : RVec 2) : H v v ≤ 0 := by
    change B (D v) (D v) ≤ 0
    rw [← hB]
    exact (native_collar_hessian_sign_radial h r ε collar (f p) hp (D v)).1
  have hH : (-M).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.ext
      intro i j
      simp only [Matrix.neg_apply, star_trivial, M]
      ring
    · intro ξ
      have hh := hquad (WithLp.toLp 2 ξ)
      rw [EllipticPdes.Classical.sndFDeriv_apply_eq_sum H] at hh
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Matrix.neg_apply,
        M, Fin.sum_univ_two, EllipticPdes.Classical.e, basis2] at hh ⊢
      nlinarith only [hh]
  have hA := ((native_metric_properties S g p).2.2 _
    (mem_extChartAt_target (I := SurfaceModel) p)).inv.posSemidef
  have h01 : (MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p))⁻¹ 0 1 =
      (MetricInChart SurfaceModel g p (extChartAt SurfaceModel p p))⁻¹ 1 0 := by
    have hh := congrFun (congrFun hA.1 0) 1
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh.symm
  have htrace := EllipticPdes.Classical.sum_mul_nonpos_of_posSemidef hA hH
  rw [pulled_trace_native S g h r f p]
  simp_rw [hB]
  convert htrace using 1
  simp only [M, H, D, ContinuousLinearMap.bilinearComp_apply, basis2, Fin.sum_univ_two]
  rw [h01]
  ring <;> rfl
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private support: NativeC11
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem native_c11_local_minimum
    (g : SurfaceMetric S) (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ)
    (collar : WarpedCollar h r ε) (f : C(S, N))
    (hf : C2HolderUpToBoundary f) (hh : HarmonicInterior g h f)
    (p : S) (hp : p ∈ SurfaceModel.interior S)
    (hneg : r (f p) < 0) (hmin : IsLocalMin (r ∘ f) p) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, r (f q) = r (f p) := by
  let c := chartAt (EuclideanHalfSpace 2) p
  let E := extChartAt SurfaceModel p
  let x := E p
  let v := (r ∘ f) ∘ E.symm
  have hu := scalar_composition_regular S r collar.smooth_height f hf
  obtain ⟨V, a, b, θ, A, B, hV, hxV, hθ, ha, hb, hcoeff⟩ :=
    actual_metric_locally_uniform_elliptic S g c
      (IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p)
      p (mem_chart_source (EuclideanHalfSpace 2) p)
  have hxI : x ∈ interior E.target := SurfaceModel.isInteriorPoint_iff.mp hp
  have hv : ContDiffOn ℝ 2 v E.target := scalar_in_source_chart S (r ∘ f) hu p
  have hminx : ∀ᶠ y in 𝓝 x, v x ≤ v y := by
    change ∀ᶠ q in 𝓝 p, r (f p) ≤ r (f q) at hmin
    have hmin' : ∀ᶠ q in 𝓝 (E.symm x), r (f p) ≤ r (f q) := by
      simpa only [E, x, extChartAt_to_inv] using hmin
    have hh := (continuousAt_extChartAt_symm (I := SurfaceModel) p).tendsto.eventually hmin'
    simpa only [v, x, E, Function.comp_def, extChartAt_to_inv] using hh
  have heps : ∀ᶠ y in 𝓝 x, v y < ε := by
    have hc : ContinuousAt v x := by
      exact (collar.smooth_height.continuous.comp f.continuous).continuousAt.comp
        (continuousAt_extChartAt_symm (I := SurfaceModel) p)
    apply hc.eventually (gt_mem_nhds (show v x < ε by
      simp only [v, x, E, Function.comp_def, extChartAt_to_inv]
      exact hneg.trans collar.epsilon_pos))
  have hn : (V ∩ interior E.target ∩ {y | v x ≤ v y} ∩ {y | v y < ε}) ∈ 𝓝 x :=
    inter_mem (inter_mem (inter_mem (hV.mem_nhds hxV)
      (isOpen_interior.mem_nhds hxI)) hminx) heps
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let W := Metric.ball x ρ
  have hxW : x ∈ W := Metric.mem_ball_self hρ
  have hWT : W ⊆ E.target := fun y hy => interior_subset (hball hy).1.1.2
  have hWVT (y : RVec 2) (hy : y ∈ W) : y ∈ V ∩ (extendedCoordinates S c).target :=
    ⟨(hball hy).1.1.1, hWT hy⟩
  have hWV : ContDiffOn ℝ 2 v W := hv.mono hWT
  have hsub : ∀ y ∈ W, EllipticPdes.Classical.nondivOp a (fun y i => -b y i)
      (fun _ => 0) (-v) y ≤ 0 := by
    intro y hy
    have hyI := (hball hy).1.1.2
    have hyT := interior_subset hyI
    have hyS := E.map_target hyT
    have hq : E.symm y ∈ SurfaceModel.interior S := by
      apply (SurfaceModel.isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) p)
        (by simpa only [E, extChartAt_source] using hyS)).mpr
      change E (E.symm y) ∈ interior E.target
      rw [E.right_inv hyT]
      exact hyI
    have htrace := native_interior_harmonic_trace S g h r collar.smooth_height f hf hh (E.symm y) hq
    have hnonpos := pulled_trace_nonpos S g h r ε collar f (E.symm y) (hball hy).2
    have hfixed := native_fixed_chart_laplacian S g (r ∘ f) hu p (E.symm y) hyS hq
    rw [E.right_inv hyT] at hfixed
    have hop := (hcoeff y (hWVT y hy)).2.2.2 v
    have hnn : laplacianInCoordinates S g c v y ≤ 0 := by
      change laplacianInCoordinates S g (chartAt (EuclideanHalfSpace 2) p) v y ≤ 0
      rw [← native_chart_laplacian_eq_coordinates S g p v y hyT, hfixed, htrace]
      exact hnonpos
    have hnT : E.target ∈ 𝓝 y := mem_interior_iff_mem_nhds.mp hyI
    have hgerm : (fun z => fderivWithin ℝ v E.target z) =ᶠ[𝓝 y] fderiv ℝ v := by
      filter_upwards [isOpen_interior.mem_nhds hyI] with z hz
      exact fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hz)
    have hsecond := hgerm.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := E.target)
    change laplacianInCoordinates S g c v y =
      (∑ i : Fin 2, ∑ j : Fin 2, a y i j * fderivWithin ℝ
        (fun z => fderivWithin ℝ v E.target z) E.target y (basis2 i) (basis2 j)) +
      ∑ i : Fin 2, b y i * fderivWithin ℝ v E.target y (basis2 i) at hop
    rw [hsecond] at hop
    simp only [fderivWithin_of_mem_nhds hnT] at hop
    rw [hop] at hnn
    have hd : DifferentiableAt ℝ (fderiv ℝ (-v)) y :=
      (((hWV.neg y hy).contDiffAt (Metric.isOpen_ball.mem_nhds hy)).fderiv_right
        (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hnegfirst : fderiv ℝ (-v) = -(fderiv ℝ v) := funext (fun z => fderiv_neg)
    unfold EllipticPdes.Classical.nondivOp
    simp_rw [EllipticPdes.Classical.partialD_partialD_eq hd]
    simp only [hnegfirst, EllipticPdes.Sobolev.partialD, fderiv_neg, fderiv_fun_neg,
      neg_apply, mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib, zero_mul, add_zero,
      EllipticPdes.Classical.e, basis2]
    exact hnn
  have hconst := EllipticPdes.Classical.strong_maximum_principle (by norm_num : 0 < 2)
    Metric.isOpen_ball (convex_ball x ρ).isPreconnected hθ
    (fun y hy i j => ((hcoeff y (hWVT y hy)).1 i j).1)
    (fun y hy ξ => (hcoeff y (hWVT y hy)).2.2.1 ξ)
    (fun y hy i j => ((hcoeff y (hWVT y hy)).1 i j).2)
    (fun y hy i => by simpa only [abs_neg] using (hcoeff y (hWVT y hy)).2.1 i)
    (fun _ _ => le_refl (0 : ℝ)) (C := 0) (fun _ _ => le_refl (0 : ℝ))
    hWV.neg hsub hxW (fun y hy => neg_le_neg ((hball hy).1.2))
    (fun _ _ => by simp)
  let U : Set S := E.source ∩ E ⁻¹' W
  refine ⟨U, ?_, ⟨mem_extChartAt_source p, hxW⟩, ?_⟩
  · simpa only [U, E, W, extChartAt_source] using
      isOpen_extChartAt_preimage (I := SurfaceModel) p (s := W) Metric.isOpen_ball
  · intro q hq
    have hc := hconst (E q) hq.2
    simpa only [v, x, E, Pi.neg_apply, neg_inj, Function.comp_def,
      extChartAt_to_inv, (extChartAt SurfaceModel p).left_inv hq.1] using hc

theorem native_c11_barrier [ConnectedSpace S]
    (hboundary : (SurfaceModel.boundary S).Nonempty)
    (g : SurfaceMetric S) (h : AmbientMetric N) (r : N → ℝ) (ε : ℝ)
    (collar : WarpedCollar h r ε) (M curve : Set N)
    (hcore : M = {q | 0 ≤ r q}) (hcurve : curve ⊆ {q | r q = 0})
    (f : C(S, N)) (hf : LemaireMinimizer S g h f curve) :
    range f ⊆ M ∧ ∀ p : S, 0 ≤ r (f p) := by
  have hzero (p : S) (hp : p ∈ SurfaceModel.boundary S) : r (f p) = 0 := by
    apply hcurve
    exact hf.boundary.boundary_maps hp
  have hnonneg := c11_barrier_from_local_minimum_principle (r ∘ f)
    (collar.smooth_height.continuous.comp f.continuous) (SurfaceModel.boundary S)
    hboundary hzero (fun p hneg hmin => by
      have hp : p ∈ SurfaceModel.interior S := by
        rw [← SurfaceModel.compl_boundary]
        intro hb
        exact (ne_of_lt hneg) (hzero p hb)
      exact native_c11_local_minimum S g h r ε collar f hf.regularity hf.harmonic p hp hneg hmin)
  refine ⟨?_, hnonneg⟩
  rintro q ⟨p, rfl⟩
  rw [hcore]
  exact hnonneg p
end SeifertSurfaces.PrivateHelpers.C6Native


-- Paid private boundary support: FixedPullTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations

theorem coordinate_bilinear_trace_transport (G : Matrix (Fin 2) (Fin 2) ℝ)
    (A : RVec 2 →L[ℝ] RVec 2) (hA : Function.Bijective A)
    (G' : Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsUnit G.det)
    (hmetric : ∀ i j, G' i j = ∑ a : Fin 2, ∑ b : Fin 2,
      G a b * (A (basis2 i)) a * (A (basis2 j)) b)
    (H : RVec 2 →L[ℝ] RVec 2 →L[ℝ] ℝ) :
    (∑ i : Fin 2, ∑ j : Fin 2, G'⁻¹ i j * H (A (basis2 i)) (A (basis2 j))) =
      ∑ i : Fin 2, ∑ j : Fin 2, G⁻¹ i j * H (basis2 i) (basis2 j) := by
  let D : Matrix (Fin 2) (Fin 2) ℝ := fun a i => A (basis2 i) a
  have hsum (v : RVec 2) : (∑ i : Fin 2, v i • basis2 i) = v := by
    ext j
    fin_cases j <;> simp [basis2, EuclideanSpace.single]
  have hrepr (v : RVec 2) (a : Fin 2) : A v a = ∑ i : Fin 2, D a i * v i := by
    conv_lhs => rw [← hsum v]
    simp only [map_sum, map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, D]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hD : IsUnit D := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro v w hvw
    have hh : (WithLp.toLp 2 v : RVec 2) = WithLp.toLp 2 w := by
      apply hA.injective
      ext a
      rw [hrepr, hrepr]
      exact congrFun hvw a
    exact WithLp.toLp_injective 2 hh
  have hDdet := (Matrix.isUnit_iff_isUnit_det _).mp hD
  have hDTdet : IsUnit D.transpose.det := by simpa only [Matrix.det_transpose] using hDdet
  have hmet : G' = D.transpose * G * D := by
    ext i j
    rw [hmetric]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, D, Fin.sum_univ_two]
    ring
  have hinv : G'⁻¹ = D⁻¹ * G⁻¹ * D.transpose⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hmet]
    calc
      (D.transpose * G * D) * (D⁻¹ * G⁻¹ * D.transpose⁻¹) =
          D.transpose * G * (D * D⁻¹) * G⁻¹ * D.transpose⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D.transpose * (G * G⁻¹) * D.transpose⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hDdet, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hG, Matrix.mul_one,
        Matrix.mul_nonsing_inv _ hDTdet]
  have ht : D * G'⁻¹ * D.transpose = G⁻¹ := by
    rw [hinv]
    calc
      D * (D⁻¹ * G⁻¹ * D.transpose⁻¹) * D.transpose =
          (D * D⁻¹) * G⁻¹ * (D.transpose⁻¹ * D.transpose) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hDdet, Matrix.nonsing_inv_mul _ hDTdet,
        Matrix.one_mul, Matrix.mul_one]
  have hbilin (v w : RVec 2) : H v w = ∑ a : Fin 2, ∑ b : Fin 2,
      H (basis2 a) (basis2 b) * v a * w b := by
    conv_lhs => rw [← hsum v, ← hsum w]
    simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hbilinA (i j : Fin 2) := hbilin (A (basis2 i)) (A (basis2 j))
  simp_rw [hbilinA]
  rw [← ht]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, D, Fin.sum_univ_two, basis2,
    EuclideanSpace.single, PiLp.single_apply]
  ring

variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
def fixedPulledTrace (g : SurfaceMetric S) (h : AmbientMetric N) (r : N → ℝ)
    (f : S → N) (p : S) (x : RVec 2) : ℝ :=
  let q := (extChartAt SurfaceModel p).symm x
  let A := mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
    (range SurfaceModel) x
  ∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p x)⁻¹ i j *
    covariantHessian h r (f q)
      (mfderiv SurfaceModel AmbientModel f q (A (basis2 i)))
      (mfderiv SurfaceModel AmbientModel f q (A (basis2 j)))

theorem fixed_pulled_trace_eq_native (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (f : S → N) (p : S) (x : RVec 2)
    (hx : x ∈ (extChartAt SurfaceModel p).target) :
    fixedPulledTrace S g h r f p x =
      pulledHessianTrace S g h r f ((extChartAt SurfaceModel p).symm x) := by
  let q := (extChartAt SurfaceModel p).symm x
  let A : RVec 2 →L[ℝ] RVec 2 := mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel
    (extChartAt SurfaceModel p).symm (range SurfaceModel) x
  let G := MetricInChart SurfaceModel g q (extChartAt SurfaceModel q q)
  obtain ⟨B, hB⟩ := covariant_hessian_bilinear h r (f q)
  let D : RVec 2 →L[ℝ] RVec 3 := mfderiv SurfaceModel AmbientModel f q
  let H : RVec 2 →L[ℝ] RVec 2 →L[ℝ] ℝ := B.bilinearComp D D
  have hsum (v : RVec 2) : (∑ i : Fin 2, v i • basis2 i) = v := by
    ext j
    fin_cases j <;> simp [basis2, EuclideanSpace.single]
  have hmetric (i j : Fin 2) : MetricInChart SurfaceModel g p x i j =
      ∑ a : Fin 2, ∑ b : Fin 2, G a b * (A (basis2 i)) a * (A (basis2 j)) b := by
    dsimp only [G]
    rw [native_surface_center_metric S g q]
    change g.inner q (A (basis2 i)) (A (basis2 j)) = _
    conv_lhs => rw [← hsum (A (basis2 i)), ← hsum (A (basis2 j))]
    simp only [Fin.sum_univ_two, map_add, map_smul, add_apply, smul_apply, smul_eq_mul, basis2]
    ring
  have hA : Function.Bijective A := (isInvertible_mfderivWithin_extChartAt_symm
    (I := SurfaceModel) (x := p) hx).bijective
  have hG : IsUnit G.det := isUnit_iff_ne_zero.mpr (ne_of_gt
    (((native_metric_properties S g q).2.2 _ (mem_extChartAt_target q)).det_pos))
  have ht := coordinate_bilinear_trace_transport G A hA
    (MetricInChart SurfaceModel g p x) hG hmetric H
  unfold fixedPulledTrace
  dsimp only
  change (∑ i : Fin 2, ∑ j : Fin 2, (MetricInChart SurfaceModel g p x)⁻¹ i j *
    covariantHessian h r (f q) (D (A (basis2 i))) (D (A (basis2 j)))) =
    pulledHessianTrace S g h r f q
  rw [pulled_trace_native S g h r f q]
  simp_rw [hB]
  exact ht
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: FixedCollarQuadratic
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints SeifertSurfaces.AppendixACoordinates
variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem fixed_collar_quadratic (h : AmbientMetric N) (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r)
    (d : SmoothAmbientChart N) (K : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hrc : ∀ q ∈ d.chart.source, r q = d.chart q 0)
    (hm : ∀ z ∈ d.chart.target, ∀ v w : E3,
      coordinateInner (actualChartTensor h d) z v w = v 0 * w 0 + (1-z 0)^2 *
        ∑ i : Fin 2, ∑ j : Fin 2, K (levelCoordinates z) i j * v i.succ * w j.succ)
    (q : N) (hq : q ∈ d.chart.source) (hqr : r q < 1)
    (v : TangentSpace AmbientModel q) :
    covariantHessian h r q v v =
      (r q - 1) / (1 - r q)^2 * ∑ i : Fin 2, ∑ j : Fin 2,
        actualChartTensor h d (d.chart q) i.succ j.succ *
          (chartDifferential d q v) i.succ * (chartDifferential d q v) j.succ := by
  let e := ambientNativeChart q
  have hqe : q ∈ e.chart.source := mem_chart_source E3 q
  have hye : e.chart q ∈ e.chart.target := e.chart.map_source hqe
  have heinv : e.chart.symm (e.chart q) = q := e.chart.left_inv hqe
  rw [covariant_hessian_chart_quadratic h r hr]
  rw [radial_hessian_chart_transport r d e hrc (e.chart q) hye (by rw [heinv]; exact hq)]
  have hcoord : r ∘ d.chart.symm =ᶠ[𝓝 (d.chart q)] (fun z : E3 => z 0) := by
    filter_upwards [d.chart.open_target.mem_nhds (d.chart.map_source hq)] with z hz
    rw [Function.comp_apply, hrc _ (d.chart.map_target hz), d.chart.right_inv hz]
  have hgerm (G : MetricTensor) (R T : E3 → ℝ) (x v : E3)
      (heq : R =ᶠ[𝓝 x] T) : hessianQuadratic G R x v = hessianQuadratic G T x v := by
    have hfirst (a : Fin 3) : partial3 R x a = partial3 T x a :=
      congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) heq.fderiv_eq
    have hsecond (a b : Fin 3) : partial3 (fun z => partial3 R z b) x a =
        partial3 (fun z => partial3 T z b) x a := by
      have hn : (fun z => partial3 R z b) =ᶠ[𝓝 x] (fun z => partial3 T z b) :=
        heq.fderiv.mono (fun z hz => congrArg
        (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 b)) hz)
      exact congrArg (fun L : E3 →L[ℝ] ℝ => L (coordinateVector 3 a)) hn.fderiv_eq
    simp only [hessianQuadratic, hessianCoefficient, hfirst, hsecond]
  rw [heinv]
  rw [hgerm _ _ _ _ _ hcoord, linear_warped_coordinate_hessian d K hm
    (d.chart q) (d.chart.map_source hq)]
  have hMD (c : SmoothAmbientChart N) : c.chart.MDifferentiable AmbientModel AmbientModel :=
    ⟨c.smooth.mdifferentiableOn (by simp), c.inverse_smooth.mdifferentiableOn (by simp)⟩
  have ht : fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart q)
      (chartDifferential e q v) = chartDifferential d q v := by
    have hh := mfderiv_comp (e.chart q)
      ((hMD d).mdifferentiableAt (by rw [heinv]; exact hq))
      ((hMD e).mdifferentiableAt_symm hye)
    rw [mfderiv_eq_fderiv] at hh
    change fderiv ℝ (d.chart ∘ e.chart.symm) (e.chart q) =
      (mfderiv AmbientModel AmbientModel d.chart (e.chart.symm (e.chart q))).comp
        (mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q)) at hh
    rw [hh]
    have hInv := congrArg (fun L : E3 →L[ℝ] E3 => L v) ((hMD e).symm_comp_deriv hqe)
    change (mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q))
      (mfderiv AmbientModel AmbientModel e.chart q v) = v at hInv
    change (mfderiv AmbientModel AmbientModel d.chart (e.chart.symm (e.chart q)))
      ((mfderiv AmbientModel AmbientModel e.chart.symm (e.chart q))
        ((mfderiv AmbientModel AmbientModel e.chart q) v)) =
      (mfderiv AmbientModel AmbientModel d.chart q) v
    rw [hInv, heinv]
  rw [ht, ← hrc q hq]
  have hentries (i j : Fin 2) : actualChartTensor h d (d.chart q) i.succ j.succ =
      (1-r q)^2 * K (levelCoordinates (d.chart q)) i j := by
    have hh := hm (d.chart q) (d.chart.map_source hq)
      (coordinateVector 3 i.succ) (coordinateVector 3 j.succ)
    simpa [coordinateInner, coordinateVector, EuclideanSpace.single, PiLp.single_apply,
      ← hrc q hq] using hh
  simp_rw [hentries]
  have hn : 1 - r q ≠ 0 := ne_of_gt (sub_pos.mpr hqr)
  simp only [Fin.sum_univ_two]
  field_simp <;> ring
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: FixedCollarCoordinateMap
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem fixed_collar_coordinate_smooth (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (d : SmoothAmbientChart N) (W : Set (RVec 2))
    (hmap : MapsTo (f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) d.chart.source) :
    ContDiffOn ℝ 2 (d.chart ∘ f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) := by
  have hi := ((contMDiffOn_extChartAt_symm (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p).of_le
    (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).mono (inter_subset_right (s := W))
  have hh := hf.comp_contMDiffOn hi
  have hd := (d.smooth.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))).comp hh hmap
  exact hd.contDiffOn

theorem fixed_collar_coordinate_derivative (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (d : SmoothAmbientChart N) (W : Set (RVec 2)) (hW : IsOpen W)
    (hmap : MapsTo (f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) d.chart.source)
    (x : RVec 2) (hx : x ∈ W ∩ (extChartAt SurfaceModel p).target) (v : RVec 2) :
    fderivWithin ℝ (d.chart ∘ f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) x v =
    chartDifferential d (f ((extChartAt SurfaceModel p).symm x))
      (mfderiv SurfaceModel AmbientModel f ((extChartAt SurfaceModel p).symm x)
        (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
          (range SurfaceModel) x v)) := by
  let D := W ∩ (extChartAt SurfaceModel p).target
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, RVec 2) D x := by
    apply UniqueDiffWithinAt.uniqueMDiffWithinAt
    simpa only [inter_comm] using (uniqueDiffOn_extChartAt_target (I := SurfaceModel) p x hx.2).inter
      (hW.mem_nhds hx.1)
  have hi := (mdifferentiableOn_extChartAt_symm (I := SurfaceModel) (x := p) x hx.2).mono (inter_subset_right (s := W))
  have hfmd := hf.mdifferentiable (by norm_num) ((extChartAt SurfaceModel p).symm x)
  have hfcomp := hfmd.comp_mdifferentiableWithinAt x hi
  have hdmd := (d.smooth.contMDiffAt (d.chart.open_source.mem_nhds (hmap hx))).mdifferentiableAt (by simp)
  have hdchain := mfderiv_comp_mfderivWithin x hdmd hfcomp hu
  have hfchain := mfderiv_comp_mfderivWithin x hfmd hi hu
  have hgerm : D =ᶠ[𝓝 x] (extChartAt SurfaceModel p).target := by
    filter_upwards [hW.mem_nhds hx.1] with y hy
    simp only [D, mem_inter_iff, hy, true_and]
  have hiset := mfderivWithin_congr_set (I := 𝓘(ℝ, RVec 2)) (I' := SurfaceModel)
    (f := (extChartAt SurfaceModel p).symm) hgerm
  have hirange := mfderivWithin_congr_set (I := 𝓘(ℝ, RVec 2)) (I' := SurfaceModel)
    (f := (extChartAt SurfaceModel p).symm)
    (extChartAt_target_eventuallyEqSet_of_mem (I := SurfaceModel) hx.2)
  rw [hfchain, hiset, hirange] at hdchain
  rw [mfderivWithin_eq_fderivWithin] at hdchain
  have hv := congrArg (fun L => L ((tangentSpaceCastModel 𝓘(ℝ, RVec 2) x).symm v)) hdchain
  exact hv
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: FixedPullTraceContinuity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
def collarCoordinateQuad (h : AmbientMetric N) (r : N → ℝ) (f : S → N)
    (p : S) (d : SmoothAmbientChart N) (W : Set (RVec 2)) (w x : RVec 2) : ℝ :=
  let q := (extChartAt SurfaceModel p).symm x
  let F := d.chart ∘ f ∘ (extChartAt SurfaceModel p).symm
  let D := W ∩ (extChartAt SurfaceModel p).target
  (r (f q) - 1) / (1 - r (f q))^2 * ∑ i : Fin 2, ∑ j : Fin 2,
    actualChartTensor h d (F x) i.succ j.succ *
      (fderivWithin ℝ F D x w) i.succ * (fderivWithin ℝ F D x w) j.succ

theorem fixed_pulled_height_diagonal (h : AmbientMetric N) (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r) (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (d : SmoothAmbientChart N) (K : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hrc : ∀ q ∈ d.chart.source, r q = d.chart q 0)
    (hm : ∀ z ∈ d.chart.target, ∀ v w : E3,
      coordinateInner (actualChartTensor h d) z v w = v 0 * w 0 + (1-z 0)^2 *
        ∑ i : Fin 2, ∑ j : Fin 2, K (levelCoordinates z) i j * v i.succ * w j.succ)
    (W : Set (RVec 2)) (hW : IsOpen W)
    (hmap : MapsTo (f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) d.chart.source)
    (x : RVec 2) (hx : x ∈ W ∩ (extChartAt SurfaceModel p).target)
    (hxr : r (f ((extChartAt SurfaceModel p).symm x)) < 1) (w : RVec 2) :
    covariantHessian h r (f ((extChartAt SurfaceModel p).symm x))
      (mfderiv SurfaceModel AmbientModel f ((extChartAt SurfaceModel p).symm x)
        (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
          (range SurfaceModel) x w))
      (mfderiv SurfaceModel AmbientModel f ((extChartAt SurfaceModel p).symm x)
        (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
          (range SurfaceModel) x w)) = collarCoordinateQuad S h r f p d W w x := by
  have hh := fixed_collar_quadratic h r hr d K hrc hm _ (hmap hx) hxr
    (mfderiv SurfaceModel AmbientModel f ((extChartAt SurfaceModel p).symm x)
      (mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel (extChartAt SurfaceModel p).symm
        (range SurfaceModel) x w))
  have hd := fixed_collar_coordinate_derivative S f hf p d W hW hmap x hx w
  calc
    _ = _ := hh
    _ = collarCoordinateQuad S h r f p d W w x := by
      unfold collarCoordinateQuad
      dsimp only
      rw [hd]
      rfl


theorem collar_coordinate_quad_continuous (h : AmbientMetric N) (r : N → ℝ)
    (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r) (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (d : SmoothAmbientChart N) (W : Set (RVec 2)) (hW : IsOpen W)
    (hmap : MapsTo (f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) d.chart.source)
    (hheight : ∀ x ∈ W ∩ (extChartAt SurfaceModel p).target,
      r (f ((extChartAt SurfaceModel p).symm x)) < 1) (w : RVec 2) :
    ContinuousOn (collarCoordinateQuad S h r f p d W w)
      (W ∩ (extChartAt SurfaceModel p).target) := by
  let D := W ∩ (extChartAt SurfaceModel p).target
  let F := d.chart ∘ f ∘ (extChartAt SurfaceModel p).symm
  have hD : UniqueDiffOn ℝ D := by
    intro x hx
    simpa only [inter_comm] using (uniqueDiffOn_extChartAt_target (I := SurfaceModel) p x hx.2).inter
      (hW.mem_nhds hx.1)
  have hF := fixed_collar_coordinate_smooth S f hf p d W hmap
  have hd := (hF.fderivWithin hD (m := 1) (by norm_num)).continuousOn
  have hu : ContinuousOn (r ∘ f ∘ (extChartAt SurfaceModel p).symm) D := by
    have hr2 := hr.of_le (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω))
    exact (((hr2.comp hf).comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p).of_le
        (by norm_num : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω)))).continuousOn).mono inter_subset_right
  have hG := (SeifertSurfaces.OriginalEndpoints.A4GeometryBridges.actual_chart_tensor_metric_properties h d).1
  have hGc (i j : Fin 2) : ContinuousOn (fun x => actualChartTensor h d (F x) i.succ j.succ) D :=
    (hG i.succ j.succ).continuousOn.comp hF.continuousOn
      (fun x hx => d.chart.map_source (hmap hx))
  have hDc (i : Fin 2) : ContinuousOn (fun x => (fderivWithin ℝ F D x w) i.succ) D := by
    have hh : ContinuousOn (fun x => fderivWithin ℝ F D x w) D := hd.clm_apply continuousOn_const
    exact (EuclideanSpace.proj (𝕜 := ℝ) i.succ).continuous.comp_continuousOn hh
  unfold collarCoordinateQuad
  dsimp only
  apply (hu.sub continuousOn_const).div
    ((continuousOn_const.sub hu).pow 2)
    (fun x hx => pow_ne_zero 2 (ne_of_gt (sub_pos.mpr (hheight x hx)))) |>.mul
  apply continuousOn_finset_sum
  intro i hi
  apply continuousOn_finset_sum
  intro j hj
  exact ((hGc i j).mul (hDc i)).mul (hDc j)

theorem fixed_pulled_trace_collar_continuous (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (hr : ContMDiff AmbientModel 𝓘(ℝ, ℝ) (∞ : ℕ∞ω) r) (f : S → N)
    (hf : ContMDiff SurfaceModel AmbientModel 2 f) (p : S)
    (d : SmoothAmbientChart N) (K : E2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hrc : ∀ q ∈ d.chart.source, r q = d.chart q 0)
    (hm : ∀ z ∈ d.chart.target, ∀ v w : E3,
      coordinateInner (actualChartTensor h d) z v w = v 0 * w 0 + (1-z 0)^2 *
        ∑ i : Fin 2, ∑ j : Fin 2, K (levelCoordinates z) i j * v i.succ * w j.succ)
    (W : Set (RVec 2)) (hW : IsOpen W)
    (hmap : MapsTo (f ∘ (extChartAt SurfaceModel p).symm)
      (W ∩ (extChartAt SurfaceModel p).target) d.chart.source)
    (hheight : ∀ x ∈ W ∩ (extChartAt SurfaceModel p).target,
      r (f ((extChartAt SurfaceModel p).symm x)) < 1) :
    ContinuousOn (fixedPulledTrace S g h r f p) (W ∩ (extChartAt SurfaceModel p).target) := by
  let G := MetricInChart SurfaceModel g p
  let Q := collarCoordinateQuad S h r f p d W
  have hc := IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p
  have hInv (i j : Fin 2) : ContinuousOn (fun x => (G x)⁻¹ i j)
      (W ∩ (extChartAt SurfaceModel p).target) := by
    apply ((actual_inverse_metric_smooth S g (chartAt (EuclideanHalfSpace 2) p) hc i j).continuousOn.mono
      inter_subset_right).congr
    intro x hx
    dsimp only [G]
    rw [native_surface_metric S g p x hx.2]
  have hQ (w : RVec 2) := collar_coordinate_quad_continuous S h r hr f hf p d W hW hmap hheight w
  have heq : ∀ x ∈ W ∩ (extChartAt SurfaceModel p).target,
      fixedPulledTrace S g h r f p x =
      ((G x)⁻¹ 0 0 - (G x)⁻¹ 0 1) * Q (basis2 0) x +
      ((G x)⁻¹ 1 1 - (G x)⁻¹ 0 1) * Q (basis2 1) x +
      (G x)⁻¹ 0 1 * Q (basis2 0 + basis2 1) x := by
    intro x hx
    let q := (extChartAt SurfaceModel p).symm x
    let A : RVec 2 →L[ℝ] RVec 2 := mfderivWithin 𝓘(ℝ, RVec 2) SurfaceModel
      (extChartAt SurfaceModel p).symm (range SurfaceModel) x
    let D : RVec 2 →L[ℝ] RVec 3 := mfderiv SurfaceModel AmbientModel f q
    obtain ⟨B, hB⟩ := covariant_hessian_bilinear h r (f q)
    have hdiag (w : RVec 2) := fixed_pulled_height_diagonal S h r hr f hf p d K hrc hm W hW hmap
      x hx (hheight x hx) w
    change ∀ w : RVec 2, covariantHessian h r (f q) (D (A w)) (D (A w)) = Q w x at hdiag
    have h00 := hdiag (basis2 0)
    have h11 := hdiag (basis2 1)
    have hsum := hdiag (basis2 0 + basis2 1)
    simp_rw [hB] at h00 h11 hsum
    simp only [map_add, add_apply] at hsum
    have hmetric := ((native_metric_properties S g p).2.2 x hx.2).inv.1
    have h01 : (G x)⁻¹ 1 0 = (G x)⁻¹ 0 1 := by
      simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hmetric 0) 1
    unfold fixedPulledTrace
    dsimp only
    change (∑ i : Fin 2, ∑ j : Fin 2, (G x)⁻¹ i j *
      covariantHessian h r (f q) (D (A (basis2 i))) (D (A (basis2 j)))) = _
    simp_rw [hB]
    simp only [Fin.sum_univ_two, h01]
    linear_combination (G x)⁻¹ 0 1 * hsum +
      ((G x)⁻¹ 0 0 - (G x)⁻¹ 0 1) * h00 + ((G x)⁻¹ 1 1 - (G x)⁻¹ 0 1) * h11
  have hresult := ((((hInv 0 0).sub (hInv 0 1)).mul (hQ (basis2 0))).add
    (((hInv 1 1).sub (hInv 0 1)).mul (hQ (basis2 1)))).add
    ((hInv 0 1).mul (hQ (basis2 0 + basis2 1)))
  exact hresult.congr heq
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: FixedSourceScalarContinuity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface)
theorem fixed_scalar_laplacian_continuous (g : SurfaceMetric S) (p : S)
    (v : RVec 2 → ℝ)
    (hv : ContDiffOn ℝ 2 v (extChartAt SurfaceModel p).target) :
    ContinuousOn (chartLaplacian S g p v) (extChartAt SurfaceModel p).target := by
  let c := chartAt (EuclideanHalfSpace 2) p
  let E := extChartAt SurfaceModel p
  have hc := IsManifold.chart_mem_maximalAtlas (I := SurfaceModel) (n := (∞ : ℕ∞ω)) p
  have hU := uniqueDiffOn_extChartAt_target (I := SurfaceModel) p
  have hInv := actual_inverse_metric_smooth S g c hc
  have hΓ := actual_christoffel_smooth S g c hc
  have hfirst := (hv.fderivWithin hU (m := 1) (by norm_num)).continuousOn
  have hsecond := ((hv.fderivWithin hU (m := 1) (by norm_num)).fderivWithin hU
    (m := 0) (by norm_num)).continuousOn
  have hcoord : ContinuousOn (laplacianInCoordinates S g c v) E.target := by
    unfold laplacianInCoordinates
    dsimp only
    apply continuousOn_finset_sum
    intro i hi
    apply continuousOn_finset_sum
    intro j hj
    apply (hInv i j).continuousOn.mul
    apply (hsecond.clm_apply continuousOn_const).clm_apply continuousOn_const |>.sub
    apply continuousOn_finset_sum
    intro k hk
    exact (hΓ k i j).continuousOn.mul (hfirst.clm_apply continuousOn_const)
  apply hcoord.congr
  intro x hx
  exact native_chart_laplacian_eq_coordinates S g p v x hx
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: NativeBoundaryTrace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators Matrix
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.OriginalEndpoints SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem native_boundary_harmonic_trace (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε) (f : C(S, N))
    (hf : C2HolderUpToBoundary f) (hh : HarmonicInterior g h f)
    (p : S) (hp : r (f p) < ε) :
    laplacian S g (r ∘ f) p = pulledHessianTrace S g h r f p := by
  let E := extChartAt SurfaceModel p
  let x := E p
  let v := (r ∘ f) ∘ E.symm
  obtain ⟨d, K, hpd, hrc, hm, _⟩ := native_collar_hessian_formula h r ε collar (f p) hp
  have hψ : ContinuousAt (f ∘ E.symm) x := by
    exact f.continuous.continuousAt.comp (continuousAt_extChartAt_symm (I := SurfaceModel) p)
  have hdN : ∀ᶠ y in 𝓝 x, f (E.symm y) ∈ d.chart.source := by
    apply hψ.preimage_mem_nhds
    simpa only [E, x, Function.comp_def, extChartAt_to_inv] using d.chart.open_source.mem_nhds hpd
  have hrN : ∀ᶠ y in 𝓝 x, r (f (E.symm y)) < 1 := by
    have hc : ContinuousAt v x := (collar.smooth_height.continuous.comp f.continuous).continuousAt.comp
      (continuousAt_extChartAt_symm (I := SurfaceModel) p)
    apply hc.eventually (gt_mem_nhds (show v x < 1 by
      simp only [v, x, E, Function.comp_def, extChartAt_to_inv]
      exact hp.trans collar.epsilon_lt_one))
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp (hdN.and hrN)
  have hmap : MapsTo (f ∘ E.symm) (W ∩ E.target) d.chart.source :=
    fun y hy => (hWsub hy.1).1
  have hheight : ∀ y ∈ W ∩ E.target, r (f (E.symm y)) < 1 :=
    fun y hy => (hWsub hy.1).2
  have hscalar := scalar_composition_regular S r collar.smooth_height f hf
  have hv : ContDiffOn ℝ 2 v E.target := scalar_in_source_chart S (r ∘ f) hscalar p
  have hLc : ContinuousOn (chartLaplacian S g p v) (W ∩ E.target) :=
    (fixed_scalar_laplacian_continuous S g p v hv).mono inter_subset_right
  have hTc : ContinuousOn (fixedPulledTrace S g h r f p) (W ∩ E.target) :=
    fixed_pulled_trace_collar_continuous S g h r collar.smooth_height f hf.regular p d K hrc hm
      W hW hmap hheight
  have hxT : x ∈ E.target := mem_extChartAt_target (I := SurfaceModel) p
  have hxcl : x ∈ closure (W ∩ interior E.target) := by
    apply mem_closure_iff.mpr
    intro O hO hxO
    have hh := extChartAt_target_subset_closure_interior hxT
    obtain ⟨y, ⟨hyO, hyW⟩, hyI⟩ := mem_closure_iff.mp hh (O ∩ W) (hO.inter hW) ⟨hxO, hxW⟩
    exact ⟨y, hyO, hyW, hyI⟩
  have hEq : EqOn (chartLaplacian S g p v) (fixedPulledTrace S g h r f p)
      (W ∩ interior E.target) := by
    intro y hy
    have hyT := interior_subset hy.2
    have hyS := E.map_target hyT
    have hq : E.symm y ∈ SurfaceModel.interior S := by
      apply (SurfaceModel.isInteriorPoint_iff_of_mem_atlas (n := (∞ : ℕ∞ω)) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) p)
        (by simpa only [E, extChartAt_source] using hyS)).mpr
      change E (E.symm y) ∈ interior E.target
      rw [E.right_inv hyT]
      exact hy.2
    have hfixed := native_fixed_chart_laplacian S g (r ∘ f) hscalar p (E.symm y) hyS hq
    rw [E.right_inv hyT] at hfixed
    change chartLaplacian S g p v y = laplacian S g (r ∘ f) (E.symm y) at hfixed
    rw [hfixed, fixed_pulled_trace_eq_native S g h r f p y hyT]
    exact native_interior_harmonic_trace S g h r collar.smooth_height f hf hh (E.symm y) hq
  have hsubset : W ∩ interior E.target ⊆ W ∩ E.target :=
    fun y hy => ⟨hy.1, interior_subset hy.2⟩
  letI hne : (𝓝[W ∩ interior E.target] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxcl
  have hcenter := tendsto_nhds_unique_of_eventuallyEq
    ((hLc x ⟨hxW, hxT⟩).mono hsubset)
    ((hTc x ⟨hxW, hxT⟩).mono hsubset)
    (hEq.eventuallyEq_of_mem self_mem_nhdsWithin)
  rw [fixed_pulled_trace_eq_native S g h r f p x hxT] at hcenter
  simpa only [x, E, v, laplacian, extChartAt_to_inv] using hcenter
end SeifertSurfaces.PrivateHelpers.C6Native

-- Paid private boundary support: NativeC6Endpoint
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.PrivateHelpers.C6Native
open SeifertSurfaces.AppendixC SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel (∞ : ℕ∞ω) N]
theorem native_c6_endpoint (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (f : C(S, N)) (curve : Set N) (hf : LemaireMinimizer S g h f curve) :
    (∀ p : S, r (f p) < ε →
      laplacian S g (r ∘ f) p = pulledHessianTrace S g h r f p ∧
      ∀ e : Fin 2 → TangentSpace SurfaceModel p,
        (∀ i j, g.inner p (e i) (e j) = if i = j then 1 else 0) →
        laplacian S g (r ∘ f) p =
          ∑ i : Fin 2, covariantHessian h r (f p)
            (mfderiv SurfaceModel AmbientModel f p (e i))
            (mfderiv SurfaceModel AmbientModel f p (e i)) ∧
        laplacian S g (r ∘ f) p ≤ 0 ∧
        (laplacian S g (r ∘ f) p = 0 ↔
          ∀ i, IsRadial h r (f p) (mfderiv SurfaceModel AmbientModel f p (e i)))) ∧
    ScalarC2HolderUpToBoundary S (r ∘ f) ∧ SmoothLocallyUniformElliptic S g := by
  refine ⟨?_, scalar_composition_holder S r collar.smooth_height f hf.regularity,
    actual_metric_locally_uniform_elliptic S g⟩
  intro p hp
  have ht := native_boundary_harmonic_trace S g h r ε collar f hf.regularity hf.harmonic p hp
  refine ⟨ht, ?_⟩
  intro e he
  have hframe := actual_frame_trace S g h r f p e he
  have hs := frame_hessian_sign_radial S g h r ε collar f p hp e
  have heq := ht.trans hframe
  exact ⟨heq, heq.symm ▸ hs.1, heq.symm ▸ hs.2⟩
end SeifertSurfaces.PrivateHelpers.C6Native
namespace SeifertSurfaces.AppendixC.OriginalEndpoints
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable (S : CompactOrientedSurface) {N : Type*}
  [TopologicalSpace N] [ChartedSpace (RVec 3) N] [IsManifold AmbientModel ∞ N]
/-- Original Lemma C.6, source lines 2091–2112, including every clause. -/
theorem generalized_C6 (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (f : C(S, N)) (curve : Set N) (hf : LemaireMinimizer S g h f curve) :
    (∀ p : S, r (f p) < ε →
      laplacian S g (r ∘ f) p = pulledHessianTrace S g h r f p ∧
      ∀ e : Fin 2 → TangentSpace SurfaceModel p,
        (∀ i j, g.inner p (e i) (e j) = if i = j then 1 else 0) →
        laplacian S g (r ∘ f) p =
          ∑ i : Fin 2, covariantHessian h r (f p)
            (mfderiv SurfaceModel AmbientModel f p (e i))
            (mfderiv SurfaceModel AmbientModel f p (e i)) ∧
        laplacian S g (r ∘ f) p ≤ 0 ∧
        (laplacian S g (r ∘ f) p = 0 ↔
          ∀ i, IsRadial h r (f p) (mfderiv SurfaceModel AmbientModel f p (e i)))) ∧
    ScalarC2HolderUpToBoundary S (r ∘ f) ∧ SmoothLocallyUniformElliptic S g := by
  exact SeifertSurfaces.PrivateHelpers.C6Native.native_c6_endpoint S g h r ε collar f curve hf

/-- Original Proposition C.11, source lines 2218–2227. Core membership is
stated for the actual supplied core, characterized by r ≥ 0; no local minimum
principle, PDE inequality, or image containment is an input. -/
theorem generalized_C11 [ConnectedSpace S]
    (hboundary : (SurfaceModel.boundary S).Nonempty)
    (g : SurfaceMetric S) (h : AmbientMetric N)
    (r : N → ℝ) (ε : ℝ) (collar : WarpedCollar h r ε)
    (M curve : Set N) (hcore : M = {q | 0 ≤ r q})
    (hcurve : curve ⊆ {q | r q = 0})
    (f : C(S, N)) (hf : LemaireMinimizer S g h f curve) :
    range f ⊆ M ∧ ∀ p : S, 0 ≤ r (f p) := by
  exact SeifertSurfaces.PrivateHelpers.C6Native.native_c11_barrier S hboundary
    g h r ε collar M curve hcore hcurve f hf

/-- The actual Appendix C ambient extension of the supplied knot exterior.
The core is the image of its genuine smooth embedding; the entire collar is
homeomorphic to (-∞, ε) × ∂E, with r the first coordinate and its zero slice
identified with the embedded boundary. No construction existence or endpoint
conclusion is asserted by this supplied geometric bundle. -/
structure AppendixCAmbient {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (J : LongitudeFoliation.{0} E)
    (N : Type*) [TopologicalSpace N] [ChartedSpace (RVec 3) N]
    [IsManifold AmbientModel ∞ N] where
  metric : AmbientMetric N
  coreMetric : SmoothMetric E.Carrier
  coreEmbedding : E.Carrier → N
  coreEmbedding_smooth : Manifold.IsSmoothEmbedding (𝓡∂ 3) AmbientModel ∞ coreEmbedding
  core_metric : ∀ x : E.Carrier, ∀ v w : TangentSpace (𝓡∂ 3) x,
    metric.inner (coreEmbedding x)
      (mfderiv (𝓡∂ 3) AmbientModel coreEmbedding x v)
      (mfderiv (𝓡∂ 3) AmbientModel coreEmbedding x w) = coreMetric.inner x v w
  height : N → ℝ
  epsilon : ℝ
  collar : WarpedCollar metric height epsilon
  core_image : range coreEmbedding = {q | 0 ≤ height q}
  boundary_image : coreEmbedding '' ((𝓡∂ 3).boundary E.Carrier) = {q | height q = 0}
  collarProduct : {q : N | height q < epsilon} ≃ₜ
    (Iio epsilon × ((𝓡∂ 3).boundary E.Carrier))
  collar_height : ∀ q : {q : N | height q < epsilon},
    ((collarProduct q).1 : ℝ) = height q
  collar_zero : ∀ x : ((𝓡∂ 3).boundary E.Carrier),
    ((collarProduct.symm (⟨0, collar.epsilon_pos⟩, x)) : N) = coreEmbedding x
  foliation_analytic : J.IntrinsicallyAnalytic
  leafLabel : Circle

namespace AppendixCAmbient
variable {K : OrientedKnot} {T : TubularNeighborhood K}
  {E : SmoothExterior T} {J : LongitudeFoliation.{0} E}

def core (A : AppendixCAmbient E J N) : Set N := range A.coreEmbedding

def leafParameter (A : AppendixCAmbient E J N) (z : Circle) : N :=
  A.coreEmbedding (J.torus (A.leafLabel, z))

def curve (A : AppendixCAmbient E J N) : Set N := range A.leafParameter
end AppendixCAmbient

/-- Original C.6 on the actual embedded knot-exterior core and the actual
analytic longitude leaf. The source S is connected with connected nonempty
boundary. All previously reviewed analytic output clauses are retained. The
accepted uniform ellipticity interpretation is local in every smooth chart. -/
theorem original_C6 [ConnectedSpace S]
    (hboundary : IsConnected (SurfaceModel.boundary S))
    {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (J : LongitudeFoliation.{0} E)
    (A : AppendixCAmbient E J N) (g : SurfaceMetric S)
    (f : C(S, N)) (hf : LemaireMinimizer S g A.metric f A.curve) :
    (∀ p : S, A.height (f p) < A.epsilon →
      laplacian S g (A.height ∘ f) p =
        pulledHessianTrace S g A.metric A.height f p ∧
      ∀ e : Fin 2 → TangentSpace SurfaceModel p,
        (∀ i j, g.inner p (e i) (e j) = if i = j then 1 else 0) →
        laplacian S g (A.height ∘ f) p =
          ∑ i : Fin 2, covariantHessian A.metric A.height (f p)
            (mfderiv SurfaceModel AmbientModel f p (e i))
            (mfderiv SurfaceModel AmbientModel f p (e i)) ∧
        laplacian S g (A.height ∘ f) p ≤ 0 ∧
        (laplacian S g (A.height ∘ f) p = 0 ↔
          ∀ i, IsRadial A.metric A.height (f p)
            (mfderiv SurfaceModel AmbientModel f p (e i)))) ∧
    ScalarC2HolderUpToBoundary S (A.height ∘ f) ∧
      SmoothLocallyUniformElliptic S g := by
  exact generalized_C6 S g A.metric A.height A.epsilon A.collar f A.curve hf

/-- Original C.11: the minimizer for this actual longitude leaf stays inside
the actual supplied knot-exterior core embedded in its Appendix C extension.
No arbitrary curve/core parameters or future source-instantiation caller remain. -/
theorem original_C11 [ConnectedSpace S]
    (hboundary : IsConnected (SurfaceModel.boundary S))
    {K : OrientedKnot} {T : TubularNeighborhood K}
    (E : SmoothExterior T) (J : LongitudeFoliation.{0} E)
    (A : AppendixCAmbient E J N) (g : SurfaceMetric S)
    (f : C(S, N)) (hf : LemaireMinimizer S g A.metric f A.curve) :
    range f ⊆ A.core ∧ ∀ p : S, 0 ≤ A.height (f p) := by
  apply generalized_C11 S hboundary.nonempty g A.metric A.height A.epsilon A.collar
    A.core A.curve A.core_image
  · rintro q ⟨z, rfl⟩
    change A.height (A.coreEmbedding (J.torus (A.leafLabel, z))) = 0
    have hz : A.coreEmbedding (J.torus (A.leafLabel, z)) ∈
        A.coreEmbedding '' ((𝓡∂ 3).boundary E.Carrier) :=
      ⟨J.torus (A.leafLabel, z), J.torus_lands_boundary _, rfl⟩
    rw [A.boundary_image] at hz
    exact hz
  · exact hf

end SeifertSurfaces.AppendixC.OriginalEndpoints
