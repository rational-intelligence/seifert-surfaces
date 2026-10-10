import OriginalC8

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace SeifertSurfaces.AppendixC.Original

universe u v
variable (S : Type u) [TopologicalSpace S] [ChartedSpace (EuclideanHalfSpace 2) S]
  [IsManifold (𝓡∂ 2) ∞ S]
  (D : Type v) [TopologicalSpace D] [ChartedSpace Plane D]
  [IsManifold (𝓡 2) ∞ D]

/-- The source's fixed smooth double: the two actual copies of S cover D,
meet along the actual boundary, and are exchanged by the fixed smooth swap.
Its complement has the two connected interiors stipulated in §C.3. -/
structure SmoothDouble (j : S → D) where
  inclusion : SmoothSubsurface D S j
  swap : Diffeomorph (𝓡 2) (𝓡 2) D D ∞
  involutive : Function.Involutive swap
  fixed_boundary : {q | swap q = q} = j '' (𝓡∂ 2).boundary S
  cover : Set.range j ∪ swap '' Set.range j = Set.univ
  overlap : Set.range j ∩ swap '' Set.range j = j '' (𝓡∂ 2).boundary S
  interior_connected : IsConnected (j '' (𝓡∂ 2).interior S)

/-- A diffeomorphism onto an actual subset before the induced subsurface
atlas is constructed. The homeomorphism retains its exact inverse; both
directions are smooth. Smoothness of the inverse is expressed by its local
extensions in the GIVEN source charts. This avoids assuming the C.8-induced
subsurface atlas or the boundary identification that still must be proved. -/
structure GivenDiffeomorphismOnto (A : Set D) where
  homeomorph : S ≃ₜ A
  smooth : ContMDiff (𝓡∂ 2) (𝓡 2) ∞ (fun p => (homeomorph p : D))
  immersion : ∀ p, Function.Injective
    (mfderiv (𝓡∂ 2) (𝓡 2) (fun p => (homeomorph p : D)) p)
  smooth_inverse : ∀ q : A, ∃ (U : Set D) (f : D → Plane),
    IsOpen U ∧ (q : D) ∈ U ∧ ContMDiffOn (𝓡 2) (𝓡 2) ∞ f U ∧
    ∀ r : A, (r : D) ∈ U →
      homeomorph.symm r ∈ (extChartAt (𝓡∂ 2) (homeomorph.symm q)).source ∧
      f r = extChartAt (𝓡∂ 2) (homeomorph.symm q) (homeomorph.symm r)

/-- Literal L2′: a conformal structure on the same fixed closed double and
a diffeomorphism preserving the same subsurface, with positive-ray equality
to t under the actual differential. A double metric is NOT an input. -/
structure RawL2Prime (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D) where
  double_class : SmoothConformalField (𝓡 2) D
  diffeomorph : Diffeomorph (𝓡 2) (𝓡 2) D D ∞
  preserves_subsurface : diffeomorph '' Set.range j = Set.range j
  class_pullback : ∀ p : S, ∃ c : ℝ, 0 < c ∧ ∀ v w,
    double_class.representative (diffeomorph (j p))
      (mfderiv (𝓡 2) (𝓡 2) diffeomorph (j p) (mfderiv (𝓡∂ 2) (𝓡 2) j p v))
      (mfderiv (𝓡 2) (𝓡 2) diffeomorph (j p) (mfderiv (𝓡∂ 2) (𝓡 2) j p w)) =
      c * t.representative p v w

/-- Literal L2″: the conformal double, an anti-conformal involution
topologically conjugate to the fixed swap, one actual connected component,
and the GIVEN diffeomorphism onto its closure. Neither metric nor reflection
charts nor boundary identification is assumed. -/
structure RawL2DoublePrime (t : InteriorConformalField (𝓡∂ 2) S)
    (swap : D ≃ₜ D) where
  double_class : SmoothConformalField (𝓡 2) D
  atlas : ComplexConformalAtlas (𝓡 2) D
  class_in_atlas : ∀ p q : D, q ∈ (atlas.chart p).source →
    ∃ c : ℝ, 0 < c ∧ ∀ v w,
      double_class.representative q v w = c * inner ℝ
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (atlas.chart p) q v)
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) (atlas.chart p) q w)
  involution : D ≃ₜ D
  involutive : Function.Involutive involution
  anti_conformal : AntiholomorphicInAtlas (𝓡 2) D atlas involution
  conjugacy : D ≃ₜ D
  conjugate_swap : ∀ q, involution (conjugacy q) = conjugacy (swap q)
  component_point : D
  point_not_fixed : involution component_point ≠ component_point
  component : Set D
  component_eq : component = connectedComponentIn {q | involution q ≠ q} component_point
  diffeomorph : GivenDiffeomorphismOnto S D (closure component)
  class_pullback : ∀ p : S, ∃ c : ℝ, 0 < c ∧ ∀ v w,
    double_class.representative (diffeomorph.homeomorph p : D)
      (mfderiv (𝓡∂ 2) (𝓡 2) (fun q => (diffeomorph.homeomorph q : D)) p v)
      (mfderiv (𝓡∂ 2) (𝓡 2) (fun q => (diffeomorph.homeomorph q : D)) p w) =
      c * t.representative p v w

/-- The standard half-space coordinates, with coordinate zero the normal
coordinate and coordinate one the real-axis coordinate. -/
def halfSpaceComplex (x : EuclideanHalfSpace 2) : ℂ := ⟨x.1 1, x.1 0⟩

/-- Boundary analyticity in the actual pulled-back conformal structure:
same given diffeomorphism/inverse, same double atlas, and a genuine smooth
half-space chart obtained by restricting the SAME reflection disk chart.
The choice of upper or lower half records which component was supplied. -/
structure AnalyticBoundaryPullback
    (t : InteriorConformalField (𝓡∂ 2) S) (swap : D ≃ₜ D)
    (c : RawL2DoublePrime S D t swap) where
  boundary_fixed : ∀ p, (𝓡∂ 2).IsBoundaryPoint p ↔
    c.involution (c.diffeomorph.homeomorph p : D) = (c.diffeomorph.homeomorph p : D)
  charts : ∀ p : S, (𝓡∂ 2).IsBoundaryPoint p →
    DiskReflectionChart D c.atlas c.involution (c.diffeomorph.homeomorph p : D)
  subsurface_chart : ∀ (p : S) (_hp : (𝓡∂ 2).IsBoundaryPoint p),
    OpenPartialHomeomorph S (EuclideanHalfSpace 2)
  upper_side : ∀ (p : S), (𝓡∂ 2).IsBoundaryPoint p → Bool
  source_eq : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    (subsurface_chart p hp).source =
      (fun q => (c.diffeomorph.homeomorph q : D)) ⁻¹' (charts p hp).chart.source
  mem_source : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    p ∈ (subsurface_chart p hp).source
  half_disk_target : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    (subsurface_chart p hp).target =
      {x : EuclideanHalfSpace 2 | ‖halfSpaceComplex x‖ < (charts p hp).radius}
  smooth : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (subsurface_chart p hp)
      (subsurface_chart p hp).source
  smooth_inverse : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    ContMDiffOn (𝓡∂ 2) (𝓡∂ 2) ∞ (subsurface_chart p hp).symm
      (subsurface_chart p hp).target
  coordinate_identity : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p) (q : S),
    q ∈ (subsurface_chart p hp).source →
    halfSpaceComplex (subsurface_chart p hp q) =
      if upper_side p hp then (charts p hp).chart (c.diffeomorph.homeomorph q : D)
      else star ((charts p hp).chart (c.diffeomorph.homeomorph q : D))
  inverse_identity : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p)
      (x : EuclideanHalfSpace 2), x ∈ (subsurface_chart p hp).target →
    (c.diffeomorph.homeomorph ((subsurface_chart p hp).symm x) : D) =
      (charts p hp).chart.symm
        (if upper_side p hp then halfSpaceComplex x else star (halfSpaceComplex x))
  boundary_axis : ∀ (p : S) (hp : (𝓡∂ 2).IsBoundaryPoint p),
    (subsurface_chart p hp) ''
      ((𝓡∂ 2).boundary S ∩ (subsurface_chart p hp).source) =
      {x ∈ (subsurface_chart p hp).target | x.1 0 = 0}

/-- The paid C.9 support concludes interior conformality. For the original
whole-S class equality, conformality of two smooth positive metrics extends
from the dense manifold interior; the raw pullback relation then identifies
the prescribed boundary class as well. -/
theorem conformality_extends_to_boundary
    (g h : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ Plane
      (fun p : S => TangentSpace (𝓡∂ 2) p))
    (hinterior : ConformalOnInterior (𝓡∂ 2) S g.inner h.inner) :
    PointwiseConformal (𝓡∂ 2) S g.inner h.inner := by
  classical
  have hdense : Dense ((𝓡∂ 2).interior S) := by
    intro p
    let a := extChartAt (𝓡∂ 2) p
    have ht : a p ∈ closure (interior a.target) :=
      extChartAt_target_subset_closure_interior (mem_extChartAt_target p)
    have hc : ContinuousWithinAt a.symm (interior a.target) (a p) :=
      (continuousOn_extChartAt_symm p _ (mem_extChartAt_target p)).mono interior_subset
    have hm : Set.MapsTo a.symm (interior a.target) ((𝓡∂ 2).interior S) := by
      intro y hy
      have hyt := interior_subset hy
      have hs := a.map_target hyt
      have hs' : a.symm y ∈ (chartAt (EuclideanHalfSpace 2) p).source := by
        simpa only [a, extChartAt_source] using hs
      apply ((𝓡∂ 2).isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
        (chart_mem_atlas (EuclideanHalfSpace 2) p) hs').2
      change a (a.symm y) ∈ interior a.target
      rw [a.right_inv hyt]
      exact hy
    simpa only [a.left_inv (mem_extChartAt_source p)] using hc.mem_closure ht hm
  intro p
  let e := trivializationAt Plane (fun q : S => TangentSpace (𝓡∂ 2) q) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hsection (a : Plane) : ContinuousOn
      (fun q : S => TotalSpace.mk' Plane q (e.symm q a)) e.baseSet := by
    exact e.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun q hq => ⟨hq, Set.mem_univ _⟩)
  have hcont (m : ContMDiffRiemannianMetric (𝓡∂ 2) ∞ Plane
      (fun q : S => TangentSpace (𝓡∂ 2) q)) (a b : Plane) :
      ContinuousOn (fun q => m.inner q (e.symm q a) (e.symm q b)) e.baseSet := by
    letI : RiemannianBundle (fun q : S => TangentSpace (𝓡∂ 2) q) :=
      ⟨m.toContinuousRiemannianMetric.toRiemannianMetric⟩
    exact (hsection a).inner_bundle (hsection b)
  let z : TangentSpace (𝓡∂ 2) p := EuclideanSpace.single (0 : Fin 2) 1
  have hz : z ≠ 0 := by
    change EuclideanSpace.single (0 : Fin 2) (1 : ℝ) ≠ 0
    simp
  refine ⟨g.inner p z z / h.inner p z z, div_pos (g.pos p z hz) (h.pos p z hz), ?_⟩
  intro v w
  let za := e.linearMapAt ℝ p z
  let va := e.linearMapAt ℝ p v
  let wa := e.linearMapAt ℝ p w
  have hzp : e.symm p za = z := e.symm_linearMapAt hp z
  have hvp : e.symm p va = v := e.symm_linearMapAt hp v
  have hwp : e.symm p wa = w := e.symm_linearMapAt hp w
  have hcross : g.inner p v w * h.inner p z z = h.inner p v w * g.inner p z z := by
    have hpc : p ∈ closure ((𝓡∂ 2).interior S ∩ e.baseSet) := by
      rw [mem_closure_iff_nhds]
      intro U hU
      obtain ⟨q, hqU, hqI⟩ := mem_closure_iff_nhds.mp (hdense p) _
        (Filter.inter_mem hU (e.open_baseSet.mem_nhds hp))
      exact ⟨q, hqU.1, hqI, hqU.2⟩
    letI : Filter.NeBot (nhdsWithin p ((𝓡∂ 2).interior S ∩ e.baseSet)) :=
      mem_closure_iff_nhdsWithin_neBot.mp hpc
    have hL := ((hcont g va wa).mul (hcont h za za) p hp).continuousAt
      (e.open_baseSet.mem_nhds hp)
    have hR := ((hcont h va wa).mul (hcont g za za) p hp).continuousAt
      (e.open_baseSet.mem_nhds hp)
    have heq : (fun q => g.inner q (e.symm q va) (e.symm q wa) *
        h.inner q (e.symm q za) (e.symm q za)) =ᶠ[nhdsWithin p
          ((𝓡∂ 2).interior S ∩ e.baseSet)]
        (fun q => h.inner q (e.symm q va) (e.symm q wa) *
          g.inner q (e.symm q za) (e.symm q za)) := by
      filter_upwards [self_mem_nhdsWithin] with q hq
      obtain ⟨a, ha, hea⟩ := hinterior q hq.1
      rw [hea, hea]
      ring
    have hh := tendsto_nhds_unique (hL.mono_left nhdsWithin_le_nhds)
      ((hR.mono_left nhdsWithin_le_nhds).congr' heq.symm)
    simpa only [Pi.mul_apply, hzp, hvp, hwp] using hh
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (ne_of_gt (h.pos p z hz))).2
  simpa only [mul_comm] using hcross

/-- Only the residual raw-to-paid-support translation for L2′. The double
metric is produced by C.7 and all original witness identities are retained. -/
theorem raw_L2prime_support_interface
    [T2Space D] [SecondCountableTopology D] [CompactSpace D]
    (t : InteriorConformalField (𝓡∂ 2) S) (j : S → D)
    (d : SmoothDouble S D j) (c : RawL2Prime S D t j) :
    ∃ h : L2PrimeCompatibility (𝓡∂ 2) (𝓡 2) S D t j,
      PointwiseConformal (𝓡 2) D h.double_metric.inner c.double_class.representative ∧
      h.preserving_diffeomorph = c.diffeomorph := by
  obtain ⟨g, hg⟩ := c7_smooth_metric_representative (𝓡 2) D c.double_class
  refine ⟨{
    double_compact := isCompact_univ
    double_boundaryless := inferInstance
    double_metric := g
    preserving_diffeomorph := c.diffeomorph
    preserves_subsurface := c.preserves_subsurface
    inclusion_smooth := d.inclusion.smooth
    inclusion_immersion := d.inclusion.immersion
    pullback_conformal := ?_ }, hg, rfl⟩
  intro p hp
  obtain ⟨a, ha, hea⟩ := hg (c.diffeomorph (j p))
  obtain ⟨b, hb, heb⟩ := c.class_pullback p
  refine ⟨a * b, mul_pos ha hb, ?_⟩
  intro v w
  rw [hea, heb, mul_assoc]

end SeifertSurfaces.AppendixC.Original
