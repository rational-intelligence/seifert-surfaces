import Mathlib

/-!
# The concrete analytic clauses of Definition C.2

Source: `references/seifert-surfaces.txt`, lines 2014–2031.
This file formalizes the boundary monotonicity, harmonic-map equation, weak
conformality, smooth boundary metric, and C²,α boundary regularity. It does
NOT call their conjunction a Lemaire minimiser: L1's area-minimizing relative
homotopy class and C.3's cited existence remain separate source obligations.
-/

noncomputable section
open Bundle
open scoped Manifold ContDiff BigOperators NNReal Topology
namespace SeifertSurfaces.AppendixC

abbrev RVec (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev SurfaceModel := modelWithCornersEuclideanHalfSpace 2
abbrev AmbientModel := 𝓘(ℝ, RVec 3)

variable {S N : Type*} [TopologicalSpace S] [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 2) S] [ChartedSpace (RVec 3) N]
    [IsManifold SurfaceModel ∞ S] [IsManifold AmbientModel ∞ N]

/-- The interpretation of "monotone" explicitly adopted in Remark C.5.
The curve is fixed; its parametrisation is not pinned pointwise. -/
structure L1BoundaryMonotone (f : S → N) (curve : Set N) : Prop where
  continuous : Continuous f
  boundary_maps : Set.MapsTo f (SurfaceModel.boundary S) curve
  boundary_onto : Set.SurjOn f (SurfaceModel.boundary S) curve
  fibers_connected : ∀ q ∈ curve,
    IsConnected {p : S | SurfaceModel.IsBoundaryPoint p ∧ f p = q}

/-- [11, Definition (1.6)], p. 94, with Remark C.5's explicit interpretation
of monotonicity. The entire homotopy keeps the curve, while allowing the
boundary parametrisation to move. The endpoint maps are continuous maps. -/
def LemaireRelativeHomotopic (f₀ f₁ : C(S, N)) (curve : Set N) : Prop :=
  ∃ H : ContinuousMap.Homotopy f₀ f₁,
    ∀ t : unitInterval, L1BoundaryMonotone (fun p => H (t, p)) curve

/-- C.1(iv)'s homotopy clause after the global collar deformation is glued.
The deformation fixes the actual target curve pointwise, and composition
therefore preserves every intermediate boundary parametrisation. -/
theorem c1iv_relative_homotopy_from_curve_fixed_deformation
    (ρ : C(N, N)) (H : ContinuousMap.Homotopy (ContinuousMap.id N) ρ)
    (curve : Set N) (hfixed : ∀ (t : unitInterval) (q : N),
      q ∈ curve → H (t, q) = q)
    (f : C(S, N)) (hf : L1BoundaryMonotone f curve) :
    LemaireRelativeHomotopic f (ρ.comp f) curve := by
  let Hf : ContinuousMap.Homotopy f (ρ.comp f) := H.compContinuousMap f
  have hboundary : ∀ t p, SurfaceModel.IsBoundaryPoint p → Hf (t, p) = f p := by
    intro t p hp
    exact hfixed t (f p) (hf.boundary_maps hp)
  refine ⟨Hf, fun t => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact Hf.continuous.comp (continuous_const.prodMk continuous_id)
  · intro p hp
    change Hf (t, p) ∈ curve
    rw [hboundary t p hp]
    exact hf.boundary_maps hp
  · intro q hq
    obtain ⟨p, hp, hfp⟩ := hf.boundary_onto hq
    exact ⟨p, hp, (hboundary t p hp).trans hfp⟩
  · intro q hq
    convert hf.fibers_connected q hq using 1
    ext p
    simp only [Set.mem_setOf_eq]
    exact and_congr_right (fun hp => by rw [hboundary t p hp])

abbrev SurfaceMetric (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanHalfSpace 2) S] [IsManifold SurfaceModel ∞ S] :=
  ContMDiffRiemannianMetric SurfaceModel ∞ (RVec 2)
    (fun p : S => TangentSpace SurfaceModel p)

abbrev AmbientMetric (N : Type*) [TopologicalSpace N]
    [ChartedSpace (RVec 3) N] [IsManifold AmbientModel ∞ N] :=
  ContMDiffRiemannianMetric AmbientModel ∞ (RVec 3)
    (fun p : N => TangentSpace AmbientModel p)

/-- Weak conformality on Int S, with the actual two Riemannian metrics and
the actual manifold differential. Boundary extension is a separate theorem. -/
def WeakConformalInterior (g : SurfaceMetric S) (h : AmbientMetric N)
    (f : S → N) : Prop :=
  ∃ μ : S → ℝ, (∀ p ∈ SurfaceModel.interior S, 0 ≤ μ p) ∧
    ∀ p ∈ SurfaceModel.interior S, ∀ v w,
      h.inner (f p) (mfderiv SurfaceModel AmbientModel f p v)
        (mfderiv SurfaceModel AmbientModel f p w) = μ p * g.inner p v w

/-- The tensor components in actual extended-chart coordinates. Chart
inverse derivatives are taken within the half-space at boundary points. -/
def MetricInChart {n : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (RVec n) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ (RVec n)
      (fun p : M => TangentSpace I p))
    (p : M) (x : RVec n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => g.inner ((extChartAt I p).symm x)
    (mfderivWithin 𝓘(ℝ, RVec n) I (extChartAt I p).symm (Set.range I) x
      (EuclideanSpace.single i 1))
    (mfderivWithin 𝓘(ℝ, RVec n) I (extChartAt I p).symm (Set.range I) x
      (EuclideanSpace.single j 1))

/-- The Levi-Civita Christoffel formula for a coordinate metric matrix. -/
def ChristoffelCoordinate {n : ℕ}
    (g : RVec n → Matrix (Fin n) (Fin n) ℝ)
    (x : RVec n) (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin n, (g x)⁻¹ k l *
    (fderiv ℝ (fun y => g y j l) x (EuclideanSpace.single i 1) +
      fderiv ℝ (fun y => g y i l) x (EuclideanSpace.single j 1) -
      fderiv ℝ (fun y => g y i j) x (EuclideanSpace.single l 1))

/-- The actual tension components from the coordinate equation printed in
the proof of C.6. This is evaluated only on the source interior. -/
def CoordinateTension (g : SurfaceMetric S) (h : AmbientMetric N)
    (f : S → N) (p : S) : RVec 3 :=
  let F := writtenInExtChartAt SurfaceModel AmbientModel p f
  let x := extChartAt SurfaceModel p p
  let gs := MetricInChart SurfaceModel g p
  let ht := MetricInChart AmbientModel h (f p)
  ∑ a : Fin 3, (∑ i : Fin 2, ∑ j : Fin 2, (gs x)⁻¹ i j *
    ((fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1)) a -
      (∑ k : Fin 2, ChristoffelCoordinate gs x k i j *
        (fderiv ℝ F x (EuclideanSpace.single k 1)) a) +
      (∑ b : Fin 3, ∑ c : Fin 3, ChristoffelCoordinate ht (F x) a b c *
        (fderiv ℝ F x (EuclideanSpace.single i 1)) b *
        (fderiv ℝ F x (EuclideanSpace.single j 1)) c))) •
    EuclideanSpace.single a 1

def HarmonicInterior (g : SurfaceMetric S) (h : AmbientMetric N)
    (f : S → N) : Prop :=
  ∀ p ∈ SurfaceModel.interior S, CoordinateTension g h f p = 0

/-- C²,α up to the source boundary, encoded by genuine full-chart extensions
whose second Fréchet derivatives satisfy Mathlib's Hölder condition. -/
structure C2HolderUpToBoundary (f : S → N) : Prop where
  regular : ContMDiff SurfaceModel AmbientModel 2 f
  holder_extensions : ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧
    ∀ p : S, ∃ (U : Set (RVec 2)) (F : RVec 2 → RVec 3) (K : ℝ≥0),
      IsOpen U ∧ extChartAt SurfaceModel p p ∈ U ∧
      U ∩ Set.range SurfaceModel ⊆ (extChartAt SurfaceModel p).target ∧
      ContDiffOn ℝ 2 F U ∧ HolderOnWith K α (iteratedFDeriv ℝ 2 F) U ∧
      (∀ x ∈ U ∩ Set.range SurfaceModel,
        F x = writtenInExtChartAt SurfaceModel AmbientModel p f x)

/-- The analytic portion of C.2, explicitly conditional on the smooth
boundary metric in L2. Area minimality is deliberately not renamed away. -/
structure AnalyticBoundaryData (h : AmbientMetric N) (f : S → N) (curve : Set N) where
  boundary : L1BoundaryMonotone f curve
  metric : SurfaceMetric S
  harmonic : HarmonicInterior metric h f
  conformal : WeakConformalInterior metric h f
  regularity : C2HolderUpToBoundary f

/-- Local continuity and density lemmas used to extend the tensor identity. -/
private theorem source_metric_pair_continuousAt (g : SurfaceMetric S)
    (v w : ∀ q : S, TangentSpace SurfaceModel q) (p : S)
    (hv : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (v q)) p)
    (hw : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (w q)) p) :
    ContinuousAt (fun q => g.inner q (v q) (w q)) p := by
  have h : ContinuousAt
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial S ℝ) q (g.inner q (v q) (w q))) p :=
    g.contMDiff.continuous.continuousAt.clm_bundle_apply₂ (F₁ := RVec 2) (F₂ := RVec 2) hv hw
  simp only [FiberBundle.continuousAt_totalSpace] at h
  exact h.2

private theorem ambient_metric_pair_continuousAt (h : AmbientMetric N)
    (f : S → N) (v w : ∀ q : S, TangentSpace AmbientModel (f q)) (p : S)
    (hf : ContinuousAt f p)
    (hv : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (v q)) p)
    (hw : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (w q)) p) :
    ContinuousAt (fun q => h.inner (f q) (v q) (w q)) p := by
  have h' : ContinuousAt
      (fun q => TotalSpace.mk' ℝ (E := Bundle.Trivial N ℝ) (f q) (h.inner (f q) (v q) (w q))) p :=
    (h.contMDiff.continuous.continuousAt.comp hf).clm_bundle_apply₂ (F₁ := RVec 3) (F₂ := RVec 3) hv hw
  simp only [FiberBundle.continuousAt_totalSpace] at h'
  exact h'.2

private theorem source_local_section_continuousAt (p : S) (a : RVec 2) :
    ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q
      ((trivializationAt (RVec 2) (TangentSpace SurfaceModel) p).symmL ℝ q a)) p := by
  let e := trivializationAt (RVec 2) (TangentSpace SurfaceModel) p
  have hp : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  apply (e.continuousAt_symm_prodMk_left (v := a) hp).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hp] with q hq
  change TotalSpace.mk' (RVec 2) q (e.symmL ℝ q a) = e.toOpenPartialHomeomorph.symm (q, a)
  simpa only [e.symmL_apply hq] using e.mk_symm hq a

private theorem source_interior_dense : Dense (SurfaceModel.interior S) := by
  intro p
  have hx := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := SurfaceModel) p)
  have hm : Set.MapsTo (extChartAt SurfaceModel p).symm
      (interior (extChartAt SurfaceModel p).target) (SurfaceModel.interior S) := by
    intro x hx
    have hxt := interior_subset hx
    change SurfaceModel.IsInteriorPoint ((extChartAt SurfaceModel p).symm x)
    rw [SurfaceModel.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by norm_num)
      (chart_mem_atlas (EuclideanHalfSpace 2) p)
      (by simpa only [← extChartAt_source SurfaceModel p] using (extChartAt SurfaceModel p).map_target hxt)]
    change extChartAt SurfaceModel p ((extChartAt SurfaceModel p).symm x) ∈
      interior (extChartAt SurfaceModel p).target
    simpa only [(extChartAt SurfaceModel p).right_inv hxt] using hx
  have h := (continuousAt_extChartAt_symm (I := SurfaceModel) p).continuousWithinAt.mem_closure hx hm
  simpa only [extChartAt_to_inv] using h

private theorem local_conformal_factor (g : SurfaceMetric S) (h : AmbientMetric N) (f : S → N)
    (hregular : ContMDiff SurfaceModel AmbientModel 2 f)
    (hconformal : WeakConformalInterior g h f) (p : S) :
    ∃ μ : ℝ, 0 ≤ μ ∧ ∀ v w, h.inner (f p)
      (mfderiv SurfaceModel AmbientModel f p v)
      (mfderiv SurfaceModel AmbientModel f p w) = μ * g.inner p v w := by
  obtain ⟨μ₀, hμ₀, hc⟩ := hconformal
  let e := trivializationAt (RVec 2) (TangentSpace SurfaceModel) p
  let a : RVec 2 := EuclideanSpace.single 0 1
  let V : ∀ q : S, TangentSpace SurfaceModel q := fun q => e.symmL ℝ q a
  let d : S → ℝ := fun q => g.inner q (V q) (V q)
  let A := mfderiv SurfaceModel AmbientModel f
  let b : S → ℝ := fun q => h.inner (f q) (A q (V q)) (A q (V q))
  have hV : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (V q)) p :=
    source_local_section_continuousAt p a
  have hAV : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (A q (V q))) p :=
    (hregular.continuous_tangentMap (by norm_num)).continuousAt.comp hV
  have hd : ContinuousAt d p := source_metric_pair_continuousAt g V V p hV hV
  have hb : ContinuousAt b p := ambient_metric_pair_continuousAt h f _ _ p
    hregular.continuous.continuousAt hAV hAV
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hVne : V p ≠ 0 := by
    intro hz
    have : a = 0 := by
      simpa only [V, e.continuousLinearMapAt_symmL hpbase a, map_zero] using
        congrArg (e.continuousLinearMapAt ℝ p) hz
    have : (1 : ℝ) = 0 := by simpa [a] using congrArg (fun x : RVec 2 => x 0) this
    norm_num at this
  have hdpos : 0 < d p := g.pos p (V p) hVne
  have hbnonneg : 0 ≤ b p := by
    by_cases hzero : A p (V p) = 0
    · simp [b, hzero]
    · exact (h.pos (f p) _ hzero).le
  let μ := fun q => b q / d q
  have hμcont : ContinuousAt μ p := hb.div hd hdpos.ne'
  refine ⟨μ p, div_nonneg hbnonneg hdpos.le, ?_⟩
  intro v w
  let Vv : ∀ q : S, TangentSpace SurfaceModel q := fun q => e.symmL ℝ q (e.continuousLinearMapAt ℝ p v)
  let Vw : ∀ q : S, TangentSpace SurfaceModel q := fun q => e.symmL ℝ q (e.continuousLinearMapAt ℝ p w)
  have hVv : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (Vv q)) p :=
    source_local_section_continuousAt p _
  have hVw : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (Vw q)) p :=
    source_local_section_continuousAt p _
  have hAv : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (A q (Vv q))) p :=
    (hregular.continuous_tangentMap (by norm_num)).continuousAt.comp hVv
  have hAw : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (A q (Vw q))) p :=
    (hregular.continuous_tangentMap (by norm_num)).continuousAt.comp hVw
  have hlhs := ambient_metric_pair_continuousAt h f _ _ p hregular.continuous.continuousAt hAv hAw
  have hrhs := hμcont.mul (source_metric_pair_continuousAt g Vv Vw p hVv hVw)
  have hfrequent : ∃ᶠ q in 𝓝 p, h.inner (f q) (A q (Vv q)) (A q (Vw q)) = μ q * g.inner q (Vv q) (Vw q) := by
    apply ((mem_closure_iff_frequently.mp (source_interior_dense (S := S) p)).and_eventually
      (hd.eventually_ne hdpos.ne')).mono
    intro q hq
    have hfactor : μ q = μ₀ q := by
      apply (div_eq_iff hq.2).mpr
      exact hc q hq.1 (V q) (V q)
    rw [hfactor]
    exact hc q hq.1 (Vv q) (Vw q)
  have heq := tendsto_nhds_unique_of_frequently_eq hlhs hrhs hfrequent
  simpa only [Pi.mul_apply, Vv, Vw, e.symmL_continuousLinearMapAt hpbase, A] using heq

/-- The continuity extension invoked immediately after Definition C.2.
The conformal factor is produced on all of S, not simply assumed to extend. -/
theorem c2_weak_conformality_extends_to_boundary
    (g : SurfaceMetric S) (h : AmbientMetric N) (f : S → N)
    (hconformal : WeakConformalInterior g h f)
    (hregular : C2HolderUpToBoundary f) :
    ∃ μ : S → ℝ, Continuous μ ∧ (∀ p, 0 ≤ μ p) ∧
      ∀ p v w, h.inner (f p) (mfderiv SurfaceModel AmbientModel f p v)
        (mfderiv SurfaceModel AmbientModel f p w) = μ p * g.inner p v w := by
  choose μ hμ hc using fun p => local_conformal_factor g h f hregular.regular hconformal p
  refine ⟨μ, continuous_iff_continuousAt.mpr ?_, hμ, hc⟩
  intro p
  let e := trivializationAt (RVec 2) (TangentSpace SurfaceModel) p
  let a : RVec 2 := EuclideanSpace.single 0 1
  let V : ∀ q : S, TangentSpace SurfaceModel q := fun q => e.symmL ℝ q a
  let d : S → ℝ := fun q => g.inner q (V q) (V q)
  let A := mfderiv SurfaceModel AmbientModel f
  let b : S → ℝ := fun q => h.inner (f q) (A q (V q)) (A q (V q))
  have hV : ContinuousAt (fun q => TotalSpace.mk' (RVec 2) q (V q)) p :=
    source_local_section_continuousAt p a
  have hAV : ContinuousAt (fun q => TotalSpace.mk' (RVec 3) (f q) (A q (V q))) p :=
    (hregular.regular.continuous_tangentMap (by norm_num)).continuousAt.comp hV
  have hd : ContinuousAt d p := source_metric_pair_continuousAt g V V p hV hV
  have hb : ContinuousAt b p := ambient_metric_pair_continuousAt h f _ _ p
    hregular.regular.continuous.continuousAt hAV hAV
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hVne : V p ≠ 0 := by
    intro hz
    have : a = 0 := by
      simpa only [V, e.continuousLinearMapAt_symmL hpbase a, map_zero] using
        congrArg (e.continuousLinearMapAt ℝ p) hz
    have : (1 : ℝ) = 0 := by simpa [a] using congrArg (fun x : RVec 2 => x 0) this
    norm_num at this
  have hdpos : 0 < d p := g.pos p (V p) hVne
  apply (hb.div hd hdpos.ne').congr_of_eventuallyEq
  filter_upwards [hd.eventually_ne hdpos.ne'] with q hq
  exact ((div_eq_iff hq).mpr (hc q (V q) (V q))).symm

end SeifertSurfaces.AppendixC
