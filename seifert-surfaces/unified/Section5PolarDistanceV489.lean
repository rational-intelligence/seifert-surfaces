import Section5DistanceDifferentialV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
local instance : TopologicalSpace PolarDomain := inferInstanceAs (TopologicalSpace (Circle × (Circle × Time)))
local instance : ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) PolarDomain :=
  inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) (Circle × (Circle × Time)))
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

def distanceScaleTime (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (t : Time) : Time :=
  ⟨a * (t : ℝ),mul_nonneg ha t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 ha).trans (by simpa using ha1)⟩

theorem distance_scale_time_smooth (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ (distanceScaleTime a ha ha1) := by
  apply contMDiff_iff_comp_subtypeVal_Icc.mpr
  exact ⟨(continuous_const.mul continuous_subtype_val).subtype_mk _,
    contMDiff_const.mul contMDiff_subtypeVal_Icc⟩

include P in
theorem polar_collar_uniform_inside {U : Set E.Carrier} (hU : IsOpen U)
    (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ p : Circle × Circle, ∀ t : Time,
      (t : ℝ) ≤ a → givenExteriorPolarMap E (p.1,p.2,t) ∈ U := by
  let F : (Circle × Circle) × Time → E.Carrier := fun q => givenExteriorPolarMap E (q.1.1,q.1.2,q.2)
  have hs : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ F :=
    P.smooth.comp (contMDiff_fst.fst.prodMk (contMDiff_fst.snd.prodMk contMDiff_snd))
  have hopen : IsOpen (F ⁻¹' U) := hU.preimage hs.continuous
  have hcore : (univ : Set (Circle × Circle)) ×ˢ ({(0 : Time)} : Set Time) ⊆ F ⁻¹' U := by
    rintro ⟨p,t⟩ ⟨_,ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact hb (P.boundary p.1 p.2)
  obtain ⟨A,B,hA,hB,hall,hzero,hAB⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set (Circle × Circle))) isCompact_singleton hopen hcore
  obtain ⟨ε,hε,hεB⟩ := Metric.isOpen_iff.mp hB (0 : Time) (hzero (by simp))
  refine ⟨min (ε/2) (1/2),lt_min (half_pos hε) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num),?_⟩
  intro p t ht
  change (p,t) ∈ F ⁻¹' U
  apply hAB
  refine ⟨hall (mem_univ p),hεB ?_⟩
  rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
  change |(t : ℝ)-0| < ε
  rw [sub_zero,abs_of_nonneg t.property.1]
  exact ht.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε))

include P in
theorem polar_distance_transverse (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r)
    (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) (p : Circle × Circle) :
    0 < (show ℝ from mfderiv (𝓡∂ 1) 𝓘(ℝ)
      (fun t => r (givenExteriorPolarMap E (p.1,p.2,t))) (0 : Time) timeUnit) := by
  let c : Time → E.Carrier := fun t => givenExteriorPolarMap E (p.1,p.2,t)
  have hc : ContMDiff (𝓡∂ 1) (𝓡∂ 3) ∞ c :=
    P.smooth.comp (contMDiff_const.prodMk (contMDiff_const.prodMk contMDiff_id))
  have hp := hb (P.boundary p.1 p.2)
  have hd : MDifferentiableAt (𝓡∂ 3) 𝓘(ℝ) r (c 0) :=
    ((hr.1 _ hp).contMDiffAt (hU.mem_nhds hp)).mdifferentiableAt (by simp)
  change 0 < (show ℝ from mfderiv (𝓡∂ 1) 𝓘(ℝ) (r ∘ c) 0 timeUnit)
  rw [mfderiv_comp (0 : Time) hd (hc.mdifferentiableAt (by simp))]
  exact inward_distance_differential_positive g hU hr hp (P.boundary p.1 p.2)
    _ (P.normal_positive p.1 p.2)

#print axioms polar_collar_uniform_inside
#print axioms polar_distance_transverse
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
