import Section5PolarOpenRestrictionV489
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.LongitudeProducers SeifertSurfaces.LongitudeProducers.CollarCutHelpers
noncomputable section
local instance : TopologicalSpace PolarDomain := inferInstanceAs (TopologicalSpace (Circle × (Circle × Time)))
local instance : ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) PolarDomain :=
  inferInstanceAs (ChartedSpace (ModelProd (Euc 1) (ModelProd (Euc 1) (EuclideanHalfSpace 1))) (Circle × (Circle × Time)))
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {D : TubeCoordinates T} (P : GivenExteriorPolarCollar E D)

include P in
theorem metric_polar_collar (g : SmoothMetric E.Carrier)
    {U : Set E.Carrier} (hU : IsOpen U) {r : E.Carrier → ℝ}
    (hr : IsInwardDistanceCoordinate g U r) (hb : (𝓡∂ 3).boundary E.Carrier ⊆ U) :
    ∃ b : ℝ, 0 < b ∧ ∃ V : TopologicalSpace.Opens E.Carrier,
    ∃ C : Diffeomorph (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) longitudeProductStrip V ∞,
    ∃ m : ((Circle × Circle) × Time) → E.Carrier,
      ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ m ∧
      (∀ q : longitudeProductStrip, m q.val = (C q : E.Carrier)) ∧
      (∀ p : Circle × Circle, m (p,0) = givenExteriorPolarMap E (p.1,p.2,0)) ∧
      (∀ q, m q ∈ U ∧ r (m q) = b*(q.2 : ℝ)) := by
  obtain ⟨a,b,ha,ha1,hbpos,F,tau,e,hF,htau,hF0,htau0,he,hsource,hactual,hright,hpos⟩ :=
    polar_distance_inverse_data P g hU hr hb
  obtain ⟨O,C,hC,hOb,hCb,hOsmall⟩ := distance_strip_diffeomorph a b ha ha1 hbpos F tau e
    hF htau hF0 htau0 he hsource (fun p t ht => (hactual p t ht).2.2) hright
  obtain ⟨V,d,hd⟩ := polar_collar_restrict_open P O (fun q hq => (hOsmall ⟨q,hq⟩).1.trans ha1)
  have hscaled (q : (Circle × Circle) × Time) : b*(q.2 : ℝ) ∈ Icc (0 : ℝ) b :=
    ⟨mul_nonneg hbpos.le q.2.property.1,by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left q.2.property.2 hbpos.le)⟩
  have htime (q : (Circle × Circle) × Time) : tau (b*(q.2 : ℝ),q.1) ∈ Icc (0 : ℝ) 1 :=
    ⟨(hright _ (hscaled q) _).2.1.1,((hright _ (hscaled q) _).2.1.2.trans ha1).le⟩
  let t : ((Circle × Circle) × Time) → Time := fun q => ⟨tau (b*(q.2 : ℝ),q.1),htime q⟩
  have ht : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 1) ∞ t := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    have hs : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) 𝓘(ℝ) ∞
        (fun q : (Circle × Circle) × Time => tau (b*(q.2 : ℝ),q.1)) :=
      htau.comp ((contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).prodMk contMDiff_fst)
    exact ⟨hs.continuous.subtype_mk _,hs⟩
  let m : ((Circle × Circle) × Time) → E.Carrier := fun q => givenExteriorPolarMap E (q.1.1,q.1.2,t q)
  have hm : ContMDiff (((𝓡 1).prod (𝓡 1)).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ m :=
    P.smooth.comp (contMDiff_fst.fst.prodMk (contMDiff_fst.snd.prodMk ht))
  refine ⟨b,hbpos,V,C.trans d,m,hm,?_,?_,?_⟩
  · intro q
    change m q.val = (d (C q) : E.Carrier)
    rw [hd]
    have hbase := (hC q).1
    have htq : (C q).val.2 = t q.val := Subtype.ext (hC q).2
    change givenExteriorPolarMap E (q.val.1.1,q.val.1.2,t q.val) = _
    rw [hbase,htq]
  · intro p
    have ht0 : t (p,0) = 0 := by
      apply Subtype.ext
      change tau (b*0,p) = 0
      rw [mul_zero,htau0]
    change givenExteriorPolarMap E (p.1,p.2,t (p,0)) = _
    rw [ht0]
  · intro q
    have hac := hactual q.1 (t q) (hright _ (hscaled q) _).2.1.2.le
    exact ⟨hac.2.1,hac.1.symm.trans (hright _ (hscaled q) _).2.2⟩

#print axioms metric_polar_collar
end
end SeifertSurfaces.OriginalEndpoints.Section5.CommonLeafGeometryV488
