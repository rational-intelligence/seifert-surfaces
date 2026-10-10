import A5NativeLongitudeBoundary
import A5NativeCurveEndpointTangent
import A5RegularArcGeometry
import A5ConormalEuclideanAdapter

set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped Manifold ContDiff
open Set Topology Filter
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
noncomputable section
private theorem embedded_map_through_partial_homeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : PartialHomeomorph Y Z) (f : X → Y) (hf : IsEmbedding f)
    (hmaps : MapsTo f univ e.source) : IsEmbedding (e ∘ f) := by
  have h := e.isEmbedding_restrict.comp (hf.codRestrict e.source
    (fun x => hmaps (mem_univ x)))
  exact h


namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
universe u
/-- The circle's native smooth structure supplies a centered real clock
with open embedded range and nonzero velocity. -/
theorem native_smooth_circle_centered_clock (s : Circle) :
    ∃ q : ℝ → Circle,
      q 0 = s ∧
      IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => q t) ∧
      IsOpen (range (fun t : Ioo (-1 : ℝ) 1 => q t)) ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ q (Ioo (-1 : ℝ) 1) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, mfderiv 𝓘(ℝ) (𝓡 1) q t 1 ≠ 0 := by
  let c : OpenPartialHomeomorph Circle (Euc 1) := chartAt (Euc 1) s
  let L : Euc 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  let d : OpenPartialHomeomorph Circle ℝ := c.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hs : s ∈ d.source := by
    exact ⟨mem_chart_source _ s, mem_univ _⟩
  have hds : d s ∈ d.target := d.map_source hs
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (d.open_target.mem_nhds hds)
  let A : ℝ ≃ₜ ℝ := (Homeomorph.mulLeft₀ r hr.ne').trans (Homeomorph.addLeft (d s))
  have hA (t : ℝ) : A t = d s + r * t := rfl
  have hmaps : MapsTo A (Ioo (-1 : ℝ) 1) d.target := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, hA, add_sub_cancel_left, abs_mul, abs_of_pos hr]
    have habs : |t| < 1 := abs_lt.mpr ht
    simpa using mul_lt_mul_of_pos_left habs hr
  let parameter : Ioo (-1 : ℝ) 1 → Circle := fun t => d.symm (A t)
  have hpembed : IsEmbedding parameter := by
    have hAe : IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => A t) :=
      A.isEmbedding.comp IsEmbedding.subtypeVal
    exact embedded_map_through_partial_homeomorph d.symm.toPartialHomeomorph
      (fun t : Ioo (-1 : ℝ) 1 => A t) hAe (fun t _ => hmaps t.property)
  have hpopen : IsOpen (range parameter) := by
    have heq : range parameter = d.symm '' (A '' Ioo (-1 : ℝ) 1) := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨A t, ⟨t, t.property, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨t, ht, rfl⟩, heq⟩
        exact ⟨⟨t, ht⟩, heq⟩
    rw [heq]
    exact d.isOpen_image_symm_of_subset_target (A.isOpenMap _ isOpen_Ioo)
      (mapsTo_iff_image_subset.mp hmaps)
  have hpcentre : parameter ⟨0, neg_one_lt_zero, zero_lt_one⟩ = s := by
    change d.symm (d s + r * 0) = s
    simpa only [mul_zero, add_zero] using d.left_inv hs
  have hdi : ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ d.symm d.target := by
    change ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ (c.symm ∘ L.symm) d.target
    exact (contMDiffOn_chart_symm (I := 𝓡 1) (n := ∞)).comp
      L.symm.contDiff.contMDiff.contMDiffOn (fun _ ht => ht.2)
  have hAsmooth : ContDiff ℝ ∞ A := by
    change ContDiff ℝ ∞ (fun t => d s + r * t)
    fun_prop
  let q : ℝ → Circle := d.symm ∘ A
  have hq : ContMDiffOn 𝓘(ℝ) (𝓡 1) ∞ q (Ioo (-1 : ℝ) 1) :=
    hdi.comp hAsmooth.contMDiff.contMDiffOn hmaps
  have hd : d.MDifferentiable (𝓡 1) 𝓘(ℝ) := by
    exact (mdifferentiable_chart (I := 𝓡 1) s).trans
      ⟨L.contDiff.contMDiff.mdifferentiable (by simp : (∞ : ℕ∞ω) ≠ 0) |>.mdifferentiableOn,
       L.symm.contDiff.contMDiff.mdifferentiable (by simp : (∞ : ℕ∞ω) ≠ 0) |>.mdifferentiableOn⟩
  have hqreg (t : Ioo (-1 : ℝ) 1) : mfderiv 𝓘(ℝ) (𝓡 1) q (t : ℝ) 1 ≠ 0 := by
    have hAd : mfderiv 𝓘(ℝ) 𝓘(ℝ) A (t : ℝ) 1 = r := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ A (t : ℝ) 1 = r
      have hder : HasDerivAt A r (t : ℝ) := by
        convert! (hasDerivAt_const (t : ℝ) (d s)).add
          ((hasDerivAt_id (t : ℝ)).const_mul r) using 1
        simp
      simpa using congrArg (fun f : ℝ →L[ℝ] ℝ => f 1) hder.hasFDerivAt.fderiv
    change mfderiv 𝓘(ℝ) (𝓡 1) (d.symm ∘ A) (t : ℝ) 1 ≠ 0
    rw [mfderiv_comp _ (hd.mdifferentiableAt_symm (hmaps t.property))
      (hAsmooth.contMDiff.mdifferentiable (by simp) _)]
    change mfderiv 𝓘(ℝ) (𝓡 1) d.symm (A t)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ) A (t : ℝ) 1) ≠ 0
    rw [hAd]
    intro hzero
    have hzero' := hd.symm.mfderiv_injective (hmaps t.property)
      (hzero.trans (map_zero _).symm)
    exact hr.ne' hzero'
  exact ⟨q,hpcentre,hpembed,hpopen,hq,fun t ht => hqreg ⟨t,ht⟩⟩

/-- The literal original longitude boundary supplies its real smooth regular
ambient parametrization at every rough native boundary point. -/
theorem native_longitude_boundary_centered_clock
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation E) {S : CompactOrientedSurface}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (x : S) (hx : x ∈ S.boundary) :
    ∃ b : ℝ → S, b 0 = x ∧ ContinuousOn b (Ioo (-1 : ℝ) 1) ∧
      (∀ t, b t ∈ S.boundary) ∧
      IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t) ∧
      ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ (E.toSphere ∘ F.map ∘ b) (Ioo (-1 : ℝ) 1) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1,
        mfderiv 𝓘(ℝ) (𝓡 3) (E.toSphere ∘ F.map ∘ b) t 1 ≠ 0 := by
  obtain ⟨a,B,hBi,hBr,hBe,hBs,hBd⟩ := native_longitude_boundary_circle E J F hF
  have hxr : x ∈ range B := hBr.symm ▸ hx
  obtain ⟨s,hs⟩ := hxr
  obtain ⟨q,hq0,hqi,hqo,hqs,hqd⟩ := native_smooth_circle_centered_clock s
  let b := B ∘ q
  refine ⟨b,?_,B.continuous.comp_continuousOn hqs.continuousOn,?_,hBi.comp hqi,
    hBs.comp_contMDiffOn hqs,?_⟩
  · change B (q 0) = x
    rw [hq0,hs]
  · intro t
    rw [← hBr]
    exact mem_range_self (q t)
  · intro t ht
    change mfderiv 𝓘(ℝ) (𝓡 3) ((E.toSphere ∘ F.map ∘ B) ∘ q) t 1 ≠ 0
    rw [mfderiv_comp _ (hBs.mdifferentiable (by simp) _)
      ((hqs.contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt (by simp))]
    intro he
    apply hqd t ht
    exact (hBd (q t)) (he.trans (map_zero _).symm)

/-- A transverse projection of the original longitude boundary has exact
smooth signed-arc geometry near the actual endpoint. No smoothness of the
rough source surface map is added. -/
theorem native_longitude_boundary_projected_signed_geometry
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (J : LongitudeFoliation E) {S : CompactOrientedSurface}
    (F : GeometricPiecewiseSurface S E.Carrier) (hF : J.BoundaryIn F.map)
    (x : S) (hx : x ∈ S.boundary)
    (c : SmoothAmbientChart ThreeSphere) (hc : E.toSphere (F.map x) ∈ c.chart.source)
    (P : Euc 3 →L[ℝ] Euc 2)
    (htrans : ∀ i j z, z ∈ ((F.domain i).chart j).map.target →
      F.parametrization i (((F.domain i).chart j).map.symm z) = x →
      Function.Bijective (P.comp (fderivWithin ℝ
        (c.chart ∘ E.toSphere ∘ sectorCoordinateMap (F.map ∘ F.parametrization i) j)
        ((F.domain i).chart j).map.target z))) :
    ∃ b : ℝ → S, b 0 = x ∧ ContinuousOn b (Ioo (-1 : ℝ) 1) ∧
      (∀ t, b t ∈ S.boundary) ∧
      IsEmbedding (fun t : Ioo (-1 : ℝ) 1 => b t) ∧
      ∃ r : ℝ, 0 < r ∧ ∃ left right : ℝ, left < 0 ∧ 0 < right ∧
      ∃ s : Euc 2 → ℝ,
        CurvedDivergence.SignedArcGeometry (Metric.ball 0 r) s
          (fun t => P (c.chart (E.toSphere (F.map (b t)))) - P (c.chart (E.toSphere (F.map x))))
          left right := by
  obtain ⟨b,hb0,hbc,hbb,hbi,hbs,hbr⟩ := native_longitude_boundary_centered_clock E J F hF x hx
  let γ := E.toSphere ∘ F.map ∘ b
  let U := Ioo (-1 : ℝ) 1 ∩ γ ⁻¹' c.chart.source
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨neg_one_lt_zero,zero_lt_one⟩
  have hc0 : γ 0 ∈ c.chart.source := by change E.toSphere (F.map (b 0)) ∈ _; rw [hb0]; exact hc
  have hU : IsOpen U := hbs.continuousOn.isOpen_inter_preimage isOpen_Ioo c.chart.open_source
  have h0U : (0 : ℝ) ∈ U := ⟨h0,hc0⟩
  have hcoords : ContDiffOn ℝ ∞ (c.chart ∘ γ) U :=
    (c.smooth.comp (hbs.mono inter_subset_left) (fun t ht => ht.2)).contDiffOn
  have hder : HasDerivAt (c.chart ∘ γ) (deriv (c.chart ∘ γ) 0) 0 :=
    ((hcoords.contDiffAt (hU.mem_nhds h0U)).differentiableAt (by simp)).hasDerivAt
  obtain ⟨C,hC⟩ := ambient_chart_tangent_equivalence c (γ 0) hc0
  have hvel : deriv (c.chart ∘ γ) 0 = C (mfderiv 𝓘(ℝ) (𝓡 3) γ 0 1) := by
    rw [hC]
    exact ambient_chart_curve_derivative_transport γ 0
      ((hbs.contMDiffAt (isOpen_Ioo.mem_nhds h0)).mdifferentiableAt (by simp)) c hc0
  have hv : deriv (c.chart ∘ γ) 0 ≠ 0 := by
    rw [hvel]
    exact fun hh => hbr 0 h0 (C.injective (hh.trans (map_zero _).symm))
  have hPv := native_curve_endpoint_transverse_velocity_nonzero E F b 0
    (hbc.continuousAt (isOpen_Ioo.mem_nhds h0)) c hc0 _ hder hv P
    (fun i j z hz he => htrans i j z hz (he.trans hb0))
  let δ := fun t => P (c.chart (γ t)) - P (c.chart (E.toSphere (F.map x)))
  have hδ : ContDiffOn ℝ ∞ δ U :=
    (P.contDiff.comp_contDiffOn hcoords).sub contDiffOn_const
  have hdδ : HasDerivAt δ (P (deriv (c.chart ∘ γ) 0)) 0 :=
    (P.hasFDerivAt.comp_hasDerivAt 0 hder).sub_const _
  obtain ⟨r,hr,left,right,hl,hright,s,hs⟩ := local_signed_geometry_of_regular_curve δ U hU h0U hδ
    (by rw [hdδ.deriv]; exact hPv)
  refine ⟨b,hb0,hbc,hbb,hbi,r,hr,left,right,hl,hright,s,?_⟩
  have hδ0 : δ 0 = 0 := by dsimp [δ,γ]; rw [hb0,sub_self]
  rw [hδ0] at hs
  exact hs

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
