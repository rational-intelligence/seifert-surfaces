import A5RegularSeamIncidenceV472

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff
open Set Topology Filter
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC CurvedDivergence
universe u

def regularSeamZero : SeamLocalTime := ⟨0,neg_one_lt_zero,zero_lt_one⟩

theorem regular_seam_actual_conormal_coordinate_congr
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    {S : CompactOrientedSurface.{u}} (F : GeometricPiecewiseSurface S E.Carrier)
    (i : Fin F.pieceCount) (j : Fin (F.domain i).count)
    (x y v : E2) (hxy : x = y) (p : ThreeSphere)
    (hx : pieceSphereCoordinate E F i j x = p)
    (hy : pieceSphereCoordinate E F i j y = p) :
    actualPieceConormal E F i j x v p hx = actualPieceConormal E F i j y v p hy := by
  cases hxy
  rfl

/-- Assembly of all actual local chart inputs for one balanced native pair.
Its clock, incidence, metric, minimal pieces and zero-set coverage are the
literal native providers; no graph or image regularity is assumed. -/
theorem regular_seam_chart_of_balanced_native_pair
    {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)
    (G : A7.SourceGeometry E) {S : CompactOrientedSurface.{u}}
    (F : GeometricPiecewiseSurface S E.Carrier)
    (x : S) (trace : SeamLocalTime → S) (hcenter : trace regularSeamZero = x)
    (htraceboundary : ∀ t, trace t ∉ S.boundary)
    (edge : ℝ → ThreeSphere) (himage : ∀ t : SeamLocalTime, edge t = E.toSphere (F.map (trace t)))
    (hsmooth : ContMDiffOn 𝓘(ℝ) (𝓡 3) ∞ edge (Ioo (-1 : ℝ) 1))
    (hregular : ∀ t : SeamLocalTime, mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1 ≠ 0)
    (i : Fin 2 → Fin F.pieceCount) (j : ∀ k, Fin (F.domain (i k)).count)
    (q n : Fin 2 → SeamLocalTime → E2)
    (hq : ∀ k t, q k t ∈ ((F.domain (i k)).chart (j k)).map.target ∩
      frontier ((F.domain (i k)).chart (j k)).map.target)
    (him : ∀ k t, pieceSphereCoordinate E F (i k) (j k) (q k t) = edge t)
    (hinward : ∀ k, ∃ eps : ℝ, 0 < eps ∧ ∀ b ∈ Ioo (0 : ℝ) eps,
      q k regularSeamZero - b • n k regularSeamZero ∈ ((F.domain (i k)).chart (j k)).map.target)
    (hu : ∀ k (t : SeamLocalTime), G.extension.inner (edge t)
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t))
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t)) = 1)
    (ho : ∀ k (t : SeamLocalTime), G.extension.inner (edge t)
      (actualPieceConormal E F (i k) (j k) (q k t) (n k t) (edge t) (him k t))
      (mfderiv 𝓘(ℝ) (𝓡 3) edge (t : ℝ) 1) = 0)
    (hbal : ∀ t, actualPieceConormal E F (i 0) (j 0) (q 0 t) (n 0 t) (edge t) (him 0 t) +
      actualPieceConormal E F (i 1) (j 1) (q 1 t) (n 1 t) (edge t) (him 1 t) = 0)
    (W : Set ThreeSphere) (hW : IsOpen W) (hxW : E.toSphere (F.map x) ∈ W)
    (hcover : ∀ z ∈ E.toSphere '' F.image ∩ W,
      ∃ k : Fin 2, z ∈ range (E.toSphere ∘ F.map ∘ F.parametrization (i k)))
    (hincident : ∀ t v, trace t ∈ range (F.parametrization v) ↔ v = i 0 ∨ v = i 1)
    (V : Set S) (hV : IsOpen V) (hxV : x ∈ V) (hVboundary : V ⊆ S.boundaryᶜ)
    (htrace : ∀ z ∈ V, z ∈ F.seam.carrier → ∃ t, trace t = z)
    (hpieces : ∀ i j, IsMinimalPatch G.extension (pieceSphereCoordinate E F i j)
      (interior ((F.domain i).chart j).map.target))
    (hzeroCover : ∀ (c : SmoothAmbientChart ThreeSphere) (P : E3 →L[ℝ] E2)
      (ρ : ℝ) (s : E2 → ℝ) (left right : ℝ), left < 0 → 0 < right →
      SignedArcGeometry (Metric.ball 0 ρ) s
        (fun t => P (c.chart (edge t)) - P (c.chart (edge 0))) left right →
      ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ U ⊆ S.boundaryᶜ ∧
        ∀ z ∈ U, z ∈ F.seam.carrier →
          P (c.chart (E.toSphere (F.map z))) - P (c.chart (E.toSphere (F.map x))) ∈ Metric.ball 0 ρ →
          s (P (c.chart (E.toSphere (F.map z))) - P (c.chart (E.toSphere (F.map x)))) = 0) :
    ∃ C : SmoothImageChart S F.map, x ∈ C.chart.source := by
  have hxboundary : x ∉ S.boundary := hcenter ▸ htraceboundary regularSeamZero
  have hxint : x ∈ (𝓡∂ 2).interior S :=
    ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint x).mpr hxboundary
  have hedge0 : edge 0 = E.toSphere (F.map x) := by
    exact (himage regularSeamZero).trans (congrArg (fun z => E.toSphere (F.map z)) hcenter)
  have hpoint : ∀ k t, F.parametrization (i k) (((F.domain (i k)).chart (j k)).map.symm (q k t)) = trace t := by
    intro k t
    apply F.embedding.injective
    apply Subtype.val_injective
    exact (him k t).trans (himage t)
  let c : SmoothAmbientChart ThreeSphere := {
    chart := chartAt (Euc 3) (E.toSphere (F.map x))
    smooth := contMDiffOn_chart
    inverse_smooth := contMDiffOn_chart_symm }
  have hc : E.toSphere (F.map x) ∈ c.chart.source := mem_chart_source _ _
  obtain ⟨P,height,hsep,U,hU,hxU,hmaps,_,_,_,htrans,_⟩ :=
    native_projection_isolated_fiber_all_charts E F x c hc
  have hP (k : Fin 2) : Function.Bijective (P.comp (fderivWithin ℝ
      (c.chart ∘ pieceSphereCoordinate E F (i k) (j k))
      ((F.domain (i k)).chart (j k)).map.target (q k regularSeamZero))) := by
    apply htrans x hxU (i k) (j k) (q k regularSeamZero) (hq k regularSeamZero).1
    exact congrArg F.map ((hpoint k regularSeamZero).trans hcenter)
  have hqext (k : Fin 2) : MapsTo (regularSeamLiftExtension (q k)) (Ioo (-1 : ℝ) 1)
      (((F.domain (i k)).chart (j k)).map.target ∩ frontier ((F.domain (i k)).chart (j k)).map.target) := by
    intro t ht
    change regularSeamLiftExtension (q k) (⟨t,ht⟩ : SeamLocalTime) ∈ _
    rw [regularSeamLiftExtension_apply]
    exact hq k ⟨t,ht⟩
  have hext : ∀ k t, t ∈ Ioo (-1 : ℝ) 1 → pieceSphereCoordinate E F (i k) (j k)
      (regularSeamLiftExtension (q k) t) = edge t := by
    intro k t ht
    change pieceSphereCoordinate E F (i k) (j k)
      (regularSeamLiftExtension (q k) (⟨t,ht⟩ : SeamLocalTime)) = _
    rw [regularSeamLiftExtension_apply]
    exact him k ⟨t,ht⟩
  have hqzero (k : Fin 2) : regularSeamLiftExtension (q k) 0 = q k regularSeamZero :=
    regularSeamLiftExtension_apply (q k) regularSeamZero
  obtain ⟨ρ,hρ,left,right,hl,hr,s,hgeom⟩ := native_projected_arc_signed_geometry E F (i 0) (j 0)
    (Ioo (-1 : ℝ) 1) isOpen_Ioo (by norm_num) edge (regularSeamLiftExtension (q 0)) hsmooth
    (fun t ht => (hqext 0 ht).1) (hext 0) (hregular regularSeamZero) c (hedge0.symm ▸ hc) P
    (by simpa only [hqzero,pieceSphereCoordinate,sectorCoordinateMap,Function.comp_def] using hP 0)
  obtain ⟨Uzero,hUzero,hxUzero,hUzeroBoundary,hzeros⟩ := hzeroCover c P ρ s left right hl hr hgeom
  have hnormal (k : Fin 2) : actualPieceConormal E F (i k) (j k)
      (regularSeamLiftExtension (q k) 0) (n k regularSeamZero) (edge 0) (hext k 0 (by norm_num)) =
      actualPieceConormal E F (i k) (j k) (q k regularSeamZero) (n k regularSeamZero)
        (edge 0) (him k regularSeamZero) :=
    regular_seam_actual_conormal_coordinate_congr E F (i k) (j k) _ _ _ (hqzero k) _ _ _
  have hlocal := native_regular_seam_projection_local_homeomorph E F i j
    (Ioo (-1 : ℝ) 1) isOpen_Ioo (by norm_num) edge
    (fun k => regularSeamLiftExtension (q k)) (fun k => n k regularSeamZero)
    (hsmooth.of_le (by simp)) (hregular regularSeamZero) hqext hext
    (by
      intro k
      obtain ⟨eps,heps,hdir⟩ := hinward k
      refine ⟨eps,heps,?_⟩
      intro b hb
      rw [hqzero]
      exact hdir b hb)
    c (hedge0.symm ▸ hc) (G.extension.inner (edge 0)) P x hxint hedge0 W hW hxW hcover
    (by
      intro k
      change G.extension.inner (edge 0)
        (actualPieceConormal E F (i k) (j k) (regularSeamLiftExtension (q k) 0) (n k regularSeamZero) (edge 0) (hext k 0 (by norm_num)))
        (actualPieceConormal E F (i k) (j k) (regularSeamLiftExtension (q k) 0) (n k regularSeamZero) (edge 0) (hext k 0 (by norm_num))) = 1
      rw [hnormal]
      exact hu k regularSeamZero)
    (by
      intro k
      change G.extension.inner (edge 0)
        (actualPieceConormal E F (i k) (j k) (regularSeamLiftExtension (q k) 0) (n k regularSeamZero) (edge 0) (hext k 0 (by norm_num)))
        (mfderiv 𝓘(ℝ) (𝓡 3) edge 0 1) = 0
      rw [hnormal]
      exact ho k regularSeamZero)
    (by
      change actualPieceConormal E F (i 0) (j 0) (regularSeamLiftExtension (q 0) 0) (n 0 regularSeamZero) (edge 0) (hext 0 0 (by norm_num)) +
        actualPieceConormal E F (i 1) (j 1) (regularSeamLiftExtension (q 1) 0) (n 1 regularSeamZero) (edge 0) (hext 1 0 (by norm_num)) = 0
      rw [hnormal 0,hnormal 1]
      exact hbal regularSeamZero)
    (by simpa only [hqzero,pieceSphereCoordinate,sectorCoordinateMap,Function.comp_def] using hP)
  obtain ⟨e,hxe,he⟩ := hlocal x (mem_singleton x)
  let Z := U ∩ Uzero ∩ V
  have hZ : IsOpen Z := (hU.inter hUzero).inter hV
  have hxZ : x ∈ Z := ⟨⟨hxU,hxUzero⟩,hxV⟩
  let er := e.restrOpen Z hZ
  have hxer : x ∈ er.source := ⟨hxe,hxZ⟩
  have her (z : S) : er z = P (c.chart (E.toSphere (F.map z))) := congrFun he.symm z
  have hmapsEr : MapsTo (E.toSphere ∘ F.map) er.source c.chart.source := fun z hz => hmaps hz.2.1.1
  have htangent := native_tangent_ranges_of_exact_pair_incidence E F i j trace q
    (fun k t => (hq k t).1) hpoint hincident V hVboundary htrace c (by
      intro t ht
      apply balanced_native_pair_tangent_ranges E F i j edge (hsmooth.of_le (by simp)) hregular q n
        (fun k t => (hq k t).1) him (fun t => G.extension.inner (edge t)) hu ho hbal t c
      exact (himage t).symm ▸ ht)
  obtain ⟨C,hxC,_⟩ := native_seam_chart_from_projection_and_tangents E F G.extension x c P height hsep
    er hxer hxboundary her hmapsEr
    (fun ii jj z hz hzs => htrans _ hzs.2.1.1 ii jj z hz rfl)
    (fun ii jj kk ll z w hz hw heq hzs _ => htangent ii jj kk ll z w hz hw heq hzs.2.2 (hmapsEr hzs))
    hpieces ρ hρ s
      (fun t => P (c.chart (edge t)) - P (c.chart (edge 0))) left right hgeom
      (by
        intro y hy ht hs
        let z := er.symm (er x + y)
        have hz : z ∈ er.source := er.map_target ht
        have hzG : z ∈ F.seam.carrier := hs.resolve_right (hVboundary hz.2.2)
        have hpz : P (c.chart (E.toSphere (F.map z))) - P (c.chart (E.toSphere (F.map x))) = y := by
          rw [← her z,← her x,er.right_inv ht,add_sub_cancel_left]
        have hh := hzeros z hz.2.1.2 hzG (hpz.symm ▸ hy)
        rwa [hpz] at hh)
  exact ⟨C,hxC⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
