import OriginalA3

noncomputable section
open Set Topology Function MeasureTheory
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints
open SeifertSurfaces.AppendixACoordinates SeifertSurfaces.AppendixC
universe u v
variable {N : Type u} [TopologicalSpace N] [ChartedSpace E3 N]
  [IsManifold 𝓘(ℝ, E3) ∞ N]

/-- All geometric witnesses refer to the original two sheets and the same metric.
The larger closed disc is local shrinkage data for uniform coefficient bounds.
The signed defining function supplies the two curved sides and their normals. -/
structure A3SharedGraph {h : AmbientMetric N} {M : Set N}
    (D : A3OriginalData.{u,v} h M) where
  neighborhood : Set N
  neighborhood_open : IsOpen neighborhood
  point_mem : D.edge D.pointParameter ∈ neighborhood
  radius : ℝ
  radius_pos : 0 < radius
  coordinates : SmoothAmbientChart N
  point_in_chart : D.edge D.pointParameter ∈ coordinates.chart.source
  plane : E2 →L[ℝ] E3
  normal : E3
  splitting : Function.Bijective (fun z : E2 × ℝ => plane z.1 + z.2 • normal)
  height : E2 → ℝ
  height_zero : height 0 = 0
  height_C1 : ContDiffOn ℝ 1 height (Metric.closedBall 0 (2 * radius))
  graph_in_chart : MapsTo
    (graphMap (coordinates.chart (D.edge D.pointParameter)) plane normal height)
    (Metric.closedBall 0 (2 * radius)) coordinates.chart.target
  sideOne : Set E2
  sideTwo : Set E2
  sideOne_in_disc : sideOne ⊆ Metric.ball 0 radius
  sideTwo_in_disc : sideTwo ⊆ Metric.ball 0 radius
  sides_cover : sideOne ∪ sideTwo = Metric.ball 0 radius
  sideOne_closed : IsClosed ((Subtype.val : Metric.ball (0 : E2) radius → E2) ⁻¹' sideOne)
  sideTwo_closed : IsClosed ((Subtype.val : Metric.ball (0 : E2) radius → E2) ⁻¹' sideTwo)
  interiors_disjoint : Disjoint (interior sideOne) (interior sideTwo)
  height_smooth_one : ContDiffOn ℝ ∞ height sideOne
  height_smooth_two : ContDiffOn ℝ ∞ height sideTwo
  sheetOne_exact :
    (coordinates.chart.symm ∘ graphMap (coordinates.chart (D.edge D.pointParameter))
      plane normal height) '' sideOne = D.sheetOne.image ∩ neighborhood
  sheetTwo_exact :
    (coordinates.chart.symm ∘ graphMap (coordinates.chart (D.edge D.pointParameter))
      plane normal height) '' sideTwo = D.sheetTwo.image ∩ neighborhood
  edgeLeft : ℝ
  edgeRight : ℝ
  edgeLeft_lower : -1 < edgeLeft
  point_after_left : edgeLeft < (D.pointParameter : ℝ)
  point_before_right : (D.pointParameter : ℝ) < edgeRight
  edgeRight_upper : edgeRight < 1
  projectedEdge : ℝ → E2
  edge_smooth : ContDiffOn ℝ ∞ projectedEdge (Ioo edgeLeft edgeRight)
  edge_embedding : IsEmbedding (fun t : Ioo edgeLeft edgeRight => projectedEdge t)
  edge_regular : ∀ t ∈ Ioo edgeLeft edgeRight, fderiv ℝ projectedEdge t 1 ≠ 0
  edge_zero : projectedEdge D.pointParameter = 0
  shared_edge : sideOne ∩ sideTwo =
    (projectedEdge '' Ioo edgeLeft edgeRight) ∩ Metric.ball 0 radius
  edge_exact : ∀ t ∈ Ioo edgeLeft edgeRight,
    coordinates.chart.symm (graphMap (coordinates.chart (D.edge D.pointParameter))
      plane normal height (projectedEdge t)) = D.edge t
  signedSide : E2 → ℝ
  signedSide_smooth : ContDiffOn ℝ ∞ signedSide (Metric.ball 0 radius)
  signedSide_regular : ∀ x ∈ Metric.ball 0 radius,
    signedSide x = 0 → planarGradient signedSide x ≠ 0
  sideOne_signed : sideOne = {x ∈ Metric.ball 0 radius | signedSide x ≤ 0}
  sideTwo_signed : sideTwo = {x ∈ Metric.ball 0 radius | 0 ≤ signedSide x}

namespace A3SharedGraph
variable {h : AmbientMetric N} {M : Set N} {D : A3OriginalData.{u,v} h M}
def disc (G : A3SharedGraph D) : Set E2 := Metric.ball 0 G.radius
def interface (G : A3SharedGraph D) : Set E2 := G.sideOne ∩ G.sideTwo
def parameter (G : A3SharedGraph D) : E2 → N :=
  G.coordinates.chart.symm ∘ graphMap (G.coordinates.chart (D.edge D.pointParameter))
    G.plane G.normal G.height
end A3SharedGraph

/-- A.3 lines 1159--1164, with harmless local shrinking for compact control. -/
theorem A3_same_metric_two_sided_graph {h : AmbientMetric N} {M : Set N}
    (D : A3OriginalData.{u,v} h M) : Nonempty (A3SharedGraph D) := by
  let x₁ := D.liftOne D.pointParameter
  let h₁ := D.sheetOne.smoothEmbedding.isImmersion.isImmersionAt x₁
  let F := h₁.complement
  let hF := h₁.isImmersionAtOfComplement_complement
  letI : FiniteDimensional ℝ (E2 × F) :=
    FiniteDimensional.of_injective hF.equiv.toLinearEquiv.toLinearMap hF.equiv.injective
  letI : FiniteDimensional ℝ F :=
    FiniteDimensional.of_injective (LinearMap.inr ℝ E2 F) LinearMap.inr_injective
  have hdim : Module.finrank ℝ F = Module.finrank ℝ ℝ := by
    have hsum := hF.equiv.toLinearEquiv.finrank_eq
    change Module.finrank ℝ (E2 × F) = Module.finrank ℝ E3 at hsum
    simp only [Module.finrank_prod] at hsum
    have h2 : Module.finrank ℝ E2 = 2 := by simp [E2]
    have h3 : Module.finrank ℝ E3 = 3 := by simp [E3]
    rw [h2, h3] at hsum
    simp only [Module.finrank_self]
    omega
  let H := hF.trans_F (ContinuousLinearEquiv.ofFinrankEq hdim)
  let c : SmoothAmbientChart N := {
    chart := H.codChart
    smooth := contMDiffOn_of_mem_maximalAtlas H.codChart_mem_maximalAtlas
    inverse_smooth := contMDiffOn_symm_of_mem_maximalAtlas H.codChart_mem_maximalAtlas }
  have hq : D.edge D.pointParameter ∈ c.chart.source := by
    rw [← D.liftOne_exact D.pointParameter]
    exact H.mem_codChart_source
  let L : E2 →L[ℝ] E3 := H.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E2 ℝ)
  let normal : E3 := H.equiv (0, 1)
  have hsplit : Function.Bijective (fun z : E2 × ℝ => L z.1 + z.2 • normal) := by
    have heq : (fun z : E2 × ℝ => L z.1 + z.2 • normal) = H.equiv := by
      funext z
      change H.equiv (z.1, 0) + z.2 • H.equiv (0, 1) = H.equiv z
      rw [← map_smul, ← map_add]
      congr 1
      ext <;> simp
    rw [heq]
    exact H.equiv.bijective
  have hfirst_sheet := H.writtenInCharts
  let x₂ := D.liftTwo D.pointParameter
  let H₂ := D.sheetTwo.smoothEmbedding.isImmersion.isImmersionAt x₂
  let c₂ : SmoothAmbientChart N := {
    chart := H₂.codChart
    smooth := contMDiffOn_of_mem_maximalAtlas H₂.codChart_mem_maximalAtlas
    inverse_smooth := contMDiffOn_symm_of_mem_maximalAtlas H₂.codChart_mem_maximalAtlas }
  let B₂ : E2 →L[ℝ] E3 := H₂.equiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ E2 H₂.complement)
  let W₂ := c₂.chart.target ∩ c₂.chart.symm ⁻¹' c.chart.source
  have hW₂ : IsOpen W₂ :=
    c₂.chart.symm.continuousOn.isOpen_inter_preimage c₂.chart.open_target c.chart.open_source
  let U₂ : Set E2 := B₂ ⁻¹' W₂
  have hU₂ : IsOpen U₂ := hW₂.preimage B₂.continuous
  let F₂ : E2 → E3 := c.chart ∘ c₂.chart.symm ∘ B₂
  have hF₂ : ContDiffOn ℝ ∞ F₂ U₂ := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact c.smooth.comp
      (c₂.inverse_smooth.comp B₂.contMDiff.contMDiffOn (fun z hz => hz.1))
      (fun z hz => hz.2)
  let z₂ : E2 := (H₂.domChart.extend (𝓡∂ 2)) x₂
  have hz₂ : z₂ ∈ (H₂.domChart.extend (𝓡∂ 2)).target :=
    (H₂.domChart.extend (𝓡∂ 2)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using H₂.mem_domChart_source)
  have hB₂ : B₂ z₂ = c₂.chart (D.edge D.pointParameter) := by
    have ht := H₂.writtenInCharts hz₂
    change (H₂.codChart.extend 𝓘(ℝ, E3))
      (D.sheetTwo.inclusion ((H₂.domChart.extend (𝓡∂ 2)).symm z₂)) = B₂ z₂ at ht
    rw [(H₂.domChart.extend (𝓡∂ 2)).left_inv
      (by simpa only [OpenPartialHomeomorph.extend_source] using H₂.mem_domChart_source)] at ht
    simpa [c₂, x₂, D.liftTwo_exact D.pointParameter] using ht.symm
  have hq₂ : D.edge D.pointParameter ∈ c₂.chart.source := by
    rw [← D.liftTwo_exact D.pointParameter]
    exact H₂.mem_codChart_source
  have hzU₂ : z₂ ∈ U₂ := by
    change B₂ z₂ ∈ W₂
    rw [hB₂]
    refine ⟨c₂.chart.map_source hq₂, ?_⟩
    change c₂.chart.symm (c₂.chart (D.edge D.pointParameter)) ∈ c.chart.source
    rwa [c₂.chart.left_inv hq₂]
  have hF₂base : F₂ z₂ = c.chart (D.edge D.pointParameter) := by
    change c.chart (c₂.chart.symm (B₂ z₂)) = _
    rw [hB₂, c₂.chart.left_inv hq₂]
  have hF₂exact : ∀ y ∈ H₂.domChart.source,
      F₂ ((H₂.domChart.extend (𝓡∂ 2)) y) = c.chart (D.sheetTwo.inclusion y) := by
    intro y hy
    have hy' : y ∈ (H₂.domChart.extend (𝓡∂ 2)).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hy
    have hcoord := H₂.writtenInCharts ((H₂.domChart.extend (𝓡∂ 2)).map_source hy')
    change (H₂.codChart.extend 𝓘(ℝ, E3))
      (D.sheetTwo.inclusion ((H₂.domChart.extend (𝓡∂ 2)).symm
        ((H₂.domChart.extend (𝓡∂ 2)) y))) = B₂ ((H₂.domChart.extend (𝓡∂ 2)) y) at hcoord
    rw [(H₂.domChart.extend (𝓡∂ 2)).left_inv hy'] at hcoord
    have hcoord' : c₂.chart (D.sheetTwo.inclusion y) =
        B₂ ((H₂.domChart.extend (𝓡∂ 2)) y) := by simpa [c₂] using hcoord
    change c.chart (c₂.chart.symm (B₂ ((H₂.domChart.extend (𝓡∂ 2)) y))) = _
    rw [← hcoord', c₂.chart.left_inv (H₂.source_subset_preimage_source hy)]
  let π : E3 →L[ℝ] E2 := (ContinuousLinearMap.fst ℝ E2 ℝ).comp
    H.equiv.symm.toContinuousLinearMap
  have hπL : ∀ z : E2, π (L z) = z := by
    intro z
    change (H.equiv.symm (H.equiv (z, 0))).1 = z
    rw [H.equiv.symm_apply_apply]
  have hπnormal : π normal = 0 := by
    change (H.equiv.symm (H.equiv (0, 1))).1 = 0
    rw [H.equiv.symm_apply_apply]
  have hprojectedSmooth : ContDiffOn ℝ ∞ (π ∘ F₂) U₂ :=
    π.contDiff.comp_contDiffOn hF₂
  -- Remaining geometric construction: represent the second sheet over the same
  -- projection, identify opposite sides, glue matching first jets and shrink.
  have projection_invertible_of_same_range
      (B : E2 →L[ℝ] E3) (π : E3 →L[ℝ] E2) (A : E2 →L[ℝ] E3)
      (hπB : π.comp B = ContinuousLinearMap.id ℝ E2)
      (hA : Function.Injective A)
      (hRange : LinearMap.range A.toLinearMap = LinearMap.range B.toLinearMap) :
      (π.comp A).IsInvertible := by
    classical
    have hleft : ∀ x, π (B x) = x := fun x => congrArg (fun f : E2 →L[ℝ] E2 => f x) hπB
    have hsurj : Function.Surjective (π.comp A) := by
      intro x
      have hx : B x ∈ LinearMap.range A.toLinearMap := by
        rw [hRange]
        exact ⟨x, rfl⟩
      obtain ⟨y, hy⟩ := hx
      change A y = B x at hy
      exact ⟨y, by change π (A y) = x; rw [hy, hleft]⟩
    have hinj : Function.Injective (π.comp A) := by
      intro x y hxy
      have hx : A x ∈ LinearMap.range B.toLinearMap := by rw [← hRange]; exact ⟨x, rfl⟩
      have hy : A y ∈ LinearMap.range B.toLinearMap := by rw [← hRange]; exact ⟨y, rfl⟩
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      change B u = A x at hu
      change B v = A y at hv
      have huv : u = v := by
        change π (A x) = π (A y) at hxy
        rw [← hu, ← hv, hleft, hleft] at hxy
        exact hxy
      apply hA
      rw [← hu, ← hv, huv]
    exact ⟨(LinearEquiv.ofBijective (π.comp A).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, rfl⟩
  
  /- Transport through the same genuine immersion charts at an arbitrary point
  of their fixed overlap. The full Euclidean extension is differentiated at the
  literal source coordinate, including source-boundary points. -/
  have full_extension_derivative_transport_real
      (P : EmbeddedSheet.{u,v} N) (y0 : P.carrier)
      (H : Manifold.IsImmersionAtOfComplement (ℝ) (𝓡∂ 2) 𝓘(ℝ, E3) ∞ P.inclusion y0)
      (c : OpenPartialHomeomorph N E3)
      (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E3) ∞ N)
      (y : P.carrier) (hy : y ∈ H.domChart.source)
      (hcy : P.inclusion y ∈ c.source) :
      let b := H.domChart.extend (𝓡∂ 2)
      let B := H.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 (ℝ))
      let F := c ∘ H.codChart.symm ∘ B
      let z := b y
      let dP := mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion y
      let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
      let C := (tangentSpaceCastModel 𝓘(ℝ, E3) (c (P.inclusion y))).toContinuousLinearMap.comp
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c (P.inclusion y))
      J.IsInvertible ∧ C.IsInvertible ∧
        DifferentiableAt ℝ F z ∧
        (fderiv ℝ F z).comp J = C.comp dP ∧
        LinearMap.range (fderiv ℝ F z).toLinearMap =
          (LinearMap.range dP.toLinearMap).map C.toLinearMap ∧
        Function.Injective (fderiv ℝ F z) := by
    classical
    let b := H.domChart.extend (𝓡∂ 2)
    let B := H.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 (ℝ))
    let F := c ∘ H.codChart.symm ∘ B
    let z := b y
    let dP := mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion y
    let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
    let C := (tangentSpaceCastModel 𝓘(ℝ, E3) (c (P.inclusion y))).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c (P.inclusion y))
    change J.IsInvertible ∧ C.IsInvertible ∧ DifferentiableAt ℝ F z ∧
      (fderiv ℝ F z).comp J = C.comp dP ∧
      LinearMap.range (fderiv ℝ F z).toLinearMap =
        (LinearMap.range dP.toLinearMap).map C.toLinearMap ∧
      Function.Injective (fderiv ℝ F z)
    have hdom := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
      H.domChart_mem_maximalAtlas
    have hcod := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
      H.codChart_mem_maximalAtlas
    have hc1 := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp) hc
    have hJ : J.IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv.comp (isInvertible_mfderiv_extend hdom hy)
    have hC : C.IsInvertible := by
      apply ContinuousLinearMap.isInvertible_equiv.comp
      let hm : c.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) := ⟨
        fun a ha => (mdifferentiableAt_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt,
        fun a ha => (mdifferentiableAt_symm_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt⟩
      exact ⟨hm.mfderiv hcy, rfl⟩
    have hyb : y ∈ b.source := by simpa only [b, OpenPartialHomeomorph.extend_source] using hy
    have hz : z ∈ b.target := b.map_source hyb
    have hBz : B z = H.codChart (P.inclusion y) := by
      have ht := H.writtenInCharts hz
      change H.codChart (P.inclusion (b.symm (b y))) = B z at ht
      rw [b.left_inv hyb] at ht
      exact ht.symm
    have hpy : P.inclusion y ∈ H.codChart.source := H.source_subset_preimage_source hy
    have hBtarget : B z ∈ H.codChart.target := by rw [hBz]; exact H.codChart.map_source hpy
    have hinv : H.codChart.symm (B z) = P.inclusion y := by rw [hBz, H.codChart.left_inv hpy]
    have hF : DifferentiableAt ℝ F z := by
      apply mdifferentiableAt_iff_differentiableAt.mp
      apply (mdifferentiableAt_of_mem_maximalAtlas hc1 (by simpa [hinv] using hcy)).comp
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas hcod hBtarget).comp z B.mdifferentiableAt
    have heq : F ∘ b =ᶠ[𝓝 y] c ∘ P.inclusion := by
      filter_upwards [H.domChart.open_source.mem_nhds hy] with a ha
      have hab : a ∈ b.source := by simpa only [b, OpenPartialHomeomorph.extend_source] using ha
      have ht := H.writtenInCharts (b.map_source hab)
      change H.codChart (P.inclusion (b.symm (b a))) = B (b a) at ht
      rw [b.left_inv hab] at ht
      change c (H.codChart.symm (B (b a))) = c (P.inclusion a)
      rw [← ht, H.codChart.left_inv (H.source_subset_preimage_source ha)]
    have hchain : (fderiv ℝ F z).comp J = C.comp dP := by
      have hh := heq.mfderiv_eq (I := 𝓡∂ 2) (I' := 𝓘(ℝ, E3))
      have hb := H.domChart.mdifferentiableAt_extend hdom hy
      have hp := P.smoothEmbedding.contMDiff.mdifferentiable (by simp) y
      rw [mfderiv_comp y hF.mdifferentiableAt hb,
        mfderiv_comp y (mdifferentiableAt_of_mem_maximalAtlas hc1 hcy) hp] at hh
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun T => T v) hh
      rw [mfderiv_eq_fderiv] at hv
      exact hv
    refine ⟨hJ, hC, hF, hchain, ?_, ?_⟩
    · ext a
      constructor
      · rintro ⟨v, rfl⟩
        obtain ⟨v', hv'⟩ := hJ.surjective v
        refine ⟨dP v', ⟨v', rfl⟩, ?_⟩
        have ht := congrArg (fun T : TangentSpace (𝓡∂ 2) y →L[ℝ] E3 => T v') hchain
        change (fderiv ℝ F z) (J v') = C (dP v') at ht
        rw [hv'] at ht
        exact ht.symm
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        refine ⟨J v, ?_⟩
        exact congrArg (fun T : TangentSpace (𝓡∂ 2) y →L[ℝ] E3 => T v) hchain
    · intro v w hvw
      obtain ⟨v', rfl⟩ := hJ.surjective v
      obtain ⟨w', rfl⟩ := hJ.surjective w
      have hvw' : C (dP v') = C (dP w') := by
        simpa only [← ContinuousLinearMap.comp_apply, hchain] using hvw
      have he : v' = w' := (P.smoothEmbedding.isImmersion.isImmersionAt y).mfderiv_injective (by simp) (hC.injective hvw')
      exact congrArg J he
  
  /- The exact compiler-tested ProjectionDerivativeRequest expression, with
  the original supplied sheets and the two original immersion witnesses. -/
  have full_extension_derivative_transport_second
      (P : EmbeddedSheet.{u,v} N) (y0 : P.carrier)
      (H : Manifold.IsImmersionAtOfComplement (H₂.complement) (𝓡∂ 2) 𝓘(ℝ, E3) ∞ P.inclusion y0)
      (c : OpenPartialHomeomorph N E3)
      (hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E3) ∞ N)
      (y : P.carrier) (hy : y ∈ H.domChart.source)
      (hcy : P.inclusion y ∈ c.source) :
      let b := H.domChart.extend (𝓡∂ 2)
      let B := H.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 (H₂.complement))
      let F := c ∘ H.codChart.symm ∘ B
      let z := b y
      let dP := mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion y
      let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
      let C := (tangentSpaceCastModel 𝓘(ℝ, E3) (c (P.inclusion y))).toContinuousLinearMap.comp
        (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c (P.inclusion y))
      J.IsInvertible ∧ C.IsInvertible ∧
        DifferentiableAt ℝ F z ∧
        (fderiv ℝ F z).comp J = C.comp dP ∧
        LinearMap.range (fderiv ℝ F z).toLinearMap =
          (LinearMap.range dP.toLinearMap).map C.toLinearMap ∧
        Function.Injective (fderiv ℝ F z) := by
    classical
    let b := H.domChart.extend (𝓡∂ 2)
    let B := H.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 (H₂.complement))
    let F := c ∘ H.codChart.symm ∘ B
    let z := b y
    let dP := mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion y
    let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
      (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
    let C := (tangentSpaceCastModel 𝓘(ℝ, E3) (c (P.inclusion y))).toContinuousLinearMap.comp
      (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c (P.inclusion y))
    change J.IsInvertible ∧ C.IsInvertible ∧ DifferentiableAt ℝ F z ∧
      (fderiv ℝ F z).comp J = C.comp dP ∧
      LinearMap.range (fderiv ℝ F z).toLinearMap =
        (LinearMap.range dP.toLinearMap).map C.toLinearMap ∧
      Function.Injective (fderiv ℝ F z)
    have hdom := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
      H.domChart_mem_maximalAtlas
    have hcod := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
      H.codChart_mem_maximalAtlas
    have hc1 := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp) hc
    have hJ : J.IsInvertible :=
      ContinuousLinearMap.isInvertible_equiv.comp (isInvertible_mfderiv_extend hdom hy)
    have hC : C.IsInvertible := by
      apply ContinuousLinearMap.isInvertible_equiv.comp
      let hm : c.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) := ⟨
        fun a ha => (mdifferentiableAt_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt,
        fun a ha => (mdifferentiableAt_symm_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt⟩
      exact ⟨hm.mfderiv hcy, rfl⟩
    have hyb : y ∈ b.source := by simpa only [b, OpenPartialHomeomorph.extend_source] using hy
    have hz : z ∈ b.target := b.map_source hyb
    have hBz : B z = H.codChart (P.inclusion y) := by
      have ht := H.writtenInCharts hz
      change H.codChart (P.inclusion (b.symm (b y))) = B z at ht
      rw [b.left_inv hyb] at ht
      exact ht.symm
    have hpy : P.inclusion y ∈ H.codChart.source := H.source_subset_preimage_source hy
    have hBtarget : B z ∈ H.codChart.target := by rw [hBz]; exact H.codChart.map_source hpy
    have hinv : H.codChart.symm (B z) = P.inclusion y := by rw [hBz, H.codChart.left_inv hpy]
    have hF : DifferentiableAt ℝ F z := by
      apply mdifferentiableAt_iff_differentiableAt.mp
      apply (mdifferentiableAt_of_mem_maximalAtlas hc1 (by simpa [hinv] using hcy)).comp
      exact (mdifferentiableAt_symm_of_mem_maximalAtlas hcod hBtarget).comp z B.mdifferentiableAt
    have heq : F ∘ b =ᶠ[𝓝 y] c ∘ P.inclusion := by
      filter_upwards [H.domChart.open_source.mem_nhds hy] with a ha
      have hab : a ∈ b.source := by simpa only [b, OpenPartialHomeomorph.extend_source] using ha
      have ht := H.writtenInCharts (b.map_source hab)
      change H.codChart (P.inclusion (b.symm (b a))) = B (b a) at ht
      rw [b.left_inv hab] at ht
      change c (H.codChart.symm (B (b a))) = c (P.inclusion a)
      rw [← ht, H.codChart.left_inv (H.source_subset_preimage_source ha)]
    have hchain : (fderiv ℝ F z).comp J = C.comp dP := by
      have hh := heq.mfderiv_eq (I := 𝓡∂ 2) (I' := 𝓘(ℝ, E3))
      have hb := H.domChart.mdifferentiableAt_extend hdom hy
      have hp := P.smoothEmbedding.contMDiff.mdifferentiable (by simp) y
      rw [mfderiv_comp y hF.mdifferentiableAt hb,
        mfderiv_comp y (mdifferentiableAt_of_mem_maximalAtlas hc1 hcy) hp] at hh
      apply ContinuousLinearMap.ext
      intro v
      have hv := congrArg (fun T => T v) hh
      rw [mfderiv_eq_fderiv] at hv
      exact hv
    refine ⟨hJ, hC, hF, hchain, ?_, ?_⟩
    · ext a
      constructor
      · rintro ⟨v, rfl⟩
        obtain ⟨v', hv'⟩ := hJ.surjective v
        refine ⟨dP v', ⟨v', rfl⟩, ?_⟩
        have ht := congrArg (fun T : TangentSpace (𝓡∂ 2) y →L[ℝ] E3 => T v') hchain
        change (fderiv ℝ F z) (J v') = C (dP v') at ht
        rw [hv'] at ht
        exact ht.symm
      · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
        refine ⟨J v, ?_⟩
        exact congrArg (fun T : TangentSpace (𝓡∂ 2) y →L[ℝ] E3 => T v) hchain
    · intro v w hvw
      obtain ⟨v', rfl⟩ := hJ.surjective v
      obtain ⟨w', rfl⟩ := hJ.surjective w
      have hvw' : C (dP v') = C (dP w') := by
        simpa only [← ContinuousLinearMap.comp_apply, hchain] using hvw
      have he : v' = w' := (P.smoothEmbedding.isImmersion.isImmersionAt y).mfderiv_injective (by simp) (hC.injective hvw')
      exact congrArg J he
  
  /- The exact compiler-tested ProjectionDerivativeRequest expression, with
  the original supplied sheets and the two original immersion witnesses. -/
  have liftOne_continuous : Continuous D.liftOne := by
    apply D.sheetOne.smoothEmbedding.isEmbedding.continuous_iff.mpr
    have heq : D.sheetOne.inclusion ∘ D.liftOne = fun t : ArcTime => D.edge t :=
      funext D.liftOne_exact
    rw [heq]
    exact D.edge_embedding.continuous
  have liftTwo_continuous : Continuous D.liftTwo := by
    apply D.sheetTwo.smoothEmbedding.isEmbedding.continuous_iff.mpr
    have heq : D.sheetTwo.inclusion ∘ D.liftTwo = fun t : ArcTime => D.edge t :=
      funext D.liftTwo_exact
    rw [heq]
    exact D.edge_embedding.continuous
  have liftOne_smooth :
      ContMDiff 𝓘(ℝ) (𝓡∂ 2) ∞
        (fun t : (⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) => D.liftOne t) := by
    apply (ContMDiff.iff_comp_isImmersion D.sheetOne.smoothEmbedding.isImmersion).mpr
    refine ⟨liftOne_continuous, ?_⟩
    have heq : D.sheetOne.inclusion ∘ D.liftOne = fun t : ArcTime => D.edge t :=
      funext D.liftOne_exact
    rw [heq]
    intro t
    exact contMDiffAt_subtype_iff.mpr
      ((D.edge_smooth t t.property).contMDiffAt (isOpen_Ioo.mem_nhds t.property))
  have liftTwo_smooth :
      ContMDiff 𝓘(ℝ) (𝓡∂ 2) ∞
        (fun t : (⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) => D.liftTwo t) := by
    apply (ContMDiff.iff_comp_isImmersion D.sheetTwo.smoothEmbedding.isImmersion).mpr
    refine ⟨liftTwo_continuous, ?_⟩
    have heq : D.sheetTwo.inclusion ∘ D.liftTwo = fun t : ArcTime => D.edge t :=
      funext D.liftTwo_exact
    rw [heq]
    intro t
    exact contMDiffAt_subtype_iff.mpr
      ((D.edge_smooth t t.property).contMDiffAt (isOpen_Ioo.mem_nhds t.property))
  have conormalOne_ne_zero (t : ArcTime) :
      edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t ≠ 0 := by
    intro hz
    have hu := D.conormalOne_unit t
    rw [hz, map_zero] at hu
    simp at hu
  have conormal_spans_equal (t : ArcTime) :
      Submodule.span ℝ ({arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t} :
        Set (TangentSpace 𝓘(ℝ, E3) (D.edge t))) =
      Submodule.span ℝ ({arcVelocity D.edge t,
        edgeConormal D.sheetTwo D.edge D.liftTwo D.liftTwo_exact D.outwardTwo t} :
        Set (TangentSpace 𝓘(ℝ, E3) (D.edge t))) := by
    letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E3) (D.edge t)) :=
      inferInstanceAs (NormedAddCommGroup E3)
    letI : InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, E3) (D.edge t)) :=
      inferInstanceAs (InnerProductSpace ℝ E3)
    exact SeifertSurfaces.AppendixA.tangent_spans_eq_of_oppositeConormals
      (arcVelocity D.edge t)
      (edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t)
      (edgeConormal D.sheetTwo D.edge D.liftTwo D.liftTwo_exact D.outwardTwo t)
      (D.opposite_outward_conormals t)
  have tangent_conormal_independent (t : ArcTime) :
      LinearIndependent ℝ (![arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t] :
        Fin 2 → TangentSpace 𝓘(ℝ, E3) (D.edge t)) := by
    apply linearIndependent_fin2.mpr
    refine ⟨conormalOne_ne_zero t, ?_⟩
    intro a heq
    have ho := D.conormalOne_orthogonal t
    change a • edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t =
      arcVelocity D.edge t at heq
    rw [← heq, map_smul, D.conormalOne_unit t, smul_eq_mul, mul_one] at ho
    subst a
    exact D.edge_regular t (by simpa using heq.symm)
  have edge_velocity_mem_sheet_range
      (P : EmbeddedSheet.{u,v} N) (lift : ArcTime → P.carrier)
      (heq : ∀ t : ArcTime, P.inclusion (lift t) = D.edge t)
      (hsmooth : ContMDiff 𝓘(ℝ) (𝓡∂ 2) ∞
        (fun t : (⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) => lift t))
      (t : ArcTime) :
      arcVelocity D.edge t ∈ LinearMap.range
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion (lift t)).toLinearMap := by
    let U : TopologicalSpace.Opens ℝ := ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩
    let l : U → P.carrier := lift
    let e : U → N := fun t => D.edge t
    let j : U → ℝ := Subtype.val
    have hj : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ) j t :=
      (contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiableAt (by simp)
    have hinj := ((Manifold.IsImmersion.of_opens (I := 𝓘(ℝ)) (n := ∞) U).isImmersionAt t).mfderiv_injective (by simp)
    have hsurj : Function.Surjective (mfderiv 𝓘(ℝ) 𝓘(ℝ) j t) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp hinj
    obtain ⟨w, hw⟩ := hsurj ((NormedSpace.fromTangentSpace (t : ℝ)).symm 1)
    have he : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E3) D.edge (t : ℝ) :=
      ((D.edge_smooth t t.property).contMDiffAt
        (isOpen_Ioo.mem_nhds t.property)).mdifferentiableAt (by simp)
    have hechain := mfderiv_comp_apply (show U from t) he hj w
    have hl : MDifferentiableAt 𝓘(ℝ) (𝓡∂ 2) l t :=
      (hsmooth t).mdifferentiableAt (by simp)
    have hp : MDifferentiableAt (𝓡∂ 2) 𝓘(ℝ, E3) P.inclusion (l t) :=
      (P.smoothEmbedding.contMDiff (l t)).mdifferentiableAt (by simp)
    have hlchain := mfderiv_comp_apply (show U from t) hp hl w
    have hid : P.inclusion ∘ l = D.edge ∘ j := funext heq
    rw [hid] at hlchain
    have hc : mfderiv 𝓘(ℝ) 𝓘(ℝ, E3) (D.edge ∘ j) (show U from t) w =
        arcVelocity D.edge t := by
      exact (mfderiv_comp_apply (I := 𝓘(ℝ)) (I' := 𝓘(ℝ)) (I'' := 𝓘(ℝ, E3))
        (f := j) (g := D.edge) (show U from t) he hj w).trans
        (congrArg (mfderiv 𝓘(ℝ) 𝓘(ℝ, E3) D.edge (t : ℝ)) hw)
    refine ⟨mfderiv 𝓘(ℝ) (𝓡∂ 2) l t w, ?_⟩
    exact hlchain.symm.trans hc
  have tangent_conormal_span_finrank (t : ArcTime) :
      Module.finrank ℝ (Submodule.span ℝ ({arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t} :
        Set (TangentSpace 𝓘(ℝ, E3) (D.edge t)))) = 2 := by
    have hrange : Set.range (![arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t] :
        Fin 2 → TangentSpace 𝓘(ℝ, E3) (D.edge t)) =
        {arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t} := by
      ext x
      simp [or_comm]
    rw [← hrange]
    exact finrank_span_eq_card (tangent_conormal_independent t)
  have sheetOne_tangent_eq_span (t : ArcTime) :
      LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion (D.liftOne t)).toLinearMap =
      Submodule.span ℝ ({arcVelocity D.edge t,
        edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne t} :
        Set (TangentSpace 𝓘(ℝ, E3) (D.edge t))) := by
    letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) (D.sheetOne.inclusion (D.liftOne t))) := by
      change FiniteDimensional ℝ E3
      infer_instance
    letI : FiniteDimensional ℝ
        (LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion (D.liftOne t)).toLinearMap) :=
      FiniteDimensional.finiteDimensional_submodule _
    symm
    apply Submodule.eq_of_le_of_finrank_eq
      (S₂ := LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion (D.liftOne t)).toLinearMap)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact edge_velocity_mem_sheet_range D.sheetOne D.liftOne D.liftOne_exact
          (liftOne_smooth) t
      · have hx' := Set.mem_singleton_iff.mp hx
        rw [hx']
        exact ⟨D.outwardOne t, by simp [edgeConormal, TangentSpace]; rfl⟩
    · erw [tangent_conormal_span_finrank t]
      rw [LinearMap.finrank_range_of_inj
        ((D.sheetOne.smoothEmbedding.isImmersion.isImmersionAt (D.liftOne t)).mfderiv_injective (by simp))]
      change 2 = Module.finrank ℝ E2
      simp [E2]
  have sheetTwo_tangent_eq_span (t : ArcTime) :
      LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion (D.liftTwo t)).toLinearMap =
      Submodule.span ℝ ({arcVelocity D.edge t,
        edgeConormal D.sheetTwo D.edge D.liftTwo D.liftTwo_exact D.outwardTwo t} :
        Set (TangentSpace 𝓘(ℝ, E3) (D.edge t))) := by
    letI : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, E3) (D.sheetTwo.inclusion (D.liftTwo t))) := by
      change FiniteDimensional ℝ E3
      infer_instance
    letI : FiniteDimensional ℝ
        (LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion (D.liftTwo t)).toLinearMap) :=
      FiniteDimensional.finiteDimensional_submodule _
    symm
    apply Submodule.eq_of_le_of_finrank_eq
      (S₂ := LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion (D.liftTwo t)).toLinearMap)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases hx with hx | hx
      · rw [hx]
        exact edge_velocity_mem_sheet_range D.sheetTwo D.liftTwo D.liftTwo_exact
          (liftTwo_smooth) t
      · have hx' := Set.mem_singleton_iff.mp hx
        rw [hx']
        exact ⟨D.outwardTwo t, by simp [edgeConormal, TangentSpace]; rfl⟩
    · erw [← conormal_spans_equal t, tangent_conormal_span_finrank t]
      rw [LinearMap.finrank_range_of_inj
        ((D.sheetTwo.smoothEmbedding.isImmersion.isImmersionAt (D.liftTwo t)).mfderiv_injective (by simp))]
      change 2 = Module.finrank ℝ E2
      simp [E2]
  have actual_tangent_planes_equal (t : ArcTime) :
      LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion (D.liftOne t)).toLinearMap =
      LinearMap.range (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion (D.liftTwo t)).toLinearMap := by
    exact (sheetOne_tangent_eq_span t).trans
      ((conormal_spans_equal t).trans (sheetTwo_tangent_eq_span t).symm)
  have actual_projection_derivative_isInvertible :
      (fderiv ℝ (π ∘ F₂) z₂).IsInvertible := by
    let t := D.pointParameter
    let y₁ := D.liftOne t
    let y₂ := D.liftTwo t
    let c := H.codChart
    let B := H.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 ℝ)
    let π := (ContinuousLinearMap.fst ℝ E2 ℝ).comp H.equiv.symm.toContinuousLinearMap
    let A₂ := H₂.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E2 H₂.complement)
    let F := c ∘ H₂.codChart.symm ∘ A₂
    let z₂ := (H₂.domChart.extend (𝓡∂ 2)) y₂
    have hy₁ : y₁ ∈ H.domChart.source := H.mem_domChart_source
    have hy₂ : y₂ ∈ H₂.domChart.source := H₂.mem_domChart_source
    have hp : D.sheetTwo.inclusion y₂ = D.sheetOne.inclusion y₁ :=
      (D.liftTwo_exact t).trans (D.liftOne_exact t).symm
    have hcy₁ : D.sheetOne.inclusion y₁ ∈ c.source := H.mem_codChart_source
    have hcy₂ : D.sheetTwo.inclusion y₂ ∈ c.source := by rw [hp]; exact hcy₁
    have T₁ := full_extension_derivative_transport_real D.sheetOne y₁ H c
      H.codChart_mem_maximalAtlas y₁ hy₁ hcy₁
    have T₂ := full_extension_derivative_transport_second D.sheetTwo y₂ H₂.isImmersionAtOfComplement_complement c
      H.codChart_mem_maximalAtlas y₂ hy₂ hcy₂
    let z₁ := (H.domChart.extend (𝓡∂ 2)) y₁
    have hz₁ : B z₁ ∈ c.target := by
      have hh := H.writtenInCharts ((H.domChart.extend (𝓡∂ 2)).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy₁))
      change c (D.sheetOne.inclusion ((H.domChart.extend (𝓡∂ 2)).symm
        ((H.domChart.extend (𝓡∂ 2)) y₁))) = B z₁ at hh
      rw [(H.domChart.extend (𝓡∂ 2)).left_inv
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy₁)] at hh
      rw [← hh]
      exact c.map_source hcy₁
    have hFeq : (c ∘ c.symm ∘ B) =ᶠ[𝓝 z₁] B := by
      filter_upwards [B.continuous.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds hz₁)] with z hz
      exact c.right_inv hz
    have hBderiv : fderiv ℝ (c ∘ c.symm ∘ B) z₁ = B :=
      hFeq.fderiv_eq.trans B.fderiv
    have hRange : LinearMap.range (fderiv ℝ F z₂).toLinearMap = LinearMap.range B.toLinearMap := by
      have r₁ := T₁.2.2.2.2.1
      have r₂ := T₂.2.2.2.2.1
      change LinearMap.range (fderiv ℝ (c ∘ c.symm ∘ B) z₁).toLinearMap = _ at r₁
      rw [hBderiv] at r₁
      change LinearMap.range (fderiv ℝ F z₂).toLinearMap = _ at r₂
      rw [r₂, r₁]
      have ht := actual_tangent_planes_equal t
      simp only [TangentSpace] at ht ⊢
      rw [hp, ht]
      rfl
    have hπB : π.comp B = ContinuousLinearMap.id ℝ E2 := by
      apply ContinuousLinearMap.ext
      intro x
      change (H.equiv.symm (H.equiv (x, 0))).1 = x
      rw [H.equiv.symm_apply_apply]
    have hinv := projection_invertible_of_same_range B π (fderiv ℝ F z₂) hπB T₂.2.2.2.2.2 hRange
    have hd : fderiv ℝ (π ∘ F) z₂ = π.comp (fderiv ℝ F z₂) :=
      π.hasFDerivAt.comp z₂ T₂.2.2.1.hasFDerivAt |>.fderiv
    change (fderiv ℝ (π ∘ F) z₂).IsInvertible
    rw [hd]
    exact hinv
  have hinv : (fderiv ℝ (π ∘ F₂) z₂).IsInvertible := by
    exact actual_projection_derivative_isInvertible
  have hprojAt : ContDiffAt ℝ ∞ (π ∘ F₂) z₂ :=
    hprojectedSmooth.contDiffAt (hU₂.mem_nhds hzU₂)
  obtain ⟨Q, hQ⟩ := hinv
  have hderiv : HasFDerivAt (π ∘ F₂) (Q : E2 →L[ℝ] E2) z₂ := by
    rw [hQ]
    exact (hprojAt.differentiableAt (by simp)).hasFDerivAt
  let g := hprojAt.toOpenPartialHomeomorph (π ∘ F₂) hderiv (by simp)
  have hzg : z₂ ∈ g.source := hprojAt.mem_toOpenPartialHomeomorph_source hderiv (by simp)
  let p := c.chart (D.edge D.pointParameter)
  let z₀ := π p
  have hbase : g z₂ = z₀ := by
    change π (F₂ z₂) = π p
    rw [hF₂base]
  have hz₀g : z₀ ∈ g.target := hbase ▸ g.map_source hzg
  have hinverseSmooth : ContDiffAt ℝ ∞ g.symm z₀ := by
    rw [← hbase]
    exact hprojAt.to_localInverse hderiv (by simp)
  let u₂ : E2 → ℝ := fun x => (H.equiv.symm (F₂ (g.symm (z₀ + x)) - p)).2
  have hu₂zero : u₂ 0 = 0 := by
    change (H.equiv.symm (F₂ (g.symm (z₀ + 0)) - p)).2 = 0
    rw [add_zero, ← hbase, g.left_inv hzg, hF₂base, sub_self, map_zero]
    rfl
  have hu₂smooth : ContDiffAt ℝ ∞ u₂ 0 := by
    have hi0 : ContDiffAt ℝ ∞ g.symm (z₀ + 0) := by simpa only [add_zero] using hinverseSmooth
    have hi : ContDiffAt ℝ ∞ (fun x : E2 => g.symm (z₀ + x)) 0 :=
      hi0.comp 0 (contDiffAt_const.add contDiffAt_id)
    have hf : ContDiffAt ℝ ∞ F₂ (g.symm (z₀ + 0)) := by
      rw [add_zero, ← hbase, g.left_inv hzg]
      exact hF₂.contDiffAt (hU₂.mem_nhds hzU₂)
    exact ((H.equiv.symm.contDiff.contDiffAt.comp 0
      ((hf.comp 0 hi).sub contDiffAt_const)).snd)
  have hgraph₂ : ∀ x : E2, z₀ + x ∈ g.target →
      graphMap p L normal u₂ x = F₂ (g.symm (z₀ + x)) := by
    intro x hx
    have hpj : π (F₂ (g.symm (z₀ + x))) = z₀ + x := g.right_inv hx
    have hcoords : (H.equiv.symm (F₂ (g.symm (z₀ + x)) - p)).1 = x := by
      change π (F₂ (g.symm (z₀ + x)) - p) = x
      rw [map_sub, hpj]
      exact add_sub_cancel_left z₀ x
    change p + L x + u₂ x • normal = F₂ (g.symm (z₀ + x))
    have hs : L x + u₂ x • normal = F₂ (g.symm (z₀ + x)) - p := by
      calc
        L x + u₂ x • normal = H.equiv (x, u₂ x) := by
          change H.equiv (x, 0) + u₂ x • H.equiv (0, 1) = _
          rw [← map_smul, ← map_add]
          congr 1
          ext <;> simp
        _ = H.equiv (H.equiv.symm (F₂ (g.symm (z₀ + x)) - p)) := by
          congr 1
          exact Prod.ext hcoords.symm rfl
        _ = F₂ (g.symm (z₀ + x)) - p := H.equiv.apply_symm_apply _
    rw [add_assoc, hs]
    abel
  have same_local_inverse_open_control
      (Q : E2 → E2) (U : Set E2) (a : E2)
      (g : OpenPartialHomeomorph E2 E2)
      (hU : IsOpen U) (haU : a ∈ U) (hQ : ContDiffOn ℝ ∞ Q U)
      (hDQ : (fderiv ℝ Q a).IsInvertible)
      (hg : (g : E2 → E2) = Q) (hag : a ∈ g.source) :
      let z0 := Q a
      let j : E2 → E2 := fun x => g.symm (z0 + x)
      ∃ V : Set E2,
        IsOpen V ∧ (0 : E2) ∈ V ∧
        (∀ x ∈ V, z0 + x ∈ g.target ∧ j x ∈ g.source ∩ U) ∧
        ContDiffOn ℝ ∞ j V ∧
        (∀ x ∈ V, (fderiv ℝ Q (j x)).IsInvertible) ∧
        (∀ x ∈ V,
          (fderiv ℝ Q (j x)).comp (fderiv ℝ j x) = ContinuousLinearMap.id ℝ E2 ∧
          (fderiv ℝ j x).comp (fderiv ℝ Q (j x)) = ContinuousLinearMap.id ℝ E2) ∧
        j 0 = a ∧ (∀ x ∈ V, Q (j x) = z0 + x) := by
    classical
    let z0 := Q a
    let j : E2 → E2 := fun x => g.symm (z0 + x)
    let S := U ∩ {y | (fderiv ℝ Q y).IsInvertible}
    have hS : IsOpen S :=
      (hQ.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
        ContinuousLinearMap.isOpen_setOfPred_isInvertible
    have haS : a ∈ S := ⟨haU, hDQ⟩
    let T := g.target ∩ g.symm ⁻¹' S
    have hT : IsOpen T := g.symm.continuousOn.isOpen_inter_preimage g.open_target hS
    have hza : z0 = g a := by exact congrFun hg a |>.symm
    have hzT : z0 ∈ T := by
      rw [hza]
      exact ⟨g.map_source hag, by change g.symm (g a) ∈ S; rw [g.left_inv hag]; exact haS⟩
    let V := (fun x : E2 => z0 + x) ⁻¹' T
    have hV : IsOpen V := hT.preimage (continuous_const.add continuous_id)
    have hzero : (0 : E2) ∈ V := by change z0 + 0 ∈ T; simpa using hzT
    have hctrl : ∀ x ∈ V, z0 + x ∈ g.target ∧ j x ∈ g.source ∩ U := by
      intro x hx
      exact ⟨hx.1, g.symm.map_source hx.1, hx.2.1⟩
    have hInv : ∀ x ∈ V, (fderiv ℝ Q (j x)).IsInvertible := fun x hx => hx.2.2
    have hQj : ∀ x ∈ V, Q (j x) = z0 + x := by
      intro x hx
      rw [← hg]
      exact g.right_inv hx.1
    have hjsmooth : ∀ x ∈ V, ContDiffAt ℝ ∞ j x := by
      intro x hx
      obtain ⟨A, hA⟩ := hInv x hx
      have hq : ContDiffAt ℝ ∞ Q (j x) := hQ.contDiffAt (hU.mem_nhds (hctrl x hx).2.2)
      have hd : HasFDerivAt (g : E2 → E2) (A : E2 →L[ℝ] E2) (j x) := by
        rw [hg, hA]
        exact (hq.differentiableAt (by simp)).hasFDerivAt
      have hi : ContDiffAt ℝ ∞ g.symm (z0 + x) :=
        g.contDiffAt_symm hx.1 hd (by simpa only [hg] using hq)
      exact hi.comp x (contDiffAt_const.add contDiffAt_id)
    refine ⟨V, hV, hzero, hctrl, fun x hx => (hjsmooth x hx).contDiffWithinAt, hInv, ?_, ?_, hQj⟩
    · intro x hx
      have hq : DifferentiableAt ℝ Q (j x) :=
        (hQ.contDiffAt (hU.mem_nhds (hctrl x hx).2.2)).differentiableAt (by simp)
      have hj : DifferentiableAt ℝ j x := (hjsmooth x hx).differentiableAt (by simp)
      have heq : Q ∘ j =ᶠ[𝓝 x] (fun x => z0 + x) :=
        Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hQj
      have hleft : (fderiv ℝ Q (j x)).comp (fderiv ℝ j x) = ContinuousLinearMap.id ℝ E2 := by
        rw [← fderiv_comp x hq hj, heq.fderiv_eq]
        exact (hasFDerivAt_id x |>.const_add z0).fderiv
      refine ⟨hleft, ?_⟩
      apply ContinuousLinearMap.ext
      intro v
      apply (hInv x hx).injective
      have hv := congrArg (fun L : E2 →L[ℝ] E2 => L ((fderiv ℝ Q (j x)) v)) hleft
      exact hv
    · change g.symm (z0 + 0) = a
      rw [add_zero, hza, g.left_inv hag]
  have embedding_ambient_open_source_isolation
      {A : Type v} {B : Type u} [TopologicalSpace A] [TopologicalSpace B]
      (f : A → B) (hf : IsEmbedding f) (a : A)
      (O : Set A) (hO : IsOpen O) (haO : a ∈ O)
      (W : Set B) (hW : IsOpen W) (hfaW : f a ∈ W) :
      ∃ V : Set B,
        IsOpen V ∧ f a ∈ V ∧ V ⊆ W ∧ f ⁻¹' V ⊆ O ∧
        range f ∩ V = f '' (O ∩ (f ⁻¹' V)) := by
    obtain ⟨T, hT, hpre⟩ := hf.isInducing.isOpen_iff.mp hO
    refine ⟨T ∩ W, hT.inter hW, ⟨?_, hfaW⟩, inter_subset_right, ?_, ?_⟩
    · change a ∈ f ⁻¹' T
      rw [hpre]
      exact haO
    · intro x hx
      rw [← hpre]
      exact hx.1
    · ext y
      constructor
      · rintro ⟨⟨x, rfl⟩, hx⟩
        exact ⟨x, ⟨by rw [← hpre]; exact hx.1, hx⟩, rfl⟩
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩
        exact ⟨⟨x, rfl⟩, hx⟩
  have fixed_maximal_halfspace_chart_boundary_normal
      (P : EmbeddedSheet.{u,v} N)
      (e : OpenPartialHomeomorph P.carrier (EuclideanHalfSpace 2))
      (he : e ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ P.carrier)
      (y : P.carrier) (hy : y ∈ e.source)
      (hyBoundary : y ∈ (𝓡∂ 2).boundary P.carrier) :
      let b := e.extend (𝓡∂ 2)
      let z := b y
      let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) b y)
      z 0 = 0 ∧
      (∃ O : Set E2, IsOpen O ∧ z ∈ O ∧
        ∀ w ∈ O, w ∈ b.target ↔ 0 ≤ w 0) ∧
      (∃ lam : ℝ, 0 < lam ∧
        ∀ v : TangentSpace (𝓡∂ 2) y, (J v) 0 = lam * SeifertSurfaces.Foundations.inwardCoordinate y v) := by
    classical
    let I := 𝓡∂ 2
    let b := e.extend I
    let z := b y
    let J := (tangentSpaceCastModel 𝓘(ℝ, E2) z).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, E2) b y)
    change z 0 = 0 ∧ (∃ O : Set E2, IsOpen O ∧ z ∈ O ∧
      ∀ w ∈ O, w ∈ b.target ↔ 0 ≤ w 0) ∧
      (∃ lam : ℝ, 0 < lam ∧ ∀ v : TangentSpace I y, (J v) 0 = lam * SeifertSurfaces.Foundations.inwardCoordinate y v)
    let Φ : PartialDiffeomorph I I P.carrier (EuclideanHalfSpace 2) ∞ := {
      toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }
    have hed : IsLocalDiffeomorphAt I I ∞ e y := ⟨Φ, hy, fun _ _ => rfl⟩
    have hey := (hed.isBoundaryPoint_iff (by simp)).mp hyBoundary
    have hz : z 0 = 0 := by
      change extChartAt I (e y) (e y) ∈ frontier (range I) at hey
      rw [extChartAt_self_apply, frontier_range_modelWithCornersEuclideanHalfSpace] at hey
      exact hey.symm
    refine ⟨hz, ?_, ?_⟩
    · refine ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, ?_, ?_⟩
      · change I.symm (I (e y)) ∈ e.target
        rw [I.left_inv]
        exact e.map_source hy
      · intro w hw
        change w ∈ (e.extend I).target ↔ _
        rw [e.extend_target]
        rw [range_modelWithCornersEuclideanHalfSpace]
        exact and_iff_right hw
    · have he1 := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp) he
      have hd := e.mdifferentiableAt_extend he1 hy
      have hJ : J.IsInvertible :=
        ContinuousLinearMap.isInvertible_equiv.comp (isInvertible_mfderiv_extend he1 hy)
      let c0 := extChartAt I y
      let a := c0 y
      let F : E2 → E2 := b ∘ c0.symm
      let L := J.comp (tangentSpaceCastModel I y).symm.toContinuousLinearMap
      have hL : L.IsInvertible := hJ.comp ContinuousLinearMap.isInvertible_equiv
      have ha : a 0 = 0 := by
        change a ∈ frontier (range I) at hyBoundary
        rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hyBoundary
        exact hyBoundary.symm
      have hFa : F a = z := by
        change b (c0.symm (c0 y)) = b y
        rw [c0.left_inv (mem_extChartAt_source y)]
      have hF : HasFDerivWithinAt F L (range I) a := by
        have hh := hd.hasMFDerivAt.2
        simpa only [writtenInExtChartAt, extChartAt_model_space_eq_id,
          PartialEquiv.refl_coe, Function.id_comp] using! hh
      let ev : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
      have hscalar : HasFDerivWithinAt (fun x => F x 0) (ev.comp L) (range I) a :=
        ev.hasFDerivAt.comp_hasFDerivWithinAt a hF
      have hmin : IsLocalMinOn (fun x => F x 0) (range I) a := by
        filter_upwards [] with x
        rw [hFa, hz]
        exact (e (c0.symm x)).property
      have haS : a ∈ range I := by rw [range_modelWithCornersEuclideanHalfSpace]; exact le_of_eq ha.symm
      have hcone : ∀ v : E2, 0 ≤ v 0 → v ∈ posTangentConeAt (range I) a := by
        intro v hv
        apply mem_posTangentConeAt_of_segment_subset
        apply I.convex_range.segment_subset haS
        rw [range_modelWithCornersEuclideanHalfSpace]
        change 0 ≤ a 0 + v 0
        rw [ha, zero_add]
        exact hv
      have htangent : ∀ v : E2, v 0 = 0 → (L v) 0 = 0 := by
        intro v hv
        exact hmin.hasFDerivWithinAt_eq_zero hscalar
          (hcone v (le_of_eq hv.symm)) (hcone (-v) (by change 0 ≤ -(v 0); rw [hv]; simp))
      let v0 : E2 := EuclideanSpace.single 0 1
      have hv0 : v0 0 = 1 := by simp [v0]
      let lam := (L v0) 0
      have hnonneg : 0 ≤ lam := hmin.hasFDerivWithinAt_nonneg hscalar (hcone v0 (by rw [hv0]; norm_num))
      have hrow : ∀ v : E2, (L v) 0 = lam * v 0 := by
        intro v
        have ht := htangent (v - v 0 • v0) (by change v 0 - v 0 * v0 0 = 0; rw [hv0]; ring)
        change (L (v - v 0 • v0)) 0 = 0 at ht
        rw [map_sub, map_smul] at ht
        change (L v) 0 - v 0 * lam = 0 at ht
        nlinarith
      have hpos : 0 < lam := by
        apply lt_of_le_of_ne hnonneg
        intro hzero
        obtain ⟨v, hv⟩ := hL.surjective v0
        have ht := hrow v
        rw [hv, hv0, ← hzero, zero_mul] at ht
        norm_num at ht
      refine ⟨lam, hpos, ?_⟩
      intro v
      have ht := hrow ((tangentSpaceCastModel I y) v)
      simpa only [L, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, SeifertSurfaces.Foundations.inwardCoordinate, mfderiv_extChartAt_self,
        ContinuousLinearMap.id_apply, tangentSpaceCastModel] using! ht
  have hQbase : (π ∘ F₂) z₂ = z₀ := by change π (F₂ z₂) = π p; rw [hF₂base]
  have hlocal := same_local_inverse_open_control (π ∘ F₂) U₂ z₂ g hU₂ hzU₂ hprojectedSmooth
    (by rw [← hQ]; exact ContinuousLinearMap.isInvertible_equiv) rfl hzg
  dsimp only at hlocal
  rw [hQbase] at hlocal
  obtain ⟨V, hVo, hV0, hcontrol, hjSmooth, hderivativeInv, hinverseIdentities, hj0, hprojInverse⟩ := hlocal
  let j : E2 → E2 := fun x => g.symm (z₀ + x)
  have hu₂on : ContDiffOn ℝ ∞ u₂ V := by
    let ρ : E3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ E2 ℝ).comp H.equiv.symm.toContinuousLinearMap
    have hFj : ContDiffOn ℝ ∞ (F₂ ∘ j) V :=
      hF₂.comp hjSmooth (fun x hx => (hcontrol x hx).2.2)
    exact ρ.contDiff.comp_contDiffOn (hFj.sub contDiffOn_const)
  let beta : E2 → ℝ := fun x => j x 0
  have hbetaSmooth : ContDiffOn ℝ ∞ beta V := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contDiff.comp_contDiffOn hjSmooth
  have hboundary₁ := fixed_maximal_halfspace_chart_boundary_normal D.sheetOne H.domChart
    H.domChart_mem_maximalAtlas x₁ H.mem_domChart_source (D.liftOne_boundary D.pointParameter)
  have hboundary₂ := fixed_maximal_halfspace_chart_boundary_normal D.sheetTwo H₂.domChart
    H₂.domChart_mem_maximalAtlas x₂ H₂.mem_domChart_source (D.liftTwo_boundary D.pointParameter)
  obtain ⟨hz₁zero, ⟨O₁, hO₁, hz₁O, htarget₁⟩, lam₁, hlam₁, hnormal₁⟩ := hboundary₁
  obtain ⟨hz₂zero, ⟨O₂, hO₂, hz₂O, htarget₂⟩, lam₂, hlam₂, hnormal₂⟩ := hboundary₂
  have hpL : p = L ((H.domChart.extend (𝓡∂ 2)) x₁) := by
    have ht := H.writtenInCharts ((H.domChart.extend (𝓡∂ 2)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using H.mem_domChart_source))
    change c.chart (D.sheetOne.inclusion ((H.domChart.extend (𝓡∂ 2)).symm
      ((H.domChart.extend (𝓡∂ 2)) x₁))) = L ((H.domChart.extend (𝓡∂ 2)) x₁) at ht
    rw [(H.domChart.extend (𝓡∂ 2)).left_inv
      (by simpa only [OpenPartialHomeomorph.extend_source] using H.mem_domChart_source)] at ht
    simpa only [x₁, D.liftOne_exact] using ht
  have hz₀ : z₀ = (H.domChart.extend (𝓡∂ 2)) x₁ := by
    change π p = _
    rw [hpL, hπL]
  have hz₀zero : z₀ 0 = 0 := hz₀ ▸ hz₁zero
  have hbeta0 : beta 0 = 0 := by
    change (g.symm (z₀ + 0)) 0 = 0
    rw [hj0]
    exact hz₂zero
  let source₂ := H₂.domChart.source ∩ (H₂.domChart.extend (𝓡∂ 2)) ⁻¹' (g.source ∩ U₂)
  have hsource₂ : IsOpen source₂ := by
    have hc₂ : ContinuousOn (H₂.domChart.extend (𝓡∂ 2)) H₂.domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using H₂.domChart.continuousOn_extend (I := 𝓡∂ 2)
    exact hc₂.isOpen_inter_preimage H₂.domChart.open_source (g.open_source.inter hU₂)
  have hxsource₂ : x₂ ∈ source₂ := ⟨H₂.mem_domChart_source, hzg, hzU₂⟩
  obtain ⟨W, hWo, hqW, hdisjoint⟩ := D.otherwise_locally_disjoint
  let ambientW := W ∩ c.chart.source
  have hambientW : IsOpen ambientW := hWo.inter c.chart.open_source
  have hqambientW : D.edge D.pointParameter ∈ ambientW := ⟨hqW, hq⟩
  obtain ⟨A₁, hA₁, hqA₁, hA₁W, hpre₁, himage₁⟩ := embedding_ambient_open_source_isolation
    D.sheetOne.inclusion D.sheetOne.smoothEmbedding.isEmbedding x₁ H.domChart.source
    H.domChart.open_source H.mem_domChart_source ambientW hambientW
    (by simpa only [x₁, D.liftOne_exact] using hqambientW)
  obtain ⟨A₂, hA₂, hqA₂, hA₂W, hpre₂, himage₂⟩ := embedding_ambient_open_source_isolation
    D.sheetTwo.inclusion D.sheetTwo.smoothEmbedding.isEmbedding x₂ source₂ hsource₂ hxsource₂
    ambientW hambientW (by simpa only [x₂, D.liftTwo_exact] using hqambientW)
  let A0 := A₁ ∩ A₂
  have hA0 : IsOpen A0 := hA₁.inter hA₂
  have hqA0 : D.edge D.pointParameter ∈ A0 := by
    constructor
    · simpa only [x₁, D.liftOne_exact] using hqA₁
    · simpa only [x₂, D.liftTwo_exact] using hqA₂
  have hA0c : A0 ⊆ c.chart.source := fun Y hY => (hA₁W hY.1).2
  have hfullSource₁ : ∀ y : D.sheetOne.carrier, D.sheetOne.inclusion y ∈ A0 → y ∈ H.domChart.source :=
    fun y hy => hpre₁ hy.1
  have hfullSource₂ : ∀ y : D.sheetTwo.carrier, D.sheetTwo.inclusion y ∈ A0 →
      y ∈ H₂.domChart.source ∧ (H₂.domChart.extend (𝓡∂ 2)) y ∈ g.source ∩ U₂ :=
    fun y hy => hpre₂ hy.2
  let Pproj : N → E2 := fun Y => π (c.chart Y - p)
  have hprojShift : ∀ Y : N, z₀ + Pproj Y = π (c.chart Y) := by
    intro Y
    change π p + π (c.chart Y - p) = π (c.chart Y)
    rw [map_sub]
    abel
  have hpLz : p = L z₀ := by rw [hz₀]; exact hpL
  have hfirstChart : ∀ y ∈ H.domChart.source,
      c.chart (D.sheetOne.inclusion y) = L ((H.domChart.extend (𝓡∂ 2)) y) := by
    intro y hy
    have ht := H.writtenInCharts ((H.domChart.extend (𝓡∂ 2)).map_source
      (by simpa only [OpenPartialHomeomorph.extend_source] using hy))
    change c.chart (D.sheetOne.inclusion ((H.domChart.extend (𝓡∂ 2)).symm
      ((H.domChart.extend (𝓡∂ 2)) y))) = _ at ht
    rw [(H.domChart.extend (𝓡∂ 2)).left_inv
      (by simpa only [OpenPartialHomeomorph.extend_source] using hy)] at ht
    exact ht
  have hfirstImage : ∀ Y ∈ A0, Y ∈ D.sheetOne.image ↔
      z₀ + Pproj Y ∈ (H.domChart.extend (𝓡∂ 2)).target ∧
      c.chart Y = p + L (Pproj Y) := by
    intro Y hYA
    constructor
    · rintro ⟨y, rfl⟩
      have hy := hfullSource₁ y hYA
      have hcoord : z₀ + Pproj (D.sheetOne.inclusion y) = (H.domChart.extend (𝓡∂ 2)) y := by
        rw [hprojShift, hfirstChart y hy, hπL]
      refine ⟨hcoord ▸ (H.domChart.extend (𝓡∂ 2)).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy), ?_⟩
      rw [hfirstChart y hy, ← hcoord, map_add, ← hpLz]
    · rintro ⟨htarget, hcoord⟩
      let y := (H.domChart.extend (𝓡∂ 2)).symm (z₀ + Pproj Y)
      have hy : y ∈ H.domChart.source := by
        simpa only [OpenPartialHomeomorph.extend_source] using
          (H.domChart.extend (𝓡∂ 2)).map_target htarget
      refine ⟨y, ?_⟩
      apply c.chart.injOn (H.source_subset_preimage_source hy) (hA0c hYA)
      rw [hfirstChart y hy]
      change L ((H.domChart.extend (𝓡∂ 2)) ((H.domChart.extend (𝓡∂ 2)).symm (z₀ + Pproj Y))) = _
      rw [(H.domChart.extend (𝓡∂ 2)).right_inv htarget, map_add, ← hpLz, hcoord]
  have hsecondInverse : ∀ y : D.sheetTwo.carrier, D.sheetTwo.inclusion y ∈ A0 →
      j (Pproj (D.sheetTwo.inclusion y)) = (H₂.domChart.extend (𝓡∂ 2)) y := by
    intro y hyA
    have hy := hfullSource₂ y hyA
    change g.symm (z₀ + Pproj (D.sheetTwo.inclusion y)) = _
    rw [hprojShift, ← hF₂exact y hy.1]
    exact g.left_inv hy.2.1
  have hsecondForward : ∀ Y ∈ A0, Y ∈ D.sheetTwo.image →
      j (Pproj Y) ∈ (H₂.domChart.extend (𝓡∂ 2)).target ∧
      c.chart Y = graphMap p L normal u₂ (Pproj Y) := by
    intro Y hYA hY
    obtain ⟨y, rfl⟩ := hY
    have hy := hfullSource₂ y hYA
    have hji := hsecondInverse y hYA
    refine ⟨?_, ?_⟩
    · rw [hji]
      exact (H₂.domChart.extend (𝓡∂ 2)).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy.1)
    · have ht : z₀ + Pproj (D.sheetTwo.inclusion y) ∈ g.target := by
        rw [hprojShift, ← hF₂exact y hy.1]
        exact g.map_source hy.2.1
      rw [hgraph₂ _ ht]
      change _ = F₂ (j (Pproj (D.sheetTwo.inclusion y)))
      rw [hji, hF₂exact y hy.1]
  have hsecondImage : ∀ Y ∈ A0, Pproj Y ∈ V → (Y ∈ D.sheetTwo.image ↔
      j (Pproj Y) ∈ (H₂.domChart.extend (𝓡∂ 2)).target ∧
      c.chart Y = graphMap p L normal u₂ (Pproj Y)) := by
    intro Y hYA hYV
    refine ⟨hsecondForward Y hYA, ?_⟩
    rintro ⟨htarget, hcoord⟩
    let y := (H₂.domChart.extend (𝓡∂ 2)).symm (j (Pproj Y))
    have hy : y ∈ H₂.domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (H₂.domChart.extend (𝓡∂ 2)).map_target htarget
    have hb : (H₂.domChart.extend (𝓡∂ 2)) y = j (Pproj Y) :=
      (H₂.domChart.extend (𝓡∂ 2)).right_inv htarget
    have hB : B₂ (j (Pproj Y)) = c₂.chart (D.sheetTwo.inclusion y) := by
      have ht := H₂.writtenInCharts ((H₂.domChart.extend (𝓡∂ 2)).map_source
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy))
      change c₂.chart (D.sheetTwo.inclusion ((H₂.domChart.extend (𝓡∂ 2)).symm
        ((H₂.domChart.extend (𝓡∂ 2)) y))) = B₂ ((H₂.domChart.extend (𝓡∂ 2)) y) at ht
      rw [(H₂.domChart.extend (𝓡∂ 2)).left_inv
        (by simpa only [OpenPartialHomeomorph.extend_source] using hy), hb] at ht
      exact ht.symm
    have hin : D.sheetTwo.inclusion y ∈ c.chart.source := by
      have ht := (hcontrol (Pproj Y) hYV).2.2
      change B₂ (j (Pproj Y)) ∈ c₂.chart.target ∧
        c₂.chart.symm (B₂ (j (Pproj Y))) ∈ c.chart.source at ht
      rw [hB, c₂.chart.left_inv (H₂.source_subset_preimage_source hy)] at ht
      exact ht.2
    refine ⟨y, c.chart.injOn hin (hA0c hYA) ?_⟩
    rw [hcoord, hgraph₂ _ (hcontrol _ hYV).1]
    change c.chart (D.sheetTwo.inclusion y) = F₂ (j (Pproj Y))
    rw [← hb, hF₂exact y hy]
  have hPcont : ContinuousOn Pproj c.chart.source :=
    π.continuous.comp_continuousOn (c.chart.continuousOn.sub continuousOn_const)
  let Acontrol := A0 ∩ (c.chart.source ∩ Pproj ⁻¹' V)
  have hAcontrol : IsOpen Acontrol := hA0.inter
    (hPcont.isOpen_inter_preimage c.chart.open_source hVo)
  have hPq : Pproj (D.edge D.pointParameter) = 0 := by
    change π (p - p) = 0
    rw [sub_self, map_zero]
  have hqAcontrol : D.edge D.pointParameter ∈ Acontrol := ⟨hqA0, hq, by change Pproj (D.edge D.pointParameter) ∈ V; rw [hPq]; exact hV0⟩
  have hfirstControlled : ∀ Y ∈ Acontrol, Y ∈ D.sheetOne.image ↔
      z₀ + Pproj Y ∈ (H.domChart.extend (𝓡∂ 2)).target ∧ c.chart Y = p + L (Pproj Y) :=
    fun Y hY => hfirstImage Y hY.1
  have hsecondControlled : ∀ Y ∈ Acontrol, Y ∈ D.sheetTwo.image ↔
      j (Pproj Y) ∈ (H₂.domChart.extend (𝓡∂ 2)).target ∧
        c.chart Y = graphMap p L normal u₂ (Pproj Y) :=
    fun Y hY => hsecondImage Y hY.1 hY.2.2
  have hfirstGraph0 : p + L (0 : E2) ∈ c.chart.target := by
    simpa only [map_zero, add_zero] using c.chart.map_source hq
  let Vplan := (V ∩ (j ⁻¹' O₂)) ∩ ((fun x : E2 => z₀ + x) ⁻¹' O₁) ∩
    ((fun x : E2 => p + L x) ⁻¹' c.chart.target)
  have hVplan : IsOpen Vplan := by
    exact ((hjSmooth.continuousOn.isOpen_inter_preimage hVo hO₂).inter
      (hO₁.preimage (continuous_const.add continuous_id))).inter
      (c.chart.open_target.preimage (continuous_const.add L.continuous))
  have hVplan0 : (0 : E2) ∈ Vplan := by
    refine ⟨⟨⟨hV0, ?_⟩, ?_⟩, hfirstGraph0⟩
    · change j 0 ∈ O₂
      rw [show j 0 = z₂ from hj0]
      exact hz₂O
    · change z₀ + 0 ∈ O₁
      simpa only [add_zero, hz₀] using hz₁O
  have hVplanV : Vplan ⊆ V := fun _ hx => hx.1.1.1
  have hfirstTarget : ∀ x ∈ Vplan,
      z₀ + x ∈ (H.domChart.extend (𝓡∂ 2)).target ↔ 0 ≤ x 0 := by
    intro x hx
    rw [htarget₁ (z₀ + x) hx.1.2]
    change 0 ≤ z₀ 0 + x 0 ↔ 0 ≤ x 0
    rw [hz₀zero, zero_add]
  have hsecondTarget : ∀ x ∈ Vplan,
      j x ∈ (H₂.domChart.extend (𝓡∂ 2)).target ↔ 0 ≤ beta x :=
    fun x hx => htarget₂ (j x) hx.1.1.2
  have hsecondGraphTarget : ∀ x ∈ Vplan,
      graphMap p L normal u₂ x ∈ c.chart.target := by
    intro x hx
    rw [hgraph₂ _ (hcontrol _ (hVplanV hx)).1]
    exact c.chart.map_source (hcontrol _ (hVplanV hx)).2.2.2
  have hfirstCandidate : ∀ x ∈ Vplan, 0 ≤ x 0 →
      ∃ y : D.sheetOne.carrier, y ∈ H.domChart.source ∧
        (H.domChart.extend (𝓡∂ 2)) y = z₀ + x ∧
        D.sheetOne.inclusion y = c.chart.symm (p + L x) := by
    intro x hx hsign
    have ht := (hfirstTarget x hx).mpr hsign
    let y := (H.domChart.extend (𝓡∂ 2)).symm (z₀ + x)
    have hy : y ∈ H.domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (H.domChart.extend (𝓡∂ 2)).map_target ht
    have hb : (H.domChart.extend (𝓡∂ 2)) y = z₀ + x :=
      (H.domChart.extend (𝓡∂ 2)).right_inv ht
    refine ⟨y, hy, hb, ?_⟩
    have he : c.chart (D.sheetOne.inclusion y) = p + L x := by
      rw [hfirstChart y hy, hb, map_add, ← hpLz]
    rw [← he, c.chart.left_inv (H.source_subset_preimage_source hy)]
  have hsecondCandidate : ∀ x ∈ Vplan, 0 ≤ beta x →
      ∃ y : D.sheetTwo.carrier, y ∈ H₂.domChart.source ∧
        (H₂.domChart.extend (𝓡∂ 2)) y = j x ∧
        D.sheetTwo.inclusion y = c.chart.symm (graphMap p L normal u₂ x) := by
    intro x hx hsign
    have ht := (hsecondTarget x hx).mpr hsign
    let y := (H₂.domChart.extend (𝓡∂ 2)).symm (j x)
    have hy : y ∈ H₂.domChart.source := by
      simpa only [OpenPartialHomeomorph.extend_source] using
        (H₂.domChart.extend (𝓡∂ 2)).map_target ht
    have hb : (H₂.domChart.extend (𝓡∂ 2)) y = j x :=
      (H₂.domChart.extend (𝓡∂ 2)).right_inv ht
    have hB : B₂ (j x) = c₂.chart (D.sheetTwo.inclusion y) := by
      have hh := H₂.writtenInCharts ht
      change c₂.chart (D.sheetTwo.inclusion y) = B₂ (j x) at hh
      exact hh.symm
    have hin : D.sheetTwo.inclusion y ∈ c.chart.source := by
      have hh := (hcontrol x (hVplanV hx)).2.2.2
      change c₂.chart.symm (B₂ (j x)) ∈ c.chart.source at hh
      rwa [hB, c₂.chart.left_inv (H₂.source_subset_preimage_source hy)] at hh
    refine ⟨y, hy, hb, ?_⟩
    rw [hgraph₂ _ (hcontrol _ (hVplanV hx)).1]
    change D.sheetTwo.inclusion y = c.chart.symm (F₂ (j x))
    rw [← hb, hF₂exact y hy, c.chart.left_inv hin]
  let Aplan := Acontrol ∩ (c.chart.source ∩ Pproj ⁻¹' Vplan)
  have hAplan : IsOpen Aplan := hAcontrol.inter
    (hPcont.isOpen_inter_preimage c.chart.open_source hVplan)
  have hqAplan : D.edge D.pointParameter ∈ Aplan :=
    ⟨hqAcontrol, hq, by change Pproj (D.edge D.pointParameter) ∈ Vplan; rw [hPq]; exact hVplan0⟩
  have hfirstPlan : ∀ Y ∈ Aplan, Y ∈ D.sheetOne.image ↔
      0 ≤ Pproj Y 0 ∧ c.chart Y = p + L (Pproj Y) := by
    intro Y hY
    rw [hfirstControlled Y hY.1, hfirstTarget _ hY.2.2]
  have hsecondPlan : ∀ Y ∈ Aplan, Y ∈ D.sheetTwo.image ↔
      0 ≤ beta (Pproj Y) ∧ c.chart Y = graphMap p L normal u₂ (Pproj Y) := by
    intro Y hY
    rw [hsecondControlled Y hY.1, hsecondTarget _ hY.2.2]
  let Tedge := Ioo (-1 : ℝ) 1 ∩ D.edge ⁻¹' Aplan
  have hTedge : IsOpen Tedge :=
    D.edge_smooth.continuousOn.isOpen_inter_preimage isOpen_Ioo hAplan
  have htTedge : (D.pointParameter : ℝ) ∈ Tedge := ⟨D.pointParameter.property, hqAplan⟩
  let gamma : ℝ → E2 := Pproj ∘ D.edge
  have hgamma0 : gamma D.pointParameter = 0 := hPq
  have hgammaV : ∀ t ∈ Tedge, gamma t ∈ Vplan := fun t ht => ht.2.2.2
  have hchartEdge : ∀ t ∈ Tedge, c.chart (D.edge t) = p + L (gamma t) := by
    intro t ht
    exact ((hfirstPlan _ ht.2).mp ⟨D.liftOne ⟨t, ht.1⟩, D.liftOne_exact ⟨t, ht.1⟩⟩).2
  have hgammaFirst : ∀ t (ht : t ∈ Tedge),
      gamma t = (H.domChart.extend (𝓡∂ 2)) (D.liftOne ⟨t, ht.1⟩) - z₀ := by
    intro t ht
    have hy : D.liftOne ⟨t, ht.1⟩ ∈ H.domChart.source :=
      hfullSource₁ _ (by rw [D.liftOne_exact]; exact ht.2.1.1)
    have hc := hfirstChart _ hy
    rw [D.liftOne_exact] at hc
    change π (c.chart (D.edge t) - p) = _
    rw [hc, map_sub, hπL]
  have hgammaLine : ∀ t ∈ Tedge, gamma t 0 = 0 := by
    intro t ht
    have hy : D.liftOne ⟨t, ht.1⟩ ∈ H.domChart.source :=
      hfullSource₁ _ (by rw [D.liftOne_exact]; exact ht.2.1.1)
    have hb := (fixed_maximal_halfspace_chart_boundary_normal D.sheetOne H.domChart
      H.domChart_mem_maximalAtlas _ hy (D.liftOne_boundary ⟨t, ht.1⟩)).1
    rw [hgammaFirst t ht]
    change (H.domChart.extend (𝓡∂ 2)) (D.liftOne ⟨t, ht.1⟩) 0 - z₀ 0 = 0
    rw [hb, hz₀zero, sub_self]
  have hgammaSecond : ∀ t (ht : t ∈ Tedge),
      j (gamma t) = (H₂.domChart.extend (𝓡∂ 2)) (D.liftTwo ⟨t, ht.1⟩) := by
    intro t ht
    have hh := hsecondInverse (D.liftTwo ⟨t, ht.1⟩)
      (by rw [D.liftTwo_exact]; exact ht.2.1.1)
    simpa only [gamma, Function.comp_apply, D.liftTwo_exact] using! hh
  have hgammaBeta : ∀ t ∈ Tedge, beta (gamma t) = 0 := by
    intro t ht
    have hy : D.liftTwo ⟨t, ht.1⟩ ∈ H₂.domChart.source :=
      (hfullSource₂ _ (by rw [D.liftTwo_exact]; exact ht.2.1.1)).1
    have hb := (fixed_maximal_halfspace_chart_boundary_normal D.sheetTwo H₂.domChart
      H₂.domChart_mem_maximalAtlas _ hy (D.liftTwo_boundary ⟨t, ht.1⟩)).1
    change j (gamma t) 0 = 0
    rw [hgammaSecond t ht]
    exact hb
  have hgammaHeight : ∀ t ∈ Tedge, u₂ (gamma t) = 0 := by
    intro t ht
    change (H.equiv.symm (F₂ (j (gamma t)) - p)).2 = 0
    rw [hgammaSecond t ht, hF₂exact _
      (hfullSource₂ _ (by rw [D.liftTwo_exact]; exact ht.2.1.1)).1,
      D.liftTwo_exact, hchartEdge t ht, add_sub_cancel_left]
    change (H.equiv.symm (H.equiv (gamma t, 0))).2 = 0
    rw [H.equiv.symm_apply_apply]
  have hchartEdgeSmooth : ContDiffOn ℝ ∞ (c.chart ∘ D.edge) Tedge := by
    apply contMDiffOn_iff_contDiffOn.mp
    exact c.smooth.comp (D.edge_smooth.mono inter_subset_left)
      (fun t ht => ht.2.2.1)
  have hgammaSmooth : ContDiffOn ℝ ∞ gamma Tedge :=
    π.contDiff.comp_contDiffOn (hchartEdgeSmooth.sub contDiffOn_const)
  have hchartVelocity : ∀ t ∈ Tedge, fderiv ℝ (c.chart ∘ D.edge) t 1 ≠ 0 := by
    intro t ht hzero
    have he : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ, E3) D.edge t :=
      (D.edge_smooth.contMDiffAt (isOpen_Ioo.mem_nhds ht.1)).mdifferentiableAt (by simp)
    have hc1 := IsManifold.maximalAtlas_subset_of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)
      H.codChart_mem_maximalAtlas
    have hc : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (D.edge t) :=
      mdifferentiableAt_of_mem_maximalAtlas hc1 ht.2.2.1
    let hm : c.chart.MDifferentiable 𝓘(ℝ, E3) 𝓘(ℝ, E3) := ⟨
      fun a ha => (mdifferentiableAt_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt,
      fun a ha => (mdifferentiableAt_symm_of_mem_maximalAtlas hc1 ha).mdifferentiableWithinAt⟩
    have hinj := (hm.mfderiv ht.2.2.1).injective
    have hchain := mfderiv_comp_apply t hc he (1 : ℝ)
    rw [mfderiv_eq_fderiv] at hchain
    have hz : mfderiv 𝓘(ℝ) 𝓘(ℝ, E3) D.edge t 1 = 0 :=
      hinj (hchain.symm.trans hzero |>.trans (map_zero _).symm)
    exact D.edge_regular ⟨t, ht.1⟩ hz
  have hgammaRegular : ∀ t ∈ Tedge, fderiv ℝ gamma t 1 ≠ 0 := by
    intro t ht hz
    have heq : (c.chart ∘ D.edge) =ᶠ[𝓝 t] (fun s => p + L (gamma s)) :=
      Filter.eventuallyEq_of_mem (hTedge.mem_nhds ht) hchartEdge
    have hgd := (hgammaSmooth.contDiffAt (hTedge.mem_nhds ht)).differentiableAt (by simp)
    have hd := ((L.hasFDerivAt.comp t hgd.hasFDerivAt).const_add p).fderiv
    have hv := congrArg (fun A : ℝ →L[ℝ] E3 => A 1) (heq.fderiv_eq.trans hd)
    rw [ContinuousLinearMap.comp_apply, hz, map_zero] at hv
    exact hchartVelocity t ht hv
  let xi : ℝ → ℝ := fun t => gamma t 1
  have hxiSmooth : ContDiffOn ℝ ∞ xi Tedge :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).contDiff.comp_contDiffOn hgammaSmooth
  have hxiDeriv : ∀ t ∈ Tedge, deriv xi t ≠ 0 := by
    intro t ht hzero
    have hg := (hgammaSmooth.contDiffAt (hTedge.mem_nhds ht)).differentiableAt (by simp)
    have hd0 := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp t hg.hasFDerivAt).hasDerivAt
    have hd1 := ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).hasFDerivAt.comp t hg.hasFDerivAt).hasDerivAt
    have heq : (fun s => gamma s 0) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem (hTedge.mem_nhds ht) hgammaLine
    have hz0 : fderiv ℝ gamma t 1 0 = 0 := by
      exact hd0.deriv.symm.trans (heq.deriv_eq.trans (deriv_const t 0))
    have hz1 : fderiv ℝ gamma t 1 1 = 0 := hd1.deriv.symm.trans hzero
    apply hgammaRegular t ht
    ext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hxiAt := hxiSmooth.contDiffAt (hTedge.mem_nhds htTedge)
  have hxiDF := (hxiAt.differentiableAt (by simp)).hasDerivAt.hasFDerivAt_equiv
    (hxiDeriv _ htTedge)
  let ge := hxiAt.toOpenPartialHomeomorph xi hxiDF (by simp)
  have htge : (D.pointParameter : ℝ) ∈ ge.source :=
    hxiAt.mem_toOpenPartialHomeomorph_source hxiDF (by simp)
  have hgexi : (ge : ℝ → ℝ) = xi := rfl
  have hxi0 : xi D.pointParameter = 0 := by change gamma D.pointParameter 1 = 0; rw [hgamma0]; rfl
  obtain ⟨aleft, bright, ⟨hleft, hright⟩, hinterval⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp
      ((hTedge.inter ge.open_source).mem_nhds ⟨htTedge, htge⟩)
  obtain ⟨a, hla, hat⟩ := exists_between hleft
  obtain ⟨b, htb, hbr⟩ := exists_between hright
  have haedge := (hinterval ⟨hla, hat.trans hright⟩).1.1
  have hbedge := (hinterval ⟨hleft.trans htb, hbr⟩).1.1
  have hIedge : Ioo a b ⊆ Tedge := fun t ht =>
    (hinterval ⟨hla.trans ht.1, ht.2.trans hbr⟩).1
  have hIge : Ioo a b ⊆ ge.source := fun t ht =>
    (hinterval ⟨hla.trans ht.1, ht.2.trans hbr⟩).2
  have hgammaEmbedding : IsEmbedding (fun t : Ioo a b => gamma t) := by
    have hxiEmb : IsEmbedding (fun t : Ioo a b => xi t) :=
      ge.isEmbedding_restrict.comp (Topology.IsEmbedding.subtypeVal.codRestrict
        ge.source (fun t => hIge t.property))
    exact Topology.IsEmbedding.of_comp
      ((hgammaSmooth.mono hIedge).continuousOn.restrict)
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous hxiEmb
  have hxiImageOpen : IsOpen (xi '' Ioo a b) := by
    rw [← hgexi]
    exact ge.isOpen_image_of_subset_source isOpen_Ioo hIge
  have hzeroXiImage : (0 : ℝ) ∈ xi '' Ioo a b := ⟨D.pointParameter, ⟨hat, htb⟩, hxi0⟩
  let Vline := Vplan ∩ ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1) ⁻¹' (xi '' Ioo a b))
  have hVline : IsOpen Vline := hVplan.inter
    (hxiImageOpen.preimage (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 1).continuous)
  have hVline0 : (0 : E2) ∈ Vline := ⟨hVplan0, hzeroXiImage⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hVline 0 hVline0
  have hRplan : Metric.ball (0 : E2) R ⊆ Vplan := fun x hx => (hRsub hx).1
  have hlineCoverage : (gamma '' Ioo a b) ∩ Metric.ball 0 R =
      {x ∈ Metric.ball (0 : E2) R | x 0 = 0} := by
    ext x
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hx⟩
      exact ⟨hx, hgammaLine t (hIedge ht)⟩
    · rintro ⟨hx, hx0⟩
      obtain ⟨t, ht, he⟩ := (hRsub hx).2
      refine ⟨⟨t, ht, ?_⟩, hx⟩
      ext i
      fin_cases i
      · exact (hgammaLine t (hIedge ht)).trans hx0.symm
      · exact he
  have hbetaLine : ∀ x ∈ Metric.ball (0 : E2) R, x 0 = 0 → beta x = 0 := by
    intro x hx hz
    obtain ⟨⟨t, ht, rfl⟩, _⟩ := hlineCoverage.symm ▸ (show x ∈ {x ∈ Metric.ball (0 : E2) R | x 0 = 0} from ⟨hx, hz⟩)
    exact hgammaBeta t (hIedge ht)
  have hheightLine : ∀ x ∈ Metric.ball (0 : E2) R, x 0 = 0 → u₂ x = 0 := by
    intro x hx hz
    obtain ⟨⟨t, ht, rfl⟩, _⟩ := hlineCoverage.symm ▸ (show x ∈ {x ∈ Metric.ball (0 : E2) R | x 0 = 0} from ⟨hx, hz⟩)
    exact hgammaHeight t (hIedge ht)
  let ρ : E3 →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ E2 ℝ).comp
    H.equiv.symm.toContinuousLinearMap
  have hρL : ∀ x : E2, ρ (L x) = 0 := by
    intro x
    change (H.equiv.symm (H.equiv (x, 0))).2 = 0
    rw [H.equiv.symm_apply_apply]
  have hgammaFullJet : ∀ t ∈ Tedge, fderiv ℝ u₂ (gamma t) = 0 := by
    intro s hs
    let t : ArcTime := ⟨s, hs.1⟩
    let y₁ := D.liftOne t
    let y₂ := D.liftTwo t
    let w₁ := (H.domChart.extend (𝓡∂ 2)) y₁
    let w₂ := (H₂.domChart.extend (𝓡∂ 2)) y₂
    have hy₁ : y₁ ∈ H.domChart.source :=
      hfullSource₁ _ (by rw [D.liftOne_exact]; exact hs.2.1.1)
    have hy₂ : y₂ ∈ H₂.domChart.source :=
      (hfullSource₂ _ (by rw [D.liftTwo_exact]; exact hs.2.1.1)).1
    have hc₁ : D.sheetOne.inclusion y₁ ∈ c.chart.source := H.source_subset_preimage_source hy₁
    have hc₂ : D.sheetTwo.inclusion y₂ ∈ c.chart.source := by
      rw [D.liftTwo_exact]
      exact hs.2.2.1
    have T₁ := full_extension_derivative_transport_real D.sheetOne x₁ H c.chart
      H.codChart_mem_maximalAtlas y₁ hy₁ hc₁
    have T₂ := full_extension_derivative_transport_second D.sheetTwo x₂
      H₂.isImmersionAtOfComplement_complement c.chart H.codChart_mem_maximalAtlas y₂ hy₂ hc₂
    have hLw : L w₁ ∈ c.chart.target := by
      rw [← hfirstChart y₁ hy₁]
      exact c.chart.map_source hc₁
    have hFeq : (c.chart ∘ c.chart.symm ∘ L) =ᶠ[𝓝 w₁] L := by
      filter_upwards [L.continuous.continuousAt.preimage_mem_nhds
        (c.chart.open_target.mem_nhds hLw)] with z hz
      exact c.chart.right_inv hz
    have hLderiv : fderiv ℝ (c.chart ∘ c.chart.symm ∘ L) w₁ = L :=
      hFeq.fderiv_eq.trans L.fderiv
    have hRange : LinearMap.range (fderiv ℝ F₂ w₂).toLinearMap = LinearMap.range L.toLinearMap := by
      have r₁ := T₁.2.2.2.2.1
      have r₂ := T₂.2.2.2.2.1
      change LinearMap.range (fderiv ℝ (c.chart ∘ c.chart.symm ∘ L) w₁).toLinearMap = _ at r₁
      rw [hLderiv] at r₁
      change LinearMap.range (fderiv ℝ F₂ w₂).toLinearMap = _ at r₂
      rw [r₂, r₁]
      have ht := actual_tangent_planes_equal t
      have hp : D.sheetTwo.inclusion y₂ = D.sheetOne.inclusion y₁ :=
        (D.liftTwo_exact t).trans (D.liftOne_exact t).symm
      simp only [TangentSpace] at ht ⊢
      rw [hp, ht]
      rfl
    have hw : j (gamma s) = w₂ := hgammaSecond s hs
    have hjd := (hjSmooth.contDiffAt (hVo.mem_nhds (hVplanV (hgammaV s hs)))).differentiableAt (by simp)
    have hfd : DifferentiableAt ℝ F₂ (j (gamma s)) := by
      rw [hw]
      exact T₂.2.2.1
    have hd : HasFDerivAt u₂
        (ρ.comp ((fderiv ℝ F₂ (j (gamma s))).comp (fderiv ℝ j (gamma s)))) (gamma s) :=
      ρ.hasFDerivAt.comp _ ((hfd.hasFDerivAt.comp _ hjd.hasFDerivAt).sub_const p)
    rw [hd.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    have hv : (fderiv ℝ F₂ w₂) (fderiv ℝ j (gamma s) v) ∈ LinearMap.range L.toLinearMap := by
      rw [← hRange]
      exact ⟨_, rfl⟩
    obtain ⟨w, hw'⟩ := hv
    change ρ ((fderiv ℝ F₂ (j (gamma s))) (fderiv ℝ j (gamma s) v)) = 0
    rw [hw, ← hw']
    exact hρL w
  have hfullJetLine : ∀ x ∈ Metric.ball (0 : E2) R, x 0 = 0 → fderiv ℝ u₂ x = 0 := by
    intro x hx hz
    obtain ⟨⟨t, ht, rfl⟩, _⟩ := hlineCoverage.symm ▸ (show x ∈ {x ∈ Metric.ball (0 : E2) R | x 0 = 0} from ⟨hx, hz⟩)
    exact hgammaFullJet t (hIedge ht)
  let e₀ : E2 := EuclideanSpace.single 0 1
  have he₀ : e₀ 0 = 1 := by simp [e₀]
  have hbetaD := (hbetaSmooth.contDiffAt (hVo.mem_nhds hV0)).differentiableAt (by simp)
  have hbetaFlat : ∀ v : E2, v 0 = 0 → fderiv ℝ beta 0 v = 0 := by
    intro v hv
    have hpath : ContinuousAt (fun t : ℝ => t • v) 0 := continuousAt_id.smul continuousAt_const
    have heq : (fun t : ℝ => beta (t • v)) =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
      filter_upwards [hpath.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0 : E2) hR)] with t ht
      exact hbetaLine _ ht (by change t * v 0 = 0; rw [hv, mul_zero])
    have hd := hbetaD.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
    simpa only [one_smul] using hd.deriv.symm.trans (heq.deriv_eq.trans (deriv_const 0 0))
  let k := fderiv ℝ beta 0 e₀
  have hbetaRow : ∀ v : E2, fderiv ℝ beta 0 v = k * v 0 := by
    intro v
    have hh := hbetaFlat (v - v 0 • e₀) (by change v 0 - v 0 * e₀ 0 = 0; rw [he₀]; ring)
    rw [map_sub, map_smul] at hh
    change fderiv ℝ beta 0 v - v 0 * k = 0 at hh
    nlinarith
  let J₁ := (tangentSpaceCastModel 𝓘(ℝ, E2) ((H.domChart.extend (𝓡∂ 2)) x₁)).toContinuousLinearMap.comp
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (H.domChart.extend (𝓡∂ 2)) x₁)
  let J₂ := (tangentSpaceCastModel 𝓘(ℝ, E2) z₂).toContinuousLinearMap.comp
    (mfderiv (𝓡∂ 2) 𝓘(ℝ, E2) (H₂.domChart.extend (𝓡∂ 2)) x₂)
  let C := (tangentSpaceCastModel 𝓘(ℝ, E3) p).toContinuousLinearMap.comp
    (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (D.edge D.pointParameter))
  let n₁ := edgeConormal D.sheetOne D.edge D.liftOne D.liftOne_exact D.outwardOne D.pointParameter
  let n₂ := edgeConormal D.sheetTwo D.edge D.liftTwo D.liftTwo_exact D.outwardTwo D.pointParameter
  let v₁ := π (C n₁)
  let v₂ := π (C n₂)
  have hbaseFirst := full_extension_derivative_transport_real D.sheetOne x₁ H c.chart
    H.codChart_mem_maximalAtlas x₁ H.mem_domChart_source H.mem_codChart_source
  have hbaseSecond := full_extension_derivative_transport_second D.sheetTwo x₂
    H₂.isImmersionAtOfComplement_complement c.chart H.codChart_mem_maximalAtlas x₂
    H₂.mem_domChart_source (by simpa only [x₂, D.liftTwo_exact] using hq)
  have hbaseFlat : fderiv ℝ (c.chart ∘ c.chart.symm ∘ L) z₀ = L := by
    have heq : (c.chart ∘ c.chart.symm ∘ L) =ᶠ[𝓝 z₀] L := by
      filter_upwards [L.continuous.continuousAt.preimage_mem_nhds
        (c.chart.open_target.mem_nhds (by rw [← hpLz]; exact c.chart.map_source hq))] with z hz
      exact c.chart.right_inv hz
    exact heq.fderiv_eq.trans L.fderiv
  have hn₁ : (n₁ : E3) = mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion x₁
      (D.outwardOne D.pointParameter) := by simp [n₁, edgeConormal, TangentSpace]; rfl
  have hn₂ : (n₂ : E3) = mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion x₂
      (D.outwardTwo D.pointParameter) := by simp [n₂, edgeConormal, TangentSpace]; rfl
  have hfirstOut : v₁ = J₁ (D.outwardOne D.pointParameter) := by
    have ht := congrArg (fun A => A (D.outwardOne D.pointParameter)) hbaseFirst.2.2.2.1
    change (fderiv ℝ (c.chart ∘ c.chart.symm ∘ L) ((H.domChart.extend (𝓡∂ 2)) x₁))
      (J₁ (D.outwardOne D.pointParameter)) =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (D.sheetOne.inclusion x₁)
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetOne.inclusion x₁ (D.outwardOne D.pointParameter)) at ht
    rw [← hz₀, hbaseFlat, ← hn₁] at ht
    have hp1 : D.sheetOne.inclusion x₁ = D.edge D.pointParameter := D.liftOne_exact D.pointParameter
    rw [hp1] at ht
    have ht' : L (J₁ (D.outwardOne D.pointParameter)) = C n₁ := ht
    change π (C n₁) = _
    rw [← ht', hπL]
  have hsecondOut : fderiv ℝ j 0 v₂ = J₂ (D.outwardTwo D.pointParameter) := by
    have ht := congrArg (fun A => A (D.outwardTwo D.pointParameter)) hbaseSecond.2.2.2.1
    change fderiv ℝ F₂ z₂ (J₂ (D.outwardTwo D.pointParameter)) =
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, E3) c.chart (D.sheetTwo.inclusion x₂)
        (mfderiv (𝓡∂ 2) 𝓘(ℝ, E3) D.sheetTwo.inclusion x₂ (D.outwardTwo D.pointParameter)) at ht
    rw [← hn₂] at ht
    have hp2 : D.sheetTwo.inclusion x₂ = D.edge D.pointParameter := D.liftTwo_exact D.pointParameter
    rw [hp2] at ht
    have ht' : fderiv ℝ F₂ z₂ (J₂ (D.outwardTwo D.pointParameter)) = C n₂ := ht
    have hDQ : fderiv ℝ (π ∘ F₂) z₂ = π.comp (fderiv ℝ F₂ z₂) :=
      (π.hasFDerivAt.comp _ hbaseSecond.2.2.1.hasFDerivAt).fderiv
    have hi := congrArg (fun A : E2 →L[ℝ] E2 => A (J₂ (D.outwardTwo D.pointParameter)))
      (hinverseIdentities 0 hV0).2
    rw [hj0, hDQ] at hi
    change fderiv ℝ j 0 (π (fderiv ℝ F₂ z₂ (J₂ (D.outwardTwo D.pointParameter)))) = _ at hi
    rw [ht'] at hi
    exact hi
  have hv₁ : v₁ 0 < 0 := by
    rw [hfirstOut, hnormal₁]
    exact mul_neg_of_pos_of_neg hlam₁ (D.outwardOne_direction D.pointParameter)
  have hv₂ : 0 < v₂ 0 := by
    have hh : v₁ + v₂ = 0 := by
      change π (C n₁) + π (C n₂) = 0
      rw [← map_add, ← map_add, D.opposite_outward_conormals D.pointParameter, map_zero, map_zero]
    have hcoord := congrArg (fun x : E2 => x 0) hh
    change v₁ 0 + v₂ 0 = 0 at hcoord
    linarith
  have hk : k < 0 := by
    have hd : fderiv ℝ beta 0 = (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).comp (fderiv ℝ j 0) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.comp _
        ((hjSmooth.contDiffAt (hVo.mem_nhds hV0)).differentiableAt (by simp)).hasFDerivAt).fderiv
    have hout : fderiv ℝ beta 0 v₂ < 0 := by
      rw [hd, ContinuousLinearMap.comp_apply, hsecondOut]
      change (J₂ (D.outwardTwo D.pointParameter)) 0 < 0
      rw [hnormal₂]
      exact mul_neg_of_pos_of_neg hlam₂ (D.outwardTwo_direction D.pointParameter)
    rw [hbetaRow] at hout
    nlinarith
  have hderivCont : ContinuousOn (fun x => fderiv ℝ beta x e₀) V :=
    (hbetaSmooth.continuousOn_fderiv_of_isOpen hVo (by simp)).clm_apply continuousOn_const
  let Vnegative := Metric.ball (0 : E2) R ∩ {x | fderiv ℝ beta x e₀ < 0}
  have hVnegative : IsOpen Vnegative :=
    (hderivCont.mono (fun x hx => hVplanV (hRplan hx))).isOpen_inter_preimage
      Metric.isOpen_ball isOpen_Iio
  have hVnegative0 : (0 : E2) ∈ Vnegative := ⟨Metric.mem_ball_self hR, hk⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hVnegative 0 hVnegative0
  let Rside := δ / 2
  have hRside : 0 < Rside := half_pos hδ
  have hsideR : Metric.ball (0 : E2) Rside ⊆ Metric.ball 0 R := by
    intro x hx
    exact (hδsub (Metric.ball_subset_ball (by dsimp [Rside]; linarith) hx)).1
  have hsideSign : ∀ x ∈ Metric.ball (0 : E2) Rside,
      (0 ≤ beta x ↔ x 0 ≤ 0) ∧ (beta x = 0 ↔ x 0 = 0) := by
    intro x hx
    let xflat : E2 := EuclideanSpace.single 1 (x 1)
    let path : ℝ → E2 := fun t => xflat + t • e₀
    have hflat0 : xflat 0 = 0 := by simp [xflat]
    have hflatNorm : ‖xflat‖ ≤ ‖x‖ := by
      simpa only [xflat, EuclideanSpace.norm_single] using PiLp.norm_apply_le x 1
    have heNorm : ‖e₀‖ = 1 := by simp [e₀]
    have hpath0 : path 0 = xflat := by simp [path]
    have hpathx : path (x 0) = x := by
      ext i
      fin_cases i <;> simp [path, xflat, e₀]
    have hbound : ∀ t ∈ Icc (min 0 (x 0)) (max 0 (x 0)), path t ∈ Vnegative := by
      intro t ht
      apply hδsub
      rw [Metric.mem_ball, dist_zero_right]
      have htbound : |t| ≤ |x 0| := by
        rcases le_total 0 (x 0) with hp | hn
        · simp only [min_eq_left hp, max_eq_right hp] at ht
          rw [abs_of_nonneg ht.1, abs_of_nonneg hp]
          exact ht.2
        · simp only [min_eq_right hn, max_eq_left hn] at ht
          rw [abs_of_nonpos ht.2, abs_of_nonpos hn]
          linarith [ht.1]
      have htNorm : ‖t‖ ≤ ‖x‖ := htbound.trans (PiLp.norm_apply_le x 0)
      have hxnorm : ‖x‖ < δ / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      calc
        ‖path t‖ ≤ ‖xflat‖ + ‖t • e₀‖ := norm_add_le _ _
        _ = ‖xflat‖ + ‖t‖ := by rw [norm_smul, heNorm, mul_one]
        _ ≤ 2 * ‖x‖ := by linarith
        _ < δ := by linarith
    let pathD : ℝ →L[ℝ] E2 := (ContinuousLinearMap.id ℝ ℝ).smulRight e₀
    have hpathD : ∀ t : ℝ, HasFDerivAt path pathD t := by
      intro t
      exact pathD.hasFDerivAt.const_add xflat
    have hanti : StrictAntiOn (beta ∘ path) (Icc (min 0 (x 0)) (max 0 (x 0))) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      · exact hbetaSmooth.continuousOn.comp
          (fun t ht => (hpathD t).continuousAt.continuousWithinAt)
          (fun t ht => hVplanV (hRplan (hbound t ht).1))
      · intro t ht
        have ht' := interior_subset ht
        have hbt := (hbetaSmooth.contDiffAt
          (hVo.mem_nhds (hVplanV (hRplan (hbound t ht').1)))).differentiableAt (by simp)
        rw [(hbt.hasFDerivAt.comp t (hpathD t)).hasDerivAt.deriv]
        simpa only [ContinuousLinearMap.comp_apply, pathD, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, one_smul, Set.mem_setOf_eq] using! (hbound t ht').2
    have hzeroMem : (0 : ℝ) ∈ Icc (min 0 (x 0)) (max 0 (x 0)) := ⟨min_le_left _ _, le_max_left _ _⟩
    have hxMem : x 0 ∈ Icc (min 0 (x 0)) (max 0 (x 0)) := ⟨min_le_right _ _, le_max_right _ _⟩
    have hb0 : (beta ∘ path) 0 = 0 := by
      change beta (path 0) = 0
      exact hbetaLine _ (hbound 0 hzeroMem).1 (by rw [hpath0, hflat0])
    have hbx : (beta ∘ path) (x 0) = beta x := by change beta (path (x 0)) = _; rw [hpathx]
    rcases lt_trichotomy (x 0) 0 with hn | hz | hp
    · have hb : 0 < beta x := by simpa only [hb0, hbx] using hanti hxMem hzeroMem hn
      exact ⟨iff_of_true (le_of_lt hb) (le_of_lt hn), iff_of_false (ne_of_gt hb) (ne_of_lt hn)⟩
    · have hb := hbetaLine x (hsideR hx) hz
      exact ⟨iff_of_true (by rw [hb]) (le_of_eq hz), iff_of_true hb hz⟩
    · have hb : beta x < 0 := by simpa only [hb0, hbx] using hanti hzeroMem hxMem hp
      exact ⟨iff_of_false (not_le_of_gt hb) (not_le_of_gt hp), iff_of_false (ne_of_lt hb) (ne_of_gt hp)⟩
  have hsourceSigns : ∀ x ∈ Metric.ball (0 : E2) Rside,
      (z₀ + x ∈ (H.domChart.extend (𝓡∂ 2)).target ↔ 0 ≤ x 0) ∧
      (j x ∈ (H₂.domChart.extend (𝓡∂ 2)).target ↔ x 0 ≤ 0) := by
    intro x hx
    exact ⟨hfirstTarget x (hRplan (hsideR hx)),
      (hsecondTarget x (hRplan (hsideR hx))).trans (hsideSign x hx).1⟩
  classical
  let w : E2 → ℝ := fun x => if 0 ≤ x 0 then 0 else u₂ x
  let dw : E2 → E2 →L[ℝ] ℝ := fun x => if 0 ≤ x 0 then 0 else fderiv ℝ u₂ x
  have hwpos : ∀ x : E2, 0 ≤ x 0 → w x = 0 := fun x hx => if_pos hx
  have hwneg : ∀ x ∈ Metric.ball (0 : E2) R, x 0 ≤ 0 → w x = u₂ x := by
    intro x hx hz
    by_cases hn : 0 ≤ x 0
    · rw [hwpos x hn, hheightLine x hx (le_antisymm hz hn)]
    · exact if_neg hn
  have hw0 : w 0 = 0 := hwpos 0 (by simp)
  have hwd : ∀ x ∈ Metric.ball (0 : E2) R, HasFDerivAt w (dw x) x := by
    intro x hx
    have huAt := (hu₂on.contDiffAt (hVo.mem_nhds (hVplanV (hRplan hx)))).differentiableAt (by simp)
    rcases lt_trichotomy (x 0) 0 with hn | hz | hp
    · have heq : w =ᶠ[𝓝 x] u₂ := by
        filter_upwards [(isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous
          continuous_const).mem_nhds hn] with y hy
        exact if_neg (not_le_of_gt hy)
      change HasFDerivAt w (if 0 ≤ x 0 then 0 else fderiv ℝ u₂ x) x
      rw [if_neg (not_le_of_gt hn)]
      exact huAt.hasFDerivAt.congr_of_eventuallyEq heq
    · have huw := hheightLine x hx hz
      have hud := hfullJetLine x hx hz
      have hux : HasFDerivAt u₂ (0 : E2 →L[ℝ] ℝ) x := by rw [← hud]; exact huAt.hasFDerivAt
      have hwx : w x = 0 := hwpos x (le_of_eq hz.symm)
      have hdwx : dw x = 0 := if_pos (le_of_eq hz.symm)
      rw [hdwx, hasFDerivAt_iff_isLittleO]
      apply Asymptotics.IsLittleO.of_bound
      intro ε hε
      filter_upwards [(hasFDerivAt_iff_isLittleO.mp hux).bound hε] with y hy
      simp only [huw, ContinuousLinearMap.zero_apply, sub_zero] at hy
      simp only [hwx, ContinuousLinearMap.zero_apply, sub_zero]
      change ‖(if 0 ≤ y 0 then 0 else u₂ y)‖ ≤ ε * ‖y - x‖
      split_ifs
      · simpa only [norm_zero] using mul_nonneg hε.le (norm_nonneg (y - x))
      · exact hy
    · have heq : w =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
        filter_upwards [(isOpen_lt continuous_const
          (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous).mem_nhds hp] with y hy
        exact hwpos y hy.le
      change HasFDerivAt w (if 0 ≤ x 0 then 0 else fderiv ℝ u₂ x) x
      rw [if_pos hp.le]
      exact (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq heq
  have hfrontLine : ∀ x ∈ frontier {x : E2 | 0 ≤ x 0}, x 0 = 0 := by
    intro x hx
    have hh := (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous.frontier_preimage_subset
      (Ici (0 : ℝ)) hx
    simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using! hh
  have hdwCont : ContinuousOn dw (Metric.ball (0 : E2) R) := by
    apply ContinuousOn.if
    · intro x hx
      exact (hfullJetLine x hx.1 (hfrontLine x hx.2)).symm
    · exact continuousOn_const
    · exact ((hu₂on.continuousOn_fderiv_of_isOpen hVo (by simp)).mono
        (fun x hx => hVplanV (hRplan hx))).mono inter_subset_left
  have hwC1 : ContDiffOn ℝ 1 w (Metric.ball (0 : E2) R) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx => (hwd x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · rw [contDiffOn_zero]
      exact hdwCont.congr (fun x hx => (hwd x hx).fderiv)
  have hwSmoothPos : ContDiffOn ℝ ∞ w {x ∈ Metric.ball (0 : E2) R | 0 ≤ x 0} :=
    contDiffOn_const.congr (fun x hx => hwpos x hx.2)
  have hwSmoothNeg : ContDiffOn ℝ ∞ w {x ∈ Metric.ball (0 : E2) R | x 0 ≤ 0} :=
    (hu₂on.mono (fun x hx => hVplanV (hRplan hx.1))).congr
      (fun x hx => hwneg x hx.1 hx.2)
  let G := graphMap p L normal w
  let Phi : E2 → N := c.chart.symm ∘ G
  have hGpos : ∀ x : E2, 0 ≤ x 0 → G x = p + L x := by
    intro x hx
    simp only [G, graphMap, hwpos x hx, zero_smul, add_zero]
  have hGneg : ∀ x ∈ Metric.ball (0 : E2) R, x 0 ≤ 0 → G x = graphMap p L normal u₂ x := by
    intro x hx hz
    simp only [G, graphMap, hwneg x hx hz]
  have hG0 : G 0 = p := by rw [hGpos 0 (by simp), map_zero, add_zero]
  have hPhi0 : Phi 0 = D.edge D.pointParameter := by
    change c.chart.symm (G 0) = _
    rw [hG0]
    exact c.chart.left_inv hq
  have hGtarget : ∀ x ∈ Metric.ball (0 : E2) Rside, G x ∈ c.chart.target := by
    intro x hx
    rcases le_total 0 (x 0) with hp | hn
    · rw [hGpos x hp]
      exact (hRplan (hsideR hx)).2
    · rw [hGneg x (hsideR hx) hn]
      exact hsecondGraphTarget x (hRplan (hsideR hx))
  have hGcont : ContinuousOn G (Metric.ball (0 : E2) R) :=
    (continuousOn_const.add L.continuous.continuousOn).add
      (hwC1.continuousOn.smul continuousOn_const)
  have hPhiCont : ContinuousOn Phi (Metric.ball (0 : E2) Rside) :=
    c.chart.symm.continuousOn.comp (hGcont.mono hsideR) hGtarget
  let Vfinal := Metric.ball (0 : E2) Rside ∩ Phi ⁻¹' Aplan
  have hVfinal : IsOpen Vfinal :=
    hPhiCont.isOpen_inter_preimage Metric.isOpen_ball hAplan
  have hVfinal0 : (0 : E2) ∈ Vfinal :=
    ⟨Metric.mem_ball_self hRside, by change Phi 0 ∈ Aplan; rw [hPhi0]; exact hqAplan⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hVfinal 0 hVfinal0
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h2r : Metric.closedBall (0 : E2) (2 * r) ⊆ Vfinal := by
    intro x hx
    apply hεsub
    rw [Metric.mem_ball, dist_zero_right]
    have hx' : ‖x‖ ≤ 2 * r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    dsimp [r] at hx'
    linarith
  have hr2 : Metric.ball (0 : E2) r ⊆ Metric.closedBall 0 (2 * r) :=
    (Metric.ball_subset_ball (by linarith)).trans Metric.ball_subset_closedBall
  have hrSide : Metric.ball (0 : E2) r ⊆ Metric.ball 0 Rside := fun x hx => (h2r (hr2 hx)).1
  have hrR : Metric.ball (0 : E2) r ⊆ Metric.ball 0 R := fun x hx => hsideR (hrSide hx)
  have hprojectPhi : ∀ x ∈ Metric.ball (0 : E2) Rside, Pproj (Phi x) = x := by
    intro x hx
    change π (c.chart (c.chart.symm (G x)) - p) = x
    rw [c.chart.right_inv (hGtarget x hx)]
    change π (p + L x + w x • normal - p) = x
    rw [map_sub, map_add, map_add, map_smul, hπL, hπnormal, smul_zero, add_zero]
    abel
  let Afinal := Aplan ∩ (c.chart.source ∩ Pproj ⁻¹' Metric.ball 0 r)
  have hAfinal : IsOpen Afinal := hAplan.inter
    (hPcont.isOpen_inter_preimage c.chart.open_source Metric.isOpen_ball)
  have hqAfinal : D.edge D.pointParameter ∈ Afinal :=
    ⟨hqAplan, hq, by change Pproj (D.edge D.pointParameter) ∈ Metric.ball 0 r; rw [hPq]; exact Metric.mem_ball_self hr⟩
  let Sone := {x ∈ Metric.ball (0 : E2) r | 0 ≤ x 0}
  let Stwo := {x ∈ Metric.ball (0 : E2) r | x 0 ≤ 0}
  have hPhiFinal : ∀ x ∈ Metric.ball (0 : E2) r, Phi x ∈ Afinal := by
    intro x hx
    exact ⟨(h2r (hr2 hx)).2, c.chart.map_target (hGtarget x (hrSide hx)),
      by change Pproj (Phi x) ∈ Metric.ball 0 r; rwa [hprojectPhi x (hrSide hx)]⟩
  have hsheetOne : Phi '' Sone = D.sheetOne.image ∩ Afinal := by
    ext Y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(hfirstPlan _ (hPhiFinal x hx.1).1).mpr ⟨?_, ?_⟩, hPhiFinal x hx.1⟩
      · rw [hprojectPhi x (hrSide hx.1)]
        exact hx.2
      · rw [hprojectPhi x (hrSide hx.1)]
        change c.chart (c.chart.symm (G x)) = _
        rw [c.chart.right_inv (hGtarget x (hrSide hx.1)), hGpos x hx.2]
    · rintro ⟨hY, hYA⟩
      have hy := (hfirstPlan Y hYA.1).mp hY
      refine ⟨Pproj Y, ⟨hYA.2.2, hy.1⟩, ?_⟩
      change c.chart.symm (G (Pproj Y)) = Y
      rw [hGpos _ hy.1, ← hy.2, c.chart.left_inv hYA.2.1]
  have hsheetTwo : Phi '' Stwo = D.sheetTwo.image ∩ Afinal := by
    ext Y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(hsecondPlan _ (hPhiFinal x hx.1).1).mpr ⟨?_, ?_⟩, hPhiFinal x hx.1⟩
      · rw [hprojectPhi x (hrSide hx.1)]
        exact (hsideSign x (hrSide hx.1)).1.mpr hx.2
      · rw [hprojectPhi x (hrSide hx.1)]
        change c.chart (c.chart.symm (G x)) = _
        rw [c.chart.right_inv (hGtarget x (hrSide hx.1)), hGneg x (hrR hx.1) hx.2]
    · rintro ⟨hY, hYA⟩
      have hy := (hsecondPlan Y hYA.1).mp hY
      have hsign := (hsideSign _ (hrSide hYA.2.2)).1.mp hy.1
      refine ⟨Pproj Y, ⟨hYA.2.2, hsign⟩, ?_⟩
      change c.chart.symm (G (Pproj Y)) = Y
      rw [hGneg _ (hrR hYA.2.2) hsign, ← hy.2, c.chart.left_inv hYA.2.1]
  have hcover : Sone ∪ Stwo = Metric.ball 0 r := by
    ext x
    exact ⟨fun hx => hx.elim And.left And.left,
      fun hx => (le_total 0 (x 0)).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)⟩
  have hclosedOne : IsClosed ((Subtype.val : Metric.ball (0 : E2) r → E2) ⁻¹' Sone) := by
    have heq : ((Subtype.val : Metric.ball (0 : E2) r → E2) ⁻¹' Sone) =
        {x : Metric.ball (0 : E2) r | 0 ≤ (x : E2) 0} := by ext x; simp only [mem_preimage, Sone, mem_setOf_eq, x.property, true_and]
    rw [heq]
    exact isClosed_le continuous_const
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous.comp continuous_subtype_val)
  have hclosedTwo : IsClosed ((Subtype.val : Metric.ball (0 : E2) r → E2) ⁻¹' Stwo) := by
    have heq : ((Subtype.val : Metric.ball (0 : E2) r → E2) ⁻¹' Stwo) =
        {x : Metric.ball (0 : E2) r | (x : E2) 0 ≤ 0} := by ext x; simp only [mem_preimage, Stwo, mem_setOf_eq, x.property, true_and]
    rw [heq]
    exact isClosed_le
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).continuous.comp continuous_subtype_val) continuous_const
  have hdisjointSides : Disjoint (interior Sone) (interior Stwo) := by
    let ev : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
    have hev : Function.Surjective ev := by
      intro t
      exact ⟨t • e₀, by change t * e₀ 0 = t; rw [he₀, mul_one]⟩
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hxp := interior_mono (show Sone ⊆ ev ⁻¹' Ici 0 from fun x hx => hx.2) hx
    have hxn := interior_mono (show Stwo ⊆ ev ⁻¹' Iic 0 from fun x hx => hx.2) hy
    rw [ev.interior_preimage hev, interior_Ici] at hxp
    rw [ev.interior_preimage hev, interior_Iic] at hxn
    change 0 < ev x at hxp
    change ev x < 0 at hxn
    exact lt_asymm hxp hxn
  have hedge : Sone ∩ Stwo = (gamma '' Ioo a b) ∩ Metric.ball 0 r := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      have he := hlineCoverage.symm ▸ (show x ∈ {x ∈ Metric.ball (0 : E2) R | x 0 = 0}
        from ⟨hrR hx.1, le_antisymm hy.2 hx.2⟩)
      exact ⟨he.1, hx.1⟩
    · rintro ⟨⟨t, ht, rfl⟩, hx⟩
      have hz := hgammaLine t (hIedge ht)
      exact ⟨⟨hx, le_of_eq hz.symm⟩, hx, le_of_eq hz⟩
  have hedgeExact : ∀ t ∈ Ioo a b, c.chart.symm (G (gamma t)) = D.edge t := by
    intro t ht
    rw [hGpos _ (by rw [hgammaLine t (hIedge ht)]), ← hchartEdge t (hIedge ht),
      c.chart.left_inv (hIedge ht).2.2.1]
  let signed : E2 → ℝ := fun x => -(x 0)
  have hsignedSmooth : ContDiff ℝ ∞ signed :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).contDiff.neg
  have hsignedRegular : ∀ x : E2, planarGradient signed x ≠ 0 := by
    intro x hz
    have hd : fderiv ℝ signed x = -(EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).hasFDerivAt.neg.fderiv
    have hh := congrArg (fun v : E2 => v 0) hz
    simp [planarGradient, hd, coordinateVector] at hh
  refine ⟨{
    neighborhood := Afinal
    neighborhood_open := hAfinal
    point_mem := hqAfinal
    radius := r
    radius_pos := hr
    coordinates := c
    point_in_chart := hq
    plane := L
    normal := normal
    splitting := hsplit
    height := w
    height_zero := hw0
    height_C1 := hwC1.mono (fun x hx => hsideR (h2r hx).1)
    graph_in_chart := fun x hx => hGtarget x (h2r hx).1
    sideOne := Sone
    sideTwo := Stwo
    sideOne_in_disc := fun _ hx => hx.1
    sideTwo_in_disc := fun _ hx => hx.1
    sides_cover := hcover
    sideOne_closed := hclosedOne
    sideTwo_closed := hclosedTwo
    interiors_disjoint := hdisjointSides
    height_smooth_one := hwSmoothPos.mono (fun x hx => ⟨hrR hx.1, hx.2⟩)
    height_smooth_two := hwSmoothNeg.mono (fun x hx => ⟨hrR hx.1, hx.2⟩)
    sheetOne_exact := hsheetOne
    sheetTwo_exact := hsheetTwo
    edgeLeft := a
    edgeRight := b
    edgeLeft_lower := haedge.1
    point_after_left := hat
    point_before_right := htb
    edgeRight_upper := hbedge.2
    projectedEdge := gamma
    edge_smooth := hgammaSmooth.mono hIedge
    edge_embedding := hgammaEmbedding
    edge_regular := fun t ht => hgammaRegular t (hIedge ht)
    edge_zero := hgamma0
    shared_edge := hedge
    edge_exact := hedgeExact
    signedSide := signed
    signedSide_smooth := hsignedSmooth.contDiffOn
    signedSide_regular := fun x _ _ => hsignedRegular x
    sideOne_signed := by ext x; simp [Sone, signed]
    sideTwo_signed := by ext x; simp [Stwo, signed]
  }⟩

end SeifertSurfaces.OriginalEndpoints
