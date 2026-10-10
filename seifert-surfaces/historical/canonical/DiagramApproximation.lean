import DiagramGeometry
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Embedding.AmbientIsotopy
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Topology
namespace SeifertSurfaces.LongitudeProducers
open Foundations MetricFoundations
noncomputable section

/-- S0 approximation with real tube coordinates, a positive longitudinal
diffeomorphism and quantitative normal value/derivative control. -/
structure ControlledPolygon {K : OrientedKnot} (T : TubularNeighborhood K)
    (L : StereographicPlacement K) (δ : ℝ) where
  polygon : PolygonalKnot
  smoothing : PolygonSmoothing polygon
  longitudinal : PositiveCircleDiffeomorph
  normal : Circle → Euc 2
  normal_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ normal
  normal_small : ∀ z, ‖normal z‖ < δ
  derivative_small : ∀ t : ℝ,
    ‖fderiv ℝ (fun r => normal (Circle.exp r)) t‖ < δ
  tube_graph : ∀ z, ∃ w : TubeDisk, (w : Euc 2) = normal z ∧
    L.chart.symm (smoothing.curve z) = T.tube 0 (longitudinal.diffeomorph z, w)

structure FiniteProjectionPerturbation (P : PolygonalKnot) (δ : ℝ) where
  polygon : PolygonalKnot
  indexing : Fin P.polygon.count ≃ Fin polygon.polygon.count
  commutes_next : ∀ i, indexing (P.polygon.next i) = polygon.polygon.next (indexing i)
  vertices_close : ∀ i, dist (polygon.polygon.vertex (indexing i)) (P.polygon.vertex i) < δ
  diagram : RegularOrientedDiagram polygon
  isotopy : PiecewiseCurveIsotopy (polygonLoop P) (polygonLoop polygon)

/-- Genericity is finite after polygonal approximation. It is not assumed
for an arbitrary smooth projection of K. -/


/- Candidate support lemma pending review: a smooth section over a circle
diffeomorphism is a genuine smooth embedded graph in the tube domain. -/
theorem smooth_tube_graph_embedding (d : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (n : Circle → TubeDisk) (hn : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ n) :
    Manifold.IsSmoothEmbedding (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞
      (fun z => (d z, n z)) := by
  let f : Circle → TubeDomain := fun z => (d z, n z)
  have hf : ContMDiff (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞ f :=
    d.contMDiff.prodMk hn
  have hi : Manifold.IsImmersion (𝓡 1) ((𝓡 1).prod 𝓘(ℝ, Euc 2)) ∞ f := by
    apply DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hf
    intro z
    have hcomp : Prod.fst ∘ f = d := rfl
    have hdf : Function.Injective (mfderiv (𝓡 1) (𝓡 1) (Prod.fst ∘ f) z) := by
      rw [hcomp]
      exact d.isSmoothEmbedding.isImmersion.mfderiv_injective (by simp) z
    rw [mfderiv_comp z mdifferentiableAt_fst (hf.mdifferentiableAt (by simp))] at hdf
    exact Function.Injective.of_comp hdf
  have he : Topology.IsEmbedding f := by
    exact Topology.IsEmbedding.of_comp hf.continuous continuous_fst
      d.toHomeomorph.isEmbedding
  exact ⟨hi, he⟩

theorem smooth_sphere_tube_graph_embedding {K : OrientedKnot}
    (T : TubularNeighborhood K) (d : Diffeomorph (𝓡 1) (𝓡 1) Circle Circle ∞)
    (n : Circle → TubeDisk) (hn : ContMDiff (𝓡 1) 𝓘(ℝ, Euc 2) ∞ n) :
    Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞
      (fun z => T.tube 0 (d z, n z)) :=
  (T.smoothEmbedding 0).comp (smooth_tube_graph_embedding d n hn) (by simp)


/-- Candidate support lemma, pending independent statement review: the given
normal graph contracts smoothly to the tube core and stays within radius one. -/
theorem controlled_normal_graph_family {K : OrientedKnot}
    {T : TubularNeighborhood K} {L : StereographicPlacement K}
    {δ : ℝ} (C : ControlledPolygon T L δ) (h1 : δ < 1) :
    ∃ G : ℝ × Circle → ThreeSphere,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 3) ∞ G ∧
      (∀ z, G (0, z) = L.chart.symm (C.smoothing.curve z)) ∧
      (∀ z, G (1, z) = K.component 0 (C.longitudinal.diffeomorph z)) ∧
      (∀ t, Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 3) ∞ (fun z => G (t, z))) ∧
      ∀ t z, ∃ w : TubeDisk, ‖(w : Euc 2)‖ < 1 ∧
        G (t, z) = T.tube 0 (C.longitudinal.diffeomorph z, w) := by
  let n : ℝ × Circle → Euc 2 := fun q =>
    (1 - Real.smoothTransition q.1) • C.normal q.2
  have hn (q : ℝ × Circle) : ‖n q‖ < 1 := by
    have hc0 : 0 ≤ 1 - Real.smoothTransition q.1 := by
      linarith [Real.smoothTransition.le_one q.1]
    have hc1 : 1 - Real.smoothTransition q.1 ≤ 1 := by
      linarith [Real.smoothTransition.nonneg q.1]
    dsimp only [n]
    rw [norm_smul, Real.norm_of_nonneg hc0]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc1).trans_lt
      ((C.normal_small q.2).trans h1)
  let w : ℝ × Circle → TubeDisk := fun q =>
    ⟨n q, by
      change dist (n q) 0 < 2
      rw [dist_zero_right]
      exact (hn q).trans (by norm_num : (1 : ℝ) < 2)⟩
  have hw : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, Euc 2) ∞ w := by
    apply (ContMDiff.subtypeVal_comp_iff tubeDiskOpen w).mp
    exact (contMDiff_const.sub
      (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst)).smul
      (C.normal_smooth.comp contMDiff_snd)
  let G : ℝ × Circle → ThreeSphere := fun q =>
    T.tube 0 (C.longitudinal.diffeomorph q.2, w q)
  refine ⟨G, (T.smoothEmbedding 0).contMDiff.comp
    ((C.longitudinal.diffeomorph.contMDiff.comp contMDiff_snd).prodMk hw), ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨v, hv, hgraph⟩ := C.tube_graph z
    have hw0 : w (0, z) = v := by
      apply Subtype.ext
      simpa only [w, n, Real.smoothTransition.zero, sub_zero, one_smul] using hv.symm
    change T.tube 0 (C.longitudinal.diffeomorph z, w (0, z)) = _
    rw [hw0]
    exact hgraph.symm
  · intro z
    have hw1 : w (1, z) = ⟨0, Metric.mem_ball_self zero_lt_two⟩ := by
      apply Subtype.ext
      simp only [w, n, Real.smoothTransition.one, sub_self, zero_smul]
    change T.tube 0 (C.longitudinal.diffeomorph z, w (1, z)) = _
    rw [hw1]
    exact T.core 0 (C.longitudinal.diffeomorph z)
  · intro t
    exact smooth_sphere_tube_graph_embedding T C.longitudinal.diffeomorph
      (fun z => w (t, z)) (hw.comp (contMDiff_const.prodMk contMDiff_id))
  · intro t z
    exact ⟨w (t, z), hn (t, z), rfl⟩


theorem controlled_polygon_ambient_identification {K : OrientedKnot}
    {T : TubularNeighborhood K} {L : StereographicPlacement K}
    {δ : ℝ} (C : ControlledPolygon T L δ) (h1 : δ < 1) :
    ∃ A : Diffeomorph (𝓡 3) (𝓡 3) ThreeSphere ThreeSphere ∞,
      (∀ z, A (L.chart.symm (C.smoothing.curve z)) =
        K.component 0 (C.longitudinal.diffeomorph z)) ∧
      ∀ x ∉ Set.range (T.tube 0), A x = x := by
  obtain ⟨G, hG, hG0, hG1, hGemb, hGtube⟩ := controlled_normal_graph_family C h1
  let w : TubeDisk := ⟨EuclideanSpace.single 0 1, by
    change dist (EuclideanSpace.single 0 (1 : ℝ)) 0 < 2
    simp⟩
  let pole : ThreeSphere := T.tube 0 (1, w)
  have hpole (t : ℝ) (z : Circle) : G (t, z) ≠ pole := by
    obtain ⟨v, hv, hgraph⟩ := hGtube t z
    intro heq
    have hp := (T.smoothEmbedding 0).isEmbedding.injective
      (show T.tube 0 (C.longitudinal.diffeomorph z, v) = T.tube 0 (1, w) from
        hgraph.symm.trans heq)
    have hvw : v = w := congrArg Prod.snd hp
    rw [hvw] at hv
    simpa [w] using hv
  haveI : Fact (Module.finrank ℝ (Euc 4) = 3 + 1) := ⟨by simp [Euc]⟩
  let e : OpenPartialHomeomorph ThreeSphere (Euc 3) := stereographic' 3 pole
  have hes : e.source = {pole}ᶜ := stereographic'_source pole
  have het : e.target = univ := stereographic'_target pole
  have hem : e ∈ IsManifold.maximalAtlas (𝓡 3) ∞ ThreeSphere :=
    IsManifold.subset_maximalAtlas ⟨pole, rfl⟩
  have he : ContMDiffOn (𝓡 3) 𝓘(ℝ, Euc 3) ∞ e e.source :=
    contMDiffOn_of_mem_maximalAtlas hem
  have hei : ContMDiffOn 𝓘(ℝ, Euc 3) (𝓡 3) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hem
  have hsource (t : ℝ) (z : Circle) : G (t, z) ∈ e.source := by
    rw [hes]
    exact hpole t z
  let c : PartialDiffeomorph (𝓡 3) 𝓘(ℝ, Euc 3) ThreeSphere (Euc 3) ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := he
      contMDiffOn_invFun := hei }
  let F : ℝ × Circle → Euc 3 := fun q => e (G q)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, Euc 3) ∞ F := by
    intro q
    exact (he.contMDiffAt (e.open_source.mem_nhds (hsource q.1 q.2))).comp q (hG q)
  have hFemb (t : ℝ) : Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, Euc 3) ∞
      (fun z => F (t, z)) := by
    have hi : Manifold.IsImmersion (𝓡 1) 𝓘(ℝ, Euc 3) ∞
        (e ∘ (fun z => G (t, z))) :=
      (hGemb t).isImmersion.isLocalDiffeomorphOn_comp
        (fun y => c.isLocalDiffeomorphAt (𝓡 3) 𝓘(ℝ, Euc 3) ∞ (by
          obtain ⟨z, hz⟩ := y.property
          rw [← hz]
          exact hsource t z))
    refine ⟨hi, ?_⟩
    have hc : Continuous (fun z => F (t, z)) :=
      (hF.comp (contMDiff_const.prodMk contMDiff_id)).continuous
    exact (hc.isClosedEmbedding (fun z z' hz => (hGemb t).isEmbedding.injective
      (e.injOn (hsource t z) (hsource t z') hz))).isEmbedding
  let U : Set (Euc 3) := e '' (e.source ∩ Set.range (T.tube 0))
  have hU : IsOpen U := e.isOpen_image_source_inter (T.image_open 0)
  have hFU : F '' (Icc (0 : ℝ) 1 ×ˢ univ) ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨G q, ⟨hsource q.1 q.2, ?_⟩, rfl⟩
    obtain ⟨v, _, hv⟩ := hGtube q.1 q.2
    exact ⟨(C.longitudinal.diffeomorph q.2, v), hv.symm⟩
  obtain ⟨D, hD, hDi, hD0, htrack, S, hS, hSU, hfix⟩ :=
    Manifold.exists_contDiff_compact_ambient_isotopy_Icc hF.contMDiffOn
      (fun t _ => hFemb t) hU hFU
  obtain ⟨A, _, _, hformula, _, _, hAfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_chart_family
      e het he hei D hD hDi hS
      (fun t x hx => ⟨(hfix t).1 hx, (hfix t).2 hx⟩)
  refine ⟨A 1, ?_, ?_⟩
  · intro z
    have hident : D 1 (F (0, z)) = F (1, z) :=
      (htrack 1 ⟨by norm_num, le_rfl⟩ z).1
    have hA : A 1 (G (0, z)) = e.symm (D 1 (e (G (0, z)))) := by
      rw [(hformula 1 (G (0, z))).1]
      exact ite_eq_left (hsource 0 z)
    rw [show e (G (0, z)) = F (0, z) from rfl, hident] at hA
    change A 1 (G (0, z)) = e.symm (e (G (1, z))) at hA
    rw [e.left_inv (hsource 1 z)] at hA
    simpa only [hG0, hG1] using hA
  · intro x hx
    apply (hAfix 1 x ?_).1
    rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hez⟩ := hSU hy
    have hcancel : e.symm y = z := by rw [← hez]; exact e.left_inv hz.1
    exact hx (hcancel.symm ▸ hz.2)

end
end SeifertSurfaces.LongitudeProducers
