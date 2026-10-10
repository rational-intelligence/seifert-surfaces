import B1InteriorSliceChartRestriction_v475
import B1InteriorGraphGermTransfer_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- An actual common slice graph admits a height cylinder excluding every
other sheet of both original embeddings. -/
theorem native_interior_common_graph_cylinder_v475
    {S : CompactOrientedSurface.{u}} {B : CompactOrientedSurface.{v}}
    (f : NeatEmbedding S E.Carrier) (g : NeatEmbedding B E.Carrier)
    (r : E.Carrier) (hrI : r ∈ (𝓡∂ 3).interior E.Carrier)
    (Φ Ψ : OpenPartialHomeomorph ThreeSphere (E2 × ℝ))
    (hΦ : ContMDiffOn (𝓡 3) 𝓘(ℝ,E2 × ℝ) ∞ Φ Φ.source)
    (hΦi : ContMDiffOn 𝓘(ℝ,E2 × ℝ) (𝓡 3) ∞ Φ.symm Φ.target)
    (hrΦ : E.toSphere r ∈ Φ.source) (hrΨ : E.toSphere r ∈ Ψ.source)
    (hA : Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) =
      Φ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (hB : Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) =
      Ψ.target ∩ (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)))
    (p : E2) (e : OpenPartialHomeomorph E2 E2) (u : E2 → ℝ)
    (hp : p ∈ e.source) (hrpair : Ψ (E.toSphere r)=(p,0))
    (heO : e.source ⊆ {z : E2 | (z,0) ∈ Ψ.target ∧ Ψ.symm (z,0) ∈ Φ.source} ∩
      interior (range (𝓡∂ 2)))
    (hu : ContDiffOn ℝ ∞ u e.target) (hup : u (e p)=0)
    (hgraph : ∀ z ∈ e.target, Φ (Ψ.symm (e.symm z,0))=(z,u z))
    (hgraphS : ∀ z ∈ e.source, Φ (Ψ.symm (z,0))=(e z,u (e z)))
    (hebase : e p ∈ interior (range (𝓡∂ 2))) :
    ∃ c : SmoothAmbientChart ThreeSphere, ∃ O : Set E2, ∃ η : ℝ,
      IsOpen O ∧ e p ∈ O ∧ O ⊆ e.target ∧ 0 < η ∧
      c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier ∧
      c.chart.target = native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-η) η) ∧
      (∀ a, c.chart a=native_interior_graph_splitting_v475 (Φ a)) ∧
      (∀ y, c.chart.symm y=Φ.symm (native_interior_graph_splitting_v475.symm y)) ∧
      (∀ z ∈ O, jetPoint (z,0,0) ∈ c.chart.target ∧ jetPoint (z,u z,0) ∈ c.chart.target) ∧
      (∀ z ∈ O, c.chart.symm (jetPoint (z,0,0)) ∈ range (E.toSphere ∘ f.toFun)) ∧
      (∀ z ∈ O, c.chart.symm (jetPoint (z,u z,0)) ∈ range (E.toSphere ∘ g.toFun)) ∧
      (∀ a : S, E.toSphere (f.toFun a) ∈ c.chart.source →
        (c.chart (E.toSphere (f.toFun a))) 2=0) ∧
      (∀ a : B, E.toSphere (g.toFun a) ∈ c.chart.source →
        (c.chart (E.toSphere (g.toFun a))) 2=
        u (native_collar_base_v475 (c.chart (E.toSphere (g.toFun a))))) := by
  classical
  let U := (Φ.source ∩ (Ψ.source ∩ Ψ ⁻¹' (Prod.fst ⁻¹' e.source))) ∩
    (E.toSphere '' (𝓡∂ 3).interior E.Carrier)
  have hU : IsOpen U := (Φ.open_source.inter
    (Ψ.isOpen_inter_preimage (e.open_source.preimage continuous_fst))).inter
      native_actual_exterior_interior_image_open_v475
  have hrU : E.toSphere r ∈ U := by
    refine ⟨⟨hrΦ,hrΨ,?_⟩,⟨r,hrI,rfl⟩⟩
    change (Ψ (E.toSphere r)).1 ∈ e.source
    rwa [hrpair]
  obtain ⟨c₀,hc₀U,hc₀,hc₀i⟩ := native_interior_slice_chart_restriction_v475 Φ hΦ hΦi
    U hU (fun a ha => ha.1.1)
  have hrΦpair : Φ (E.toSphere r)=(e p,0) := by
    have hh := hgraphS p hp
    rw [← hrpair,Ψ.left_inv hrΨ,hup] at hh
    exact hh
  have hrT : native_interior_graph_splitting_v475 (e p,0) ∈ c₀.chart.target := by
    rw [← hrΦpair,← hc₀]
    exact c₀.chart.map_source (hc₀U ▸ hrU)
  let Z := native_interior_graph_splitting_v475 ⁻¹' c₀.chart.target
  have hZ : IsOpen Z := c₀.chart.open_target.preimage native_interior_graph_splitting_v475.continuous
  obtain ⟨N,I,hN,hpN,hI,h0I,hNI⟩ := mem_nhds_prod_iff'.mp (hZ.mem_nhds hrT)
  obtain ⟨η,hη,hηI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds h0I)
  have hinterval : Ioo (-η) η ⊆ I := by
    intro t ht
    apply hηI
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt] using (show -η < t ∧ t < η from ht)
  let O := ((N ∩ e.target) ∩ interior (range (𝓡∂ 2))) ∩ u ⁻¹' Ioo (-η) η
  have hO' : IsOpen O := by
    have hh : IsOpen (e.target ∩ u ⁻¹' Ioo (-η) η) :=
      hu.continuousOn.isOpen_inter_preimage e.open_target isOpen_Ioo
    simpa [O,inter_assoc,inter_left_comm,inter_comm] using
      ((hN.inter (isOpen_interior : IsOpen (interior (range (𝓡∂ 2))))).inter hh)
  have hpO : e p ∈ O := by
    exact ⟨⟨⟨hpN,e.map_source hp⟩,hebase⟩,by change -η < u (e p) ∧ u (e p) < η; rw [hup]; exact ⟨by linarith,hη⟩⟩
  let V := native_interior_graph_splitting_v475 '' (O ×ˢ Ioo (-η) η)
  have hV : IsOpen V := native_interior_graph_splitting_v475.toHomeomorph.isOpenMap _
    (hO'.prod isOpen_Ioo)
  have hVc : V ⊆ c₀.chart.target := by
    rintro y ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    exact hNI ⟨hz.1.1.1,hinterval ht⟩
  obtain ⟨c,hcV,hcc,hc,hci,hcsource⟩ := native_interior_chart_restrict_target_v475 c₀ V hV hVc
  have hcΦ : ∀ a, c.chart a=native_interior_graph_splitting_v475 (Φ a) :=
    fun a => (hc a).trans (hc₀ a)
  have hciΦ : ∀ y, c.chart.symm y=Φ.symm (native_interior_graph_splitting_v475.symm y) :=
    fun y => (hci y).trans (hc₀i y)
  have hcU : c.chart.source ⊆ U := by intro a ha; rw [← hc₀U]; exact hcc ha
  have hpoints (z : E2) (hz : z ∈ O) :
      jetPoint (z,0,0) ∈ c.chart.target ∧ jetPoint (z,u z,0) ∈ c.chart.target := by
    rw [hcV]
    exact ⟨⟨(z,0),⟨hz,by exact ⟨by linarith,hη⟩⟩,rfl⟩,
      ⟨(z,u z),⟨hz,hz.2⟩,rfl⟩⟩
  have hsplit (z : E2) (t : ℝ) : native_interior_graph_splitting_v475.symm (jetPoint (z,t,0))=(z,t) :=
    native_interior_graph_splitting_v475.symm_apply_apply (z,t)
  have hbase (z : E2) (t : ℝ) : native_collar_base_v475 (jetPoint (z,t,0))=z := by
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    fin_cases i <;> simp [native_collar_base_v475,jetPoint]
  refine ⟨c,O,η,hO',hpO,(fun z hz => hz.1.1.2),hη,(fun a ha => (hcU ha).2),hcV,
    hcΦ,hciΦ,hpoints,?_,?_,?_,?_⟩
  · intro z hz
    have ht := (hpoints z hz).1
    have hs := (hcU (c.chart.map_target ht)).1.1
    have hcoord : Φ (c.chart.symm (jetPoint (z,0,0)))=(z,0) := by
      apply native_interior_graph_splitting_v475.injective
      rw [← hcΦ,c.chart.right_inv ht]
      rfl
    have hh : (z,0) ∈ Φ '' (Φ.source ∩ range (E.toSphere ∘ f.toFun)) := by
      rw [hA]
      exact ⟨hcoord ▸ Φ.map_source hs,interior_subset hz.1.2,rfl⟩
    obtain ⟨a,⟨ha,haR⟩,heq⟩ := hh
    rwa [Φ.injOn ha hs (heq.trans hcoord.symm)] at haR
  · intro z hz
    have he := e.map_target hz.1.1.2
    have hh := heO he
    have hparam := hgraph z hz.1.1.2
    have hsym : c.chart.symm (jetPoint (z,u z,0))=Ψ.symm (e.symm z,0) := by
      rw [hciΦ,hsplit,← hparam,Φ.left_inv hh.1.2]
    rw [hsym]
    have hmem : (e.symm z,0) ∈ Ψ '' (Ψ.source ∩ range (E.toSphere ∘ g.toFun)) := by
      rw [hB]
      exact ⟨hh.1.1,interior_subset hh.2,rfl⟩
    obtain ⟨a,⟨ha,haR⟩,heq⟩ := hmem
    rwa [← heq,Ψ.left_inv ha]
  · intro a ha
    have huA := (hcU ha).1.1
    have hh : Φ (E.toSphere (f.toFun a)) ∈ Φ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hA]
      exact mem_image_of_mem Φ ⟨huA,⟨a,rfl⟩⟩
    rw [hcΦ]
    simpa [jetPoint] using hh.2.2
  · intro a ha
    have huB := (hcU ha).1.2
    have hh : Ψ (E.toSphere (g.toFun a)) ∈ Ψ.target ∩
        (range (𝓡∂ 2) ×ˢ ({0}:Set ℝ)) := by
      rw [← hB]
      exact mem_image_of_mem Ψ ⟨huB.1,⟨a,rfl⟩⟩
    let z := (Ψ (E.toSphere (g.toFun a))).1
    have hpair : Ψ (E.toSphere (g.toFun a))=(z,0) := Prod.ext rfl hh.2.2
    have hg := hgraphS z huB.2
    rw [← hpair,Ψ.left_inv huB.1] at hg
    rw [hcΦ,hg]
    change u (e z)=u (native_collar_base_v475 (jetPoint (e z,u (e z),0)))
    rw [hbase]

#print axioms native_interior_common_graph_cylinder_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
