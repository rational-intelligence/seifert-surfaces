import B1ActualChartFlow_v475
import B1ActualVerticalField_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
open DifferentialGeometry.Analysis.ODE
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- A supported chart field is exactly the requested vertical graph variation
for a uniform time interval around an entire compact base support. -/
theorem native_compact_vertical_graph_flow_v475
    (c : SmoothAmbientChart ThreeSphere) (X : NativeInteriorSmoothVectorField_v475 E)
    (χ : ThreeSphere → ℝ) (A O : Set E2) (hA : IsCompact A)
    (hO : IsOpen O) (hAO : A ⊆ O) (u φ : E2 → ℝ)
    (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hgraph : ∀ x ∈ A, jetPoint (x,u x,0) ∈ c.chart.target)
    (hχone : χ =ᶠ[𝓝ˢ ((fun x => c.chart.symm (jetPoint (x,u x,0))) '' A)] 1)
    (hX : ∀ q ∈ c.chart.source,
      chartDifferential c q (X.field q) =
        χ q • (φ (native_collar_base_v475 (c.chart q)) • coordinateVector 3 2)) :
    ∃ δ G, 0 < δ ∧ IsOpen G ∧ A ⊆ G ∧ G ⊆ O ∧
      ∀ t ∈ Ioo (-δ) δ, ∀ x ∈ G,
        jetPoint (x,u x+t*φ x,0) ∈ c.chart.target ∧
        curveAt X.field (native_actual_field_complete_v475 X)
          (c.chart.symm (jetPoint (x,u x,0))) t =
            c.chart.symm (jetPoint (x,u x+t*φ x,0)) := by
  obtain ⟨N,hN,hAN,hNχ⟩ := eventually_nhdsSet_iff_exists.mp hχone
  let V : Set E3 := c.chart.target ∩ c.chart.symm ⁻¹' N
  have hV : IsOpen V := c.inverse_smooth.continuousOn.isOpen_inter_preimage c.chart.open_target hN
  let ψ : ℝ × E2 → E3 := fun p => jetPoint (p.2,u p.2+p.1*φ p.2,0)
  have hψ : ContDiffOn ℝ ∞ ψ (univ ×ˢ O) := by
    unfold ψ jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_snd).contDiffOn
    · exact ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_snd).contDiffOn
    · exact (hu.comp contDiffOn_snd (fun p hp => hp.2)).add
        (contDiffOn_fst.mul (hφ.comp contDiff_snd).contDiffOn)
  let P := (univ ×ˢ O) ∩ ψ ⁻¹' V
  have hP : IsOpen P := hψ.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hO) hV
  have hAP : ({(0 : ℝ)} : Set ℝ) ×ˢ A ⊆ P := by
    intro p hp
    have hp0 : p.1 = 0 := mem_singleton_iff.mp hp.1
    refine ⟨⟨mem_univ _,hAO hp.2⟩,?_⟩
    change ψ p ∈ V
    simp only [ψ,hp0,zero_mul,add_zero]
    exact ⟨hgraph p.2 hp.2,hAN ⟨p.2,hp.2,rfl⟩⟩
  obtain ⟨Q,G,hQ,hG,h0Q,hAG,hQGP⟩ := generalized_tube_lemma isCompact_singleton hA hP hAP
  have h0 : (0 : ℝ) ∈ Q := h0Q (mem_singleton 0)
  obtain ⟨δ,hδ,hδQ⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h0)
  have htime : Ioo (-δ) δ ⊆ Q := by
    intro t ht
    apply hδQ
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_lt,mem_Ioo] using ht
  have hGO : G ⊆ O := fun x hx =>
    (hQGP (show (0,x) ∈ Q ×ˢ G from ⟨h0,hx⟩)).1.2
  have hvary : ∀ t ∈ Ioo (-δ) δ, ∀ x ∈ G,
      ψ (t,x) ∈ c.chart.target ∧ χ (c.chart.symm (ψ (t,x))) = 1 := by
    intro t ht x hx
    have hh := (hQGP (show (t,x) ∈ Q ×ˢ G from ⟨htime ht,hx⟩)).2
    exact ⟨hh.1,hNχ _ hh.2⟩
  refine ⟨δ,G,hδ,hG,hAG,hGO,?_⟩
  intro t ht x hx
  refine ⟨(hvary t ht x hx).1,?_⟩
  have hderiv : ∀ τ ∈ Ioo (-δ) δ, HasDerivAt (fun τ => ψ (τ,x))
      (chartDifferential c (c.chart.symm (ψ (τ,x))) (X.field (c.chart.symm (ψ (τ,x))))) τ := by
    intro τ hτ
    have htarget := (hvary τ hτ x hx).1
    have hc := hX (c.chart.symm (ψ (τ,x))) (c.chart.map_target htarget)
    rw [c.chart.right_inv htarget,(hvary τ hτ x hx).2,one_smul] at hc
    have hbase : native_collar_base_v475 (ψ (τ,x)) = x := by
      ext i
      fin_cases i <;> simp [native_collar_base_v475,ψ,jetPoint]
    rw [hc,hbase]
    have heq : (fun τ => ψ (τ,x)) =
        (fun τ => jetPoint (x,u x,0) + (τ * φ x) • coordinateVector 3 2) := by
      funext τ
      ext i
      fin_cases i <;> simp [ψ,jetPoint,coordinateVector,EuclideanSpace.single]
    rw [heq]
    simpa only [id_eq,one_mul] using
      (((hasDerivAt_id τ).mul_const (φ x)).smul_const (coordinateVector 3 2)).const_add
        (jetPoint (x,u x,0))
  have hh := native_actual_chart_flow_of_curve_v475 X c (fun τ => ψ (τ,x)) (-δ) δ
    (by exact ⟨neg_neg_of_pos hδ,hδ⟩) (fun τ hτ => (hvary τ hτ x hx).1) hderiv t ht
  simpa only [ψ,zero_mul,add_zero] using hh

#print axioms native_compact_vertical_graph_flow_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
