import B1InteriorGraphAreaChange_v475
import B1InteriorActualGraphField_v475
import B1ActualCompactLocalGraphMinimum_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- The genuine native minimum supplies compact minima in any actual
interior graph chart of the same metric, with whole-image support cancellation. -/
theorem native_interior_actual_compact_graph_minimum_v475
    (g : SmoothMetric E.Carrier) (c : SmoothAmbientChart ThreeSphere)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (χ : E3 → E.Carrier) (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target)
    (hχeq : ∀ y ∈ c.chart.target, E.toSphere (χ y)=c.chart.symm y)
    (H : CoordinateMetric c.chart.target) (hH : H.tensor=native_actual_lift_tensor_v475 g χ)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (hmin : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O)
    (q : E2 → S) (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q O)
    (hqgraph : ∀ x ∈ O, f.toFun (q x)=χ (jetPoint (x,u x,0)))
    (hqt : ∀ x ∈ O, jetPoint (x,u x,0) ∈ c.chart.target)
    (hqi : ∀ x ∈ O, q x ∉ S.boundary)
    (hgraph : ∀ z : S, E.toSphere (f.toFun z) ∈ c.chart.source →
      (c.chart (E.toSphere (f.toFun z))) 2 =
        u (native_collar_base_v475 (c.chart (E.toSphere (f.toFun z)))))
    (p : S) (hqs : MapsTo q O (surfaceChart p).source)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    IsLocalMin (fun t => ∫ x in tsupport φ,
      native_interior_graph_density_v475 H (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) 0 := by
  let A := tsupport φ
  have hA : IsCompact A := hφc
  have hAO : A ⊆ O := hφO
  obtain ⟨X,ρ,hρone,hXs,hX⟩ := native_interior_compact_graph_vertical_field_v475
    c hcE A O hA hAO u φ hu hφ (fun x hx => hqt x (hAO hx))
  obtain ⟨δ,G,hδ,hG,hAG,hGO,hflow⟩ := native_compact_vertical_graph_flow_v475
    c X ρ A O hA hO hAO u φ hu hφ (fun x hx => hqt x (hAO hx)) hρone hX
  have hqcoord (x : E2) (hx : x ∈ O) :
      E.toSphere (f.toFun (q x)) ∈ c.chart.source ∧
      c.chart (E.toSphere (f.toFun (q x)))=jetPoint (x,u x,0) := by
    rw [hqgraph x hx,hχeq _ (hqt x hx)]
    exact ⟨c.chart.map_target (hqt x hx),c.chart.right_inv (hqt x hx)⟩
  have hzero := native_interior_actual_chart_field_support_on_graph_v475 f c X ρ q u φ A
    (Subset.refl _) (fun x hx => hqcoord x (hAO hx)) hX hXs hgraph
  have hunchanged (t : ℝ) : EqOn f.toFun (native_actual_exterior_flow_v475 X t ∘ f.toFun) (q '' A)ᶜ := by
    intro z hz
    exact (native_actual_exterior_flow_eq_self_v475 X (f.toFun z) (hzero z hz) t).symm
  let N := O ∩ G
  have hN : IsOpen N := hO.inter hG
  have hAN : A ⊆ N := fun x hx => ⟨hAO hx,hAG hx⟩
  have hqinj : InjOn q N := by
    intro x hx y hy hxy
    have he : jetPoint (x,u x,0)=jetPoint (y,u y,0) :=
      (hqcoord x hx.1).2.symm.trans ((congrArg (fun a : S => c.chart (E.toSphere (f.toFun a))) hxy).trans
        (hqcoord y hy.1).2)
    have hb := congrArg native_collar_base_v475 he
    apply (EuclideanSpace.equiv (Fin 2) ℝ).injective
    funext i
    have hi := congrArg (fun z : E2 => z i) hb
    fin_cases i <;> simpa [native_collar_base_v475,jetPoint] using hi
  have hchange (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)-area g f.toFun =
      (∫ x in A, native_interior_graph_density_v475 H
        (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x))-
      (∫ x in A, native_interior_graph_density_v475 H (x,u x,planarGradient u x)) := by
    have hmap (x : E2) (hx : x ∈ N) :
        native_actual_exterior_flow_v475 X t (f.toFun (q x))=χ (jetPoint (x,u x+t*φ x,0)) := by
      apply Subtype.ext
      change E.toSphere (native_actual_exterior_flow_v475 X t (f.toFun (q x))) =
        E.toSphere (χ (jetPoint (x,u x+t*φ x,0)))
      rw [native_actual_exterior_flow_sphere_v475,hqgraph x hx.1,hχeq _ (hqt x hx.1),
        (hflow t ht x hx.2).2,hχeq _ (hflow t ht x hx.2).1]
    have hgrad (x : E2) (hx : x ∈ N) := native_varied_planar_gradient_v475 u φ x
      ((hu.contDiffAt (hO.mem_nhds hx.1)).differentiableAt (by simp))
      ((hφ.differentiable (by simp)).differentiableAt) t
    have hh := native_interior_graph_parameter_area_change_v475 g c.chart.target c.chart.open_target
      χ hχ H hH f.toFun (native_actual_exterior_flow_v475 X t ∘ f.toFun) f.smooth
      ((native_actual_exterior_flow_v475 X t).contMDiff.comp f.smooth) p q N A hN hA hAN
      (hq.mono inter_subset_left) (fun x hx => hqs hx.1) (fun x hx => hqi x hx.1) hqinj
      u (fun x => u x+t*φ x) (hu.mono inter_subset_left)
      ((hu.mono inter_subset_left).add (contDiffOn_const.mul hφ.contDiffOn))
      (fun x hx => hqgraph x hx.1) hmap (fun x hx => hqt x (hAO hx))
      (fun x hx => (hflow t ht x (hAG hx)).1) (hunchanged t)
    rw [hh]
    congr 1
    apply setIntegral_congr_fun hA.measurableSet
    intro x hx
    simp only [hgrad x (hAN hx)]
  have hm := hmin X
  change ∀ᶠ t in 𝓝 (0 : ℝ), _ at hm ⊢
  have htime : Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) := isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩
  filter_upwards [hm,htime] with t ht htQ
  have hct := hchange t htQ
  have harea0 : area g (native_actual_exterior_flow_v475 X 0 ∘ f.toFun)=area g f.toFun := by
    congr 1
    funext z
    exact native_actual_exterior_flow_zero_v475 X (f.toFun z)
  rw [harea0] at ht
  simpa only [zero_mul,add_zero,zero_smul] using (show
    (∫ x in A, native_interior_graph_density_v475 H (x,u x,planarGradient u x)) ≤
      (∫ x in A, native_interior_graph_density_v475 H
        (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) by linarith [hct])

#print axioms native_interior_actual_compact_graph_minimum_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
