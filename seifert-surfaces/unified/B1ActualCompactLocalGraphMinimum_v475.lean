import B1ActualSurfaceFlowStationarity_v475
import B1ActualCollarGraphUniqueness_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.MetricFoundations.AreaAnalysis
open SeifertSurfaces.AppendixACoordinates
universe u v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem native_varied_planar_gradient_v475
    (u φ : E2 → ℝ) (x : E2) (hu : DifferentiableAt ℝ u x)
    (hφ : DifferentiableAt ℝ φ x) (t : ℝ) :
    planarGradient (fun z => u z+t*φ z) x = planarGradient u x+t • planarGradient φ x := by
  have hd : fderiv ℝ (fun z => u z+t*φ z) x = fderiv ℝ u x+t • fderiv ℝ φ x := by
    convert (hu.hasFDerivAt.add (hφ.hasFDerivAt.const_mul t)).fderiv using 1
  unfold planarGradient
  simp only [hd,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    add_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_smul]

/-- Every compact test inside one recovered surface chart is an actual
admissible native ambient variation of that original minimum. -/
theorem actual_compact_local_graph_minimum_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (hmin : ∀ X : NativeInteriorSmoothVectorField_v475 E,
      IsLocalMin (fun t => area g (native_actual_exterior_flow_v475 X t ∘ f.toFun)) 0)
    (u : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u W.U)
    (hheight : ∀ x ∈ halfDisc W.R, |u x| < D.eta)
    (hjets : ∀ x ∈ halfDisc W.R, jetPoint (x,u x,planarGradient u x) ∈ W.V)
    (q : E2 → S) (hq : ContMDiffOn 𝓘(ℝ,E2) (𝓡∂ 2) ∞ q (halfDisc W.R))
    (hqgraph : ∀ x ∈ halfDisc W.R, f.toFun (q x) = localCollar D s (jetPoint (x,u x,0)))
    (hqi : ∀ x ∈ halfDisc W.R, q x ∉ S.boundary)
    (hgraph : ∀ y ∈ collarDomain D W.R, localCollar D s y ∈ f.image →
      y 2 = u (native_collar_base_v475 y))
    (p : S) (O : Set E2) (hO : IsOpen O) (hOhalf : O ⊆ halfDisc W.R)
    (hqs : MapsTo q O (surfaceChart p).source)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    IsLocalMin (fun t => ∫ x in tsupport φ,
      W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) 0 := by
  let A := tsupport φ
  have hA : IsCompact A := hφc
  have hAhalf : A ⊆ halfDisc W.R := hφO.trans hOhalf
  have hhalfU : halfDisc W.R ⊆ W.U := fun x hx =>
    W.U_contains ⟨Metric.ball_subset_closedBall hx.1,hx.2.le⟩
  obtain ⟨c,X,χ,hχ,hχc,hχone,hsrc,hcoord,hX,hXs,hc⟩ :=
    actual_compact_graph_vertical_field_v475 D s W A hA hAhalf u φ hu
      (fun x hx => hheight x (hAhalf hx)) hφ
  have hinv (x : E2) (hx : x ∈ A) :
      c.chart.symm (jetPoint (x,u x,0)) = E.toSphere (localCollar D s (jetPoint (x,u x,0))) := by
    conv_lhs => rw [← hcoord x hx]
    exact c.chart.left_inv (hsrc x hx)
  have htarget (x : E2) (hx : x ∈ A) : jetPoint (x,u x,0) ∈ c.chart.target := by
    rw [← hcoord x hx]
    exact c.chart.map_source (hsrc x hx)
  have himage : ((fun x => c.chart.symm (jetPoint (x,u x,0))) '' A) =
      ((fun x => E.toSphere (localCollar D s (jetPoint (x,u x,0)))) '' A) := by
    exact image_congr hinv
  have hχone' : χ =ᶠ[𝓝ˢ ((fun x => c.chart.symm (jetPoint (x,u x,0))) '' A)] 1 := by
    rw [himage]
    exact hχone
  obtain ⟨δ,G,hδ,hG,hAG,hGU,hflow⟩ := native_compact_vertical_graph_flow_v475 c X χ A W.U
    hA W.U_open (hAhalf.trans hhalfU) u φ hu hφ htarget hχone' hX
  obtain ⟨Q,V,hQ,h0Q,hV,hAV,hVU,hvaried⟩ := actual_compact_graph_jet_tube_v475 D s W
    A W.U hA W.U_open (hAhalf.trans hhalfU) u φ hu hφ (fun x hx => hjets x (hAhalf hx))
  let N := O ∩ G ∩ V
  have hN : IsOpen N := (hO.inter hG).inter hV
  have hAN : A ⊆ N := fun x hx => ⟨⟨hφO hx,hAG hx⟩,hAV hx⟩
  have hNhalf : N ⊆ halfDisc W.R := fun x hx => hOhalf hx.1.1
  have hNU : N ⊆ W.U := fun x hx => hGU hx.1.2
  have hqinj : InjOn q N := (actual_graph_parameter_injOn_v475 D s W f u q hheight hqgraph).mono hNhalf
  have hzero := native_actual_chart_field_support_on_graph_v475 D s W f q u φ A
    (Subset.refl _) (fun x hx => hqgraph x (hAhalf hx)) c X χ hX hXs hc hgraph
  have hunchanged (t : ℝ) : EqOn f.toFun (native_actual_exterior_flow_v475 X t ∘ f.toFun) (q '' A)ᶜ := by
    intro z hz
    exact (native_actual_exterior_flow_eq_self_v475 X (f.toFun z) (hzero z hz) t).symm
  let Q0 := Ioo (-δ) δ ∩ Q
  have hQ0 : IsOpen Q0 := isOpen_Ioo.inter hQ
  have h0Q0 : (0 : ℝ) ∈ Q0 := ⟨⟨neg_neg_of_pos hδ,hδ⟩,h0Q⟩
  have hchange (t : ℝ) (ht : t ∈ Q0) :
      area g (native_actual_exterior_flow_v475 X t ∘ f.toFun) - area g f.toFun =
      (∫ x in A, W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) -
      (∫ x in A, W.density (x,u x,planarGradient u x)) := by
    have hmap (x : E2) (hx : x ∈ N) :
        native_actual_exterior_flow_v475 X t (f.toFun (q x)) =
          localCollar D s (jetPoint (x,u x+t*φ x,0)) := by
      have hh := hflow t ht.1 x hx.1.2
      apply Subtype.ext
      change E.toSphere (native_actual_exterior_flow_v475 X t (f.toFun (q x))) =
        E.toSphere (localCollar D s (jetPoint (x,u x+t*φ x,0)))
      rw [native_actual_exterior_flow_sphere_v475,hqgraph x (hNhalf hx)]
      have hinvx : c.chart.symm (jetPoint (x,u x,0)) =
          E.toSphere (localCollar D s (jetPoint (x,u x,0))) := by
        simpa only [zero_mul,add_zero] using (hc _ (hflow 0 h0Q0.1 x hx.1.2).1).2.2
      rw [← hinvx,hh.2]
      exact (hc _ hh.1).2.2
    have hgrad (x : E2) (hx : x ∈ N) := native_varied_planar_gradient_v475 u φ x
      ((hu.contDiffAt (W.U_open.mem_nhds (hNU hx))).differentiableAt (by simp))
      ((hφ.differentiable (by simp)).differentiableAt) t
    have hformula := actual_graph_parameter_area_change_v475 D s W f.toFun
      (native_actual_exterior_flow_v475 X t ∘ f.toFun) f.smooth
      ((native_actual_exterior_flow_v475 X t).contMDiff.comp f.smooth) p q N A hN hA hAN hNhalf
      (hq.mono hNhalf) (fun x hx => hqs hx.1.1) (fun x hx => hqi x (hNhalf hx)) hqinj
      u (fun x => u x+t*φ x) (hu.mono hNU) ((hu.mono hNU).add (contDiffOn_const.mul hφ.contDiffOn))
      (fun x hx => hqgraph x (hNhalf hx)) hmap (fun x hx => hheight x (hAhalf hx))
      (fun x hx => by simpa [jetPoint] using (hc _ (hflow t ht.1 x (hAG hx)).1).1.2.2)
      (fun x hx => hjets x (hAhalf hx))
      (fun x hx => by rw [hgrad x (hAN hx)]; exact hvaried t ht.2 x (hAV hx)) (hunchanged t)
    rw [hformula]
    congr 1
    apply setIntegral_congr_fun hA.measurableSet
    intro x hx
    change W.density (x,u x+t*φ x,planarGradient (fun z => u z+t*φ z) x) = _
    rw [hgrad x (hAN hx)]
  have hm := hmin X
  change ∀ᶠ t in 𝓝 (0 : ℝ), _ at hm ⊢
  filter_upwards [hm,hQ0.mem_nhds h0Q0] with t ht htQ
  have hc0 := hchange 0 h0Q0
  have hct := hchange t htQ
  have harea0 : area g (native_actual_exterior_flow_v475 X 0 ∘ f.toFun) = area g f.toFun := by
    congr 1
    funext z
    exact native_actual_exterior_flow_zero_v475 X (f.toFun z)
  rw [harea0] at ht
  simpa only [zero_mul,add_zero,zero_smul] using (show
    (∫ x in A, W.density (x,u x,planarGradient u x)) ≤
      (∫ x in A, W.density (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) by linarith [hct])

#print axioms native_varied_planar_gradient_v475
#print axioms actual_compact_local_graph_minimum_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
