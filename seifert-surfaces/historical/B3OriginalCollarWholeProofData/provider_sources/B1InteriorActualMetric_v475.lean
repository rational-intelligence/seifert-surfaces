import B1ActualInteriorLiftRank_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

def native_actual_lift_tensor_v475 (g : SmoothMetric E.Carrier) (χ : E3 → E.Carrier) : MetricTensor :=
  fun y i j => g.inner (χ y)
    (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)))
    (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 j)))

theorem native_actual_lift_coordinate_inner_v475
    (g : SmoothMetric E.Carrier) (χ : E3 → E.Carrier) (y : E3) (v w : E3) :
    coordinateInner (native_actual_lift_tensor_v475 g χ) y v w =
      g.inner (χ y)
        (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y ((NormedSpace.fromTangentSpace y).symm v))
        (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y ((NormedSpace.fromTangentSpace y).symm w)) := by
  let d := (mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y) ∘L
    (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap
  have hsum (v : E3) : v=∑ i : Fin 3, v i • coordinateVector 3 i := by
    ext j
    simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
  change coordinateInner (native_actual_lift_tensor_v475 g χ) y v w = g.inner (χ y) (d v) (d w)
  conv_rhs => rw [hsum v,hsum w]
  simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    smul_eq_mul,coordinateInner,native_actual_lift_tensor_v475]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [d,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  ring

/-- The common coordinate metric is the literal pullback of the supplied
exterior metric along the actual smooth chart lift. -/
theorem native_actual_lift_coordinate_metric_v475
    (g : SmoothMetric E.Carrier) (c : SmoothAmbientChart ThreeSphere) (χ : E3 → E.Carrier)
    (hχ : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3) ∞ χ c.chart.target)
    (heq : ∀ y ∈ c.chart.target, E.toSphere (χ y)=c.chart.symm y) :
    ∃ H : CoordinateMetric c.chart.target, H.tensor=native_actual_lift_tensor_v475 g χ := by
  have hvec (i : Fin 3) : ContMDiff 𝓘(ℝ,E3) (𝓘(ℝ,E3)).tangent ∞
      (fun y => (⟨y,(NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i)⟩ :
        TangentBundle 𝓘(ℝ,E3) E3)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    exact contDiff_const
  have htan (i : Fin 3) : ContMDiffOn 𝓘(ℝ,E3) (𝓡∂ 3).tangent ∞
      (fun y => (⟨χ y,mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) χ y
        ((NormedSpace.fromTangentSpace y).symm (coordinateVector 3 i))⟩ :
        TangentBundle (𝓡∂ 3) E.Carrier)) c.chart.target := by
    have hh := (hχ.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      c.chart.open_target.uniqueMDiffOn).comp (hvec i).contMDiffOn (fun y hy => hy)
    apply hh.congr
    intro y hy
    congr 1
    rw [mfderivWithin_of_mem_nhds (c.chart.open_target.mem_nhds hy)]
  have hcoeff (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => native_actual_lift_tensor_v475 g χ y i j) c.chart.target := by
    have hg := g.contMDiff.comp_contMDiffOn hχ
    have happ := hg.clm_bundle_apply₂ (F₁ := Euc 3) (F₂ := Euc 3) (F₃ := ℝ)
      (E₃ := Bundle.Trivial E.Carrier ℝ) (ψ := fun y => g.inner (χ y)) (htan i) (htan j)
    intro y hy
    have hscalar := (Bundle.contMDiffWithinAt_totalSpace.mp (happ y hy)).2
    simpa [native_actual_lift_tensor_v475] using hscalar.contDiffWithinAt
  refine ⟨⟨native_actual_lift_tensor_v475 g χ,hcoeff,?_,?_⟩,rfl⟩
  · intro y hy i j
    exact g.symm _ _ _
  · intro y hy v hv
    rw [native_actual_lift_coordinate_inner_v475]
    apply g.pos
    intro hh
    have hinj := native_actual_interior_lift_differential_injective_v475 c χ hχ heq y hy
    have hzero := hinj (hh.trans (map_zero _).symm)
    exact hv ((NormedSpace.fromTangentSpace y).symm.injective
      (hzero.trans ((NormedSpace.fromTangentSpace y).symm.map_zero).symm))

#print axioms native_actual_lift_coordinate_inner_v475
#print axioms native_actual_lift_coordinate_metric_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
