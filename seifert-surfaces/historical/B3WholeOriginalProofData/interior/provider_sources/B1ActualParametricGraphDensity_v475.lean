import B1ParameterAreaLocalization_v475
import B1ActualCollarTopology_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem native_graph_jet_differential_v475 (u : E2 → ℝ) (x : E2)
    (hu : DifferentiableAt ℝ u x) (i : Fin 2) :
    fderiv ℝ (fun z => jetPoint (z,u z,0)) x (coordinateVector 2 i) =
      jetTangent (planarGradient u x) i := by
  have hgraph : (fun z => jetPoint (z,u z,0)) =
      (fun z => z 0 • coordinateVector 3 0 + z 1 • coordinateVector 3 1 +
        u z • coordinateVector 3 2) := by
    funext z
    ext j
    fin_cases j <;> simp [jetPoint,coordinateVector,EuclideanSpace.single]
  rw [hgraph]
  have hd := (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt.smul_const
      (coordinateVector 3 0)).add
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt.smul_const
      (coordinateVector 3 1))).add (hu.hasFDerivAt.smul_const (coordinateVector 3 2))
  have hd' : HasFDerivAt (fun z : E2 => z 0 • coordinateVector 3 0 + z 1 • coordinateVector 3 1 +
      u z • coordinateVector 3 2)
      ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).smulRight (coordinateVector 3 0) +
        (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).smulRight (coordinateVector 3 1) +
        (fderiv ℝ u x).smulRight (coordinateVector 3 2)) x := by
    convert hd using 1 <;> rfl
  rw [hd'.fderiv]
  fin_cases i <;> simp [jetTangent,planarGradient,coordinateVector,EuclideanSpace.single,
    Fin.sum_univ_two]

/-- The supplied collar density is the literal induced metric density of the
actual graph parametrization at every interior point. -/
theorem actual_parametric_graph_density_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (u : E2 → ℝ) (x : E2) (hx : x ∈ halfDisc W.R)
    (hu : DifferentiableAt ℝ u x) (hheight : |u x| < D.eta)
    (hj : jetPoint (x,u x,planarGradient u x) ∈ W.V) :
    native_parametric_density_v475 g (fun z => localCollar D s (jetPoint (z,u z,0))) x =
      W.density (x,u x,planarGradient u x) := by
  let y : E3 := jetPoint (x,u x,0)
  have hb : ‖x‖ < W.R := by simpa only [disc,Metric.mem_ball,dist_zero_right] using hx.1
  have h0 : |x 0| < 2 * W.R := by
    have hc : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    linarith [W.R_pos]
  have hr := actual_halfdisc_radial_membership_v474 D s W x hx
  let V : Set E3 := {z | |z 0| < 2 * W.R ∧ z 1 ∈ Ioo (0 : ℝ) D.r0 ∧ |z 2| < D.eta}
  have hV : IsOpen V :=
    (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous.abs continuous_const).inter
      (((isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous)).inter
        (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.abs continuous_const))
  have hyV : y ∈ V := by simpa [V,y,jetPoint] using And.intro h0 (And.intro hr hheight)
  have hVC : V ⊆ collarDomain D W.R := fun z hz => ⟨hz.1,⟨hz.2.1.1.le,hz.2.1.2.le⟩,hz.2.2⟩
  have hC : collarDomain D W.R ∈ 𝓝 y := mem_of_superset (hV.mem_nhds hyV) hVC
  have hcollar : MDifferentiableAt 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) y :=
    ((actual_localCollar_smooth_v475 D s W.R).contMDiffAt hC).mdifferentiableAt (by simp)
  have hpoint : DifferentiableAt ℝ (fun z => jetPoint (z,u z,0)) x := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.differentiableAt.comp x
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).differentiableAt
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).differentiableAt
    · exact hu
  have hchain := mfderiv_comp x hcollar hpoint.mdifferentiableAt
  rw [mfderiv_eq_fderiv] at hchain
  let d := (mfderivWithin 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) (collarDomain D W.R) y) ∘L
    (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap
  have heval (i : Fin 2) :
      mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => localCollar D s (jetPoint (z,u z,0))) x
        ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 i)) =
          d (jetTangent (planarGradient u x) i) := by
    change mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) ((localCollar D s) ∘ (fun z => jetPoint (z,u z,0))) x
      ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 i)) = _
    rw [hchain]
    change mfderiv 𝓘(ℝ,E3) (𝓡∂ 3) (localCollar D s) y
      ((NormedSpace.fromTangentSpace y).symm
        (fderiv ℝ (fun z => jetPoint (z,u z,0)) x (coordinateVector 2 i))) = _
    rw [native_graph_jet_differential_v475 u x hu i]
    dsimp only [d]
    rw [mfderivWithin_of_mem_nhds hC]
    rfl
  have hmetric (v w : E3) : coordinateInner W.metric.tensor y v w =
      g.inner (localCollar D s y) (d v) (d w) := by
    have hv : v = ∑ i : Fin 3, v i • coordinateVector 3 i := by
      ext j
      simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
    have hw : w = ∑ i : Fin 3, w i • coordinateVector 3 i := by
      ext j
      simp [coordinateVector,EuclideanSpace.single,Pi.single_apply]
    have hy : y ∈ W.V ∩ collarDomain D W.R := ⟨hj,hVC hyV⟩
    conv_rhs => rw [hv,hw]
    simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,coordinateInner]
    simp only [Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj'
    rw [W.actual_metric y hy i j]
    change _ = _
    dsimp only [d,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    ring
  unfold native_parametric_density_v475 CollarWindow.density
  congr 2
  ext i j
  change g.inner (localCollar D s y)
    (mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => localCollar D s (jetPoint (z,u z,0))) x
      ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 i)))
    (mfderiv 𝓘(ℝ,E2) (𝓡∂ 3) (fun z => localCollar D s (jetPoint (z,u z,0))) x
      ((NormedSpace.fromTangentSpace x).symm (coordinateVector 2 j))) = _
  rw [heval,heval]
  exact (hmetric _ _).symm

#print axioms native_graph_jet_differential_v475
#print axioms actual_parametric_graph_density_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
