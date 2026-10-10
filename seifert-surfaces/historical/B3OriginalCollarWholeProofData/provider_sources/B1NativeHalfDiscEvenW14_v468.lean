import B1NativeHalfDiscL4_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open ChartMetricProvider.Variational.DirectWeak
open BoundaryContinuation BoundarySupport
set_option maxHeartbeats 1000000

/-- Boundary H2 gives a supercritical full-ball Sobolev extension. The weak
derivative is identified on the two open halves; the flat plane is null. -/
theorem native_halfdisc_even_W14_v468 (R : ℝ) (hR : 0<R) (u : E2 → ℝ)
    (hs : ContDiffOn ℝ ∞ u (halfDisc R)) (hu : MemWkp 2 2 u (halfDisc R)) :
    DeGiorgi.MemW1p 4 (fun x => if 0≤x 1 then u x else u (reflect x)) (Metric.ball 0 R) := by
  classical
  let U := halfDisc R
  let V := Metric.ball (0:E2) R ∩ {x : E2 | x 1<0}
  let f : E2 → ℝ := fun x => if 0≤x 1 then u x else u (reflect x)
  let A : E2 ≃ₗᵢ[ℝ] E2 := LinearIsometryEquiv.piLpCongrRight 2
    (fun i : Fin 2 => if i=1 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  let P : E2 ≃L[ℝ] E2 := A.toContinuousLinearEquiv
  have hP (x : E2) : P x=reflect x := by
    ext i
    fin_cases i <;> simp [P,A,reflect]
  have hRR (x : E2) : reflect (reflect x)=x := by
    ext i
    fin_cases i <;> simp [reflect]
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous)
  have hV : IsOpen V := Metric.isOpen_ball.inter
    (isOpen_lt (EuclideanSpace.proj (𝕜:=ℝ) (1:Fin 2)).continuous continuous_const)
  have hpre : P ⁻¹' U=V := by
    ext x
    simp only [mem_preimage,U,V,mem_inter_iff,Metric.mem_ball,dist_zero_right,hP]
    have hn : ‖reflect x‖=‖x‖ := by rw [←hP]; exact A.norm_map x
    change (dist (reflect x) 0<R ∧ 0 < reflect x 1) ↔ (‖x‖<R ∧ x 1<0)
    rw [dist_zero_right,hn]
    have hr1 : reflect x 1= -x 1 := by simp [reflect]
    rw [hr1]
    constructor <;> intro hx <;> exact ⟨hx.1,by linarith [hx.2]⟩
  have he := native_halfdisc_even_H1_v468 R u hs hu.memW1p
  let hw := he.someWitness
  have hnative := regular_witness_native_H1_v468 _ f hw
  have hn := native_smooth_memW1p_H1_v468 U hU u hs hu.memW1p
  have hpull := linear_h1_pullback U P u (planarGradient u) hn
  rw [hpre] at hpull
  have hsv : ContDiffOn ℝ ∞ (fun y => u (P y)) V := by
    apply hs.comp P.contDiff.contDiffOn
    intro y hy
    rw [←hpre] at hy
    exact hy
  have hEqU : hw.weakGrad =ᵐ[volume.restrict U] planarGradient u := by
    apply native_smooth_gradient_ae_v468 U hU f u _
      (h1_restrict_subset _ _ (fun x hx => hx.1) f _ hnative) hs
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact if_pos hx.2.le
  have hEqV : hw.weakGrad =ᵐ[volume.restrict V]
      (fun y => P.toContinuousLinearMap.adjoint (planarGradient u (P y))) := by
    have h1 := native_smooth_gradient_ae_v468 V hV f (fun y => u (P y)) _
      (h1_restrict_subset _ _ (fun x hx => hx.1) f _ hnative) hsv (by
        filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
        dsimp only [f]
        rw [if_neg (not_le.mpr hx.2),hP])
    have h2 := native_smooth_gradient_ae_v468 V hV (fun y => u (P y)) (fun y => u (P y)) _
      hpull hsv EventuallyEq.rfl
    exact h1.trans h2.symm
  have hG := native_halfdisc_H2_actual_gradient_L4_v468 R hR u hs hu
  have hGi : MemLp (U.indicator (planarGradient u)) 4 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet.nullMeasurableSet).mpr hG
  let dg : E2 → E2 := fun x => U.indicator (planarGradient u) x+
    P.toContinuousLinearMap.adjoint (U.indicator (planarGradient u) (P x))
  have hdg : MemLp dg 4 volume := hGi.add
    ((hGi.comp_measurePreserving A.measurePreserving).continuousLinearMap_comp P.toContinuousLinearMap.adjoint)
  have hwholeU := (ae_restrict_iff' hU.measurableSet).mp hEqU
  have hwholeV := (ae_restrict_iff' hV.measurableSet).mp hEqV
  have hflat : ∀ᵐ x : E2 ∂volume, x 1≠0 := by
    have hh : volume {x : E2 | x 1=0}=0 := by
      have hm := PiLp.volume_preserving_ofLp (Fin 2)
      calc
        volume {x : E2 | x 1=0}=volume {x : Fin 2 → ℝ | x 1=0} :=
          hm.measure_preimage (s:={x : Fin 2 → ℝ | x 1=0})
            ((isClosed_eq (continuous_apply 1) continuous_const).measurableSet.nullMeasurableSet)
        _ = 0 := Measure.pi_hyperplane (fun _ : Fin 2 => volume (α:=ℝ)) 1 0
    simpa only [ae_iff,not_not] using hh
  have hgrad : hw.weakGrad =ᵐ[volume.restrict (Metric.ball (0:E2) R)] dg := by
    filter_upwards [ae_restrict_of_ae hwholeU,ae_restrict_of_ae hwholeV,
      ae_restrict_of_ae hflat,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hxu hxv hxn hxb
    by_cases hp : 0<x 1
    · have hxU : x∈U := ⟨hxb,hp⟩
      have hxPU : P x∉U := by
        intro hx
        have hh := hx.2
        rw [hP] at hh
        change 0 < -x 1 at hh
        linarith
      rw [hxu hxU]
      simp only [dg,indicator_of_mem hxU,indicator_of_notMem hxPU,map_zero,add_zero]
    · have hxV : x∈V := ⟨hxb,lt_of_le_of_ne (not_lt.mp hp) hxn⟩
      have hxU : x∉U := fun hx => hp hx.2
      have hxPU : P x∈U := by
        change x∈P ⁻¹' U
        rw [hpre]
        exact hxV
      rw [hxv hxV]
      simp only [dg,indicator_of_notMem hxU,indicator_of_mem hxPU,zero_add]
  have hf4 := native_ball_H1_L4_v468 R hR f he
  refine ⟨hf4,?_⟩
  intro i
  refine ⟨fun x => hw.weakGrad x i,?_,hw.isWeakGrad i⟩
  apply ((hdg.restrict _).eval_piLp i).ae_eq
  exact hgrad.symm.mono fun x hx => congrArg (fun v : E2 => v i) hx
end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_halfdisc_even_W14_v468
