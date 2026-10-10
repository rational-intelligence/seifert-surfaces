import InitialCapLayerCake_v457
import InitialScalarNormalPolar_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
set_option maxHeartbeats 1000000
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_signed_layer" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialLayerCake_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.radial_signed_layer_cake_v457)⟩

local macro "paid_smooth_tail" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialLayerCake_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.smooth_radial_tail_v457)⟩

local macro "paid_cap_layer" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapLayerCake_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_cap_layer_cake_v457)⟩

local macro "paid_patch_layer" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialCapLayerCake_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.native_circle_patch_layer_cake_v457)⟩

local macro "paid_normal_polar" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialScalarNormalPolar_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_scalar_normal_polar_v457)⟩

local macro "paid_original_radial_green" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialNormalGreen_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.original_squared_radius_normal_green_v457)⟩

private theorem radial_cumulative_integrable_v457
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [SFinite mu]
    (rho : X → ℝ) (hrho : Measurable rho)
    (g : X → ℝ) (hg : Integrable g mu) (a z : ℝ) :
    IntegrableOn (fun r=>∫ x in {x | rho x<r},g x ∂mu) (Ioo a z) := by
  let nu := volume.restrict (Ioo a z)
  let : IsFiniteMeasure nu := isFiniteMeasure_restrict.mpr
    ((measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top).ne
  have hw : Integrable (fun _ : ℝ=>(1:ℝ)) nu := integrable_const 1
  have hl := paid_signed_layer mu nu rho hrho g hg (fun _=>1) hw
  simpa only [one_mul,nu,IntegrableOn] using hl.2.1

private theorem original_local_cap_green_fixed_test_ae_v457
    (f : E2 → E2) (d : Fin 2 → E2 → E2) (b : ℝ → E2)
    (H1 : ∀ i,H1On (disc 1) (fun x=>f x i) (d i))
    (green : HasGreenBoundaryTrace f d b)
    (p : E2) (a z : ℝ) (ha : 0<a) (haz : a<z) (hz : z<1)
    (psi : E2 → ℝ) (hpsi : ContDiff ℝ ∞ psi) (i j : Fin 2) :
    ∀ᵐ q ∂volume.restrict (Ioo a z),
      (∫ x in planarCap p q,f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x)=
        (q*∫ t in Ioo (-Real.pi) Real.pi,
          (disc 1).indicator (fun x=>f x i*psi x) (p+q•unitCircleParameter t)*unitCircleParameter t j)+
        ∫ t in circlePatch p q,b t i*psi (unitCircleParameter t)*unitCircleParameter t j := by
  classical
  let bulk : E2 → ℝ := fun x=>f x i*fderiv ℝ psi x (coordinateVector 2 j)+d i x j*psi x
  let bound : ℝ → ℝ := fun t=>b t i*psi (unitCircleParameter t)*unitCircleParameter t j
  let B : ℝ → ℝ := fun q=>∫ x in planarCap p q,bulk x
  let T : ℝ → ℝ := fun q=>∫ t in circlePatch p q,bound t
  let F : ℝ → ℝ := fun q=>q*∫ t in Ioo (-Real.pi) Real.pi,
    (disc 1).indicator (fun x=>f x i*psi x) (p+q•unitCircleParameter t)*unitCircleParameter t j
  have hbulk : IntegrableOn bulk (disc 1) := (green psi hpsi i j).1
  have hbound : IntegrableOn bound (Icc 0 (2*Real.pi)) := (green psi hpsi i j).2.1
  have hc : Continuous unitCircleParameter := by
    change Continuous (fun t : ℝ=>WithLp.toLp 2 ![Real.cos t,Real.sin t])
    fun_prop
  have hBI : IntegrableOn B (Ioo a z) := by
    have hmeas : Measurable (fun x:E2=>‖x-p‖) := by fun_prop
    have hl := radial_cumulative_integrable_v457 (volume.restrict (disc 1))
      (fun x:E2=>‖x-p‖) hmeas bulk hbulk a z
    have he (r : ℝ) : {x:E2 | ‖x-p‖<r} ∩ disc 1=planarCap p r := by
      ext x
      simp only [planarCap,mem_inter_iff,mem_ofPred_eq,Metric.mem_ball,dist_eq_norm]
      tauto
    simpa only [Measure.restrict_restrict (measurableSet_lt hmeas measurable_const),he,B] using hl
  have hTI : IntegrableOn T (Ioo a z) := by
    have hmeas : Measurable (fun t=>‖unitCircleParameter t-p‖) := ((hc.sub continuous_const).norm).measurable
    have hl := radial_cumulative_integrable_v457 (volume.restrict (Icc 0 (2*Real.pi)))
      (fun t=>‖unitCircleParameter t-p‖) hmeas bound hbound a z
    have he (r : ℝ) : {t | ‖unitCircleParameter t-p‖<r} ∩ Icc 0 (2*Real.pi)=circlePatch p r := by
      ext t
      simp only [circlePatch,mem_inter_iff,mem_ofPred_eq,Metric.mem_ball,dist_eq_norm]
      tauto
    simpa only [Measure.restrict_restrict (measurableSet_lt hmeas measurable_const),he,T] using hl
  have hpolar := paid_normal_polar f d H1 psi hpsi p a z ha haz hz i j
  dsimp only at hpolar
  have hFI : IntegrableOn F (Ioo a z) := hpolar.1
  let V : ℝ → ℝ := fun q=>B q-T q-F q
  have hv : LocallyIntegrableOn V (Ioo a z) volume :=
    (hBI.sub hTI |>.sub hFI).locallyIntegrableOn
  have hzero : ∀ᵐ q ∂volume.restrict (Ioo a z),V q=0 := by
    apply (CourantAnalyticB.annular_square_radius_tests_detect a z ha haz V hv).2
    intro h hh hhc hhs
    let chi : ℝ → ℝ := fun s=>∫ t in s..z^2,h t
    have hchi := paid_smooth_tail h hh (z^2)
    have hcap := paid_cap_layer p bulk hbulk h hh a z ha haz hhs
    have hpatch := paid_patch_layer p bound hbound h hh a z ha haz hhs
    have hnormal := hpolar.2 h hh hhc hhs
    have hG := paid_original_radial_green f d b H1 green p psi hpsi chi hchi.1 i j
    dsimp only at hG
    have hBm : IntegrableOn (fun q=>q*h (q^2)*B q) (Ioo a z) := by
      apply (hcap.1.const_mul (1/2:ℝ)).congr
      filter_upwards [] with q
      dsimp only [B]
      ring
    have hTm : IntegrableOn (fun q=>q*h (q^2)*T q) (Ioo a z) := by
      apply (hpatch.1.const_mul (1/2:ℝ)).congr
      filter_upwards [] with q
      dsimp only [T]
      ring
    have hFm : IntegrableOn (fun q=>q*h (q^2)*F q) (Ioo a z) := hnormal.2.1
    have hBval : (∫ x in disc 1,chi (‖x-p‖^2)*bulk x)=
        2*(∫ q in Ioo a z,q*h (q^2)*B q) := by
      have he : (∫ x in disc 1,chi (‖x-p‖^2)*bulk x)=
          ∫ x in disc 1,bulk x*chi (‖x-p‖^2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      rw [he,hcap.2]
      have he2 : (fun q=>2*q*h (q^2)*(∫ x in planarCap p q,bulk x))=
          (fun q=>2*(q*h (q^2)*B q)) := by funext q;dsimp only [B];ring
      rw [he2,integral_const_mul]
    have hTval : (∫ t in Icc 0 (2*Real.pi),bound t*chi (‖unitCircleParameter t-p‖^2))=
        2*(∫ q in Ioo a z,q*h (q^2)*T q) := by
      rw [hpatch.2]
      have he2 : (fun q=>2*q*h (q^2)*(∫ t in circlePatch p q,bound t))=
          (fun q=>2*(q*h (q^2)*T q)) := by funext q;dsimp only [T];ring
      rw [he2,integral_const_mul]
    have hFval : (∫ x in disc 1,2*deriv chi (‖x-p‖^2)*(f x i*psi x*(x j-p j)))=
        -2*(∫ q in Ioo a z,q*h (q^2)*F q) := by
      have he2 : (fun x=>2*deriv chi (‖x-p‖^2)*(f x i*psi x*(x j-p j)))=
          (fun x=>-2*(f x i*psi x*(x j-p j)*h (‖x-p‖^2))) := by
        funext x
        rw [hchi.2]
        ring
      rw [he2,integral_const_mul,hnormal.2.2]
    have heq := hG.2.2.2
    change (∫ x in disc 1,chi (‖x-p‖^2)*bulk x)+
      (∫ x in disc 1,2*deriv chi (‖x-p‖^2)*(f x i*psi x*(x j-p j)))=
      ∫ t in Icc 0 (2*Real.pi),bound t*chi (‖unitCircleParameter t-p‖^2) at heq
    rw [hBval,hFval,hTval] at heq
    have he3 : (fun q=>q*h (q^2)*V q)=
        (fun q=>(q*h (q^2)*B q-q*h (q^2)*T q)-q*h (q^2)*F q) := by
      funext q
      dsimp only [V]
      ring
    rw [he3]
    change (∫ q in Ioo a z,((fun q=>q*h (q^2)*B q)-(fun q=>q*h (q^2)*T q)) q-
      (fun q=>q*h (q^2)*F q) q)=0
    rw [integral_sub (hBm.sub hTm) hFm]
    simp only [Pi.sub_apply]
    rw [integral_sub hBm hTm]
    linarith
  filter_upwards [hzero] with q hq
  change B q=F q+T q
  dsimp only [V] at hq
  linarith

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
