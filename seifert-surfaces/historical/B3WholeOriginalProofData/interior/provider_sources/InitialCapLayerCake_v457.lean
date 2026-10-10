import InitialRadialTailSquare_v457

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
open SeifertSurfaces.AppendixACoordinates L1Independent

local macro "paid_signed_layer" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialLayerCake_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.radial_signed_layer_cake_v457)⟩
local macro "paid_square_tail" : term =>
  return ⟨Lean.mkIdent ((Lean.Name.num `_private.InitialRadialTailSquare_v457 0) ++
    `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.annular_square_tail_as_radial_indicator_v457)⟩

private theorem native_cap_layer_cake_v457
    (p : E2) (g : E2 → ℝ) (hg : IntegrableOn g (disc 1))
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (a z : ℝ) (ha : 0<a) (haz : a<z)
    (hhs : tsupport h ⊆ Ioo (a^2) (z^2)) :
    IntegrableOn (fun r=>2*r*h (r^2)*(∫ x in planarCap p r,g x)) (Ioo a z) ∧
    (∫ x in disc 1,g x*(∫ u in ‖x-p‖^2..z^2,h u))=
      ∫ r in Ioo a z,2*r*h (r^2)*(∫ x in planarCap p r,g x) := by
  classical
  let mu := volume.restrict (disc 1)
  let nu := volume.restrict (Ioo a z)
  let rho : E2 → ℝ := fun x=>‖x-p‖
  let w : ℝ → ℝ := fun r=>2*r*h (r^2)
  have hwi : Integrable w nu := (by fun_prop : Continuous w).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hl := paid_signed_layer mu nu rho (by fun_prop) g hg w hwi
  have he (r : ℝ) : (∫ x in {x | rho x<r},g x ∂mu)=∫ x in planarCap p r,g x := by
    rw [Measure.restrict_restrict (measurableSet_lt (by fun_prop) measurable_const)]
    have hs : {x | rho x<r} ∩ disc 1 = planarCap p r := by
      ext x
      simp only [planarCap,mem_inter_iff,mem_ofPred_eq,Metric.mem_ball,dist_eq_norm,rho]
      tauto
    rw [hs]
  have htail (x : E2) : (∫ u in ‖x-p‖^2..z^2,h u)=∫ r in Ioi (rho x),w r ∂nu :=
    paid_square_tail h hh a z ha haz hhs ‖x-p‖ (norm_nonneg _)
  refine ⟨?_,?_⟩
  · simpa only [he,w,nu,IntegrableOn] using hl.2.1
  · simp only [htail]
    exact hl.2.2.trans (integral_congr_ae (Eventually.of_forall fun r=>by dsimp only; rw [he]))

private theorem native_circle_patch_layer_cake_v457
    (p : E2) (g : ℝ → ℝ) (hg : IntegrableOn g (Icc 0 (2*Real.pi)))
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h)
    (a z : ℝ) (ha : 0<a) (haz : a<z)
    (hhs : tsupport h ⊆ Ioo (a^2) (z^2)) :
    IntegrableOn (fun r=>2*r*h (r^2)*(∫ t in circlePatch p r,g t)) (Ioo a z) ∧
    (∫ t in Icc 0 (2*Real.pi),g t*(∫ u in ‖unitCircleParameter t-p‖^2..z^2,h u))=
      ∫ r in Ioo a z,2*r*h (r^2)*(∫ t in circlePatch p r,g t) := by
  classical
  let mu := volume.restrict (Icc 0 (2*Real.pi))
  let nu := volume.restrict (Ioo a z)
  let rho : ℝ → ℝ := fun t=>‖unitCircleParameter t-p‖
  let w : ℝ → ℝ := fun r=>2*r*h (r^2)
  have hc : Continuous unitCircleParameter := by
    change Continuous (fun t : ℝ=>WithLp.toLp 2 ![Real.cos t,Real.sin t])
    fun_prop
  have hrho : Measurable rho := ((hc.sub continuous_const).norm).measurable
  have hwi : Integrable w nu := (by fun_prop : Continuous w).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hl := paid_signed_layer mu nu rho hrho g hg w hwi
  have he (r : ℝ) : (∫ t in {t | rho t<r},g t ∂mu)=∫ t in circlePatch p r,g t := by
    rw [Measure.restrict_restrict (measurableSet_lt hrho measurable_const)]
    have hs : {t | rho t<r} ∩ Icc 0 (2*Real.pi)=circlePatch p r := by
      ext t
      simp only [circlePatch,mem_inter_iff,mem_ofPred_eq,Metric.mem_ball,dist_eq_norm,rho]
      tauto
    rw [hs]
  have htail (t : ℝ) : (∫ u in ‖unitCircleParameter t-p‖^2..z^2,h u)=
      ∫ r in Ioi (rho t),w r ∂nu :=
    paid_square_tail h hh a z ha haz hhs ‖unitCircleParameter t-p‖ (norm_nonneg _)
  refine ⟨?_,?_⟩
  · simpa only [he,w,nu,IntegrableOn] using hl.2.1
  · simp only [htail]
    exact hl.2.2.trans (integral_congr_ae (Eventually.of_forall fun r=>by dsimp only; rw [he]))

end SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational
