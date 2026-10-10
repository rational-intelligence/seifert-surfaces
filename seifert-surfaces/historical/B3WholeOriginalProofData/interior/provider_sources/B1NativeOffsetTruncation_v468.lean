import B1HalfDiscPositiveClosure_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.IsothermalPDELower.NativeDirichlet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The positive part of a smooth native test plus a nonpositive smooth boundary offset is admissible. -/
theorem native_smooth_offset_positive_h10_v468 (U : Set E2) (hU : IsOpen U)
    (φ w : E2 → ℝ) (hs : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ U) (hw : ContDiff ℝ ∞ w) (hwn : ∀ x ∈ U, w x ≤ 0) :
    H10On U (fun x => max (φ x + w x) 0)
      (fun x => if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) := by
  classical
  obtain ⟨χ,hχ,hχc,hχrange,hχone,hχt⟩ := native_compact_cutoff_provider_v468 (tsupport φ) U hc hU ht
  let f := fun x => χ x * (φ x + w x)
  have hfs : ContDiff ℝ ∞ f := hχ.mul (hs.add hw)
  have hfc : HasCompactSupport f := hχc.mul_right
  have hft : tsupport f ⊆ U := tsupport_mul_subset_left.trans hχt
  have hfH := native_smooth_positive_h10_v468 U hU f hfs hfc hft
  have hχd (x : E2) (hx : χ x = 1) : fderiv ℝ χ x = 0 := by
    have hmax : IsLocalMax χ x := Filter.Eventually.of_forall fun y => by
      rw [hx]
      exact (hχrange ⟨y,rfl⟩).2
    exact hmax.fderiv_eq_zero
  have hgradf (x : E2) : planarGradient f x =
      χ x • (planarGradient φ x + planarGradient w x) + (φ x + w x) • planarGradient χ x := by
    unfold f planarGradient
    rw [fderiv_fun_mul (hχ.differentiable (by simp) x) ((hs.add hw).differentiable (by simp) x),
      fderiv_fun_add (hs.differentiable (by simp) x) (hw.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      add_smul,mul_smul,Finset.sum_add_distrib,Finset.smul_sum]
    simp only [smul_add,Finset.smul_sum,Finset.sum_add_distrib]
  have heq (x : E2) (hx : x ∈ U) :
      max (f x) 0 = max (φ x + w x) 0 ∧
      (if 0 < f x then planarGradient f x else 0) =
        (if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) := by
    by_cases hxs : x ∈ tsupport φ
    · have hχx := hχone x hxs
      have hχgx : planarGradient χ x = 0 := by simp [planarGradient,hχd x hχx]
      have hfx : f x = φ x + w x := by simp [f,hχx]
      have hfgx : planarGradient f x = planarGradient φ x + planarGradient w x := by
        rw [hgradf,hχx,hχgx,one_smul,smul_zero,add_zero]
      simp [hfx,hfgx]
    · have hφx := image_eq_zero_of_notMem_tsupport (f := φ) hxs
      have hχnonneg := (hχrange ⟨x,rfl⟩).1
      have hfn : f x ≤ 0 := by dsimp [f]; rw [hφx,zero_add]; exact mul_nonpos_of_nonneg_of_nonpos hχnonneg (hwn x hx)
      have hwnx : φ x + w x ≤ 0 := by rw [hφx,zero_add]; exact hwn x hx
      simp [max_eq_right hfn,max_eq_right hwnx,not_lt.mpr hfn,not_lt.mpr hwnx]
  have hscalar : (fun x => max (φ x + w x) 0) =ᵐ[volume.restrict U] (fun x => max (f x) 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (heq x hx).1.symm
  have hvector : (fun x => if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) =ᵐ[volume.restrict U]
      (fun x => if 0 < f x then planarGradient f x else 0) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact (heq x hx).2.symm
  have hp := hfH.1.2.1.ae_eq hscalar.symm
  have hg := hfH.1.2.2.ae_eq hvector.symm
  have h1 : H1On U (fun x => max (φ x + w x) 0)
      (fun x => if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) := by
    refine ⟨⟨locallyIntegrableOn_of_locallyIntegrable_restrict (hp.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num)),?_⟩,hp,hg⟩
    intro ψ hψ hcψ htψ i
    have hleft : (fun x => max (φ x + w x) 0 * fderiv ℝ ψ x (coordinateVector 2 i)) =ᵐ[volume.restrict U]
        (fun x => max (f x) 0 * fderiv ℝ ψ x (coordinateVector 2 i)) := by
      filter_upwards [hscalar] with x hx
      rw [hx]
    rw [integral_congr_ae hleft]
    have hright : (fun x => (if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) i * ψ x) =ᵐ[volume.restrict U]
        (fun x => (if 0 < f x then planarGradient f x else 0) i * ψ x) := by
      filter_upwards [hvector] with x hx
      rw [hx]
    rw [integral_congr_ae hright]
    exact hfH.1.1.2.2 ψ hψ hcψ htψ i
  refine ⟨h1,?_⟩
  intro ε hε
  obtain ⟨ψ,hψ,hψc,hψt,herr⟩ := hfH.2 ε hε
  refine ⟨ψ,hψ,hψc,hψt,?_⟩
  have he : (fun x => |max (φ x + w x) 0 - ψ x| ^ 2 +
      ‖(if 0 < φ x + w x then planarGradient φ x + planarGradient w x else 0) - planarGradient ψ x‖ ^ 2) =ᵐ[volume.restrict U]
      (fun x => |max (f x) 0 - ψ x| ^ 2 +
        ‖(if 0 < f x then planarGradient f x else 0) - planarGradient ψ x‖ ^ 2) := by
    filter_upwards [hscalar,hvector] with x hx hdx
    rw [hx,hdx]
  rw [integral_congr_ae he]
  exact herr

end SeifertSurfaces.OriginalEndpoints.B1Tangency
