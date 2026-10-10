import B1InteriorNormalizedChartExists_v475
import B1InteriorNormalizedSmooth_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def native_planar_zero_germ_v475 (O : Set E2) (u : E2 → ℝ) (q : E2) : Prop :=
  ∃ V : Set E2, IsOpen V ∧ q ∈ V ∧ V ⊆ O ∧ EqOn u (fun _ => 0) V

/-- Interior unique continuation closes the actual open-zero germ locus of
any smooth elliptic classical solution.  Its positive normalization,
isothermal chart, drift bound and weak equation are all constructed internally. -/
theorem native_interior_local_zero_continuation_v475
    (O : Set E2) (hO : IsOpen O) (p : E2) (hp : p ∈ O)
    (a : E2 → Mat2) (b : E2 → E2) (c u : E2 → ℝ)
    (hEll : SmoothEllipticOn a b c O) (hu : ContDiffOn ℝ ∞ u O)
    (heq : ∀ x ∈ O, classicalL a b c u x = 0)
    (hacc : p ∈ closure {q | q ∈ O ∧ native_planar_zero_germ_v475 O u q}) :
    native_planar_zero_germ_v475 O u p := by
  classical
  obtain ⟨V,hV,hpV,hVO,h,hhs,hhpos,hheq⟩ :=
    native_local_positive_classical_v475 O hO p hp a b c hEll
  have hEllV : SmoothEllipticOn a b c V := by
    obtain ⟨ha,hb,hc,hsym,ell,C,hell,hC,hbounds⟩ := hEll
    exact ⟨fun i j => (ha i j).mono hVO,hb.mono hVO,hc.mono hVO,
      fun x hx => hsym x (hVO hx),ell,C,hell,hC,fun x hx => hbounds x (hVO hx)⟩
  let N : InteriorNormalizationData_v475 :=
    { O := V
      isOpen_O := hV
      a := a
      b := b
      c := c
      u := u
      h := h
      elliptic := hEllV
      smooth_u := hu.mono hVO
      smooth_h := hhs
      h_positive := fun x hx => lt_of_lt_of_le (by norm_num) (hhpos x hx)
      u_classical := fun x hx => heq x (hVO hx)
      h_classical := hheq }
  obtain ⟨F,R,hR,hpF,hFV,hFt,hBb,hDensity⟩ := native_interior_normalized_chart_exists_v475 N p hpV
  obtain ⟨haN,hbN,hvN⟩ := native_interior_normalized_smooth_v475 N
  have hWeak := native_local_classical_linear_weak_v475 N.O N.isOpen_O N.normalizedA
    N.normalizedB (fun _ => 0) N.v haN hbN contDiffOn_const hvN
    (native_interior_normalized_classical_v475 N)
  obtain ⟨q,hqF,hqO,hqg⟩ := mem_closure_iff.mp hacc F.chart.source F.source_open hpF
  obtain ⟨U,hU,hqU,hUO,hUz⟩ := hqg
  let Z := U ∩ F.chart.source
  have hZ : IsOpen Z := hU.inter F.source_open
  have hZne : Z.Nonempty := ⟨q,hqU,hqF⟩
  have hNZ : EqOn N.v (fun _ => 0) Z := by
    intro x hx
    change u x/h x=0
    rw [hUz hx.1,zero_div]
  have hzero := native_interior_chart_zero_continuation_v475 F N.O N.isOpen_O hFV
    N.normalizedA N.normalizedB N.v (fun i j => (haN i j).continuousOn)
    hbN.continuousOn (hvN.of_le (by simp)) hWeak hDensity R hR hFt hBb
    Z hZ hZne inter_subset_right hNZ
  refine ⟨F.chart.source,F.source_open,hpF,hFV.trans hVO,?_⟩
  intro x hx
  have hz := hzero hx
  change u x/h x=0 at hz
  exact (div_eq_zero_iff).mp hz |>.resolve_right (N.h_positive x (hFV hx)).ne'

#print axioms native_interior_local_zero_continuation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
