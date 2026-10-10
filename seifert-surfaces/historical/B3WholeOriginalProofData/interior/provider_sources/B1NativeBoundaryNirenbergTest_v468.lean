import B1NativeBoundaryTestExtension_v468
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open ChartMetricProvider.Variational.DirectWeak
open ChartMetricProvider.Variational.DirectWeak.BoundaryContinuation
open SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
set_option maxHeartbeats 0

/-- A supported native H10 graph and its tangential translate can be consumed on
any larger actual domain. Both components are the supplied pointwise representatives. -/
theorem native_h10_shift_into_v468
    (U V : Set E2) (hU : MeasurableSet U) (c : E2)
    (hUV : U ⊆ V) (hshift : (fun x : E2 => x+c) ⁻¹' U ⊆ V)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On U u du)
    (hz : ∀ x∉U, u x=0) (hdz : ∀ x∉U, du x=0) :
    H10On V u du ∧ H10On V (fun x => u (x+c)) (fun x => du (x+c)) := by
  classical
  have he : U.indicator u=u := by
    funext x
    by_cases hx : x∈U
    · simp [hx]
    · simp [hx, hz x hx]
  have hde : U.indicator du=du := by
    funext x
    by_cases hx : x∈U
    · simp [hx]
    · simp [hx, hdz x hx]
  have hbase := native_h10_indicator_into_v468 U V hU hUV u du hu
  rw [he,hde] at hbase
  let W := (fun x : E2 => x+c) ⁻¹' U
  have hW : MeasurableSet W := hU.preimage (continuous_id.add continuous_const).measurable
  have hT := native_h10_translation U hU c u du hu
  have hinto := native_h10_indicator_into_v468 W V hW hshift _ _ hT
  have ht : W.indicator (fun x => u (x+c))=(fun x => u (x+c)) := by
    funext x
    by_cases hx : x∈W
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx]
      exact (hz _ hx).symm
  have hdt : W.indicator (fun x => du (x+c))=(fun x => du (x+c)) := by
    funext x
    by_cases hx : x∈W
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx]
      exact (hdz _ hx).symm
  rw [ht,hdt] at hinto
  exact ⟨hbase,hinto⟩

/-- The boundary Nirenberg test is constructed from the actual zero extension of
u. The cutoff and both tangential shifts fit inside the original half-disc; the
flat boundary is reached, and no boundary regularity of u is assumed. -/
theorem native_boundary_nirenberg_test_h10_v468
    (R r t : ℝ) (hroom : r+|t|<R) (htne : t≠0)
    (eta : E2 → ℝ) (hs : ContDiff ℝ ∞ eta) (hc : HasCompactSupport eta)
    (ht : tsupport eta ⊆ Metric.ball 0 r)
    (u : E2 → ℝ) (du : E2 → E2) (hu : H10On (halfDisc R) u du) :
    ∃ G : E2 → E2, H10On (halfDisc R)
      (nirenbergTestFunction 0 t eta ((halfDisc R).indicator u)) G := by
  classical
  let U := halfDisc R
  let U0 := U.indicator u
  let D0 := U.indicator du
  have hUm : MeasurableSet U := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  have hu0 := native_h10_indicator_self_v468 U hUm u du hu
  let chi : E2 → ℝ := fun x => eta x^2
  have hchis : ContDiff ℝ ∞ chi := hs.pow 2
  have hchic : HasCompactSupport chi := by
    have heq : chi = eta * eta := by funext x; simp [chi, pow_two, Pi.mul_apply]
    rw [heq]
    exact hc.mul_right (f' := eta)
  have hchit : tsupport chi ⊆ Metric.ball 0 r := by
    apply Subset.trans (b := tsupport eta) ?_ ht
    apply closure_minimal
    · intro x hx
      apply subset_tsupport
      intro hn
      exact hx (by simp [chi, hn])
    · exact isClosed_tsupport _
  let Q : E2 → ℝ := fun x => chi x*((U0 (x+t • coordinateVector 2 0)-U0 x)/t)
  let DQ : E2 → E2 := fun x => t⁻¹ •
    (cutoffGradient chi (fun y => U0 (y+t • coordinateVector 2 0))
      (fun y => D0 (y+t • coordinateVector 2 0)) x - cutoffGradient chi U0 D0 x)
  have hQ : H10On (halfDisc r) Q DQ :=
    native_tangential_cutoff_quotient_h10_v468 R r t hroom htne chi hchis hchic hchit U0 D0 hu0
  have hzero0 (x : E2) (hx : ¬0<x 1) : U0 x=0 ∧ D0 x=0 := by
    have hn : x∉U := fun hm => hx hm.2
    exact ⟨indicator_of_notMem hn u, indicator_of_notMem hn du⟩
  have hQzero : ∀ x∉halfDisc r, Q x=0 := by
    intro x hx
    by_cases hxb : x∈Metric.ball (0 : E2) r
    · have hxn : ¬0<x 1 := fun hn => hx ⟨hxb,hn⟩
      have hshift : ¬0<(x+t • coordinateVector 2 0) 1 := by
        simpa only [b1_tangential_shift_normal_v468] using hxn
      simp only [Q,(hzero0 x hxn).1,(hzero0 _ hshift).1,sub_self,zero_div,mul_zero]
    · have hn : x∉tsupport chi := fun hh => hxb (hchit hh)
      simp only [Q,image_eq_zero_of_notMem_tsupport hn,zero_mul]
  have hDQzero : ∀ x∉halfDisc r, DQ x=0 := by
    intro x hx
    by_cases hxb : x∈Metric.ball (0 : E2) r
    · have hxn : ¬0<x 1 := fun hn => hx ⟨hxb,hn⟩
      have hshift : ¬0<(x+t • coordinateVector 2 0) 1 := by
        simpa only [b1_tangential_shift_normal_v468] using hxn
      simp only [DQ,cutoffGradient,(hzero0 x hxn).1,(hzero0 x hxn).2,
        (hzero0 _ hshift).1,(hzero0 _ hshift).2,smul_zero,zero_smul,add_zero,sub_self]
    · have hn : x∉tsupport chi := fun hh => hxb (hchit hh)
      simp only [DQ,cutoffGradient,image_eq_zero_of_notMem_tsupport hn,
        planarGradient_eq_zero_off_support chi hn,zero_smul,smul_zero,add_zero,sub_self]
  have hrR : r<R := lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg t)) hroom
  have hsub : halfDisc r ⊆ halfDisc R := fun x hx =>
    ⟨Metric.ball_subset_ball hrR.le hx.1,hx.2⟩
  have hshift : (fun x : E2 => x+(-t) • coordinateVector 2 0) ⁻¹' halfDisc r ⊆ halfDisc R := by
    intro x hx
    have hxn : ‖x+(-t) • coordinateVector 2 0‖<r := by
      simpa only [disc,Metric.mem_ball,dist_zero_right] using hx.1
    have he : (x+(-t) • coordinateVector 2 0)+t • coordinateVector 2 0=x := by module
    refine ⟨?_, ?_⟩
    · apply Metric.mem_ball.mpr
      rw [dist_zero_right,← he]
      exact (b1_tangential_shift_norm_v468 t _).trans_lt (by linarith)
    · simpa only [b1_tangential_shift_normal_v468] using hx.2
  have hm : MeasurableSet (halfDisc r) := (Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)).measurableSet
  obtain ⟨hbase,htranslated⟩ := native_h10_shift_into_v468 (halfDisc r) U hm
    ((-t) • coordinateVector 2 0) hsub hshift Q DQ hQ hQzero hDQzero
  have hsubtest := native_h10_sub_v468 U _ _ _ _ htranslated hbase
  have htest := native_h10_smul_v468 U _ _ hsubtest (-t)⁻¹
  refine ⟨fun x => (-t)⁻¹ • (DQ (x+(-t) • coordinateVector 2 0)-DQ x), ?_⟩
  convert htest using 1
  funext x
  rw [nirenbergTestFunction,diffQuot_apply_of_ne 0 (neg_ne_zero.mpr htne)]
  simp only [Q, chi]
  simp only [diffQuot_apply_of_ne 0 htne, coordinateVector, U0, U]
  field_simp [htne]

end SeifertSurfaces.OriginalEndpoints.B1Tangency
#print axioms SeifertSurfaces.OriginalEndpoints.B1Tangency.native_boundary_nirenberg_test_h10_v468
