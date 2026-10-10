import B1HalfDiscNativeH2_v468
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.OriginalEndpoints.B1GraphCoefficients
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 0

private theorem compact_smooth_scalar_product_v468
    (m : ℕ) (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (a f : E2 → ℝ) (ha : ContDiff ℝ ∞ a) (hf : MemWkp m 2 f V) :
    MemWkp m 2 (fun x => a x * f x) V := by
  obtain ⟨C,_,hC⟩ := DifferentialGeometry.Analysis.Calculus.exists_uniform_iteratedFDerivWithin_bound_of_contDiffOn
    isOpen_univ ha.contDiffOn hVc (subset_univ _) m
  exact MemWkp.smul_smooth_bounded m (by norm_num) hV ha
    (fun j hj x hx => by simpa only [iteratedFDerivWithin_univ] using hC x (subset_closure hx) j hj) hf

/-- The actual lower-order source inherits the entire finite Sobolev tower from the
literal native gradient; local smooth coefficients are extended only for multiplication. -/
theorem actual_halfdisc_lower_source_tower_v468
    {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
    {g : SmoothMetric E.Carrier} {J : LongitudeFoliation E}
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du) (V : Set E2)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVU : closure V ⊆ halfDisc R)
    (m : ℕ) (hm : MemWkp (m+1) 2 u V) :
    MemWkp m 2 (fun x => inner ℝ (W.b x) (du x) + W.c x * u x) V := by
  let U := halfDisc R
  obtain ⟨O,hO,hWO,hOU,hjets,hf,hdf,ha,hq,hlg,hlh,hb,hc⟩ := actual_coefficient_open_tube D s W
  have hUW : U ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (Metric.ball_subset_ball hRW.le hx.1),hx.2.le⟩
  have hVO : closure V ⊆ O := hVU.trans (hUW.trans hWO)
  obtain ⟨χ,hχ,hχc,hχone,hχO,hχrange⟩ := DifferentialGeometry.Analysis.exists_bump_compact hVc hO hVO
  have hχ1 (x : E2) (hx : x ∈ V) : χ x = 1 := hχone.self_of_nhdsSet (subset_closure hx)
  have hbs (i : Fin 2) : ContDiff ℝ ∞ (fun x => χ x * W.b x i) :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hO hχ hχO
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp_contDiffOn hb)
  have hcs : ContDiff ℝ ∞ (fun x => χ x * W.c x) :=
    DifferentialGeometry.Analysis.contDiff_cutoff_smul hO hχ hχO hc
  let hw := (native_regular_witness_v468 U u du hu).restrict hV (subset_closure.trans hVU)
  have hdm (i : Fin 2) : MemWkp m 2 (fun x => du x i) V := by
    have he := (chosenWeakPartialOrZero_isWeakPartial_of_mem hm.memW1p i).ae_eq hV (hw.isWeakGrad i)
      ((chosenWeakPartialOrZero_memLp_of_mem hm.memW1p i).locallyIntegrable (by norm_num))
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    exact (MemWkp_congr_ae (by norm_num) hV he).mp (hm.chosenWeakPartial_mem i)
  have hp (i : Fin 2) : MemWkp m 2 (fun x => W.b x i * du x i) V := by
    have hh := compact_smooth_scalar_product_v468 m V hV hVc _ _ (hbs i) (hdm i)
    apply (MemWkp_congr_ae (by norm_num) hV _).mp hh
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hχ1 x hx,one_mul]
  have hcp : MemWkp m 2 (fun x => W.c x * u x) V := by
    have hh := compact_smooth_scalar_product_v468 m V hV hVc _ _ hcs hm.le_succ
    apply (MemWkp_congr_ae (by norm_num) hV _).mp hh
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    simp only [hχ1 x hx,one_mul]
  have hsum := MemWkp.add (by norm_num) hV (MemWkp.add (by norm_num) hV (hp 0) (hp 1)) hcp
  convert hsum using 1
  funext x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply,star_trivial]
  ring

end SeifertSurfaces.OriginalEndpoints.B1Tangency
