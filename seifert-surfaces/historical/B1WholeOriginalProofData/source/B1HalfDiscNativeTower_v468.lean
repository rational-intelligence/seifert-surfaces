import B1HalfDiscLowerSourceTower_v468
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open DifferentialGeometry.Analysis.Sobolev.Euclidean
set_option maxHeartbeats 0
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The full original lower-order equation has all finite native interior Sobolev orders.
The bootstrap consumes the paid principal elliptic theorem without replacing its source. -/
theorem actual_halfdisc_native_tower_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du)
    (heq : WeakLinearEquationOn (halfDisc R) W.a W.b W.c u du) :
    ∀ k : ℕ, ∀ V : Set E2, IsOpen V → IsCompact (closure V) →
      closure V ⊆ halfDisc R → MemWkp k 2 u V := by
  let U := halfDisc R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  let hw := native_regular_witness_v468 U u du hu
  obtain ⟨A,hAa⟩ := actual_halfdisc_elliptic_coeff_v468 D s W R hRW
  obtain ⟨-, hb, hc, M,B,C,hM,hB,hC,hMa,hBb,hCc⟩ := actual_halfdisc_full_form_bounds_v468 D s W R hRW
  have hf := native_lower_source_L2_v468 U u du W.b W.c hu hb hc B C
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hBb x hx)
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hCc x hx)
  have hweak := native_linear_principal_weak_v468 U hU W.a W.b W.c u du hu heq A hAa hf
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro V hV hVc hVU
    by_cases hk0 : k = 0
    · subst k
      exact MemWkp.zero_iff_memLp.mpr ((hw.restrict hV (subset_closure.trans hVU)).memLp)
    by_cases hk1 : k = 1
    · subst k
      exact MemWkp.one_iff_memW1p.mpr ((hw.restrict hV (subset_closure.trans hVU)).memW1p)
    have hk2 : 2 ≤ k := by omega
    let m := k-2
    obtain ⟨O,hO,hVO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hVc hU hVU
    have hOsub : O ⊆ U := subset_closure.trans hOU
    have hprev : MemWkp (m+1) 2 u O := ih (m+1) (by dsimp [m]; omega) O hO hOc hOU
    have hsource := actual_halfdisc_lower_source_tower_v468 D s W R hRW u du hu O hO hOc hOU m hprev
    let AO := A.restrict hOsub
    let hwO := hw.restrict hO hOsub
    have hweakO : ∀ v, DeGiorgi.MemH01 v O → ∀ hv : DeGiorgi.MemW1pWitness 2 v O,
        DeGiorgi.bilinFormOfCoeff AO hwO hv =
        ∫ x in O, (inner ℝ (W.b x) (du x) + W.c x * u x) * v x := by
      intro v hv0 hv
      exact DeGiorgi.bilinFormOfCoeff_restrict_eq_integral hU hO hOsub hw hweak hv0 hv
    obtain ⟨F,hFa⟩ := actual_halfdisc_smooth_elliptic_extension_v468 D s W R hRW
      (closure O) hOc hOU
    have hcoeff : ∀ x ∈ O, ∀ i j : Fin 2, AO.a x i j = (1 : ℝ) * F.a x i j := by
      intro x hx i j
      change A.a x i j = 1 * F.a x i j
      rw [hAa x (hOsub hx),one_mul]
      exact (congrFun (congrFun (hFa x (subset_closure hx)) i) j).symm
    have hh := DeGiorgi.memWkp_add_two_of_bilinFormOfCoeff_eq_integral m hO hV hVc hVO
      hwO hsource hweakO F one_ne_zero hcoeff
    convert hh using 1
    dsimp [m]
    omega

/-- Each compact interior patch admits an actual smooth a.e. representative of the
native weak solution. -/
theorem actual_halfdisc_native_smooth_patch_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du)
    (heq : WeakLinearEquationOn (halfDisc R) W.a W.b W.c u du)
    (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ halfDisc R) :
    ∃ f : E2 → ℝ, ContDiffOn ℝ ∞ f V ∧ u =ᵐ[volume.restrict V] f := by
  apply DifferentialGeometry.Analysis.Sobolev.EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hV
  intro k
  exact actual_halfdisc_native_tower_v468 D s W R hRW u du hu heq k V hV hVc hVU

end SeifertSurfaces.OriginalEndpoints.B1Tangency
