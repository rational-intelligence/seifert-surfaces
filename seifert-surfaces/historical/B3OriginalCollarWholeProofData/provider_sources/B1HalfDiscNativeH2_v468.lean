import B1HalfDiscEllipticExtension_v468
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.SecondOrder
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped ContDiff NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
set_option maxHeartbeats 0

universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}

/-- The actual coefficients and literal native weak equation discharge every premise
of the paid H2 interior regularity theorem. -/
theorem actual_halfdisc_native_H2_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (R : ℝ) (hRW : R < W.R) (u : E2 → ℝ) (du : E2 → E2)
    (hu : H1On (halfDisc R) u du)
    (heq : WeakLinearEquationOn (halfDisc R) W.a W.b W.c u du)
    (V : Set E2) (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hVU : closure V ⊆ halfDisc R) : MemWkp 2 2 u V := by
  let U := halfDisc R
  have hU : IsOpen U := Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous)
  obtain ⟨A,hAa⟩ := actual_halfdisc_elliptic_coeff_v468 D s W R hRW
  obtain ⟨-, hb, hc, M,B,C,hM,hB,hC,hMa,hBb,hCc⟩ := actual_halfdisc_full_form_bounds_v468 D s W R hRW
  have hf := native_lower_source_L2_v468 U u du W.b W.c hu hb hc B C
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hBb x hx)
    (by filter_upwards [ae_restrict_mem hU.measurableSet] with x hx; exact hCc x hx)
  have hweak := native_linear_principal_weak_v468 U hU W.a W.b W.c u du hu heq A hAa hf
  obtain ⟨eta,heta,hetac,hetaone,hetasub,hetarange⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact hVc hU hVU
  obtain ⟨rho,hrho,hroom⟩ := hetac.isCompact.exists_cthickening_subset_open hU hetasub
  have hP : IsCompact (Metric.cthickening rho (tsupport eta)) := hetac.isCompact.cthickening
  obtain ⟨F,hFa⟩ := actual_halfdisc_smooth_elliptic_extension_v468 D s W R hRW
    (Metric.cthickening rho (tsupport eta)) hP hroom
  apply DeGiorgi.memWkp_two_of_bilinFormOfCoeff_eq_integral_of_cutoff hU
    (native_regular_witness_v468 U u du hu) hf hweak F (rho := 1) one_ne_zero
    heta hetac hetarange hrho hroom _ hV _
  · intro x hx i j
    rw [hAa x (hroom hx),one_mul]
    exact (congrFun (congrFun (hFa x hx) i) j).symm
  · intro x hx
    exact hetaone.self_of_nhdsSet (subset_closure hx)

/-- Original-input positive native Dirichlet solution, now with actual H2 regularity
on every compact interior patch. -/
theorem actual_halfdisc_native_positive_H2_solution_v468
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s) :
    ∃ R : ℝ, 0 < R ∧ R < W.R ∧ ∃ h : E2 → ℝ, ∃ dh : E2 → E2,
      H1On (halfDisc R) h dh ∧
      H10On (halfDisc R) (fun x => h x - 1) dh ∧
      WeakLinearEquationOn (halfDisc R) W.a W.b W.c h dh ∧
      (∀ᵐ x ∂(volume.restrict (halfDisc R)), (1/2 : ℝ) ≤ h x) ∧
      (∀ V : Set E2, IsOpen V → IsCompact (closure V) → closure V ⊆ halfDisc R →
        MemWkp 2 2 h V) := by
  obtain ⟨R,hR,hRW,h,dh,h1,h0,heq,hpos⟩ := actual_halfdisc_native_positive_solution_v468 D s W
  exact ⟨R,hR,hRW,h,dh,h1,h0,heq,hpos,actual_halfdisc_native_H2_v468 D s W R hRW h dh h1 heq⟩

end SeifertSurfaces.OriginalEndpoints.B1Tangency
