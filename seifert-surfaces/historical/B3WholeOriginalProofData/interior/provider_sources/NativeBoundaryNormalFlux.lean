import NativeBoundaryPreliminaries

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Topology BigOperators ContDiff

namespace SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
open QuasilinearLocalization

/-- Ellipticity gives the strict normal derivative of the actual normal flux;
coordinate 0 is the native A5 normal, independently of the B1 convention. -/
theorem UniformlyEllipticOn.normal_flux_derivative_positive
    {J : Set Jet} {A : Jet → E2} (hell : UniformlyEllipticOn J A) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ j ∈ J,
      κ ≤ (fderiv ℝ (fun p : E2 => A (j.1, j.2.1, p)) j.2.2
        (coordinateVector 2 0)) 0 := by
  obtain ⟨κ, hκ, he⟩ := hell
  refine ⟨κ, hκ, ?_⟩
  intro j hj
  have hn := he j.1 j.2.1 j.2.2 (coordinateVector 2 0) hj
  simpa [coordinateVector, PiLp.norm_single, PiLp.inner_apply, Fin.sum_univ_two] using hn

theorem C1QuasilinearDirichletSolution.boundary_normal_flux_coercive
    {ρ : ℝ} {J : Set Jet} {Q : SmoothQuasilinearOperator J}
    {g : SmoothDirichletDatum ρ} {u : E2 → ℝ}
    (hsolution : C1QuasilinearDirichletSolution ρ J Q g u) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ closedHalfDisc ρ,
      κ ≤ (fluxDp Q (firstJetWithin ρ u x) (coordinateVector 2 0)) 0 := by
  obtain ⟨κ, hκ, he⟩ :=
    UniformlyEllipticOn.normal_flux_derivative_positive hsolution.uniformly_elliptic
  exact ⟨κ, hκ, fun x hx => he _ (hsolution.attained_jets x hx)⟩

end SeifertSurfaces.AppendixACoordinates.BoundaryRegularity
