import Section5BoundaryHalfspaceRestrictionV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
open SeifertSurfaces.Foundations

def boundaryCurvePerp (v : Euc 3) : Euc 3 :=
  (-v 2) • EuclideanSpace.single 1 1 + v 1 • EuclideanSpace.single 2 1

def boundaryCurveLinear (v : Euc 3) : (Euc 1 × Euc 2) →ₗ[ℝ] Euc 3 where
  toFun q := q.1 0 • v + q.2 0 • EuclideanSpace.single 0 1 + q.2 1 • boundaryCurvePerp v
  map_add' q r := by simp only [Prod.fst_add,Prod.snd_add,PiLp.add_apply,add_smul]; abel
  map_smul' c q := by
    change (c * q.1 0) • v + (c * q.2 0) • EuclideanSpace.single 0 1 +
      (c * q.2 1) • boundaryCurvePerp v = c • _
    simp only [smul_add,smul_smul]

theorem boundary_curve_linear_zero_coordinate (v : Euc 3) (hv : v 0 = 0)
    (q : Euc 1 × Euc 2) : boundaryCurveLinear v q 0 = q.2 0 := by
  simp [boundaryCurveLinear,boundaryCurvePerp,hv,EuclideanSpace.single_apply]

theorem boundary_curve_linear_injective (v : Euc 3) (hv0 : v 0 = 0) (hv : v ≠ 0) :
    Injective (boundaryCurveLinear v) := by
  have hpos : 0 < (v 1)^2 + (v 2)^2 := by
    have hne : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
      by_contra! h
      apply hv
      ext i
      fin_cases i <;> simp [hv0,h.1,h.2]
    rcases hne with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro q hq
  change boundaryCurveLinear v q = 0 at hq
  have h0 : q.2 0 = 0 := by
    simpa only [boundary_curve_linear_zero_coordinate v hv0,PiLp.zero_apply] using
      congrArg (fun w : Euc 3 => w 0) hq
  have h1 : q.1 0 * v 1 - q.2 1 * v 2 = 0 := by
    simpa [boundaryCurveLinear,boundaryCurvePerp,EuclideanSpace.single_apply,sub_eq_add_neg] using
      congrArg (fun w : Euc 3 => w 1) hq
  have h2 : q.1 0 * v 2 + q.2 1 * v 1 = 0 := by
    simpa [boundaryCurveLinear,boundaryCurvePerp,EuclideanSpace.single_apply] using
      congrArg (fun w : Euc 3 => w 2) hq
  have hu : q.1 0 * ((v 1)^2+(v 2)^2) = 0 := by
    linear_combination v 1 * h1 + v 2 * h2
  have hw : q.2 1 * ((v 1)^2+(v 2)^2) = 0 := by
    linear_combination -(v 2) * h1 + v 1 * h2
  have hu0 := (mul_eq_zero.mp hu).resolve_right hpos.ne'
  have hw0 := (mul_eq_zero.mp hw).resolve_right hpos.ne'
  change q = 0
  apply Prod.ext
  · ext i
    fin_cases i
    exact hu0
  · ext i
    fin_cases i
    · exact h0
    · exact hw0

def boundaryCurveEquiv (v : Euc 3) (hv0 : v 0 = 0) (hv : v ≠ 0) :
    (Euc 1 × Euc 2) ≃L[ℝ] Euc 3 :=
  (LinearEquiv.ofBijective (boundaryCurveLinear v)
    ⟨boundary_curve_linear_injective v hv0 hv,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        simp [Euc,Module.finrank_prod]) (f := boundaryCurveLinear v)).mp
          (boundary_curve_linear_injective v hv0 hv)⟩).toContinuousLinearEquiv

theorem boundary_curve_equiv_apply (v : Euc 3) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (q : Euc 1 × Euc 2) :
    boundaryCurveEquiv v hv0 hv q = q.1 0 • v + q.2 0 • EuclideanSpace.single 0 1 +
      q.2 1 • boundaryCurvePerp v := rfl

def standardBoundaryCurveEquiv : (Euc 1 × Euc 2) ≃L[ℝ] Euc 3 :=
  boundaryCurveEquiv (EuclideanSpace.single 1 1) (by simp [EuclideanSpace.single_apply])
    (by intro h; have := congrArg (fun w : Euc 3 => w 1) h; simpa using this)

theorem standard_boundary_curve_zero_coordinate (q : Euc 1 × Euc 2) :
    standardBoundaryCurveEquiv q 0 = q.2 0 :=
  boundary_curve_linear_zero_coordinate _ (by simp [EuclideanSpace.single_apply]) q

#print axioms boundary_curve_linear_injective
end SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
