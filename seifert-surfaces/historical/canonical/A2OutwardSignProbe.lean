import A2ConormalUniquenessReadyV469

set_option autoImplicit false
open Set Matrix
open scoped ContDiff BigOperators
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.A2NativeTests
open SeifertSurfaces.AppendixACoordinates
open SeifertSurfaces.OriginalEndpoints.A2MetricFlux
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence
open SeifertSurfaces.OriginalEndpoints.CurvedDivergence.GaussGreen
run_cmd do
  let pref := Lean.Name.num (`_private.A2MetricFluxV468) 0
  let n := (["SeifertSurfaces", "OriginalEndpoints", "A2MetricFlux"].foldl Lean.Name.str pref)
  Lean.Elab.Command.modifyScope fun s => { s with openDecls := .simple n [] :: s.openDecls }

private theorem unit_conormal_second_component_ne_zero (g : MetricTensor) (y : E3)
    (L : E2 →L[ℝ] E3) (hq : (metricGram g y L).PosDef) (v : E2)
    (hvunit : coordinateInner g y (L v) (L v) = 1)
    (hvorth : coordinateInner g y (L v) (L (coordinateVector 2 0)) = 0) : v 1 ≠ 0 := by
  intro hv1
  rw [gram_pullback] at hvorth
  have hv0 : v 0 = 0 := by
    have he : metricGram g y L 0 0 * v 0 = 0 := by
      simpa [Fin.sum_univ_two,coordinateVector,EuclideanSpace.single_apply,hv1] using hvorth
    exact (mul_eq_zero.mp he).resolve_left hq.diag_pos.ne'
  have hv : v = 0 := by
    ext a
    fin_cases a
    · exact hv0
    · exact hv1
  rw [hv,map_zero] at hvunit
  simpa [coordinateInner] using hvunit

/-- The original outward direction condition forces the negative normal
coordinate in every actual inward affine halfbox. No choice of orientation
of the boundary clock is involved. -/
theorem native_outward_second_component_negative
    (D : Set E2) (p : E2) (A : E2 →L[ℝ] E2)
    (a b h u : ℝ) (hh : 0 < h) (hu : u ∈ Ioo a b)
    (hbox : MapsTo (fun x => p + A x) (halfBoxDomain true a b h) D)
    (v : E2) (hv1 : v 1 ≠ 0)
    (hout : ∃ eps : ℝ, 0 < eps ∧ ∀ t ∈ Ioo 0 eps,
      p + A (boundaryPoint u) + t • A v ∉ D) : v 1 < 0 := by
  by_contra hneg
  have hvpos : 0 < v 1 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hv1)
  obtain ⟨eps,heps,hout⟩ := hout
  let C := |v 0| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let delta := min eps (min ((u-a)/C) (min ((b-u)/C) (h/(v 1+1))))
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min heps (lt_min (div_pos (sub_pos.mpr hu.1) hC)
      (lt_min (div_pos (sub_pos.mpr hu.2) hC) (div_pos hh (by linarith))))
  let t := delta / 2
  have ht : 0 < t := div_pos hdelta (by norm_num)
  have htd : t < delta := by dsimp [t]; linarith
  have hteps : t < eps := htd.trans_le (min_le_left _ _)
  have htleft : t * C < u-a := (lt_div_iff₀ hC).mp
    (htd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have htright : t * C < b-u := (lt_div_iff₀ hC).mp
    (htd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hth : t * (v 1+1) < h := (lt_div_iff₀ (by linarith : 0 < v 1+1)).mp
    (htd.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hb : boundaryPoint u + t • v ∈ halfBoxDomain true a b h := by
    change coordinates (boundaryPoint u + t • v) ∈ halfBox true a b h
    simp only [halfBox, ↓reduceIte,
      map_add,map_smul,boundaryPoint,ContinuousLinearEquiv.apply_symm_apply]
    have hvcoord : coordinates v = (v 0,v 1) := by rfl
    rw [hvcoord]
    change ((u,0) + t • (v 0,v 1) : ℝ × ℝ) ∈ Icc (a,0) (b,h)
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul,zero_add]
    change (u+t*v 0,t*v 1) ∈ Icc (a,0) (b,h)
    refine ⟨⟨?_,(mul_pos ht hvpos).le⟩,⟨?_,?_⟩⟩
    · have hl := mul_le_mul_of_nonneg_left (neg_abs_le (v 0)) ht.le
      dsimp [C] at htleft
      nlinarith only [htleft,hl,ht]
    · have hr := mul_le_mul_of_nonneg_left (le_abs_self (v 0)) ht.le
      dsimp [C] at htright
      nlinarith only [htright,hr,ht]
    · nlinarith only [hth,ht]
  apply hout t ⟨ht,hteps⟩
  have hi := hbox hb
  simpa only [map_add,map_smul,add_assoc] using hi

/-- Outwardness in the original native sector, plus metric unit length and
edge orthogonality, identifies its conormal with the paid halfbox vector. -/
theorem native_sector_conormal_eq_paid_halfbox
    (g : MetricTensor) (y : E3) (L : E2 →L[ℝ] E3)
    (hs : ∀ a b, g y a b = g y b a) (hq : (metricGram g y L).PosDef)
    (D : Set E2) (p : E2) (A : E2 →L[ℝ] E2)
    (a b h u : ℝ) (hh : 0 < h) (hu : u ∈ Ioo a b)
    (hbox : MapsTo (fun x => p + A x) (halfBoxDomain true a b h) D)
    (v : E2) (hvunit : coordinateInner g y (L v) (L v) = 1)
    (hvorth : coordinateInner g y (L v) (L (coordinateVector 2 0)) = 0)
    (hout : ∃ eps : ℝ, 0 < eps ∧ ∀ t ∈ Ioo 0 eps,
      p + A (boundaryPoint u) + t • A v ∉ D) :
    L v = metricConormal g y L (outwardCovector true) := by
  exact native_outward_conormal_eq_paid_halfbox_conormal g y L hs hq v hvunit hvorth
    (native_outward_second_component_negative D p A a b h u hh hu hbox v
      (unit_conormal_second_component_ne_zero g y L hq v hvunit hvorth) hout)

#print axioms native_outward_second_component_negative
#print axioms native_sector_conormal_eq_paid_halfbox
end SeifertSurfaces.OriginalEndpoints.A2NativeTests
