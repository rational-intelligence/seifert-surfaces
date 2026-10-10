import Section5BoundaryCurveLinearV488

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
open SeifertSurfaces.Foundations

theorem one_dimension_vector (w : Euc 1) :
    w = w 0 • EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i
  simp

theorem boundary_curve_local_straightening {g : Euc 1 → Euc 3}
    {U : Set (Euc 1)} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (hzero : ∀ x ∈ U, g x 0 = 0) {a : Euc 1} (ha : a ∈ U)
    {L : Euc 1 →L[ℝ] Euc 3} (hd : HasFDerivAt g L a) (hinj : Injective L) :
    ∃ β : OpenPartialHomeomorph (Euc 3) (Euc 3),
      g a ∈ β.source ∧ ContDiffOn ℝ ∞ β β.source ∧
      ContDiffOn ℝ ∞ β.symm β.target ∧
      β.IsImage (range (𝓡∂ 3)) (range (𝓡∂ 3)) ∧
      ∀ᶠ x : Euc 1 in 𝓝 a,
        g x ∈ β.source ∧ β (g x) = standardBoundaryCurveEquiv (x,0) := by
  let v := L (EuclideanSpace.single 0 1)
  have hLv (x : Euc 1) : L x = x 0 • v := by
    conv_lhs => rw [one_dimension_vector x]
    exact L.map_smul _ _
  have hv : v ≠ 0 := by
    intro hv
    have h := hinj (hv.trans (map_zero L).symm)
    have hh := congrArg (fun w : Euc 1 => w 0) h
    simpa using hh
  have hv0 : v 0 = 0 := by
    have he : (fun x : Euc 1 => g x 0) =ᶠ[𝓝 a] (fun _ => (0 : ℝ)) := by
      filter_upwards [hU.mem_nhds ha] with x hx
      exact hzero x hx
    let P : Euc 3 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0
    have hp : HasFDerivAt (fun x => g x 0) (P.comp L) a :=
      P.hasFDerivAt.comp a hd
    have hz : HasFDerivAt (fun x : Euc 1 => g x 0) (0 : Euc 1 →L[ℝ] ℝ) a :=
      (hasFDerivAt_const (0 : ℝ) a).congr_of_eventuallyEq he
    have hv' := congrArg (fun D : Euc 1 →L[ℝ] ℝ => D (EuclideanSpace.single 0 1)) (hp.unique hz)
    exact hv'
  let A := boundaryCurveEquiv v hv0 hv
  let N : (Euc 1 × Euc 2) →L[ℝ] Euc 3 :=
    A.toContinuousLinearMap - L.comp (ContinuousLinearMap.fst ℝ (Euc 1) (Euc 2))
  let G : Euc 1 × Euc 2 → Euc 3 := fun q => g q.1 + N q
  have hN (q : Euc 1 × Euc 2) :
      N q = q.2 0 • EuclideanSpace.single 0 1 + q.2 1 • boundaryCurvePerp v := by
    change A q - L q.1 = _
    rw [boundary_curve_equiv_apply,hLv]
    abel
  have hG : ContDiffOn ℝ ∞ G (U ×ˢ univ) :=
    (hg.comp contDiff_fst.contDiffOn (fun _ h => h.1)).add N.contDiff.contDiffOn
  have hdG : HasFDerivAt G A.toContinuousLinearMap (a,0) := by
    have h := (hd.comp (a,(0 : Euc 2)) hasFDerivAt_fst).add
      (N.hasFDerivAt (x := (a,(0 : Euc 2))))
    have heq : L.comp (ContinuousLinearMap.fst ℝ (Euc 1) (Euc 2)) + N =
        A.toContinuousLinearMap := by
      dsimp only [N]
      abel
    rw [heq] at h
    exact h
  obtain ⟨e,hea,heU,he,hei,heq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      hG (hU.prod isOpen_univ) ⟨ha,mem_univ _⟩ hdG
  let β := e.symm.trans standardBoundaryCurveEquiv.toHomeomorph.toOpenPartialHomeomorph
  have he0 (x : Euc 1) : e (x,0) = g x := by
    rw [heq]
    simp [G,hN]
  have hGs (q : Euc 1 × Euc 2) (hq : q ∈ e.source) : e q 0 = q.2 0 := by
    rw [heq]
    dsimp only [G]
    rw [hN]
    simp [hzero q.1 (heU hq).1,boundaryCurvePerp]
  have hβs : ContDiffOn ℝ ∞ β β.source :=
    standardBoundaryCurveEquiv.contDiff.comp_contDiffOn (hei.mono inter_subset_left)
  have hβi : ContDiffOn ℝ ∞ β.symm β.target :=
    he.comp standardBoundaryCurveEquiv.symm.contDiff.contDiffOn (fun _ h => h.2)
  have hβimage : β.IsImage (range (𝓡∂ 3)) (range (𝓡∂ 3)) := by
    intro y hy
    have hys : e.symm y ∈ e.source := e.map_target hy.1
    have hy0 : y 0 = (e.symm y).2 0 := by
      exact (congrArg (fun w : Euc 3 => w 0) (e.right_inv hy.1)).symm.trans (hGs _ hys)
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ standardBoundaryCurveEquiv (e.symm y) 0 ↔ 0 ≤ y 0
    rw [standard_boundary_curve_zero_coordinate,hy0]
  have hgraph (x : Euc 1) (hx : (x,(0 : Euc 2)) ∈ e.source) :
      g x ∈ β.source ∧ β (g x) = standardBoundaryCurveEquiv (x,0) := by
    refine ⟨⟨he0 x ▸ e.map_source hx,mem_univ _⟩,?_⟩
    change standardBoundaryCurveEquiv (e.symm (g x)) = _
    rw [← he0 x,e.left_inv hx]
  refine ⟨β,(hgraph a hea).1,hβs,hβi,hβimage,?_⟩
  have hn : ∀ᶠ x : Euc 1 in 𝓝 a, (x,(0 : Euc 2)) ∈ e.source :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (e.open_source.mem_nhds hea)
  filter_upwards [hn] with x hx
  exact hgraph x hx

#print axioms boundary_curve_local_straightening
end SeifertSurfaces.OriginalEndpoints.Section5.BoundaryNormalFormV488
