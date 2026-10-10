import B1InteriorCompactGraphVariation_v475
noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Compactness provides an actual time-space jet tube around an attained
smooth graph.  No uniform-neighborhood regularity is supplied by the caller. -/
theorem native_interior_compact_graph_jet_tube_v475
    (V : Set E3) (hV : IsOpen V)
    (A U : Set E2) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hφ : ContDiff ℝ ∞ φ)
    (ha : ∀ x ∈ A, jetPoint (x,u x,planarGradient u x) ∈ V) :
    ∃ Q O, IsOpen Q ∧ (0 : ℝ) ∈ Q ∧ IsOpen O ∧ A ⊆ O ∧ O ⊆ U ∧
      ∀ t ∈ Q, ∀ x ∈ O,
        jetPoint (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x) ∈ V := by
  have hgrad : ContDiffOn ℝ ∞ (planarGradient u) U := by
    unfold planarGradient
    exact ContDiffOn.sum (fun i _ =>
      ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const).smul_const _)
  have hgradφ : ContDiff ℝ ∞ (planarGradient φ) := by
    unfold planarGradient
    exact ContDiff.sum (fun i _ => (hφ.fderiv_right (by simp)).clm_apply contDiff_const |>.smul_const _)
  let v : ℝ × E2 → E3 := fun p =>
    jetPoint (p.2,u p.2+p.1*φ p.2,planarGradient u p.2+p.1 • planarGradient φ p.2)
  have hpoint : ContDiff ℝ ∞ jetPoint := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp contDiff_fst
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp contDiff_fst
    · exact contDiff_fst.comp contDiff_snd
  have huv : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => u p.2) (univ ×ˢ U) :=
    hu.comp contDiffOn_snd (fun p hp => hp.2)
  have hgv : ContDiffOn ℝ ∞ (fun p : ℝ × E2 => planarGradient u p.2) (univ ×ˢ U) :=
    hgrad.comp contDiffOn_snd (fun p hp => hp.2)
  have hv : ContDiffOn ℝ ∞ v (univ ×ˢ U) :=
    hpoint.comp_contDiffOn (contDiffOn_snd.prodMk
      ((huv.add (contDiffOn_fst.mul (hφ.comp contDiff_snd).contDiffOn)).prodMk
        (hgv.add (contDiffOn_fst.smul (hgradφ.comp contDiff_snd).contDiffOn))))
  let P := (univ ×ˢ U) ∩ v ⁻¹' V
  have hP : IsOpen P := hv.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU) hV
  have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ A ⊆ P := by
    intro p hp
    have hp0 : p.1 = 0 := mem_singleton_iff.mp hp.1
    refine ⟨⟨mem_univ _,hAU hp.2⟩,?_⟩
    change v p ∈ V
    simpa [v,hp0] using ha p.2 hp.2
  obtain ⟨Q,O,hQ,hO,h0Q,hAO,hQOP⟩ := generalized_tube_lemma isCompact_singleton hA hP hsub
  have h0 : (0 : ℝ) ∈ Q := h0Q (mem_singleton 0)
  have hOU : O ⊆ U := fun x hx => (hQOP (show (0,x) ∈ Q ×ˢ O from ⟨h0,hx⟩)).1.2
  exact ⟨Q,O,hQ,h0,hO,hAO,hOU,fun t ht x hx => (hQOP (show (t,x) ∈ Q ×ˢ O from ⟨ht,hx⟩)).2⟩

/-- Compact minimum tests for an actual interior graph imply its literal
Euler-Lagrange equation. The minimum premise is intended to be discharged by
the native relative-minimum flow and the actual area transport modules. -/
theorem native_interior_graph_pde_from_compact_minima_v475
    (V : Set E3) (hV : IsOpen V) (H : CoordinateMetric V)
    (O : Set E2) (hO : IsOpen O) (u : E2 → ℝ)
    (hu : ContDiffOn ℝ ∞ u O)
    (hjets : ∀ x ∈ O, jetPoint (x,u x,planarGradient u x) ∈ V)
    (hminimum : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      IsLocalMin (fun t => ∫ x in tsupport φ,
        (native_interior_graph_density_v475 H)
          (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x)) 0) :
    ∀ x ∈ O, native_interior_graph_residual_v475 H u x=0 := by
  have hweak : ∀ φ : E2 → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, inner ℝ ((native_interior_graph_flux_v475 H)
          (x,u x,planarGradient u x)) (planarGradient φ x) -
        (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x)=0 := by
    intro φ hφ hφc hφO
    let A := tsupport φ
    have hA : IsCompact A := hφc
    have hAO : A ⊆ O := hφO
    obtain ⟨Q,N,hQ,h0,hN,hAN,hNO,hvaried⟩ :=
      native_interior_compact_graph_jet_tube_v475 V hV A O hA hO hAO u φ hu hφ
        (fun x hx => hjets x (hAO hx))
    have hvar := native_interior_compact_graph_density_variation_v475 V hV H A N hA hN hAN
      Q hQ h0 u φ (hu.mono hNO) hφ hvaried
    have hz := (hminimum φ hφ hφc hφO).hasDerivAt_eq_zero hvar.2
    have hzero (x : E2) (hx : x ∉ A) :
        inner ℝ ((native_interior_graph_flux_v475 H) (x,u x,planarGradient u x)) (planarGradient φ x) -
        (native_interior_graph_lower_v475 H) (x,u x,planarGradient u x) * φ x = 0 := by
      have hφz : φ x=0 := image_eq_zero_of_notMem_tsupport hx
      have hgradz : planarGradient φ x=0 := by
        unfold planarGradient
        rw [fderiv_of_notMem_tsupport ℝ hx]
        simp
      simp [hφz,hgradz]
    change (∫ x in A, _) = 0 at hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hz
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hzero x (fun hh => hx (hφO hh)))]
    exact hz
  exact native_interior_graph_residual_of_tests_v475 V hV H O hO u hu
    hjets hweak

#print axioms native_interior_graph_pde_from_compact_minima_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
