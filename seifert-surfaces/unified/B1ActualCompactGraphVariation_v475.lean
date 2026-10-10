import B1CompactGraphVariation_v475

noncomputable section
open Set Topology Function MeasureTheory Filter
open scoped Manifold ContDiff BigOperators NNReal ENNReal
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe v
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{v} E}
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Compactness provides an actual time-space jet tube around an attained
smooth graph.  No uniform-neighborhood regularity is supplied by the caller. -/
theorem actual_compact_graph_jet_tube_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (A U : Set E2) (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u U) (hφ : ContDiff ℝ ∞ φ)
    (ha : ∀ x ∈ A, jetPoint (x,u x,planarGradient u x) ∈ W.V) :
    ∃ Q O, IsOpen Q ∧ (0 : ℝ) ∈ Q ∧ IsOpen O ∧ A ⊆ O ∧ O ⊆ U ∧
      ∀ t ∈ Q, ∀ x ∈ O,
        jetPoint (x,u x+t*φ x,planarGradient u x+t • planarGradient φ x) ∈ W.V := by
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
  let P := (univ ×ˢ U) ∩ v ⁻¹' W.V
  have hP : IsOpen P := hv.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hU) W.V_open
  have hsub : ({(0 : ℝ)} : Set ℝ) ×ˢ A ⊆ P := by
    intro p hp
    have hp0 : p.1 = 0 := mem_singleton_iff.mp hp.1
    refine ⟨⟨mem_univ _,hAU hp.2⟩,?_⟩
    change v p ∈ W.V
    simpa [v,hp0] using ha p.2 hp.2
  obtain ⟨Q,O,hQ,hO,h0Q,hAO,hQOP⟩ := generalized_tube_lemma isCompact_singleton hA hP hsub
  have h0 : (0 : ℝ) ∈ Q := h0Q (mem_singleton 0)
  have hOU : O ⊆ U := fun x hx => (hQOP (show (0,x) ∈ Q ×ˢ O from ⟨h0,hx⟩)).1.2
  exact ⟨Q,O,hQ,h0,hO,hAO,hOU,fun t ht x hx => (hQOP (show (t,x) ∈ Q ×ˢ O from ⟨ht,hx⟩)).2⟩

/-- The original attained graph needs only compact support inside the half-disc
for its actual area-density first variation. -/
theorem actual_compact_height_graph_variation_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (A : Set E2) (hA : IsCompact A) (hAhalf : A ⊆ halfDisc W.R)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    HasDerivAt (fun t => ∫ x in A,
      W.density (x,localHeight D s x+t*φ x,
        planarGradient (localHeight D s) x+t • planarGradient φ x))
      (∫ x in A,
        inner ℝ (W.flux (x,localHeight D s x,planarGradient (localHeight D s) x))
          (planarGradient φ x) -
        W.lower (x,localHeight D s x,planarGradient (localHeight D s) x) * φ x) 0 := by
  have hAc : A ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hAhalf hx).1,(hAhalf hx).2.le⟩
  obtain ⟨Q,O,hQ,h0,hO,hAO,hOU,hjets⟩ := actual_compact_graph_jet_tube_v475 D s W
    A W.U hA W.U_open (hAc.trans W.U_contains) (localHeight D s) φ W.height_smooth hφ
    (fun x hx => by simpa using W.jets_inside x (hAc hx) 1 (by simp))
  exact (actual_compact_graph_density_variation_v475 D s W A O hA hO hAO Q hQ h0
    (localHeight D s) φ (W.height_smooth.mono hOU) hφ hjets).2

/-- The zero sheet uses its own attained jet; its first variation includes the
height derivative of the original metric density. -/
theorem actual_compact_zero_graph_variation_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (A : Set E2) (hA : IsCompact A) (hAhalf : A ⊆ halfDisc W.R)
    (φ : E2 → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    HasDerivAt (fun t => ∫ x in A,
      W.density (x,t*φ x,t • planarGradient φ x))
      (∫ x in A, inner ℝ (W.flux (x,0,0)) (planarGradient φ x) -
        W.lower (x,0,0) * φ x) 0 := by
  have hAc : A ⊆ closedHalfDisc W.R := fun x hx =>
    ⟨Metric.ball_subset_closedBall (hAhalf hx).1,(hAhalf hx).2.le⟩
  obtain ⟨Q,O,hQ,h0,hO,hAO,hOU,hjets⟩ := actual_compact_graph_jet_tube_v475 D s W
    A W.U hA W.U_open (hAc.trans W.U_contains) (fun _ => 0) φ contDiffOn_const hφ
    (fun x hx => by simpa [planarGradient] using W.jets_inside x (hAc hx) 0 (by simp))
  simpa [planarGradient] using
    (actual_compact_graph_density_variation_v475 D s W A O hA hO hAO Q hQ h0
      (fun _ => 0) φ contDiffOn_const hφ hjets).2

#print axioms actual_compact_graph_jet_tube_v475
#print axioms actual_compact_height_graph_variation_v475
#print axioms actual_compact_zero_graph_variation_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
