import ActualParametricBoundaryExactLocalizationV894
import ActualVariableNormalFamilyFixedPhaseV905
import ActualSupportedChartAmbientSetPreservationV916
import ActualThinCompactNormalNeighborhoodV847
import ActualAnnulusHalfPolarModelV768

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped Manifold ContDiff
open Set Topology Metric Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualAnnulusHalfPolarModelV768
noncomputable section
namespace CompressionActualVariableAnnularAmbientSurfaceV917

/-- Realize the SAME whole annular family through an actual normal chart.
    The positive normal width and ambient support are constructed. Every
    variable whole-strip point matches its original family endpoint. -/
theorem variable_annular_ambient_surface
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) 1 M]
    (G : Time → Plane ≃ₜ Plane)
    (hG : Continuous (fun p : Time × Plane => G p.1 p.2))
    (hGi : Continuous (fun p : Time × Plane => (G p.1).symm p.2))
    (hG1 : ∀ x,G 1 x = x) (hGfix : ∀ s x,‖x‖ ≤ 1 → G s x = x)
    (hGbound : ∀ s x,‖x‖ ≤ 2 → ‖G s x‖ ≤ 2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (e : OpenPartialHomeomorph (Plane × ℝ) M)
    (he : ∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 → (x,0) ∈ e.source)
    (Z : Set M) (hZ : IsClosed Z)
    (haway : ∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 →
      e (x,0) ∉ Z ∧ e (x,0) ∉ (𝓡∂ 3).boundary M)
    (S : Set M) (heS : ∀ p,p ∈ e.source → (e p ∈ S ↔ p.2 = 0)) :
    ∃ ρ : ℝ,0 < ρ ∧
      (∀ (s : Time) (z : Circle) (t : Time),ε ≤ t.val →
        ∀ n,n ∈ Icc (-ρ) ρ → (G s (polar (z,t)),n) ∈ e.source) ∧
      ∀ φ : ℝ → Time,Continuous φ → φ 0 = 1 →
        (∀ n,n ∉ Ioo (-ρ) ρ → φ n = 0) →
        ∃ I : TopologicalAmbientIsotopy M,∃ V : Set M,
          IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) Z ∧
          Disjoint (closure V) ((𝓡∂ 3).boundary M) ∧ V ⊆ e.target ∧
          (∀ z : Circle,e ((2:ℝ) • circleVector z,0) ∈ V) ∧
          (∀ t x,x ∉ V → I.stage t x = x) ∧
          (∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x) ∧
          (∀ t p,p ∈ e.source → φ p.2 = 0 → I.stage t (e p) = e p) ∧
          (∀ t x,I.stage t x ∈ S ↔ x ∈ S) ∧ (∀ t,I.stage t '' S = S) ∧
          (∀ (z : Circle) (t : Time),ε ≤ t.val →
            I.stage 1 (e (polar (z,t),0)) = e (G 0 (polar (z,t)),0)) ∧
          ∀ (z : Circle) (t : Time),ε ≤ t.val → ∀ n,n ∈ Icc (-ρ) ρ →
            I.stage 1 (e (G (φ n) (polar (z,t)),n)) = e (G 0 (polar (z,t)),n) := by
  classical
  let A : Set (Circle × Time) := {p | ε ≤ p.2.val}
  have hAc : IsCompact A := (isClosed_le continuous_const continuous_snd.subtype_val).isCompact
  let B : Set Plane := polar '' A
  have hBc : IsCompact B := hAc.image polar_continuous
  have hBn (x : Plane) (hx : x ∈ B) : 1 < ‖x‖ := by
    obtain ⟨p,hp,rfl⟩ := hx
    rw [polar_norm]
    change ε ≤ p.2.val at hp
    linarith
  have hB2 (x : Plane) (hx : x ∈ B) : ‖x‖ ≤ 2 := by
    obtain ⟨p,hp,rfl⟩ := hx
    rw [polar_norm]
    linarith [p.2.property.2]
  obtain ⟨K,W,hK,hKi,hW,hWc,hWR,hWD,hKG,hKfix,hoff,hKid⟩ :=
    CompressionActualParametricBoundaryExactLocalizationV894.parametric_boundary_exact_localization
      G hG hGi hGfix hGbound B hBc hBn hB2
  have hK1 : ∀ x,K 1 x = x := hKid 1 hG1
  let Q : Set Plane := (fun p : Time × Plane => G p.1 p.2) '' (univ ×ˢ B)
  have hQc : IsCompact Q := (isCompact_univ.prod hBc).image hG
  have hQn (x : Plane) (hx : x ∈ Q) : 1 < ‖x‖ := by
    obtain ⟨⟨s,y⟩,⟨hs,hy⟩,rfl⟩ := hx
    exact CompressionActualBoundaryExactDiskSeparatedIsotopyV845.image_outside_fixed_disk
      (G s) (hGfix s) (hBn y hy)
  have hQ2 (x : Plane) (hx : x ∈ Q) : ‖x‖ ≤ 2 := by
    obtain ⟨⟨s,y⟩,⟨hs,hy⟩,rfl⟩ := hx
    exact hGbound s y (hB2 y hy)
  obtain ⟨m,hm,hQm⟩ := hQc.exists_forall_le' continuous_norm.continuousOn
    (a := (1:ℝ)) hQn
  let c : ℝ := (1+min m (3/2))/2
  have hc : 1 < c := by dsimp [c]; have hh := lt_min hm (by norm_num : (1:ℝ)<3/2); linarith
  have hcm : c < m := by dsimp [c]; have hh := min_le_left m (3/2); linarith
  have hc2 : c < 2 := by dsimp [c]; have hh := min_le_right m (3/2); linarith
  let O : Set Plane := {x | c < ‖x‖ ∧ ‖x‖ < 5/2}
  have hOo : IsOpen O := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hOcl : closure O ⊆ {x : Plane | c ≤ ‖x‖ ∧ ‖x‖ ≤ 5/2} :=
    closure_minimal (fun _ hx => ⟨hx.1.le,hx.2.le⟩)
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
  have hOc : IsCompact (closure O) := (isCompact_closedBall (0 : Plane) (5/2)).of_isClosed_subset
    isClosed_closure (fun _ hx => mem_closedBall_zero_iff.mpr (hOcl hx).2)
  have hQO : Q ⊆ O := fun x hx => ⟨hcm.trans_le (hQm x hx),(hQ2 x hx).trans_lt (by norm_num)⟩
  let U : Set Plane := W ∪ O
  have hUo : IsOpen U := hW.union hOo
  have hUc : IsCompact (closure U) := by rw [closure_union]; exact hWc.union hOc
  have hUn (x : Plane) (hx : x ∈ closure U) : 1 < ‖x‖ ∧ ‖x‖ < 3 := by
    rw [closure_union] at hx
    rcases hx with hx | hx
    · exact ⟨lt_of_not_ge (fun hn => disjoint_left.mp hWD hx (mem_closedBall_zero_iff.mpr hn)),
        mem_ball_zero_iff.mp (hWR hx)⟩
    · obtain ⟨hlo,hhi⟩ := hOcl hx
      exact ⟨hc.trans_le hlo,hhi.trans_lt (by norm_num)⟩
  have hUzero : closure U ×ˢ ({0} : Set ℝ) ⊆ e.source := by
    rintro ⟨x,n⟩ ⟨hx,hn⟩
    have hn0 : n = 0 := mem_singleton_iff.mp hn
    rw [hn0]
    exact he x (hUn x hx).1 (hUn x hx).2
  let Z' : Set M := Z ∪ (𝓡∂ 3).boundary M
  have hZ' : IsClosed Z' := hZ.union ((𝓡∂ 3).isClosed_boundary (M := M) (n := 1) (by norm_num))
  have hUZ : Disjoint (e '' (closure U ×ˢ {0})) Z' := by
    apply disjoint_left.mpr
    rintro y ⟨⟨x,n⟩,⟨hx,hn⟩,rfl⟩ (hy | hy)
    · exact (haway x (hUn x hx).1 (hUn x hx).2).1 ((mem_singleton_iff.mp hn) ▸ hy)
    · exact (haway x (hUn x hx).1 (hUn x hx).2).2 ((mem_singleton_iff.mp hn) ▸ hy)
  obtain ⟨δ,hδ,hδs,hδZ⟩ :=
    CompressionActualThinCompactNormalNeighborhoodV847.chart_normal_block_away_closed_set
      e (closure U) hUc hUzero Z' hZ' hUZ
  let ρ : ℝ := δ/2
  have hρ : 0 < ρ := half_pos hδ
  have hρδ : Icc (-ρ) ρ ⊆ Icc (-δ) δ := fun _ hn => ⟨by dsimp [ρ] at hn; linarith [hn.1],by dsimp [ρ] at hn; linarith [hn.2]⟩
  have hsource (s : Time) (z : Circle) (t : Time) (ht : ε ≤ t.val)
      (n : ℝ) (hn : n ∈ Icc (-ρ) ρ) : (G s (polar (z,t)),n) ∈ e.source := by
    apply hδs
    exact ⟨subset_closure (Or.inr (hQO
      ⟨(s,polar (z,t)),⟨mem_univ _,⟨(z,t),ht,rfl⟩⟩,rfl⟩)),hρδ hn⟩
  refine ⟨ρ,hρ,hsource,?_⟩
  intro φ hφ hφ0 hφoff
  have hKUoff : ∀ t x,x ∉ U → K t x = x := fun t x hx => hoff t x (fun hw => hx (Or.inl hw))
  obtain ⟨L,hL,hLi,hL0,hLn,hLoff,hCo,hCc,hLzero,hLpoint,hLphase⟩ :=
    CompressionActualVariableNormalFamilyFixedPhaseV905.variable_normal_family_fixed_phase
      K hK hKi hK1 U hUo hUc hKUoff ρ hρ φ hφ hφ0 hφoff
  let C : Set (Plane × ℝ) := U ×ˢ Ioo (-ρ) ρ
  have hcl : closure C = closure U ×ˢ Icc (-ρ) ρ := by
    rw [closure_prod_eq,closure_Ioo (by linarith : -ρ ≠ ρ)]
  have hcls : closure C ⊆ e.source := by
    rw [hcl]
    exact (prod_mono Subset.rfl hρδ).trans hδs
  have hclZ : Disjoint (e '' closure C) Z' := by
    rw [hcl]
    exact hδZ.mono_left (image_mono (prod_mono Subset.rfl hρδ))
  have hLS : ∀ t p,p ∈ closure C → (e (L t p) ∈ S ↔ e p ∈ S) :=
    CompressionActualSupportedChartAmbientSetPreservationV916.normal_block_preserves_zero_surface
      e C hcls L hLoff hLn S heS
  obtain ⟨I,hV,hVc,hVZ,hVbd,hIo,hIbd,hIon,hIS,hIimage⟩ :=
    CompressionActualSupportedChartAmbientSetPreservationV916.supported_chart_ambient_set_preservation
      e C hCo hCc hcls L hL hL0 hLoff Z' hclZ (hclZ.mono_right subset_union_right) S hLS
  have hcurve (s : Time) (z : Circle) (t : Time) (ht : ε ≤ t.val) : G s (polar (z,t)) ∈ U :=
    Or.inr (hQO ⟨(s,polar (z,t)),⟨mem_univ _,⟨(z,t),ht,rfl⟩⟩,rfl⟩)
  have hpoint (z : Circle) (t : Time) (ht : ε ≤ t.val) (n : ℝ) (hn : n ∈ Icc (-ρ) ρ) :
      I.stage 1 (e (G (φ n) (polar (z,t)),n)) = e (G 0 (polar (z,t)),n) := by
    have hx : polar (z,t) ∈ B := ⟨(z,t),ht,rfl⟩
    have hp : (G (φ n) (polar (z,t)),n) ∈ closure C := by
      rw [hcl]
      exact ⟨subset_closure (hcurve _ z t ht),hn⟩
    rw [← hKG (φ n) _ hx] at hp ⊢
    exact (hIon 1 _ hp).trans (congrArg e ((hLpoint n (polar (z,t))).trans
      (Prod.ext (hKG 0 _ hx) rfl)))
  have hfixedPhase (t : Time) (p : Plane × ℝ) (hp : p ∈ e.source) (hpφ : φ p.2 = 0) :
      I.stage t (e p) = e p := by
    by_cases hpC : p ∈ closure C
    · rw [hIon t p hpC]
      apply congrArg e
      have hpoint0 := hLpoint p.2 ((K 0).symm p.1)
      have hLid : L t p = p := by
        -- The straightening formula follows from the zero phase at all times.
        -- Retain it from the supplied explicit family below.
        exact hLphase t p hpφ
      exact hLid
    · apply hIo
      rintro ⟨q,hq,hqe⟩
      have heq : q = p := e.injOn (hcls (subset_closure hq)) hp hqe
      exact hpC (heq ▸ subset_closure hq)
  refine ⟨I,e '' C,hV,hVc,hVZ.mono_right subset_union_left,hVbd,?_,?_,hIo,hIbd,hfixedPhase,hIS,hIimage,?_,hpoint⟩
  · rintro y ⟨p,hp,rfl⟩
    exact e.map_source (hcls (subset_closure hp))
  · intro z
    have hn : ‖(2:ℝ) • circleVector z‖ = 2 := by
      rw [norm_smul,circleVector_norm,Real.norm_eq_abs]; norm_num
    exact ⟨((2:ℝ) • circleVector z,0),⟨Or.inr (by change c < _ ∧ _ < 5/2; rw [hn]; constructor; exact hc2; norm_num),⟨by linarith,hρ⟩⟩,rfl⟩
  · intro z t ht
    have hp := hpoint z t ht 0 ⟨by linarith,hρ.le⟩
    rwa [hφ0,hG1] at hp

#print axioms variable_annular_ambient_surface
end CompressionActualVariableAnnularAmbientSurfaceV917
