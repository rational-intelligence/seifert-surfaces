import ActualAnnulusHalfSupportedClosedStripV848
import ActualSupportedChartAmbientIsotopyV846
import ActualThinCompactNormalNeighborhoodV847

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric Manifold
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualPlanarWholeDiskExtensionV756
open CompressionActualPlanarPolarCoordinatesV761
noncomputable section
namespace CompressionActualAnnularStripAmbientExtensionV851

/-- The actual prescribed annular half has a supported ambient extension
    on its whole closed outer strip. The normal thickness, compact bundle,
    ambient stages and seam-containing support are all constructed. -/
theorem annular_strip_ambient_extension
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) 1 M]
    (q : C(Circle × Time,Plane)) (hq : IsEmbedding q)
    (hq0 : ∀ z,q (z,0) = circleVector z)
    (hqout : ∀ z t,t ≠ 0 → 1 < ‖q (z,t)‖)
    (hqbound : ∀ z t,‖q (z,t)‖ ≤ 2)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (e : OpenPartialHomeomorph (Plane × ℝ) M)
    (he : ∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 → (x,0) ∈ e.source)
    (Z : Set M) (hZ : IsClosed Z)
    (haway : ∀ x : Plane,1 < ‖x‖ → ‖x‖ < 3 →
      e (x,0) ∉ Z ∧ e (x,0) ∉ (𝓡∂ 3).boundary M) :
    ∃ I : TopologicalAmbientIsotopy M,∃ V : Set M,
      IsOpen V ∧ IsCompact (closure V) ∧ Disjoint (closure V) Z ∧
      Disjoint (closure V) ((𝓡∂ 3).boundary M) ∧
      (∀ z : Circle,e ((2:ℝ) • circleVector z,0) ∈ V) ∧
      (∀ t x,x ∉ V → I.stage t x = x) ∧
      (∀ t x,x ∈ (𝓡∂ 3).boundary M → I.stage t x = x) ∧
      ∀ (z : Circle) (t : Time),ε ≤ (t:ℝ) →
        I.stage 1 (e ((1+(t:ℝ)) • circleVector z,0)) = e (q (z,t),0) := by
  classical
  obtain ⟨K,W,hK,hW,hWc,hWR,hWD,h0,h1,hfix,hoff⟩ :=
    CompressionActualAnnulusHalfSupportedClosedStripV848.annulus_half_supported_closed_strip
      q hq hq0 hqout hqbound ε hε hε1
  let B : Set Plane := {x | (3/2:ℝ) < ‖x‖ ∧ ‖x‖ < 5/2}
  have hBo : IsOpen B := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have hBcl : closure B ⊆ {x : Plane | (3/2:ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 5/2} :=
    closure_minimal (fun _ hx => ⟨hx.1.le,hx.2.le⟩)
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
  have hBc : IsCompact (closure B) := (isCompact_closedBall (0 : Plane) (5/2)).of_isClosed_subset
    isClosed_closure (fun _ hx => mem_closedBall_zero_iff.mpr (hBcl hx).2)
  let U : Set Plane := W ∪ B
  have hUo : IsOpen U := hW.union hBo
  have hUc : IsCompact (closure U) := by
    rw [closure_union]
    exact hWc.union hBc
  have hUn (x : Plane) (hx : x ∈ closure U) : 1 < ‖x‖ ∧ ‖x‖ < 3 := by
    rw [closure_union] at hx
    rcases hx with hx | hx
    · exact ⟨lt_of_not_ge (fun hn => disjoint_left.mp hWD hx (mem_closedBall_zero_iff.mpr hn)),
        mem_ball_zero_iff.mp (hWR hx)⟩
    · obtain ⟨hlo,hhi⟩ := hBcl hx
      constructor <;> linarith
  have hUzero : closure U ×ˢ ({0} : Set ℝ) ⊆ e.source := by
    rintro ⟨x,z⟩ ⟨hx,hz⟩
    have hz0 : z = 0 := mem_singleton_iff.mp hz
    rw [hz0]
    exact he x (hUn x hx).1 (hUn x hx).2
  let Q : Set M := Z ∪ (𝓡∂ 3).boundary M
  have hQc : IsClosed Q := hZ.union ((𝓡∂ 3).isClosed_boundary (M := M) (n := 1) (by norm_num))
  have hUQ : Disjoint (e '' (closure U ×ˢ {0})) Q := by
    apply disjoint_left.mpr
    rintro y ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩ (hy | hy)
    · have hz0 : z = 0 := mem_singleton_iff.mp hz
      exact (haway x (hUn x hx).1 (hUn x hx).2).1 (hz0 ▸ hy)
    · have hz0 : z = 0 := mem_singleton_iff.mp hz
      exact (haway x (hUn x hx).1 (hUn x hx).2).2 (hz0 ▸ hy)
  obtain ⟨δ,hδ,hδs,hδQ⟩ :=
    CompressionActualThinCompactNormalNeighborhoodV847.chart_normal_block_away_closed_set
      e (closure U) hUc hUzero Q hQc hUQ
  have hKoff : ∀ t x,x ∉ U → K t x = x := fun t x hx => hoff t x (fun hw => hx (Or.inl hw))
  obtain ⟨L,hL,hL0,hLzero,-,hLoff,hLo,hLc,-⟩ :=
    CompressionActualTaperedNormalBlockIsotopyV837.tapered_normal_block_isotopy
      K hK h0 U hUo hUc hKoff δ hδ
  let C : Set (Plane × ℝ) := U ×ˢ Ioo (-δ) δ
  have hcl : closure C ⊆ closure U ×ˢ Icc (-δ) δ := by
    rw [closure_prod_eq]
    exact prod_mono Subset.rfl (closure_minimal Ioo_subset_Icc_self isClosed_Icc)
  obtain ⟨I,hV,hVc,hVZ,hVbd,hIo,hIbd,hIon⟩ :=
    CompressionActualSupportedChartAmbientIsotopyV846.supported_chart_ambient_isotopy
      e C hLo hLc (hcl.trans hδs) L hL hL0 hLoff Q
      (hδQ.mono_left (image_mono hcl))
      ((hδQ.mono_left (image_mono hcl)).mono_right subset_union_right)
  refine ⟨I,e '' C,hV,hVc,hVZ.mono_right subset_union_left,hVbd,?_,hIo,hIbd,?_⟩
  · intro z
    have hn : ‖(2:ℝ) • circleVector z‖ = 2 := by
      rw [norm_smul,circleVector_norm,Real.norm_eq_abs]; norm_num
    exact ⟨((2:ℝ) • circleVector z,0),⟨Or.inr (by change 3/2 < _ ∧ _ < 5/2; rw [hn]; norm_num),
      ⟨by linarith, hδ⟩⟩,rfl⟩
  · intro z t ht
    let x : Plane := (1+(t:ℝ)) • circleVector z
    have hnx : ‖x‖ = 1+(t:ℝ) := by
      dsimp [x]
      rw [norm_smul,circleVector_norm,Real.norm_eq_abs,
        abs_of_pos (by linarith [t.property.1] : 0 < 1+(t:ℝ)),mul_one]
    have hxS : (x,0) ∈ e.source := he x (by rw [hnx]; linarith) (by rw [hnx]; linarith [t.property.2])
    have hKI : I.stage 1 (e (x,0)) = e (K 1 x,0) := by
      by_cases hxU : x ∈ U
      · have hxC : (x,0) ∈ closure C := subset_closure ⟨hxU,⟨by linarith,hδ⟩⟩
        exact (hIon 1 (x,0) hxC).trans (congrArg e (hLzero 1 x))
      · have hxe : e (x,0) ∉ e '' C := by
          rintro ⟨p,hp,hpe⟩
          have hpS : p ∈ e.source := hδs (hcl (subset_closure hp))
          have hpx : p = (x,0) := e.injOn hpS hxS hpe
          exact hxU (hpx ▸ hp).1
        rw [hIo _ _ hxe,hKoff _ _ hxU]
    exact hKI.trans (congrArg (fun y : Plane => e (y,0)) (h1 z t ht))

#print axioms annular_strip_ambient_extension
end CompressionActualAnnularStripAmbientExtensionV851
