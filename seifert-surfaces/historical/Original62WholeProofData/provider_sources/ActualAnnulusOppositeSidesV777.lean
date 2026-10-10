import ActualAnnulusHalfSideClassificationV776

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
open CompressionActualAnnulusFullFamilyGluingV774
noncomputable section
namespace CompressionActualAnnulusOppositeSidesV777

theorem open_core_has_both_sides (U : Set (Circle × Time)) (hU : IsOpen U)
    (z : Circle) (hz : (z,middleTime) ∈ U) :
    ∃ t₀ t₁ : Time,(z,t₀) ∈ U ∧ (z,t₁) ∈ U ∧
      t₀.val < 1/2 ∧ 1/2 < t₁.val := by
  let v : Time → Circle × Time := fun t => (z,t)
  have hv : Continuous v := continuous_const.prodMk continuous_id
  have hV : IsOpen (v ⁻¹' U) := hU.preimage hv
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hz)
  let a : ℝ := min (r/2) (1/4)
  have ha : 0 < a := lt_min (half_pos hr) (by norm_num)
  have ha4 : a ≤ 1/4 := min_le_right _ _
  have har : a < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  let t₀ : Time := ⟨1/2-a,by constructor <;> linarith⟩
  let t₁ : Time := ⟨1/2+a,by constructor <;> linarith⟩
  have ht₀ : t₀ ∈ Metric.ball middleTime r := by
    change dist t₀ middleTime < r
    rw [Subtype.dist_eq,Real.dist_eq]
    change |(1/2-a)-(1/2)| < r
    rw [show (1/2-a)-(1/2) = -a by ring,abs_neg,abs_of_pos ha]
    exact har
  have ht₁ : t₁ ∈ Metric.ball middleTime r := by
    change dist t₁ middleTime < r
    rw [Subtype.dist_eq,Real.dist_eq]
    change |(1/2+a)-(1/2)| < r
    rw [show (1/2+a)-(1/2) = a by ring,abs_of_pos ha]
    exact har
  refine ⟨t₀,t₁,hball ht₀,hball ht₁,?_,?_⟩ <;> dsimp [t₀,t₁] <;> linarith

/-- The two side choices are necessarily opposite because the embedded open
    band contains an open neighborhood of every literal core point. -/
theorem annulus_half_side_permutation
    (β : C(Circle × Time,Circle × Time)) (hβ : IsEmbedding β)
    (hcore : ∀ z,β (z,middleTime) = (z,middleTime))
    (hopen : IsOpen (β '' (Set.univ ×ˢ Set.Ioo (0:Time) 1))) :
    ∃ π : Fin 2 ≃ Fin 2,∀ k p,side (π k) (β (half k p)) := by
  classical
  choose f hf using fun k =>
    CompressionActualAnnulusHalfSideClassificationV776.half_has_one_side β hβ hcore k
  have hdiff : f 0 ≠ f 1 := by
    intro he
    have hall (p : Circle × Time) : side (f 0) (β p) := by
      obtain ⟨k,q,rfl⟩ := half_cover p
      fin_cases k
      · exact hf 0 q
      · rw [he]
        exact hf 1 q
    let U : Set (Circle × Time) := β '' (Set.univ ×ˢ Set.Ioo (0:Time) 1)
    have hUcore : ((1:Circle),middleTime) ∈ U := by
      refine ⟨((1:Circle),middleTime),⟨mem_univ _,?_,?_⟩,hcore 1⟩
      · change (0:ℝ) < 1/2
        norm_num
      · change (1/2:ℝ) < 1
        norm_num
    obtain ⟨t₀,t₁,ht₀,ht₁,hleft,hright⟩ := open_core_has_both_sides U hopen 1 hUcore
    have hUside (p : Circle × Time) (hp : p ∈ U) : side (f 0) p := by
      obtain ⟨q,hq,rfl⟩ := hp
      exact hall q
    have h₀ := hUside (1,t₀) ht₀
    have h₁ := hUside (1,t₁) ht₁
    generalize hf0 : f 0 = m at h₀ h₁
    fin_cases m <;> dsimp [side] at h₀ h₁
    · linarith
    · linarith
  have hfinj : Function.Injective f := by
    intro k l he
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim (hdiff he)
    · exact False.elim (hdiff he.symm)
    · rfl
  let π : Fin 2 ≃ Fin 2 := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
  exact ⟨π,hf⟩

end CompressionActualAnnulusOppositeSidesV777
