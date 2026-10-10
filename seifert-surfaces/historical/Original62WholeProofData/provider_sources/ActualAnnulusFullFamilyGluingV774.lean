import ActualAnnulusHalfCoordinatesV772

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualAnnulusFullFamilyGluingV774

def radial (k : Fin 2) (p : Circle × Time) : Circle × Time :=
  (p.1,Set.projIcc 0 1 zero_le_one
    (if k = 0 then 1-2*(p.2:ℝ) else 2*(p.2:ℝ)-1))

lemma radial_continuous (k : Fin 2) : Continuous (radial k) := by
  apply Continuous.prodMk continuous_fst
  apply continuous_projIcc.comp
  fin_cases k <;> dsimp <;> fun_prop

lemma radial_half (k : Fin 2) (p : Circle × Time) : radial k (half k p) = p := by
  refine Prod.ext (by rfl) ?_
  fin_cases k
  · dsimp [radial,half,halfTime]
    rw [show (1:ℝ)-2*((1-(p.2:ℝ))/2)=(p.2:ℝ) by ring]
    exact Set.projIcc_of_mem zero_le_one p.2.property
  · dsimp [radial,half,halfTime]
    rw [show (2:ℝ)*((1+(p.2:ℝ))/2)-1=(p.2:ℝ) by ring]
    exact Set.projIcc_of_mem zero_le_one p.2.property

lemma radial_core (k : Fin 2) (z : Circle) : radial k (z,middleTime) = (z,0) := by
  rw [← half_core k z,radial_half]

lemma half_cover (p : Circle × Time) : ∃ k q,half k q = p := by
  by_cases hp : p.2.val ≤ 1/2
  · have hs : side 0 p := hp
    exact ⟨0,unhalf 0 p hs,half_unhalf _ _ _⟩
  · have hs : side 1 p := (lt_of_not_ge hp).le
    exact ⟨1,unhalf 1 p hs,half_unhalf _ _ _⟩

/-- Glue the two whole confined half-families along their literal fixed core. -/
theorem full_family_gluing
    (Γ : Fin 2 → C(Time × (Circle × Time),Circle × Time))
    (hΓ : ∀ k s,IsEmbedding (fun p => Γ k (s,p)))
    (hcore : ∀ k s z,Γ k (s,(z,0)) = (z,0)) :
    ∃ G : C(Time × (Circle × Time),Circle × Time),
      (∀ k s p,G (s,half k p) = half k (Γ k (s,p))) ∧
      (∀ s,IsEmbedding (fun p => G (s,p))) ∧
      ∀ s z,G (s,(z,middleTime)) = (z,middleTime) := by
  classical
  let g (k : Fin 2) : Time × (Circle × Time) → Circle × Time :=
    fun p => half k (Γ k (p.1,radial k p.2))
  have hgc (k : Fin 2) : Continuous (g k) := (half_continuous k).comp
    ((Γ k).continuous.comp (continuous_fst.prodMk ((radial_continuous k).comp continuous_snd)))
  let G : Time × (Circle × Time) → Circle × Time :=
    fun p => if (p.2.2:ℝ) ≤ 1/2 then g 0 p else g 1 p
  have hGc : Continuous G := by
    apply continuous_if_le continuous_snd.snd.subtype_val continuous_const
      (hgc 0).continuousOn (hgc 1).continuousOn
    intro p hp
    have ht : p.2.2 = middleTime := Subtype.ext hp
    change half 0 (Γ 0 (p.1,radial 0 p.2)) = half 1 (Γ 1 (p.1,radial 1 p.2))
    have he : p.2 = (p.2.1,middleTime) := Prod.ext rfl ht
    rw [he,radial_core,radial_core,hcore,hcore,half_core,half_core]
  have hGcore (s : Time) (z : Circle) : G (s,(z,middleTime)) = (z,middleTime) := by
    dsimp only [G]
    rw [ite_eq_left (by change (1/2:ℝ) ≤ 1/2; rfl)]
    change half 0 (Γ 0 (s,radial 0 (z,middleTime))) = _
    rw [radial_core,hcore,half_core]
  have hGhalf (k : Fin 2) (s : Time) (p : Circle × Time) :
      G (s,half k p) = half k (Γ k (s,p)) := by
    fin_cases k
    · have hp : ((half 0 p).2:ℝ) ≤ 1/2 := half_side 0 p
      change (if ((half 0 p).2:ℝ) ≤ 1/2 then g 0 (s,half 0 p) else g 1 (s,half 0 p)) =
        half 0 (Γ 0 (s,p))
      rw [ite_eq_left hp]
      change half 0 (Γ 0 (s,radial 0 (half 0 p))) = _
      rw [radial_half]
    · by_cases hp : p.2 = 0
      · have he : p = (p.1,0) := Prod.ext rfl hp
        rw [he,half_core,hGcore,hcore,half_core]
      · have ht : 1/2 < ((half 1 p).2:ℝ) := by
          have hn : 0 < p.2.val := lt_of_le_of_ne p.2.property.1
            (by intro he; exact hp (Subtype.ext he.symm))
          dsimp [half,halfTime]
          linarith
        change (if ((half 1 p).2:ℝ) ≤ 1/2 then g 0 (s,half 1 p) else g 1 (s,half 1 p)) =
          half 1 (Γ 1 (s,p))
        rw [ite_eq_right (not_le_of_gt ht)]
        change half 1 (Γ 1 (s,radial 1 (half 1 p))) = _
        rw [radial_half]
  have hGinj (s : Time) : Function.Injective (fun p => G (s,p)) := by
    intro p q he
    change G (s,p) = G (s,q) at he
    obtain ⟨k,r,hr⟩ := half_cover p
    obtain ⟨l,u,hu⟩ := half_cover q
    rw [← hr,← hu,hGhalf,hGhalf] at he
    have hsame (k : Fin 2) (r u : Circle × Time)
        (he : half k (Γ k (s,r)) = half k (Γ k (s,u))) : half k r = half k u := by
      exact congrArg (half k) ((hΓ k s).injective (half_injective k he))
    have hcross (r u : Circle × Time)
        (he : half 0 (Γ 0 (s,r)) = half 1 (Γ 1 (s,u))) : half 0 r = half 1 u := by
      obtain ⟨hz,ht,ht'⟩ := opposite_half_eq _ _ he
      have he0 : Γ 0 (s,r) = ((Γ 0 (s,r)).1,0) := Prod.ext rfl ht
      have he1 : Γ 1 (s,u) = ((Γ 1 (s,u)).1,0) := Prod.ext rfl ht'
      have hr' : r = ((Γ 0 (s,r)).1,0) := (hΓ 0 s).injective (he0.trans (hcore 0 s _).symm)
      have hu' : u = ((Γ 1 (s,u)).1,0) := (hΓ 1 s).injective (he1.trans (hcore 1 s _).symm)
      rw [hr',hu',half_core,half_core,hz]
    have he' : half k r = half l u := by
      fin_cases k <;> fin_cases l
      · exact hsame 0 r u he
      · exact hcross r u he
      · exact (hcross u r he.symm).symm
      · exact hsame 1 r u he
    exact hr.symm.trans (he'.trans hu)
  refine ⟨⟨G,hGc⟩,hGhalf,?_,hGcore⟩
  intro s
  exact ((hGc.comp (continuous_const.prodMk continuous_id)).isClosedEmbedding
    (hGinj s)).isEmbedding

end CompressionActualAnnulusFullFamilyGluingV774
