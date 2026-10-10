import ActualAnnulusHalfPolarModelV768

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Topology
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
noncomputable section
namespace CompressionActualAnnulusHalfCoordinatesV772

def halfTime (k : Fin 2) (t : Time) : Time :=
  ⟨if k = 0 then (1-(t:ℝ))/2 else (1+(t:ℝ))/2,by
    split_ifs <;> constructor <;> linarith [t.property.1,t.property.2]⟩

lemma halfTime_zero (k : Fin 2) : halfTime k 0 = middleTime := by
  apply Subtype.ext
  fin_cases k <;> simp [halfTime,middleTime]

lemma halfTime_continuous (k : Fin 2) : Continuous (halfTime k) := by
  apply Continuous.subtype_mk
  fin_cases k <;> dsimp [halfTime] <;> fun_prop

lemma halfTime_injective (k : Fin 2) : Function.Injective (halfTime k) := by
  intro t u he
  have h := congrArg Subtype.val he
  apply Subtype.ext
  fin_cases k <;> dsimp [halfTime] at h <;> linarith

def half (k : Fin 2) (p : Circle × Time) : Circle × Time := (p.1,halfTime k p.2)

lemma half_continuous (k : Fin 2) : Continuous (half k) :=
  continuous_fst.prodMk ((halfTime_continuous k).comp continuous_snd)

lemma half_injective (k : Fin 2) : Function.Injective (half k) := by
  intro p q he
  have hz := congrArg (fun a : Circle × Time => a.1) he
  have ht := congrArg (fun a : Circle × Time => a.2) he
  change p.1 = q.1 at hz
  change halfTime k p.2 = halfTime k q.2 at ht
  exact Prod.ext hz (halfTime_injective k ht)

lemma half_embedding (k : Fin 2) : IsEmbedding (half k) :=
  ((half_continuous k).isClosedEmbedding (half_injective k)).isEmbedding

def side (k : Fin 2) (p : Circle × Time) : Prop :=
  if k = 0 then (p.2:ℝ) ≤ 1/2 else 1/2 ≤ (p.2:ℝ)

lemma half_side (k : Fin 2) (p : Circle × Time) : side k (half k p) := by
  fin_cases k <;> dsimp [side,half,halfTime] <;> linarith [p.2.property.1]

def unhalf (k : Fin 2) (p : Circle × Time) (hp : side k p) : Circle × Time :=
  (p.1,⟨if k = 0 then 1-2*(p.2:ℝ) else 2*(p.2:ℝ)-1,by
    fin_cases k <;> dsimp [side] at hp ⊢ <;> constructor <;>
      linarith [p.2.property.1,p.2.property.2]⟩)

lemma half_unhalf (k : Fin 2) (p : Circle × Time) (hp : side k p) :
    half k (unhalf k p hp) = p := by
  refine Prod.ext (by rfl) ?_
  apply Subtype.ext
  fin_cases k <;> dsimp [half,halfTime,unhalf] <;> ring

lemma unhalf_half (k : Fin 2) (p : Circle × Time) :
    unhalf k (half k p) (half_side k p) = p := by
  apply half_injective k
  exact half_unhalf _ _ _

lemma half_core (k : Fin 2) (z : Circle) : half k (z,0) = (z,middleTime) := by
  exact Prod.ext rfl (halfTime_zero k)

lemma opposite_half_eq (p q : Circle × Time) (he : half 0 p = half 1 q) :
    p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 := by
  have hz := congrArg Prod.fst he
  have ht := congrArg (fun p : Circle × Time => p.2.val) he
  dsimp [half,halfTime] at ht
  refine ⟨hz,Subtype.ext ?_,Subtype.ext ?_⟩ <;>
    change _ = (0:ℝ) <;> linarith [p.2.property.1,q.2.property.1]

end CompressionActualAnnulusHalfCoordinatesV772
