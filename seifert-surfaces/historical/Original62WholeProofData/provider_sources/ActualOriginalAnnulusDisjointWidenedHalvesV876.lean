import ActualCompactCollarNeighborhoodV857
import ActualAnnulusHalfCoordinatesV772

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualOriginalAnnulusDisjointWidenedHalvesV876

/-- Widen each literal original annulus half by its actual outside collar.
    Its original half is retained with every parameter label, and its open
    middle is a genuine native surface neighborhood across the original edge. -/
theorem original_annulus_disjoint_widened_halves
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) (U : Set S) (hU : IsOpen U) (hAU : range A.band ⊆ U) :
    ∃ w : Fin 2 → C(Circle × Time,S),
      (∀ k,IsEmbedding (w k)) ∧
      (∀ k z,w k (z,0) = D.surfaceLoop z) ∧
      (∀ k z,w k (z,middleTime) = A.band (z,CompressionAnnulus.sideTime k)) ∧
      (∀ k (z : Circle) (t : Time),w k (z,⟨t.val/2,by constructor; exact div_nonneg t.property.1 (by norm_num); linarith [t.property.2]⟩) =
        A.band (half k (z,t))) ∧
      (∀ k,IsOpen (w k '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1})) ∧
      (∀ k,range (w k) ⊆ S.boundaryᶜ) ∧ (∀ k,range (w k) ⊆ U) ∧
      Disjoint
        (w 0 '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1})
        (w 1 '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1}) := by
  classical
  obtain ⟨ξ,hξ,hξ0,hξout,-,hξdis,hξbd⟩ := original_compression_annulus_outside_collars_v835 A
  let c (k : Fin 2) : C(Circle × Time,S) := ⟨fun p => (ξ k p).val,
    continuous_subtype_val.comp (ξ k).continuous⟩
  have hc0 (k : Fin 2) (z : Circle) : c k (z,0) ∈ U := by
    change (ξ k (z,0)).val ∈ U
    rw [hξ0]
    exact hAU (mem_range_self _)
  choose r hr hr1 hrU using fun k : Fin 2 =>
    CompressionActualCompactCollarNeighborhoodV857.compact_collar_neighborhood (c k) U hU (hc0 k)
  let R (k : Fin 2) (t : Time) : Time := ⟨r k*t.val,mul_nonneg (hr k).le t.property.1,
    (mul_le_mul_of_nonneg_left t.property.2 (hr k).le).trans (by simpa using (hr1 k).le)⟩
  have hR (k : Fin 2) : Continuous (R k) := by apply Continuous.subtype_mk; fun_prop
  have hRi (k : Fin 2) : Function.Injective (R k) := by
    intro t u he
    exact Subtype.ext (mul_left_cancel₀ (hr k).ne' (congrArg Subtype.val he))
  have hR0 (k : Fin 2) : R k 0 = 0 := Subtype.ext (by simp [R])
  let κ (k : Fin 2) : C(Circle × Time,A.Remainder) := ⟨fun p => ξ k (p.1,R k p.2),
    (ξ k).continuous.comp (continuous_fst.prodMk ((hR k).comp continuous_snd))⟩
  have hκ (k : Fin 2) : IsEmbedding (κ k) := (κ k).continuous.isClosedEmbedding (by
    intro p q he
    have hv := (hξ k).injective he
    have hz := congrArg (fun p : Circle × Time => p.1) hv
    have ht := congrArg (fun p : Circle × Time => p.2) hv
    exact Prod.ext hz (hRi k ht)) |>.isEmbedding
  have hκ0 (k : Fin 2) (z : Circle) : κ k (z,0) = A.edgePoint k z := by
    change ξ k (z,R k 0) = _
    rw [hR0,hξ0]
  have hκout (k : Fin 2) (p : Circle × Time) (hp : 0 < p.2.val) : (κ k p).val ∉ range A.band :=
    hξout k (p.1,R k p.2) (mul_pos (hr k) hp)
  have hκdis : Disjoint (range (κ 0)) (range (κ 1)) :=
    hξdis.mono (by rintro x ⟨p,rfl⟩; exact mem_range_self _)
      (by rintro x ⟨p,rfl⟩; exact mem_range_self _)
  have hκbd (k : Fin 2) : range (fun p => (κ k p).val) ⊆ S.boundaryᶜ := by
    rintro x ⟨p,rfl⟩
    exact hξbd k (mem_range_self _)
  have hκU (k : Fin 2) (p : Circle × Time) : (κ k p).val ∈ U :=
    hrU k p.1 (R k p.2) (by change r k*p.2.val ≤ r k
                            exact (mul_le_mul_of_nonneg_left p.2.property.2 (hr k).le).trans_eq (mul_one _))
  let a (t : Time) : Time := ⟨min 1 (2*t.val),le_min (by norm_num) (mul_nonneg (by norm_num) t.property.1),min_le_left _ _⟩
  let b (t : Time) : Time := ⟨max 0 (2*t.val-1),le_max_left _ _,max_le (by norm_num) (by linarith [t.property.2])⟩
  have hac : Continuous a := by apply Continuous.subtype_mk; fun_prop
  have hbc : Continuous b := by apply Continuous.subtype_mk; fun_prop
  have hav (t : Time) (ht : t.val ≤ 1/2) : (a t).val = 2*t.val :=
    min_eq_right (by linarith)
  have hbv (t : Time) (ht : 1/2 ≤ t.val) : (b t).val = 2*t.val-1 :=
    max_eq_right (by linarith)
  have haM : a middleTime = 1 := Subtype.ext (by norm_num [a,middleTime])
  have hbM : b middleTime = 0 := Subtype.ext (by norm_num [b,middleTime])
  have hh (k : Fin 2) (z : Circle) : half k (z,(1:Time)) = (z,CompressionAnnulus.sideTime k) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    fin_cases k <;> norm_num [half,halfTime,CompressionAnnulus.sideTime]
  let inn (k : Fin 2) : Circle × Time → S := fun p => A.band (half k (p.1,a p.2))
  let out (k : Fin 2) : Circle × Time → S := fun p => (κ k (p.1,b p.2)).val
  have hinn (k : Fin 2) : Continuous (inn k) := A.band.continuous.comp
    ((half_continuous k).comp (continuous_fst.prodMk (hac.comp continuous_snd)))
  have hout (k : Fin 2) : Continuous (out k) := continuous_subtype_val.comp
    ((κ k).continuous.comp (continuous_fst.prodMk (hbc.comp continuous_snd)))
  let wf (k : Fin 2) : Circle × Time → S := fun p =>
    if p.2.val ≤ 1/2 then inn k p else out k p
  have hwc (k : Fin 2) : Continuous (wf k) := by
    apply continuous_if_le continuous_snd.subtype_val continuous_const (hinn k).continuousOn (hout k).continuousOn
    intro p hp
    have ht : p.2 = middleTime := Subtype.ext hp
    change A.band (half k (p.1,a p.2)) = (κ k (p.1,b p.2)).val
    rw [ht,haM,hbM,hκ0,hh]
    rfl
  have hwi (k : Fin 2) : Function.Injective (wf k) := by
    intro p q he
    dsimp only [wf] at he
    split_ifs at he with hp hq hq
    · have hv := half_injective k (A.embedded.injective he)
      have hz := congrArg (fun x : Circle × Time => x.1) hv
      have ht := congrArg (fun x : Circle × Time => x.2.val) hv
      change (a p.2).val = (a q.2).val at ht
      rw [hav _ hp,hav _ hq] at ht
      exact Prod.ext hz (Subtype.ext (by linarith))
    · have hbq : 0 < (b q.2).val := by rw [hbv _ (le_of_lt (lt_of_not_ge hq))]; linarith [lt_of_not_ge hq]
      exact False.elim (hκout k (q.1,b q.2) hbq ⟨half k (p.1,a p.2),he⟩)
    · have hbp : 0 < (b p.2).val := by rw [hbv _ (le_of_lt (lt_of_not_ge hp))]; linarith [lt_of_not_ge hp]
      exact False.elim (hκout k (p.1,b p.2) hbp ⟨half k (q.1,a q.2),he.symm⟩)
    · have hv := (hκ k).injective (Subtype.ext he)
      have hz := congrArg (fun x : Circle × Time => x.1) hv
      have ht := congrArg (fun x : Circle × Time => x.2.val) hv
      change (b p.2).val = (b q.2).val at ht
      rw [hbv _ (le_of_lt (lt_of_not_ge hp)),hbv _ (le_of_lt (lt_of_not_ge hq))] at ht
      exact Prod.ext hz (Subtype.ext (by linarith))
  let w (k : Fin 2) : C(Circle × Time,S) := ⟨wf k,hwc k⟩
  have hwemb (k : Fin 2) : IsEmbedding (w k) := ((w k).continuous.isClosedEmbedding (hwi k)).isEmbedding
  refine ⟨w,hwemb,?_,?_,?_,fun k =>
    CompressionActualAnnulusEmbeddingOpenMiddleV853.annulus_embedding_open_middle S (w k) (hwemb k),?_,?_,?_⟩
  · intro k z
    change wf k (z,0) = D.surfaceLoop z
    rw [show wf k (z,0) = A.band (half k (z,0)) by simp [wf,inn,a],half_core,A.center]
  · intro k z
    change wf k (z,middleTime) = A.band (z,CompressionAnnulus.sideTime k)
    dsimp only [wf,inn]
    rw [ite_eq_left (by norm_num [middleTime]),haM,hh]
  · intro k z t
    let s : Time := ⟨t.val/2,by constructor; exact div_nonneg t.property.1 (by norm_num); linarith [t.property.2]⟩
    have hs : s.val ≤ 1/2 := by dsimp [s]; linarith [t.property.2]
    have ha : a s = t := Subtype.ext (by rw [hav _ hs]; dsimp [s]; ring)
    change wf k (z,s) = A.band (half k (z,t))
    dsimp only [wf,inn]
    rw [ite_eq_left hs,ha]
  · intro k x hx
    obtain ⟨p,rfl⟩ := hx
    change wf k p ∈ S.boundaryᶜ
    dsimp only [wf]
    split_ifs
    · exact A.interior_surface (mem_range_self _)
    · exact hκbd k (mem_range_self _)

  · intro k x hx
    obtain ⟨p,rfl⟩ := hx
    change wf k p ∈ U
    dsimp only [wf]
    split_ifs
    · exact hAU (mem_range_self _)
    · exact hκU k _

  · apply disjoint_left.mpr
    rintro x ⟨p,hp,rfl⟩ ⟨q,hq,he⟩
    have he' : wf 0 p = wf 1 q := he.symm
    dsimp only [wf] at he'
    split_ifs at he' with hpi hqi hqi
    · have hh := opposite_half_eq (p.1,a p.2) (q.1,a q.2) (A.embedded.injective he')
      have hz := congrArg Subtype.val hh.2.1
      change (a p.2).val = 0 at hz
      rw [hav _ hpi] at hz
      linarith [hp.1]
    · have hbq : 0 < (b q.2).val := by
        rw [hbv _ (le_of_lt (lt_of_not_ge hqi))]
        linarith [lt_of_not_ge hqi]
      exact hκout 1 (q.1,b q.2) hbq ⟨half 0 (p.1,a p.2),he'⟩
    · have hbp : 0 < (b p.2).val := by
        rw [hbv _ (le_of_lt (lt_of_not_ge hpi))]
        linarith [lt_of_not_ge hpi]
      exact hκout 0 (p.1,b p.2) hbp ⟨half 1 (q.1,a q.2),he'.symm⟩
    · exact disjoint_left.mp hκdis (mem_range_self (p.1,b p.2))
        ⟨(q.1,b q.2),Subtype.ext he'.symm⟩

#print axioms original_annulus_disjoint_widened_halves
end CompressionActualOriginalAnnulusDisjointWidenedHalvesV876
