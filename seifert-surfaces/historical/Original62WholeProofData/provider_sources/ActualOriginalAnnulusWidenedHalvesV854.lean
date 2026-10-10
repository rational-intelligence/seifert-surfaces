import ActualAnnulusEmbeddingOpenMiddleV853
import ActualAnnulusHalfCoordinatesV772

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped Manifold ContDiff
open Set Topology Metric
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
open CompressionActualAnnulusHalfCoordinatesV772
noncomputable section
namespace CompressionActualOriginalAnnulusWidenedHalvesV854

/-- Widen each literal original annulus half by its actual outside collar.
    Its original half is retained with every parameter label, and its open
    middle is a genuine native surface neighborhood across the original edge. -/
theorem original_annulus_widened_halves
    {S : CompactOrientedSurface.{0}} {M : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    {f : NeatEmbedding S M} {D : InteriorCompressingDisk f}
    (A : CompressionAnnulus D) :
    ∃ w : Fin 2 → C(Circle × Time,S),
      (∀ k,IsEmbedding (w k)) ∧
      (∀ k z,w k (z,0) = D.surfaceLoop z) ∧
      (∀ k z,w k (z,middleTime) = A.band (z,CompressionAnnulus.sideTime k)) ∧
      (∀ k (z : Circle) (t : Time),w k (z,⟨t.val/2,by constructor; exact div_nonneg t.property.1 (by norm_num); linarith [t.property.2]⟩) =
        A.band (half k (z,t))) ∧
      (∀ k,IsOpen (w k '' {p : Circle × Time | 0 < p.2.val ∧ p.2.val < 1})) ∧
      ∀ k,range (w k) ⊆ S.boundaryᶜ := by
  classical
  obtain ⟨κ,hκ,hκ0,hκout,-,-,hκbd⟩ := original_compression_annulus_outside_collars_v835 A
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
    CompressionActualAnnulusEmbeddingOpenMiddleV853.annulus_embedding_open_middle S (w k) (hwemb k),?_⟩
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

#print axioms original_annulus_widened_halves
end CompressionActualOriginalAnnulusWidenedHalvesV854
