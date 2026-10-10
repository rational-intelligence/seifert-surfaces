import CurveComplexGenusTwo.Topology.ActualFareyClassification.CompactLatticeContacts
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFarSideEndpoints

open Set Topology Schoenflies Metric

/-- Actual compact full-grid finiteness isolates both old corners throughout
an enlarged parameter interval. No two-event certificate is input. -/
theorem normalized_clean_bigon_has_actual_enlarged_two_event_interval
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c r s : ℝ) (hT : 0<T)
    (hrs : r<s) (hshort : s-r<T)
    (hp : ∀ (k : ℤ) (t : ℝ), G (t+(k:ℝ)*T)=G t+Plane.mk ((k:ℝ)*T) 0)
    (hfinite : {t : ℝ | G t 0=c}.Finite)
    (hno : ∀ i : ℤ, ∀ t∈Ioo r s, G t 0≠c+(i:ℝ)*T) :
    ∃ a b : ℝ, a<r ∧ s<b ∧ b-a<T ∧
      ∀ t∈Icc a b, (∃ i : ℤ, G t 0=c+(i:ℝ)*T) → t=r ∨ t=s := by
  let K := G '' Icc (r-1) (s+1)
  have hK : IsCompact K := isCompact_Icc.image G.continuous
  have hfin := normalized_line_full_grid_contacts_finite_in_compact G T c hT hp hfinite K hK
  let E := {t : ℝ | t∈Icc (r-1) (s+1) ∧ ∃ i : ℤ, G t 0=c+(i:ℝ)*T}
  have hE : E.Finite := by
    apply (hfin.preimage hG.injective.injOn).subset
    intro t ht
    refine ⟨⟨mem_iUnion.mpr ⟨0,t,?_⟩,ht.2⟩,t,ht.1,rfl⟩
    ext k
    fin_cases k <;> simp [Plane.mk]
  let P := E\{r,s}
  let O := Pᶜ∩Ioo (r-1) (s+1)
  have hO : IsOpen O := (show IsClosed P from hE.sdiff.isClosed).isOpen_compl.inter isOpen_Ioo
  have hcore : Icc r s⊆O := by
    intro t ht
    refine ⟨?_,⟨by linarith [ht.1],by linarith [ht.2]⟩⟩
    rintro ⟨htE,htP⟩
    by_cases htr : t=r
    · exact htP (Or.inl htr)
    by_cases hts : t=s
    · exact htP (Or.inr hts)
    obtain ⟨i,hi⟩ := htE.2
    exact hno i t ⟨lt_of_le_of_ne ht.1 (Ne.symm htr),lt_of_le_of_ne ht.2 hts⟩ hi
  obtain ⟨ε,hε,hεO⟩ := isCompact_Icc.exists_cthickening_subset_open hO hcore
  let d := min (ε/2) ((T-(s-r))/4)
  have hd : 0<d := by dsimp [d]; positivity
  have hdε : d ≤ ε := by
    have hh := min_le_left (ε/2) ((T-(s-r))/4)
    dsimp [d]; linarith
  have hdT : d ≤ (T-(s-r))/4 := min_le_right _ _
  have hnear : Icc (r-d) (s+d)⊆O := by
    intro t ht
    apply hεO
    by_cases htr : t<r
    · apply mem_cthickening_of_dist_le t r ε (Icc r s) ⟨le_rfl,hrs.le⟩
      rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr htr.le)]
      linarith [ht.1]
    by_cases hst : s<t
    · apply mem_cthickening_of_dist_le t s ε (Icc r s) ⟨hrs.le,le_rfl⟩
      rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hst.le)]
      linarith [ht.2]
    · exact self_subset_cthickening (Icc r s) ⟨le_of_not_gt htr,le_of_not_gt hst⟩
  refine ⟨r-d,s+d,by linarith,by linarith,by linarith,?_⟩
  intro t ht hgrid
  have htO := hnear ht
  by_contra hn
  apply htO.1
  refine ⟨⟨⟨htO.2.1.le,htO.2.2.le⟩,hgrid⟩,?_⟩
  intro hh
  exact hn hh

#print axioms normalized_clean_bigon_has_actual_enlarged_two_event_interval
