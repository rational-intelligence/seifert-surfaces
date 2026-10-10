import A5NativeLocalCover

set_option autoImplicit false
open scoped Manifold ContDiff
open Set Topology
noncomputable section
namespace SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- Every ordinary point of a native arc has an open source neighborhood
whose entire seam is the chosen arbitrarily small parameter interval.
The neighborhood also avoids the literal source boundary. -/
theorem native_regular_arc_seam_isolation
    {S : CompactOrientedSurface.{u}} {f : S → M} (G : SeamGraph S f)
    (a : Fin G.arcCount) (s : Time) (hs0 : 0 < s) (hs1 : s < 1)
    (V : Set Time) (hV : IsOpen V) (hsV : s ∈ V) :
    ∃ U : Set S, IsOpen U ∧ G.arc a s ∈ U ∧ U ⊆ S.boundaryᶜ ∧
      G.carrier ∩ U = (G.arc a '' V) ∩ U := by
  classical
  let A (i : Fin G.arcCount) : Set S := if i = a then univ else (range (G.arc i))ᶜ
  let C (i : Fin G.circleCount) : Set S := (range (G.circle i))ᶜ
  have hA (i : Fin G.arcCount) : IsOpen (A i) := by
    by_cases hi : i = a
    · simp only [A, ite_eq_left hi]; exact isOpen_univ
    · simp only [A, ite_eq_right hi]
      exact (isCompact_range (G.arc i).continuous).isClosed.isOpen_compl
  have hC (i : Fin G.circleCount) : IsOpen (C i) :=
    (isCompact_range (G.circle i).continuous).isClosed.isOpen_compl
  have hxA (i : Fin G.arcCount) : G.arc a s ∈ A i := by
    by_cases hi : i = a
    · simp only [A, ite_eq_left hi, mem_univ]
    · simp only [A, ite_eq_right hi, mem_compl_iff]
      intro hm
      have he := (G.arc_intersections a i (Ne.symm hi) ⟨mem_range_self s, hm⟩).1
      rcases he with he | he
      · exact (ne_of_gt hs0) ((G.arc_embedding a).injective he)
      · exact (ne_of_lt hs1) ((G.arc_embedding a).injective he)
  have hxC (i : Fin G.circleCount) : G.arc a s ∈ C i := by
    exact fun hc => (Set.disjoint_left.mp (G.arc_circle_disjoint a i)) (mem_range_self s) hc
  have hxb : G.arc a s ∉ S.boundary := by
    intro hb
    rcases G.arc_boundary a hb with h | h
    · exact (ne_of_gt hs0) h
    · exact (ne_of_lt hs1) h
  let B := (G.arc a '' Vᶜ)ᶜ
  have hB : IsOpen B := (hV.isClosed_compl.isCompact.image (G.arc a).continuous).isClosed.isOpen_compl
  have hxB : G.arc a s ∈ B := by
    rintro ⟨t, ht, he⟩
    exact ht ((G.arc_embedding a).injective he ▸ hsV)
  let U := S.boundaryᶜ ∩ B ∩ (⋂ i, A i) ∩ (⋂ i, C i)
  have hU : IsOpen U :=
    ((((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.inter hB).inter
      (isOpen_iInter_of_finite hA)).inter (isOpen_iInter_of_finite hC)
  refine ⟨U, hU, ⟨⟨⟨hxb, hxB⟩, mem_iInter.mpr hxA⟩, mem_iInter.mpr hxC⟩,
    fun _ hy => hy.1.1.1, ?_⟩
  ext y
  constructor
  · rintro ⟨hyG, hyU⟩
    refine ⟨?_, hyU⟩
    rcases hyG with hya | hyc
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hya
      have hi : i = a := by
        by_contra hn
        have hnmem := mem_iInter.mp hyU.1.2 i
        simp only [A, ite_eq_right hn, mem_compl_iff] at hnmem
        exact hnmem (mem_range_self t)
      subst i
      exact ⟨t, by
        by_contra hn
        exact hyU.1.1.2 ⟨t, hn, rfl⟩, rfl⟩
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hyc
      exact False.elim ((mem_iInter.mp hyU.2 i) (mem_range_self t))
  · rintro ⟨⟨t, _, rfl⟩, hyU⟩
    exact ⟨Or.inl (mem_iUnion.mpr ⟨a, mem_range_self t⟩), hyU⟩

/-- A native circle component has the analogous exact local seam
isolation, for any open circle parameter neighborhood of its point. -/
theorem native_circle_seam_isolation
    {S : CompactOrientedSurface.{u}} {f : S → M} (G : SeamGraph S f)
    (a : Fin G.circleCount) (s : Circle)
    (V : Set Circle) (hV : IsOpen V) (hsV : s ∈ V) :
    ∃ U : Set S, IsOpen U ∧ G.circle a s ∈ U ∧ U ⊆ S.boundaryᶜ ∧
      G.carrier ∩ U = (G.circle a '' V) ∩ U := by
  classical
  let A (i : Fin G.arcCount) : Set S := (range (G.arc i))ᶜ
  let C (i : Fin G.circleCount) : Set S := if i = a then univ else (range (G.circle i))ᶜ
  have hA (i : Fin G.arcCount) : IsOpen (A i) :=
    (isCompact_range (G.arc i).continuous).isClosed.isOpen_compl
  have hC (i : Fin G.circleCount) : IsOpen (C i) := by
    by_cases hi : i = a
    · simp only [C, ite_eq_left hi]; exact isOpen_univ
    · simp only [C, ite_eq_right hi]
      exact (isCompact_range (G.circle i).continuous).isClosed.isOpen_compl
  have hxA (i : Fin G.arcCount) : G.circle a s ∈ A i :=
    fun ha => Set.disjoint_left.mp (G.arc_circle_disjoint i a) ha (mem_range_self s)
  have hxC (i : Fin G.circleCount) : G.circle a s ∈ C i := by
    by_cases hi : i = a
    · simp only [C, ite_eq_left hi, mem_univ]
    · simp only [C, ite_eq_right hi, mem_compl_iff]
      exact fun hm => Set.disjoint_left.mp (G.circle_intersections (Ne.symm hi)) (mem_range_self s) hm
  have hxb : G.circle a s ∉ S.boundary :=
    fun hb => Set.disjoint_left.mp (G.circle_off_boundary a) (mem_range_self s) hb
  let B := (G.circle a '' Vᶜ)ᶜ
  have hB : IsOpen B := (hV.isClosed_compl.isCompact.image (G.circle a).continuous).isClosed.isOpen_compl
  have hxB : G.circle a s ∈ B := by
    rintro ⟨t, ht, he⟩
    exact ht ((G.circle_embedding a).injective he ▸ hsV)
  let U := S.boundaryᶜ ∩ B ∩ (⋂ i, A i) ∩ (⋂ i, C i)
  have hU : IsOpen U :=
    ((((𝓡∂ 2).isClosed_boundary (M := S) (n := ∞) (by simp)).isOpen_compl.inter hB).inter
      (isOpen_iInter_of_finite hA)).inter (isOpen_iInter_of_finite hC)
  refine ⟨U, hU, ⟨⟨⟨hxb, hxB⟩, mem_iInter.mpr hxA⟩, mem_iInter.mpr hxC⟩,
    fun _ hy => hy.1.1.1, ?_⟩
  ext y
  constructor
  · rintro ⟨hyG, hyU⟩
    refine ⟨?_, hyU⟩
    rcases hyG with hya | hyc
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hya
      exact False.elim ((mem_iInter.mp hyU.1.2 i) (mem_range_self t))
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hyc
      have hi : i = a := by
        by_contra hn
        have hnmem := mem_iInter.mp hyU.2 i
        simp only [C, ite_eq_right hn, mem_compl_iff] at hnmem
        exact hnmem (mem_range_self t)
      subst i
      exact ⟨t, by
        by_contra hn
        exact hyU.1.1.2 ⟨t, hn, rfl⟩, rfl⟩
  · rintro ⟨⟨t, _, rfl⟩, hyU⟩
    exact ⟨Or.inr (mem_iUnion.mpr ⟨a, mem_range_self t⟩), hyU⟩

end SeifertSurfaces.OriginalEndpoints.AppendixAOriginal
