import Section2.Downsets

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]

/-- A descending ambient apex lies in a complexity downset and remains an apex
after induction. -/
private theorem downset_descending_apex
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D)
    (u w : D) (hd : (G.induce D).edist u w = 2) :
    ∃ x, IsIntervalApex (G.induce D) u w x ∧
      restrictedComplexity c D x < max (restrictedComplexity c D u)
        (restrictedComplexity c D w) := by
  have hd' : G.edist u.1 w.1 = 2 :=
    (complexity_downset_edist G c h hc D hD u w).symm.trans hd
  obtain ⟨x, hx, hxc⟩ := h.descendingApex u.1 w.1 hd'
  have hxD : x ∈ D := by
    rcases le_total (c u.1) (c w.1) with huv | hwu
    · exact hD (by simpa [max_eq_right huv] using hxc.le) w.2
    · exact hD (by simpa [max_eq_left hwu] using hxc.le) u.2
  refine ⟨⟨x, hxD⟩, ⟨hx.1, ?_⟩, hxc⟩
  intro y hy
  rcases hx.2 y.1 hy with heq | hadj
  · exact Or.inl (Subtype.ext heq)
  · exact Or.inr hadj

/-- A descending apex between two lower neighbours is itself a lower neighbour. -/
private theorem link_descending_apex
    (G : SimpleGraph V) (c : V → W) (h : ExchangeStructure G c) (v : V)
    (u w : descendingLinkVertices G c v) (hd : G.edist u.1 w.1 = 2) :
    ∃ x, IsIntervalApex (G.induce (descendingLinkVertices G c v)) u w x ∧
      restrictedComplexity c (descendingLinkVertices G c v) x <
        max (restrictedComplexity c (descendingLinkVertices G c v) u)
          (restrictedComplexity c (descendingLinkVertices G c v) w) := by
  obtain ⟨x, hx, hxc⟩ := h.descendingApex u.1 w.1 hd
  have hxv : c x < c v := hxc.trans (max_lt u.2.2 w.2.2)
  have hvI : v ∈ twoInterval G u.1 w.1 := ⟨u.2.1.symm, w.2.1.symm⟩
  have hvx : G.Adj v x := by
    rcases hx.2 v hvI with heq | hadj
    · exact (lt_irrefl (c v) (heq ▸ hxv)).elim
    · exact hadj.symm
  refine ⟨⟨x, hvx, hxv⟩, ⟨hx.1, ?_⟩, hxc⟩
  intro y hy
  rcases hx.2 y.1 hy with heq | hadj
  · exact Or.inl (Subtype.ext heq)
  · exact Or.inr hadj

omit [WellFoundedLT W] in
/-- Nonadjacent distinct descending-link vertices have ambient distance two,
because the original vertex is a common neighbour. -/
private theorem link_ambient_edist_two
    (G : SimpleGraph V) (c : V → W) (v : V)
    (u w : descendingLinkVertices G c v) (hne : u ≠ w)
    (hnadj : ¬ (G.induce (descendingLinkVertices G c v)).Adj u w) :
    G.edist u.1 w.1 = 2 := by
  apply SimpleGraph.edist_eq_two_iff.mpr
  exact ⟨fun heq => hne (Subtype.ext heq), hnadj, v, u.2.1.symm, w.2.1.symm⟩

/-- Lemma 2.4(1), the inherited exchange axioms. The induced graph is the
one-skeleton of the full subcomplex on `D`. -/
theorem complexity_downset_exchange_structure
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D) :
    ExchangeStructure (G.induce D) (restrictedComplexity c D) := by
  constructor
  · intro u w hd
    obtain ⟨x, hx, _⟩ := downset_descending_apex G c h hc D hD u w hd
    exact ⟨x, hx⟩
  · exact downset_descending_apex G c h hc D hD

/-- Lemma 2.4(1), the nonempty full downset is again an exchange graph. -/
theorem nonempty_complexity_downset_exchange_graph
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D)
    (hne : D.Nonempty) :
    ExchangeGraph (G.induce D) (restrictedComplexity c D) := by
  exact ⟨complexity_downset_exchange_structure G c h hc D hD,
    nonempty_complexity_downset_connected G c h hc D hD hne⟩

/-- The strict sublevel instance of Lemma 2.4(1). Its nonemptiness condition
must also apply to the printed phrase "in particular so is X_<v". -/
theorem nonempty_strict_sublevel_exchange_graph
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (v : V) (hne : (strictSublevel c v).Nonempty) :
    ExchangeGraph (G.induce (strictSublevel c v))
      (restrictedComplexity c (strictSublevel c v)) := by
  apply nonempty_complexity_downset_exchange_graph G c h hc (strictSublevel c v) ?_ hne
  intro u w huw hw
  exact huw.trans_lt hw

/-- Lemma 2.4(2), the descending link inherits both exchange axioms. -/
theorem descending_link_exchange_structure
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (v : V) :
    ExchangeStructure (G.induce (descendingLinkVertices G c v))
      (restrictedComplexity c (descendingLinkVertices G c v)) := by
  have hdesc : ∀ u w : descendingLinkVertices G c v,
      (G.induce (descendingLinkVertices G c v)).edist u w = 2 →
      ∃ x, IsIntervalApex (G.induce (descendingLinkVertices G c v)) u w x ∧
        restrictedComplexity c (descendingLinkVertices G c v) x <
          max (restrictedComplexity c (descendingLinkVertices G c v) u)
            (restrictedComplexity c (descendingLinkVertices G c v) w) := by
    intro u w hd
    obtain ⟨hne, hnadj, _⟩ := SimpleGraph.edist_eq_two_iff.mp hd
    exact link_descending_apex G c h.toExchangeStructure v u w
      (link_ambient_edist_two G c v u w hne hnadj)
  exact ⟨fun u w hd => (hdesc u w hd).imp (fun _ hx => hx.1), hdesc⟩

/-- The diameter bound stated in the proof of Lemma 2.4(2). -/
theorem descending_link_edist_le_two
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (v : V) :
    ∀ u w : descendingLinkVertices G c v,
      (G.induce (descendingLinkVertices G c v)).edist u w ≤ 2 := by
  intro u w
  by_cases heq : u = w
  · simp [heq]
  by_cases hadj : (G.induce (descendingLinkVertices G c v)).Adj u w
  · simp [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
  obtain ⟨x, hx, _⟩ := link_descending_apex G c h.toExchangeStructure v u w
    (link_ambient_edist_two G c v u w heq hadj)
  let p : (G.induce (descendingLinkVertices G c v)).Walk u w :=
    .cons hx.1.1 (.cons hx.1.2.symm .nil)
  have hl : p.length = 2 := rfl
  simpa only [hl, Nat.cast_ofNat] using p.edist_le

/-- Lemma 2.4(2), a nonempty descending link is an exchange graph. -/
theorem nonempty_descending_link_exchange_graph
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (v : V)
    (hne : (descendingLinkVertices G c v).Nonempty) :
    ExchangeGraph (G.induce (descendingLinkVertices G c v))
      (restrictedComplexity c (descendingLinkVertices G c v)) := by
  refine ⟨descending_link_exchange_structure G c h hc v, ?_⟩
  let : Nonempty (descendingLinkVertices G c v) := hne.to_subtype
  refine ⟨?_⟩
  intro u w
  apply SimpleGraph.reachable_of_edist_ne_top
  exact ne_top_of_le_ne_top (by simp) (descending_link_edist_le_two G c h hc v u w)

/-- The final assertion of Lemma 2.4(2): the descending link is nonempty
unless its vertex is the least vertex in the complexity order. -/
theorem descending_link_nonempty_of_not_least
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (v : V)
    (hv : ¬ IsLeastComplexityVertex c v) :
    (descendingLinkVertices G c v).Nonempty := by
  classical
  obtain ⟨w, hw⟩ : ∃ w, c w < c v := by
    simpa [IsLeastComplexityVertex, not_forall, not_le] using hv
  obtain ⟨p, _, _, hb⟩ := exists_geodesic_below_max G c h hc v w
  cases p with
  | nil => exact (lt_irrefl _ hw).elim
  | @cons v x w hvx p =>
    refine ⟨x, hvx, lt_of_le_of_ne ?_ ?_⟩
    · simpa [max_eq_left hw.le] using hb x (by simp)
    · intro heq
      exact hvx.ne (hc heq).symm

end SeifertSurfaces
