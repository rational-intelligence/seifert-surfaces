import Section2.Definitions

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]

omit [WellFoundedLT W] in
/-- A finite walk has a vertex of greatest complexity. -/
private theorem walk_support_max (G : SimpleGraph V) (c : V → W)
    {u w : V} (p : G.Walk u w) :
    ∃ z ∈ p.support, ∀ x ∈ p.support, c x ≤ c z := by
  classical
  obtain ⟨z, hz, hmax⟩ := p.support.toFinset.exists_max_image c
    ⟨u, by simp⟩
  exact ⟨z, by simpa using hz, fun x hx => hmax x (by simpa using hx)⟩

/-- If a shortest walk has both endpoints strictly below an upper bound, its
unique possible peak at that bound can be replaced by a descending apex. -/
private theorem lower_peak_walk (G : SimpleGraph V) (c : V → W)
    (h : ExchangeStructure G c) (hc : Function.Injective c) (C : W)
    {u w : V} (p : G.Walk u w) (hp : p.length = G.dist u w)
    (hbound : ∀ z ∈ p.support, c z ≤ C) (hu : c u < C) (hw : c w < C) :
    ∃ q : G.Walk u w, q.length = p.length ∧ ∀ z ∈ q.support, c z < C := by
  classical
  induction p with
  | nil =>
    exact ⟨.nil, rfl, by simpa using hu⟩
  | @cons u a w ua p ih =>
    have hp' : p.length = G.dist a w :=
      SimpleGraph.length_eq_dist_of_subwalk hp ⟨ua.toWalk, .nil, by simp⟩
    have hb' : ∀ z ∈ p.support, c z ≤ C := by
      intro z hz
      exact hbound z (by simp [hz])
    by_cases ha : c a < C
    · obtain ⟨q, hq, hqb⟩ := ih hp' hb' ha hw
      refine ⟨q.cons ua, by simpa using hq, ?_⟩
      simpa using (show ∀ z, z = u ∨ z ∈ q.support → c z < C from
        fun z hz => hz.elim (fun hz => hz ▸ hu) (hqb z))
    · have haC : c a = C := le_antisymm (hb' a p.start_mem_support) (le_of_not_gt ha)
      cases p with
      | nil => exact (ha (by simpa using hw)).elim
      | @cons a b w ab r =>
        have hpath := (SimpleGraph.Walk.cons ua (r.cons ab)).isPath_of_length_eq_dist hp
        have hanot : a ∉ r.support :=
          (SimpleGraph.Walk.cons_isPath_iff ab r).mp hpath.of_cons |>.2
        have hrb : ∀ z ∈ r.support, c z < C := by
          intro z hz
          apply lt_of_le_of_ne (hb' z (by simp [hz]))
          intro heq
          exact hanot (hc (heq.trans haC.symm) ▸ hz)
        have hb : c b < C := hrb b r.start_mem_support
        have hub : u ≠ b := by
          intro heq
          have hh := SimpleGraph.dist_le r
          simp only [SimpleGraph.Walk.length_cons] at hp
          subst b
          omega
        have hn : ¬G.Adj u b := by
          intro ub
          have hh := SimpleGraph.dist_le (r.cons ub)
          simp only [SimpleGraph.Walk.length_cons] at hp hh
          omega
        have htwo : G.edist u b = 2 :=
          SimpleGraph.edist_eq_two_iff.mpr ⟨hub, hn, a, by
            exact ⟨ua, ab.symm⟩⟩
        obtain ⟨x, hx, hxc⟩ := h.descendingApex u b htwo
        have hxC : c x < C := hxc.trans (max_lt hu hb)
        have hux : G.Adj u x := hx.1.1
        have hxb : G.Adj x b := hx.1.2.symm
        refine ⟨(r.cons hxb).cons hux, by simp, ?_⟩
        intro z hz
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact hu
        · exact hxC
        · exact hrb z hz

/-- The final assertion of Corollary 2.3, including the bound on every vertex
of a shortest path, not only on its endpoints or internal vertices. -/
theorem exists_geodesic_below_max
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (u w : V) :
    ∃ p : G.Walk u w, p.IsPath ∧
      (p.length : ℕ∞) = G.edist u w ∧
      ∀ z ∈ p.support, c z ≤ max (c u) (c w) := by
  classical
  let S : Set W := {C | ∃ p : G.Walk u w,
    p.length = G.dist u w ∧ ∀ z ∈ p.support, c z ≤ C}
  have hS : S.Nonempty := by
    obtain ⟨p, _, hp⟩ := h.connected.exists_path_of_dist u w
    obtain ⟨z, _, hz⟩ := walk_support_max G c p
    exact ⟨c z, p, hp, hz⟩
  obtain ⟨C, hC, hmin⟩ := wellFounded_lt.has_min S hS
  obtain ⟨p, hp, hpb⟩ := hC
  have hCmax : C ≤ max (c u) (c w) := by
    by_contra! hlarge
    obtain ⟨q, hq, hqb⟩ := lower_peak_walk G c h.toExchangeStructure hc C p hp hpb
      ((le_max_left _ _).trans_lt hlarge) ((le_max_right _ _).trans_lt hlarge)
    obtain ⟨z, hz, hzm⟩ := walk_support_max G c q
    exact hmin (c z) ⟨q, hq.trans hp, hzm⟩ (hqb z hz)
  refine ⟨p, p.isPath_of_length_eq_dist hp, ?_, fun z hz => (hpb z hz).trans hCmax⟩
  have he := G.edist_ne_top_iff_reachable.mpr (h.connected u w)
  have hdist : (G.dist u w : ℕ∞) = G.edist u w := ENat.natCast_toNat he
  exact congrArg (fun n : ℕ => (n : ℕ∞)) hp |>.trans hdist

end SeifertSurfaces
