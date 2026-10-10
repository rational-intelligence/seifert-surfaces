import Section2.Geodesics

namespace SeifertSurfaces

universe u v

variable {V : Type u} {W : Type v} [LinearOrder W] [WellFoundedLT W]

/-- Mapping an induced walk into its ambient graph can only decrease distance. -/
private theorem ambient_edist_le_induced (G : SimpleGraph V) (D : Set V) (u w : D) :
    G.edist u.1 w.1 ≤ (G.induce D).edist u w := by
  by_cases hr : (G.induce D).Reachable u w
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    calc G.edist u.1 w.1
      _ ≤ (p.map (SimpleGraph.Embedding.induce D).toHom).length :=
        (p.map (SimpleGraph.Embedding.induce D).toHom).edist_le
      _ = (p.length : ℕ∞) := by rw [SimpleGraph.Walk.length_map]
      _ = (G.induce D).edist u w := hp
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Corollary 2.3, isometric inclusion of a full downset. Extended distances
avoid assigning distance zero to unreachable vertices. This is valid for the
empty downset too, as a statement about all pairs of its vertices. -/
theorem complexity_downset_edist
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D) :
    ∀ u w : D, (G.induce D).edist u w = G.edist u.1 w.1 := by
  intro u w
  apply le_antisymm
  · obtain ⟨p, _, hp, hpb⟩ := exists_geodesic_below_max G c h hc u.1 w.1
    have hmem : ∀ z ∈ p.support, z ∈ D := by
      intro z hz
      rcases le_total (c u.1) (c w.1) with huv | hwu
      · exact hD (by simpa [max_eq_right huv] using hpb z hz) w.2
      · exact hD (by simpa [max_eq_left hwu] using hpb z hz) u.2
    have hq := (p.induce D hmem).edist_le
    have hl : (p.induce D hmem).length = p.length := by
      rw [← SimpleGraph.Walk.length_map (SimpleGraph.Embedding.induce D).toHom,
        SimpleGraph.Walk.map_induce]
      rfl
    simpa [hl, hp] using hq
  · exact ambient_edist_le_induced G D u w

/-- The pairwise reachability part of Corollary 2.3, with no nonemptiness
assumption. In particular this has the correct empty-downset behaviour. -/
theorem complexity_downset_preconnected
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D) :
    (G.induce D).Preconnected := by
  intro u w
  apply SimpleGraph.reachable_of_edist_ne_top
  rw [complexity_downset_edist G c h hc D hD u w]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (h.connected u.1 w.1)

/-- Corollary 2.3, connectedness with its necessary nonempty-downset repair.
The printed corollary omits this condition; Mathlib's `Connected` includes it. -/
theorem nonempty_complexity_downset_connected
    (G : SimpleGraph V) (c : V → W) (h : ExchangeGraph G c)
    (hc : Function.Injective c) (D : Set V) (hD : ComplexityDownset c D)
    (hne : D.Nonempty) :
    (G.induce D).Connected := by
  let : Nonempty D := hne.to_subtype
  exact ⟨complexity_downset_preconnected G c h hc D hD⟩

end SeifertSurfaces
