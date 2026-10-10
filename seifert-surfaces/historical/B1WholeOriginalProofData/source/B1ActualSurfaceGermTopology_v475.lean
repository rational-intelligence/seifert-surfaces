import B1ActualSurfaceInteriorTopology_v475

noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
universe u v w
variable {M : Type v} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M]
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- Agreement of actual ambient surface-image germs. -/
def native_surface_germ_eq_v475 (A B : Set M) (p : M) : Prop :=
  ∃ O : Set M, IsOpen O ∧ p ∈ O ∧ A ∩ O = B ∩ O

theorem native_surface_germ_locus_open_v475
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S M) (B : Set M) :
    IsOpen {x : S | native_surface_germ_eq_v475 f.image B (f.toFun x)} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨O,hO,hxO,heq⟩
  apply Filter.mem_of_superset ((hO.preimage f.smooth.continuous).mem_nhds hxO)
  intro y hy
  exact ⟨O,hO,hy,heq⟩

/-- Once the germ locus is closed in the connected manifold interior, its
nonempty seed forces the entire original embedded image into the other closed
image. Boundary points are recovered by actual interior density. -/
theorem native_connected_surface_germ_global_inclusion_v475
    {S : CompactOrientedSurface.{u}} [ConnectedSpace S]
    (f : ProperSmoothEmbedding S M) (B : Set M) (hB : IsClosed B)
    (hseed : ∃ x : S, x ∈ (𝓡∂ 2).interior S ∧ native_surface_germ_eq_v475 f.image B (f.toFun x))
    (hclosed : IsClosed {x : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image B (f.toFun x)}) :
    f.image ⊆ B := by
  obtain ⟨x,hxI,hxg⟩ := hseed
  have hI : IsConnected ((𝓡∂ 2).interior S) :=
    ⟨⟨x,hxI⟩,native_surface_interior_preconnected_v475 S⟩
  letI : ConnectedSpace ((𝓡∂ 2).interior S) := isConnected_iff_connectedSpace.mp hI
  have hopen : IsOpen {x : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image B (f.toFun x)} :=
    (native_surface_germ_locus_open_v475 f B).preimage continuous_subtype_val
  have hfull : {x : (𝓡∂ 2).interior S |
      native_surface_germ_eq_v475 f.image B (f.toFun x)} = univ :=
    IsClopen.eq_univ ⟨hclosed,hopen⟩ ⟨⟨x,hxI⟩,hxg⟩
  have hinside : (𝓡∂ 2).interior S ⊆ f.toFun ⁻¹' B := by
    intro y hy
    have hyg : native_surface_germ_eq_v475 f.image B (f.toFun y) := by
      have hh : (⟨y,hy⟩ : (𝓡∂ 2).interior S) ∈
          {x : (𝓡∂ 2).interior S | native_surface_germ_eq_v475 f.image B (f.toFun x)} := by
        rw [hfull]
        trivial
      exact hh
    obtain ⟨O,hO,hyO,heq⟩ := hyg
    exact (heq ▸ (show f.toFun y ∈ f.image ∩ O from ⟨⟨y,rfl⟩,hyO⟩)).1
  have hall : univ ⊆ f.toFun ⁻¹' B := by
    rw [← native_surface_interior_dense_v475 S]
    exact closure_minimal hinside (hB.preimage f.smooth.continuous)
  rintro p ⟨z,rfl⟩
  exact hall (mem_univ z)

variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{w} E}

/-- Exact topological end of the original propagation proof. The remaining
analytic obligation is displayed explicitly as closure of each actual image
germ locus; it is not added to either protected theorem. -/
theorem actual_surface_agreement_of_closed_germ_loci_v475
    (D : B1OriginalData g J) (s : Circle) (W : CollarWindow D s)
    (hzero : ∃ U : Set AppendixACoordinates.E2, IsOpen U ∧ U.Nonempty ∧ U ⊆ halfDisc W.R ∧
      ∀ x ∈ U, localHeight D s x = 0)
    (hclosedA : IsClosed {x : (𝓡∂ 2).interior D.A.1.surface |
      native_surface_germ_eq_v475 D.A.1.image D.B.1.image (D.A.1.embedding.toFun x)})
    (hclosedB : IsClosed {x : (𝓡∂ 2).interior D.B.1.surface |
      native_surface_germ_eq_v475 D.B.1.image D.A.1.image (D.B.1.embedding.toFun x)}) :
    D.A.1.image = D.B.1.image := by
  let fA := ProperSmoothEmbedding.ofNeat D.A.1.embedding
  let fB := ProperSmoothEmbedding.ofNeat D.B.1.embedding
  letI : ConnectedSpace D.A.1.surface := D.A.1.connected_for_knot
  letI : ConnectedSpace D.B.1.surface := D.B.1.connected_for_knot
  obtain ⟨p,O,hO,hpO,hpA,hpint,heq⟩ := actual_local_zero_ambient_germ_v475 D s W hzero
  obtain ⟨a,ha⟩ := hpA.1
  obtain ⟨b,hb⟩ := hpA.2
  have haI : a ∈ (𝓡∂ 2).interior D.A.1.surface := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hbd
    change a ∈ D.A.1.surface.boundary at hbd
    have hpbd : D.A.1.embedding.toFun a ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← D.A.1.embedding.boundary_preimage] at hbd
    exact hpint (ha ▸ hpbd)
  have hbI : b ∈ (𝓡∂ 2).interior D.B.1.surface := by
    rw [← (𝓡∂ 2).compl_boundary]
    intro hbd
    change b ∈ D.B.1.surface.boundary at hbd
    have hpbd : D.B.1.embedding.toFun b ∈ (𝓡∂ 3).boundary E.Carrier := by
      rwa [← D.B.1.embedding.boundary_preimage] at hbd
    exact hpint (hb ▸ hpbd)
  have hAc : IsClosed D.A.1.image := (isCompact_range fA.smooth.continuous).isClosed
  have hBc : IsClosed D.B.1.image := (isCompact_range fB.smooth.continuous).isClosed
  apply Subset.antisymm
  · exact native_connected_surface_germ_global_inclusion_v475 fA D.B.1.image hBc
      ⟨a,haI,O,hO,(by change D.A.1.embedding.toFun a ∈ O; rwa [ha]),heq⟩ hclosedA
  · exact native_connected_surface_germ_global_inclusion_v475 fB D.A.1.image hAc
      ⟨b,hbI,O,hO,(by change D.B.1.embedding.toFun b ∈ O; rwa [hb]),heq.symm⟩ hclosedB

#print axioms actual_surface_agreement_of_closed_germ_loci_v475

#print axioms native_surface_germ_locus_open_v475
#print axioms native_connected_surface_germ_global_inclusion_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
