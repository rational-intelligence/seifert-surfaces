import B1ActualFieldGraphSupport_v475
noncomputable section
open Set Topology Function Filter
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.B1Tangency
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.AppendixACoordinates
universe u
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

/-- A compact vertical field in an actual interior chart, on a compact attained
graph, using the same native ambient flow as the relative minimum. -/
theorem native_interior_compact_graph_vertical_field_v475
    (c : SmoothAmbientChart ThreeSphere)
    (hcE : c.chart.source ⊆ E.toSphere '' (𝓡∂ 3).interior E.Carrier)
    (A O : Set E2) (hA : IsCompact A) (hAO : A ⊆ O)
    (u φ : E2 → ℝ) (hu : ContDiffOn ℝ ∞ u O) (hφ : ContDiff ℝ ∞ φ)
    (hgraph : ∀ x ∈ A, jetPoint (x,u x,0) ∈ c.chart.target) :
    ∃ (X : NativeInteriorSmoothVectorField_v475 E) (ρ : ThreeSphere → ℝ),
      ρ =ᶠ[𝓝ˢ ((fun x => c.chart.symm (jetPoint (x,u x,0))) '' A)] 1 ∧
      closure {p | X.field p ≠ 0} ⊆ c.chart.source ∧
      (∀ p ∈ c.chart.source, chartDifferential c p (X.field p)=
        ρ p • (φ (native_collar_base_v475 (c.chart p)) • coordinateVector 3 2)) := by
  have hΓ : ContinuousOn (fun x => jetPoint (x,u x,0)) A := by
    unfold jetPoint
    apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    fin_cases i
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.continuousOn
    · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.continuousOn
    · exact hu.continuousOn.mono hAO
  have hC : IsCompact ((fun x => c.chart.symm (jetPoint (x,u x,0))) '' A) :=
    hA.image_of_continuousOn (c.inverse_smooth.continuousOn.comp hΓ hgraph)
  have hCs : (fun x => c.chart.symm (jetPoint (x,u x,0))) '' A ⊆ c.chart.source := by
    rintro p ⟨x,hx,rfl⟩
    exact c.chart.map_target (hgraph x hx)
  have hW : ContDiff ℝ ∞ (fun y : E3 => φ (native_collar_base_v475 y) • coordinateVector 3 2) :=
    (hφ.comp native_collar_base_smooth_v475).smul contDiff_const
  obtain ⟨X,ρ,hρ,hρc,hρrange,hρone,hXs,hX⟩ := native_chart_compact_cutoff_field_v475
    c c.chart.source _ c.chart.open_source (Subset.refl _) hcE hC hCs _ hW.contDiffOn
  exact ⟨X,ρ,hρone,hXs,hX⟩

/-- Whole-image graph uniqueness makes the field vanish on the original
surface off the actual recovered compact source parameter. -/
theorem native_interior_actual_chart_field_support_on_graph_v475
    {S : CompactOrientedSurface.{u}} (f : ProperSmoothEmbedding S E.Carrier)
    (c : SmoothAmbientChart ThreeSphere) (X : NativeInteriorSmoothVectorField_v475 E)
    (ρ : ThreeSphere → ℝ) (q : E2 → S) (u φ : E2 → ℝ) (A : Set E2)
    (hφA : tsupport φ ⊆ A)
    (hq : ∀ x ∈ A, E.toSphere (f.toFun (q x)) ∈ c.chart.source ∧
      c.chart (E.toSphere (f.toFun (q x)))=jetPoint (x,u x,0))
    (hX : ∀ p ∈ c.chart.source, chartDifferential c p (X.field p)=
      ρ p • (φ (native_collar_base_v475 (c.chart p)) • coordinateVector 3 2))
    (hXs : closure {p | X.field p ≠ 0} ⊆ c.chart.source)
    (hgraph : ∀ z : S, E.toSphere (f.toFun z) ∈ c.chart.source →
      (c.chart (E.toSphere (f.toFun z))) 2 =
        u (native_collar_base_v475 (c.chart (E.toSphere (f.toFun z))))) :
    ∀ z ∉ q '' A, X.field (E.toSphere (f.toFun z))=0 := by
  intro z hz
  let p := E.toSphere (f.toFun z)
  by_cases hp : p ∈ c.chart.source
  · let y := c.chart p
    have hyheight : y 2=u (native_collar_base_v475 y) := hgraph z hp
    have hφzero : φ (native_collar_base_v475 y)=0 := by
      by_contra hφn
      have hb : native_collar_base_v475 y ∈ A := hφA (subset_tsupport φ hφn)
      apply hz
      refine ⟨native_collar_base_v475 y,hb,?_⟩
      apply f.embedding.injective
      apply Subtype.ext
      apply c.chart.injOn (hq _ hb).1 hp
      rw [(hq _ hb).2]
      ext i
      fin_cases i <;> simp [jetPoint,native_collar_base_v475,hyheight,y]
    have hd : chartDifferential c p (X.field p)=0 := by
      rw [hX p hp]
      change ρ p • (φ (native_collar_base_v475 y) • coordinateVector 3 2)=0
      rw [hφzero,zero_smul,smul_zero]
    exact (native_actual_chart_differential_invertible_v475 c p hp).injective
      (hd.trans (map_zero _).symm)
  · by_contra hn
    exact hp (hXs (subset_closure hn))

#print axioms native_interior_compact_graph_vertical_field_v475
#print axioms native_interior_actual_chart_field_support_on_graph_v475
end SeifertSurfaces.OriginalEndpoints.B1Tangency
