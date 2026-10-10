import Section5ConsumerLinks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4
open SeifertSurfaces.OriginalEndpoints.Section5.Obligations
variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

/-- The inherited existence/disjointness setting keeps the identical metric and foliation. -/
theorem relative_source_setting_to_v480 {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}
    (H : AppendixBOriginalV479.RelativeSourceSetting g J) :
    AppendixBOriginalV480.RelativeSourceSetting g J where
  strictly_convex := H.strictly_convex
  analytic_foliation := H.analytic_foliation
  source_E := H.source_E
  source_U := H.source_U

/-- Exchanging the order of the two embeddings preserves the actual tangency set. -/
theorem interior_tangencies_swap (A B : IncompressibleSpanningSurface.{0} E) :
    AppendixBOriginalV479.interiorTangencies A.1.embedding B.1.embedding =
      AppendixBOriginalV480.interiorTangencies B.1.embedding A.1.embedding := by
  ext p
  constructor
  · rintro ⟨hp, a, b, ha, hb, heq⟩
    exact ⟨hp, b, a, hb, ha, heq.symm⟩
  · rintro ⟨hp, b, a, hb, ha, heq⟩
    exact ⟨hp, a, b, ha, hb, heq.symm⟩

/-- The complete B.5 endpoint gives the native 5.1 pair directly for T1. -/
theorem t1_native_exchange_pair (H : SourceGeometry E) (hK : KnotIsNontrivial K)
    (S A B : IncompressibleSpanningSurface.{0} E)
    (hS : IsRelativeAreaMinimizer H.metric H.foliation S)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hSA : graphDistance E (SurfaceVertex E S) (SurfaceVertex E A) = 1)
    (hSB : graphDistance E (SurfaceVertex E S) (SurfaceVertex E B) = 1)
    (hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2)
    (hdisj : Disjoint S.1.image (A.1.image ∪ B.1.image))
    (hT1 : ConfigurationT1 E A B) :
    ∃ up down : Vertices E,
      ExchangePair E H (SurfaceVertex E S) (SurfaceVertex E A) (SurfaceVertex E B) up down := by
  let setting := relative_source_setting_to_v480 E (native_geometry_to_appendix_b_setting E H)
  let D : AppendixBOriginalV480.OriginalPair H.metric H.foliation := {
    A := B
    B := A
    A_minimum := hB
    B_minimum := hA
    distance_two := by
      change graphDistance E (SurfaceVertex E B) (SurfaceVertex E A) = 2
      simpa only [graphDistance, SimpleGraph.dist_comm] using hAB
    convex := setting.strictly_convex
    analytic := H.analytic }
  have ht : (AppendixBOriginalV480.interiorTangencies D.A.1.embedding D.B.1.embedding).Nonempty := by
    rw [← interior_tangencies_swap E A B]
    exact hT1.2
  obtain ⟨package, up, down, hpair⟩ := AppendixBOriginalV480.B5_original_T1
    setting hK D hT1.1.symm ht S hS (disjoint_union_right.mp hdisj).2
      (disjoint_union_right.mp hdisj).1 hSB hSA
  exact ⟨up, down, ConsumerLinks.B5_T1_native_consumer E H D S package up down hpair⟩

/-- The complete B.4 endpoint gives the native 5.1 pair directly for T2. -/
theorem t2_native_exchange_pair (H : SourceGeometry E) (hK : KnotIsNontrivial K)
    (S A B : IncompressibleSpanningSurface.{0} E)
    (hS : IsRelativeAreaMinimizer H.metric H.foliation S)
    (hA : IsRelativeAreaMinimizer H.metric H.foliation A)
    (hB : IsRelativeAreaMinimizer H.metric H.foliation B)
    (hSA : graphDistance E (SurfaceVertex E S) (SurfaceVertex E A) = 1)
    (hSB : graphDistance E (SurfaceVertex E S) (SurfaceVertex E B) = 1)
    (hAB : graphDistance E (SurfaceVertex E A) (SurfaceVertex E B) = 2)
    (hdisj : Disjoint S.1.image (A.1.image ∪ B.1.image))
    (hT2 : ConfigurationT2 E A B) :
    ∃ up down : Vertices E,
      ExchangePair E H (SurfaceVertex E S) (SurfaceVertex E A) (SurfaceVertex E B) up down := by
  let setting := relative_source_setting_to_v480 E (native_geometry_to_appendix_b_setting E H)
  have hBA : graphDistance E (SurfaceVertex E B) (SurfaceVertex E A) = 2 := by
    simpa only [graphDistance, SimpleGraph.dist_comm] using hAB
  obtain ⟨D, hDB, hDA⟩ := minimizer_common_leaf_graph E H hK B A hB hA hBA hT2.symm
  have hSDA : Disjoint S.1.image D.A.1.image := by
    rw [hDB]
    exact (disjoint_union_right.mp hdisj).2
  have hSDB : Disjoint S.1.image D.B.1.image := by
    rw [hDA]
    exact (disjoint_union_right.mp hdisj).1
  have hSdA : (oneSkeleton E).dist (AppendixBOriginalV480.vertexOf S)
      (AppendixBOriginalV480.vertexOf D.A) = 1 := by
    rw [hDB]
    exact hSB
  have hSdB : (oneSkeleton E).dist (AppendixBOriginalV480.vertexOf S)
      (AppendixBOriginalV480.vertexOf D.B) = 1 := by
    rw [hDA]
    exact hSA
  obtain ⟨package, up, down, hpair⟩ := AppendixBOriginalV480.B4_original_T2
    setting hK D S hS hSDA hSDB hSdA hSdB
  have hn := ConsumerLinks.B4_T2_native_consumer E H D S package up down hpair
  rw [hDA, hDB] at hn
  exact ⟨up, down, hn⟩

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
