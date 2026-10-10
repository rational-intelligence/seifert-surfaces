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

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
