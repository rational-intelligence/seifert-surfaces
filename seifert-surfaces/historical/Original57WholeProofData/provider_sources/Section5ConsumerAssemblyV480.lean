import Section5AreaAssemblyV480
import OriginalB2B5V480

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff BigOperators

namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
open SeifertSurfaces.GenusLinking SeifertSurfaces.Complexity
open SeifertSurfaces.OriginalEndpoints.Section4

variable {K : OrientedKnot} {T : TubularNeighborhood K} (E : SmoothExterior T)

theorem appendix_b480_native_area_eq (H : SourceGeometry E) (v : Vertices E) :
    AppendixBOriginalV480.relativeVertexArea H.metric H.foliation v = areaInfimum E H v := by
  exact appendix_b_native_area_eq E H v

theorem appendix_b480_exchange_pair_to_native (H : SourceGeometry E)
    (x u w up down : Vertices E)
    (hpair : SeifertSurfaces.Section5.Combinatorics.IsExchangePair (oneSkeleton E)
      (vertexGenus E) (AppendixBOriginalV480.relativeVertexArea H.metric H.foliation)
      x u w up down) : ExchangePair E H x u w up down := by
  have harea : AppendixBOriginalV480.relativeVertexArea H.metric H.foliation =
      areaInfimum E H := funext (appendix_b480_native_area_eq E H)
  rw [harea] at hpair
  exact hpair

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
