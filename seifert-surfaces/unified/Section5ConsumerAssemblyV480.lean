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

end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
