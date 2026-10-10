import B3NativeFullCollarReplayV488
import B3LocalInteriorDonorBridgeV481

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology Function
open scoped Manifold ContDiff
namespace SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
open SeifertSurfaces.Foundations SeifertSurfaces.MetricFoundations
variable {K : OrientedKnot} {T : TubularNeighborhood K} {E : SmoothExterior T}
variable {g : SmoothMetric E.Carrier} {J : LongitudeFoliation.{0} E}

theorem b3_native_full_collar_result (D : B1OriginalData g J) :
    CollarTangencyResult E D ∧
      (AppendixBOriginalV479.interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  obtain ⟨r,hr,hrD,hcrit,hfin,hzero,haway,hfinite⟩ :=
    AppendixBOriginalV480.original_b3_collar_all_clauses_v480 D
  exact ⟨⟨r,hr,hrD,hcrit,hfin,hzero,haway⟩,hfinite⟩

theorem b3_native_distinct_boundary_finite (D : AppendixBOriginalV479.OriginalPair g J)
    (hne : SurfaceBoundary E D.A ≠ SurfaceBoundary E D.B) :
    (AppendixBOriginalV479.interiorTangencies D.A.1.embedding D.B.1.embedding).Finite := by
  obtain ⟨a,ha⟩ := D.A_minimum.1
  obtain ⟨b,hb⟩ := D.B_minimum.1
  have hab : a ≠ b := by
    intro h
    apply hne
    exact ha.trans ((congrArg J.leaf h).trans hb.symm)
  exact (AppendixBOriginalV480.original_pair_distinct_boundary_labels_full_B3_v480
    (original_pair_to_v480 D) ⟨a,b,hab,ha,hb⟩).2

#print axioms b3_native_full_collar_result
#print axioms b3_native_distinct_boundary_finite
end SeifertSurfaces.OriginalEndpoints.Section5.WholeAssemblyV480
