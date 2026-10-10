import ActualAnnulusCapSidePermutationV911

set_option autoImplicit false
open SeifertSurfaces.Foundations SeifertSurfaces.GenusLinking
namespace CompressionActualCapSideNormalCoordinateV949

theorem side_normal_coordinate (k : Fin 2) (ε : ℝ) :
    ε*(2*(CompressionAnnulus.sideTime k).val-1) =
      (if k = 0 then -1 else 1)*ε := by
  fin_cases k <;> norm_num [CompressionAnnulus.sideTime]

#print axioms side_normal_coordinate
end CompressionActualCapSideNormalCoordinateV949
