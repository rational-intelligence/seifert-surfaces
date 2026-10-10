import CurveComplexGenusTwo.Octagon.OctagonChartGlueWave10

namespace CurveComplex.Octagon

/-- The outer collar is a genuine open saturated quotient piece of the actual
octagon quotient. This is the topological input needed before applying any
singular excision/Mayer–Vietoris construction to the collar. -/
theorem octagon_outerBand_open_saturated_quotient :
    IsOpen outerBand ∧
      mk ⁻¹' (mk '' outerBand) = outerBand ∧
      Topology.IsQuotientMap ((mk '' outerBand).restrictPreimage mk) := by
  exact ⟨outerBand_isOpen, outerBand_preimage_image,
    outerBand_restricted_isQuotientMap⟩

end CurveComplex.Octagon
