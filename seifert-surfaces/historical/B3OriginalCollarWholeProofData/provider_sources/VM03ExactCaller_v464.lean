import AffineDirichletLower
import AffineErrorEnergyLower
import AppendixACoordinatesReady
import ApprovedDataClosure
import B1ChartMetricProvider
import B1GreenBoundaryAE
import B1MetricVariationalInterfaces
import B1MovingCapPoincare
import B1ScalarCapPoincare
import B1TangencyCoordinates
import B1TangencyGraph
import B1TangencyPositive
import BoundaryPotentialB00B02
import BoundarySupport
import CampanatoVector.Basic
import CampanatoVector.Compare
import CampanatoVector.Holder
import CampanatoVector.Telescope
import CompactProductLower
import ConjugatePotentialLower
import ConstantEquationTransport
import ContinuousGradientReconstruction
import CourantAnnularBoundaryA
import CourantAnnularProfiles
import CourantGreenChordFlux
import CourantTranslatedPolar
import GradientEstimateRescalingData
import HarmonicCaccioppoli
import HarmonicDerivativeEquation
import HarmonicGradientBound
import HarmonicHessianBound
import HarmonicScalarBounds
import HemisphereQSupported
import InteriorBootstrapLower
import InteriorPotentialData
import IsothermalInverseLower
import IsothermalPDEData
import LaxMilgramRelease
import LinearSobolevTransport
import LocalizationBasic
import NativeGradientRescalingLower
import NativeH10DirichletD1D2
import NativeH10DirichletD3D5D6
import NativeH10DirichletData
import NativePlanarConstancy
import NormalizedMetricDirichletCorollary
import NormalizedMetricEnergyCorollary
import NormalizedMetricLocalBounds
import NumericIteration
import OddH1LocalTrace
import PlanarLiftAlgebra
import ProductCoordinates
import QuasilinearLocalization
import SmoothCapL2Uniform
import SmoothSlices
import SymmetricWeakEquation
import VM03WeakJets
import WeakDivergenceData
import WeakPoincarePotential
import WeakSmoothRepresentative
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.Harmonic
import DifferentialGeometry.External.DeGiorgi.Oscillation.Campanato
import InitialCapEnergyDecay_v463
import InitialCapH1ExtensionContract_v445
import Lean
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.PartialHomeomorph.Basic
import Mathlib.Topology.Piecewise
import NativeOriginalSignedDegree
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 100000
run_cmd do
 let source := System.FilePath.mk (← getFileName)
 let dir := source.parent.getD "." / "WholeProofData"
 let files : Array String := #["AffineCoordinates.olean","BoundaryPathNonzero.olean","ClosedConformality.olean","ClosedHomeomorphismTransport.olean","ClosedInverseC1.olean","ClosedNonbranchAlgebra.olean","ClosedNonbranchComplete.olean","ClosedNonbranchConsumer_v445.olean","ClosedRegularSet_v393.olean","ClosedSignedJacobian_v403.olean","ClosedWeakHomeomorphismBridge.olean","ConditionalAssembly.olean","EuclideanNonbranch.olean","HolomorphicNonbranch.olean","InitialCapEnergyDecay_v463.olean","InitialClosedDiscTestJets_v457.olean","InteriorNonbranch.olean","InverseBoundaryEnergy.olean","InverseBoundaryPath.olean","InverseBoundaryTransport.olean","InverseChartData.olean","InverseChartEquation.olean","InverseCoefficient.olean","InverseCoefficientExtension.olean","InverseEquation.olean","InverseFluxAlgebra.olean","InverseInteriorPoint.olean","InverseVerticalBound.olean","InverseVerticalLipschitz.olean","InverseWeak.olean","JordanInwardWork.olean","OriginalReconstructionPaid.olean","PositiveTrace.olean","SameMinimumTransport.olean","SourceChartWork.olean","VM03ExactCaller_v464.olean","ChartCoefficientHolderWork.olean","ChartJordanSideWork.olean","ChartMetricPositiveWork.olean","ChartPullbackIntegralWork.olean","ChartWindowWork.olean","ComparisonFlatTraceReuse.olean","FlatPatchGeometry.olean","GradientEnergySizeBounds.olean","HalfDiscVolume.olean","HolderFrozenComparisonReuse.olean","HolderFrozenInteriorComparison.olean","HolderGradientRepresentativeBounds.olean","InteriorContractionData.olean","InteriorRefinedInitialCost.olean","JordanApplicabilityWork.olean","JordanTubeWork.olean","LinearPullbackMeasure.olean","NativeBoundaryAllScaleCampanato.olean","NativeBoundaryAllScaleControl.olean","NativeBoundaryCampanatoDecay.olean","NativeBoundaryExcessRecurrence.olean","NativeBoundaryMeanAllScale.olean","NativeBoundaryRestriction.olean","NativeBoundaryTestWork.olean","NativeBoundaryToolbox.olean","NativeBoundedFluxLp.olean","NativeChartH1Work.olean","NativeChartL2AllWork.olean","NativeCutoffWork.olean","NativeDiscMean.olean","NativeFlatHarmonicDecay.olean","NativeFlatHarmonicRegularEquation.olean","NativeFlatTraceLinearPullback.olean","NativeFlatTraceWork.olean","NativeFrozenPhysicalDecay.olean","NativeH10CutoffLocalization.olean","NativeH10CutoffReuse.olean","NativeH10ExtensionInto.olean","NativeH10TestingGeneric.olean","NativeH10Use.olean","NativeH1Restriction.olean","NativeH1SubsetRestriction.olean","NativeHalfDiscContinuousGradient.olean","NativeHalfDiscMean.olean","NativeHolderOneScaleBoundary.olean","NativeHolderOneScaleInterior.olean","NativeInteriorAllScaleCampanato.olean","NativeInteriorCampanatoDecay.olean","NativeInteriorExcessRecurrence.olean","NativeInteriorHarmonicDecay.olean","NativeInteriorPhysicalDecay.olean","NativeLocalL1Energy.olean","NativeLocalizedOddGradientCampanato.olean","NativeNestedDiscMean.olean","NativeNestedHalfDiscMean.olean","NativeNormalizedFrozenH10Equation.olean","NativeNormalizedFrozenHalfDiscDecay.olean","NativeNormalizedInteriorDecay.olean","NativeOddExtensionWork.olean","NativeOddGradientCampanato.olean","NativeOddHarmonicExtension.olean","NativeOriginalEnergyInputs.olean","NativePatchInitialEnergy.olean","NativeRefinedInteriorAllScaleCampanato.olean","NativeRefinedInteriorCampanatoDecay.olean","NativeRefinedTranslatedInteriorCampanato.olean","NativeTraceIntegrableWork.olean","NativeTranslatedBoundaryCampanato.olean","NativeTranslatedBoundaryControl.olean","NativeTranslatedBoundaryData.olean","NativeTranslatedInteriorCampanato.olean","NativeTranslatedInteriorData.olean","NativeTranslation.olean","NativeUniformBoundaryPatchControl.olean","NativeUniformFrozenDecay.olean","NativeUniformInteriorDecay.olean","NativeUniformInteriorPatchControl.olean","NativeZeroScalarProviderAssembly.olean","NativeZeroScalarTwoPaidProviders.olean","NewtonianKernelLower.olean","OddExtensionTesting.olean","OddGradientField.olean","OddGradientPatchCampanato.olean","OriginalMorreyPotentialPaid.olean","OriginalWeakScalarPaid.olean","OriginalZeroScalarPaid.olean","PlanarExactCampanatoIteration.olean","PlanarGradientLinearComp.olean","PlanarHarmonicGradientVariation.olean","PlanarHarmonicHessianBound.olean","PlanarHarmonicIntegralDecay.olean","PlanarHarmonicLift.olean","PlanarLiftBallEnergy.olean","PlanarRefinedCampanatoIteration.olean","PlanarThreeCoordinateIteration.olean","RefinedNumericIteration.olean","ScalarInnerCampanato.olean","ScalarRepresentativeBounds.olean","SmoothFlatZeroH10.olean","SmoothOddGradientReflection.olean","SmoothTransitionDerivativeBounds.olean","SymmetricHalfDiscIntegral.olean","TranslatedInteriorInitialCost.olean","VectorCampanatoAverages.olean","VectorCampanatoBound.olean","VectorInnerCampanatoHolder.olean","ZeroScalarGradientAssembly.olean","CURRENT__InteriorContractionLower.olean","CURRENT__NativeInteriorDivergenceSchauderLower.olean","CURRENT__NativeOriginalAlphaCampanatoLower.olean"]
 let mut cis : Array ConstantInfo := #[]
 let mut all : Std.HashMap Name ConstantInfo := {}
 for f in files do
  let (data,_) ← liftIO <| readModuleData (dir / f)
  for ci in data.constants do
   if !(all.contains ci.name) then cis := cis.push ci; all := all.insert ci.name ci
 let roots := #[(Name.num `_private.VM03ExactCaller_v464 0) ++ `SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.same_minimizer_regular_representative_v464]
 let preservedFields : Array String := #["SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.hU","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.J_left_inverse","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.J","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.f_compatible","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.embed","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.embed_bound","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.embed_identity","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.identification","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.mult_identity","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.mult","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta_one","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.scaled_bound","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.T","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta_smooth","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.T_literal","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.supplied_fixed_point","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.hf","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.Pgrad","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.hE","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.Qgrad","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.local_half","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.fixed_bound","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.b","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.b_identity","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi_compact","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi_bounds","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.holder_half","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.full_half","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.P_identity","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi_one","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.embed_injective","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.fixed_point","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi_smooth","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.Q_identity","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta_bounds","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta_compact","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.commute","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.b_bound","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.chi_support","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.J_isometry","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.eta_support","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.cutoff_weak","SeifertSurfaces.OriginalEndpoints.B1Tangency.ChartMetricProvider.Variational.IsothermalPDELower.GradientEstimateLower.InteriorPotential.Contraction.LocalContractionWitness.J_identity"]
 let mut todo := roots ++ preservedFields.map (fun name => (name.splitOn ".").foldl (fun n s => match s.toNat? with | some k => n.num k | none => n.str s) Name.anonymous)
 let mut required : NameSet := {}
 let mut j := 0
 let initial := (← getEnv).setExporting false
 while j < todo.size do
  let n := todo[j]!; j := j+1
  if required.contains n then continue
  required := required.insert n
  if (initial.find? n).isSome then continue
  let some ci := all[n]? | throwError "finite frozen native cut missing {n}"
  todo := todo ++ ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque:=true) then todo := todo ++ v.getUsedConstants
  match ci with
  | .inductInfo d => todo := todo ++ d.all.toArray ++ d.ctors.toArray
  | .ctorInfo d => todo := todo.push d.induct
  | .recInfo d =>
   todo := todo ++ d.all.toArray
   for r in d.rules do todo := todo ++ r.rhs.getUsedConstants |>.push r.ctor
  | _ => pure ()
 let rawEq (a b : ConstantInfo) : Bool :=
  a == b && a.levelParams == b.levelParams && Expr.equal a.type b.type && ExprStructEq.mk a.type == ExprStructEq.mk b.type &&
  (match a.value? (allowOpaque := true),b.value? (allowOpaque := true) with
   | some x,some y => Expr.equal x y && ExprStructEq.mk x == ExprStructEq.mk y
   | none,none => true
   | _,_ => false) &&
  (match a,b with
   | .recInfo x,.recInfo y => x.rules.length == y.rules.length && (x.rules.zip y.rules).all (fun (r,s) => r.ctor == s.ctor && r.nfields == s.nfields && Expr.equal r.rhs s.rhs && ExprStructEq.mk r.rhs == ExprStructEq.mk s.rhs)
   | .recInfo _,_ => false
   | _,.recInfo _ => false
   | _,_ => true)
 let initialEnv := (← getEnv).setExporting false
 let mut pending := cis.filter (fun ci => required.contains ci.name && (initialEnv.find? ci.name).isNone)
 while !pending.isEmpty do
  let mut next := #[]; let mut progress := false
  for ci in pending do
   let env := (← getEnv).setExporting false
   if let some b := env.find? ci.name then
    unless Expr.equal ci.type b.type && ExprStructEq.mk ci.type == ExprStructEq.mk b.type && ci.levelParams == b.levelParams do throwError "existing native contract drift {ci.name}"
    progress := true
    continue
   match ci with
   | .inductInfo iv =>
    let mut types : List InductiveType := []
    let mut family : NameSet := {}
    for n in iv.all do
     let some (.inductInfo v) := all[n]? | throwError "paid inductive member absent {n}"
     family := family.insert n
     for cn in v.ctors do family := family.insert cn
    let mut deps : NameSet := {}
    for n in family.toArray do
     let some x := all[n]? | throwError "paid family member absent {n}"
     deps := deps.union x.type.getUsedConstantsAsSet
    if deps.toArray.any (fun n => !family.contains n && (env.find? n).isNone) then
     next := next.push ci
     continue
    for n in iv.all do
     let some (.inductInfo v) := all[n]? | throwError "family missing"
     let mut ctors : List Constructor := []
     for cn in v.ctors do
      let some (.ctorInfo c) := all[cn]? | throwError "constructor missing"
      ctors := ctors ++ [{name:=cn,type:=c.type}]
     types := types ++ [{name:=n,type:=v.type,ctors:=ctors}]
    liftCoreM <| addDecl (.inductDecl iv.levelParams iv.numParams types iv.isUnsafe)
    for n in family.toArray do
     let some x := all[n]? | throwError "family missing"
     let some b := ((← getEnv).setExporting false).find? n | throwError "generated family missing"
     unless rawEq x b do throwError "generated paid family drift {n}"
    progress := true
   | .ctorInfo _ => next := next.push ci
   | .recInfo _ => next := next.push ci
   | _ =>
    let some value := ci.value? (allowOpaque := true) | throwError "unreplayable foreign primitive {ci.name}"
    let deps := ci.type.getUsedConstantsAsSet.union value.getUsedConstantsAsSet
    if deps.toArray.any (fun n => (env.find? n).isNone) then next := next.push ci; continue
    match ci with
    | .defnInfo d => liftCoreM <| addDecl (.defnDecl d)
    | .thmInfo d => liftCoreM <| addDecl (.thmDecl d)
    | .opaqueInfo d => liftCoreM <| addDecl (.opaqueDecl d)
    | _ => throwError "unexpected paid declaration kind {ci.name}"
    let some b := ((← getEnv).setExporting false).find? ci.name | throwError "paid declaration not stored"
    unless rawEq ci b do throwError "stored paid type/value drift {ci.name}"
    progress := true
  unless progress do throwError "unavailable paid native dependencies {next.map ConstantInfo.name}"
  pending := next
 for n in roots do
  let some ci := ((← getEnv).setExporting false).find? n | throwError "paid provider root absent"
  let some v := ci.value? (allowOpaque := true) | throwError "paid provider body absent"
  liftTermElabM <| Lean.Meta.checkWithKernel v


