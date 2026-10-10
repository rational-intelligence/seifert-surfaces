import SchoenfliesNativeCoimportProbeV754
import OriginalSection62
import Lean

open Lean in
run_elab do
  let current := (← getEnv).setExporting false
  let (approved, _region) ← Lean.Core.liftIOCore <| Lean.readModuleData
    "/home/caoyichuan/test/seifert-surfaces/scratch/f-generator/original62_proof_v477/native_objects/OriginalSection62.olean"
  let pins := #[
    ("Foundations", #[`SeifertSurfaces.Foundations.CompactOrientedSurface,
      `SeifertSurfaces.Foundations.CompactOrientedSurface.mk,
      `SeifertSurfaces.Foundations.NeatEmbedding,`SeifertSurfaces.Foundations.NeatEmbedding.mk,
      `SeifertSurfaces.Foundations.TopologicalAmbientIsotopy,
      `SeifertSurfaces.Foundations.TopologicalAmbientIsotopy.mk]),
    ("LinkExterior", #[`SeifertSurfaces.Foundations.LinkSpanningSurface,
      `SeifertSurfaces.Foundations.LinkSpanningSurface.mk]),
    ("CompressionContracts", #[`SeifertSurfaces.GenusLinking.InteriorCompressingDisk,
      `SeifertSurfaces.GenusLinking.InteriorCompressingDisk.mk,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.mk,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.removed,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.Remainder,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.sideTime,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.edgePoint,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.capEdge,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.Gluing,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.Gluing.attach,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.SurgerySpace,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.remainderInclusion,
      `SeifertSurfaces.GenusLinking.CompressionAnnulus.capInclusion,
      `SeifertSurfaces.GenusLinking.SmoothCompressionSurface,
      `SeifertSurfaces.GenusLinking.SmoothCompressionSurface.mk,
      `SeifertSurfaces.GenusLinking.EmbeddedCompression,
      `SeifertSurfaces.GenusLinking.EmbeddedCompression.mk])]
  for (modName,pinNames) in pins do
    let (data,_region) ← Lean.Core.liftIOCore <| Lean.readModuleData
      (System.FilePath.mk "/home/caoyichuan/test/seifert-surfaces/target/.lake/build/lib/lean" /
        (modName ++ ".olean"))
    for name in pinNames do
      let some localInfo := current.find? name | throwError "geometry pin missing: {name}"
      let some sourceInfo := data.constants.find? (fun c => c.name == name) |
        throwError "native geometry pin missing: {name}"
      unless localInfo.levelParams == sourceInfo.levelParams &&
          Expr.equal localInfo.type sourceInfo.type &&
          ExprStructEq.mk localInfo.type == ExprStructEq.mk sourceInfo.type do
        throwError "raw native geometry pin type differs: {name}"
      if let some value := sourceInfo.value? (allowOpaque := true) then
        let some localValue := localInfo.value? (allowOpaque := true) |
          throwError "geometry pin body absent: {name}"
        unless Expr.equal localValue value &&
            ExprStructEq.mk localValue == ExprStructEq.mk value do
          throwError "raw native geometry pin body differs: {name}"
  logInfo "PASS: native geometry pins have identical raw types and operative values"
  let head := `SeifertSurfaces.OriginalEndpoints.ActualCompressionRealization
  let names := #[head,Name.str head "mk",Name.str head "toEmbeddedCompression",
    Name.str head "diskParam",Name.str head "diskParam_boundary",
    Name.str head "thickening",Name.str head "thickening_embedded",Name.str head "thickening_center",
    Name.str head "thickening_lateral",Name.str head "thickening_interior",
    Name.str head "thickening_surface_intersection",Name.str head "caps_disjoint",
    Name.str head "caps_avoid_suppliedDisk",Name.str head "caps_meet_remainder_only_at_attachment",
    Name.str head "unrounded",Name.str head "unrounded_embedded",Name.str head "unrounded_remainder",
    Name.str head "unrounded_caps",Name.str head "rounding",Name.str head "roundingSupport",
    Name.str head "roundingSupport_open",Name.str head "roundingSupport_contains_seams",
    Name.str head "roundingSupport_away_boundary",Name.str head "roundingSupport_away_centralDisk",
    Name.str head "rounding_fixed_outside",Name.str head "rounding_boundary_fixed",
    Name.str head "rounded_identification",Name.str head "seam_closure_away_boundary",
    Name.str head "remainderMarking",Name.str head "remainderMarking_eq",
    Name.str head "remainderMarking_smooth",Name.str head "remainder_orientation"]
  for name in names do
    let some localInfo := current.find? name | throwError "local record declaration missing: {name}"
    let some sourceInfo := approved.constants.find? (fun c => c.name == name) |
      throwError "approved record declaration missing: {name}"
    unless localInfo.levelParams == sourceInfo.levelParams do
      throwError "record universe parameters differ: {name}"
    unless Expr.equal localInfo.type sourceInfo.type &&
      ExprStructEq.mk localInfo.type == ExprStructEq.mk sourceInfo.type do
      throwError "raw native record type differs: {name}"
    if let some value := sourceInfo.value? (allowOpaque := true) then
      let some localValue := localInfo.value? (allowOpaque := true) |
        throwError "raw native record body absent: {name}"
      unless Expr.equal localValue value &&
        ExprStructEq.mk localValue == ExprStructEq.mk value do
        throwError "raw native record body differs: {name}"
  logInfo m!"PASS: {names.size} literal realization declarations have identical raw native types"
