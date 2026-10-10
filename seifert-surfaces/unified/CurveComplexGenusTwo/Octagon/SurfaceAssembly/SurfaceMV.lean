import CurveComplexGenusTwo.Octagon.SurfaceAssembly.SurfaceCoverMaps
import CurveComplexGenusTwo.CWHurewicz.MVComplex

namespace CurveComplex.Octagon
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz

noncomputable abbrev surfaceTop : TopCat := TopCat.of Surface
noncomputable abbrev surfaceMVFaceComplex := mvOrdinaryComplex surfaceTop faceSet
noncomputable abbrev surfaceMVBandComplex := mvOrdinaryComplex surfaceTop bandSet
noncomputable abbrev surfaceMVOverlapComplex := mvOrdinaryComplex surfaceTop overlapSet
noncomputable abbrev surfaceMVPairComplex := mvPairComplex surfaceTop faceSet bandSet
noncomputable abbrev surfaceMVSmallComplex := mvSmallComplex surfaceTop faceSet bandSet
noncomputable abbrev surfaceMVComplex := mvAmbientComplex surfaceTop

noncomputable def surfaceMVDifference : surfaceMVOverlapComplex ⟶ surfaceMVPairComplex :=
  mvDifference surfaceTop faceSet bandSet

noncomputable def surfaceMVSum : surfaceMVPairComplex ⟶ surfaceMVSmallComplex :=
  mvSum surfaceTop faceSet bandSet

noncomputable def surfaceMVHomologyDifference (n : ℕ) :
    surfaceMVOverlapComplex.homology n ⟶ surfaceMVPairComplex.homology n :=
  mvHomologyDifference surfaceTop faceSet bandSet n

noncomputable def surfaceMVHomologySum (n : ℕ) :
    surfaceMVPairComplex.homology n ⟶ surfaceMVComplex.homology n :=
  mvAmbientHomologySum surfaceTop faceSet bandSet n

/-- The comparison is induced by the actual inclusion of small chains. -/
noncomputable def surfaceMVSmallIso (n : ℕ) :
    surfaceMVSmallComplex.homology n ≅ surfaceMVComplex.homology n :=
  mvOpenCoverHomologyIso surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- Connecting morphism for the actual face/outer-band open cover. -/
noncomputable def surfaceMVConnecting (n : ℕ) :
    surfaceMVComplex.homology (n + 1) ⟶ surfaceMVOverlapComplex.homology n :=
  mvAmbientConnecting surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

noncomputable def surfaceMVPairCoordinates (n : ℕ) :
    surfaceMVPairComplex.homology n ≃ₗ[ℤ]
      (surfaceMVFaceComplex.homology n × surfaceMVBandComplex.homology n) :=
  mvPairHomologyEquiv surfaceTop faceSet bandSet n

/-- Projection of the first chain map is the actual overlap-to-face inclusion. -/
theorem surfaceMVDifference_face :
    surfaceMVDifference ≫ mvPairFst surfaceTop faceSet bandSet =
      mvSubsetMap surfaceTop overlapSet faceSet Set.inter_subset_left := mvDifference_fst surfaceTop faceSet bandSet

/-- Projection of the second chain map is minus the actual overlap-to-band inclusion. -/
theorem surfaceMVDifference_band :
    surfaceMVDifference ≫ mvPairSnd surfaceTop faceSet bandSet =
      -mvSubsetMap surfaceTop overlapSet bandSet Set.inter_subset_right := mvDifference_snd surfaceTop faceSet bandSet

theorem surfaceMVHomologyDifference_face (n : ℕ) :
    surfaceMVHomologyDifference n ≫
      HomologicalComplex.homologyMap (mvPairFst surfaceTop faceSet bandSet) n =
        HomologicalComplex.homologyMap
          (mvSubsetMap surfaceTop overlapSet faceSet Set.inter_subset_left) n := mvHomologyDifference_fst surfaceTop faceSet bandSet n

theorem surfaceMVHomologyDifference_band (n : ℕ) :
    surfaceMVHomologyDifference n ≫
      HomologicalComplex.homologyMap (mvPairSnd surfaceTop faceSet bandSet) n =
        -HomologicalComplex.homologyMap
          (mvSubsetMap surfaceTop overlapSet bandSet Set.inter_subset_right) n := mvHomologyDifference_snd surfaceTop faceSet bandSet n

/-- Inclusion of the face summand followed by the MV sum is the actual face inclusion. -/
theorem surfaceMVHomologySum_face (n : ℕ) :
    HomologicalComplex.homologyMap (mvPairInl surfaceTop faceSet bandSet) n ≫
      surfaceMVHomologySum n =
        HomologicalComplex.homologyMap (mvAmbientPush surfaceTop faceSet) n := mvHomologyInl_sum_inclusion surfaceTop faceSet bandSet n

/-- Inclusion of the band summand followed by the MV sum is the actual band inclusion. -/
theorem surfaceMVHomologySum_band (n : ℕ) :
    HomologicalComplex.homologyMap (mvPairInr surfaceTop faceSet bandSet) n ≫
      surfaceMVHomologySum n =
        HomologicalComplex.homologyMap (mvAmbientPush surfaceTop bandSet) n := mvHomologyInr_sum_inclusion surfaceTop faceSet bandSet n

theorem surfaceMVConnecting_difference (n : ℕ) :
    surfaceMVConnecting n ≫ surfaceMVHomologyDifference n = 0 := mvAmbientConnecting_difference surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

theorem surfaceMVHomologyDifference_sum (n : ℕ) :
    surfaceMVHomologyDifference n ≫ surfaceMVHomologySum n = 0 := mvHomologyDifference_ambientSum surfaceTop faceSet bandSet n

theorem surfaceMVSum_connecting (n : ℕ) :
    surfaceMVHomologySum (n + 1) ≫ surfaceMVConnecting n = 0 := mvAmbientSum_connecting surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- Exactness at the actual overlap homology. -/
theorem surfaceMV_exact_overlap (n : ℕ) :
    (ShortComplex.mk (surfaceMVConnecting n) (surfaceMVHomologyDifference n)
      (surfaceMVConnecting_difference n)).Exact := mvAmbient_exact_intersection surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- Exactness at the direct sum of face and band homology. -/
theorem surfaceMV_exact_pair (n : ℕ) :
    (ShortComplex.mk (surfaceMVHomologyDifference n) (surfaceMVHomologySum n)
      (surfaceMVHomologyDifference_sum n)).Exact := mvAmbient_exact_pair surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- Exactness at the actual surface homology in every positive degree. -/
theorem surfaceMV_exact_surface (n : ℕ) :
    (ShortComplex.mk (surfaceMVHomologySum (n + 1)) (surfaceMVConnecting n)
      (surfaceMVSum_connecting n)).Exact := mvAmbient_exact_ambient surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

/-- The non-augmented sequence ends surjectively at H₀ of the actual surface. -/
theorem surfaceMV_zero_epi : Epi (surfaceMVHomologySum 0) := mvAmbientHomologySum_zero_epi surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2

/-- The transported connecting morphism agrees with the small-chain connecting morphism. -/
theorem surfaceMVConnecting_comparison (n : ℕ) :
    (surfaceMVSmallIso (n + 1)).hom ≫ surfaceMVConnecting n =
      mvConnecting surfaceTop faceSet bandSet n := mvAmbientConnecting_comparison surfaceTop faceSet bandSet
    octagon_face_outerBand_cover_exact.1 octagon_face_outerBand_cover_exact.2.1
    octagon_face_outerBand_cover_exact.2.2 n

end CurveComplex.Octagon
