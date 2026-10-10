import DifferentialGeometry.Topology.SimplicialComplex.GeometricEulerCharacteristic import ClassificationOfSurfaces.Moise.ChartInduction import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness import Mathlib.Analysis.Convex.SimplicialComplex.AffineIndependentUnion import Mathlib.Analysis.Convex.StdSimplex import Mathlib.LinearAlgebra.Dimension.Constructions import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero import Mathlib.Algebra.Category.ModuleCat.Products import Lean import DependencyImports
import DifferentialGeometry.Topology.FixedPoint.Brouwer
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false

open scoped Manifold ContDiff Classical
open CategoryTheory
open Set Topology

namespace SeifertSurfaces.GenusLinking

open SeifertSurfaces.Foundations

universe u v
noncomputable section

/-- Actual rational singular homology, not freely supplied ranks. -/
abbrev rationalHomology (X : Type) [TopologicalSpace X] (k : ℕ) :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X))

def betti (X : Type) [TopologicalSpace X] (k : ℕ) : ℕ :=
  Module.finrank ℚ (rationalHomology X k)

/-- For compact surfaces the higher degrees vanish; their finiteness and that
vanishing are named debts below. This alternating sum is not yet asserted to
equal a simplicial cell count without the comparison theorem. -/
def eulerCharacteristic (S : CompactOrientedSurface.{0}) : ℤ :=
  (betti S 0 : ℤ) - (betti S 1 : ℤ) + (betti S 2 : ℤ)

def boundaryCount (S : CompactOrientedSurface.{0}) : ℕ :=
  Nat.card (ConnectedComponents ↥S.boundary)

def componentCount (S : CompactOrientedSurface.{0}) : ℕ :=
  Nat.card (ConnectedComponents S)

/-- Total handle genus over connected components, derived from the actual
homology Euler characteristic and actual boundary components. Integer/natural
truncation and division are justified by the classification debts below. -/
def surfaceGenus (S : CompactOrientedSurface.{0}) : ℕ :=
  (2 * (componentCount S : ℤ) - eulerCharacteristic S -
    (boundaryCount S : ℤ)).toNat / 2

theorem betti_homeomorph {X : Type} {Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (k : ℕ) :
    betti X k = betti Y k := by
  let H := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) k).obj
    (ModuleCat.of ℚ ℚ)
  exact (H.mapIso (TopCat.isoOfHomeo e)).toLinearEquiv.finrank_eq

theorem surface_euler_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    eulerCharacteristic S = eulerCharacteristic R := by
  unfold eulerCharacteristic
  rw [betti_homeomorph e 0, betti_homeomorph e 1, betti_homeomorph e 2]

/-- Boundary invariance for manifold-with-boundary homeomorphisms must be
proved; it is not a preservation field asserted on an arbitrary map. -/
theorem surface_boundary_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    e '' S.boundary = R.boundary := by
  have hb : ∀ x : S, x ∈ S.boundary ↔ e x ∈ R.boundary := by
    intro x
    let f := e.toOpenPartialHomeomorph.trans (chartAt (EuclideanHalfSpace 2) (e x))
    have hf : x ∈ f.source := by
      exact ⟨Set.mem_univ x, ChartedSpace.mem_chart_source (e x)⟩
    change (𝓡∂ 2).IsBoundaryPoint x ↔ (𝓡∂ 2).IsBoundaryPoint (e x)
    rw [DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart (𝓡∂ 2) hf,
      DifferentialGeometry.Topology.isBoundaryPoint_iff_any_chart (𝓡∂ 2)
        (ChartedSpace.mem_chart_source (e x))]
    rfl
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hb x).mp hx
  · intro hy
    exact ⟨e.symm y, (hb (e.symm y)).mpr (by simpa using hy), e.apply_symm_apply y⟩

theorem surface_genus_homeomorph (S R : CompactOrientedSurface.{0}) (e : S ≃ₜ R) :
    surfaceGenus S = surfaceGenus R := by
  have card_components {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : X ≃ₜ Y) : Nat.card (ConnectedComponents X) =
        Nat.card (ConnectedComponents Y) := by
    apply Nat.card_congr
    exact (f.isQuotientMap.isCoinducing.connectedComponentsHomeomorph (by
      intro y
      have hpre : f ⁻¹' {y} = {f.symm y} := by
        ext x
        simp only [mem_preimage, mem_singleton_iff]
        exact f.toEquiv.apply_eq_iff_eq_symm_apply
      rw [hpre]
      exact isConnected_singleton)).toEquiv
  have hc : componentCount S = componentCount R := card_components e
  have hb : ∀ x : S, x ∈ S.boundary ↔ e x ∈ R.boundary := by
    intro x
    have hx := congrArg (fun q => e x ∈ q) (surface_boundary_homeomorph S R e)
    simpa using hx
  have hbc : boundaryCount S = boundaryCount R := card_components (e.subtype hb)
  unfold surfaceGenus
  rw [hc, hbc, surface_euler_homeomorph S R e]

theorem surface_genus_diffeomorph (S R : CompactOrientedSurface.{0})
    (e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S R ∞) :
    surfaceGenus S = surfaceGenus R := by
  exact surface_genus_homeomorph S R e.toHomeomorph

variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}

theorem spanning_boundary_count (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E) :
    boundaryCount F.surface = n := by
  let U : Fin n → Set ↥F.surface.boundary := fun i =>
    Subtype.val ⁻¹' Set.range (F.boundaryCircle i).toFun
  let c : Fin n → Circle → ↥F.surface.boundary := fun i z =>
    ⟨(F.boundaryCircle i).toFun z, (F.boundaryCircle i).lands_boundary z⟩
  have hc : ∀ i, Continuous (c i) := fun i =>
    (F.boundaryCircle i).smoothEmbedding.contMDiff.continuous.subtype_mk _
  have hrange : ∀ i, Set.range (c i) = U i := by
    intro i
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext hz⟩
  have hclosed : ∀ i, IsClosed (U i) := by
    intro i
    rw [← hrange i]
    exact (isCompact_range (hc i)).isClosed
  have hdisj : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j hij
    exact (F.boundary_disjoint hij).preimage Subtype.val
  have hunion : (⋃ i, U i) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : x.val ∈ ⋃ i, Set.range (F.boundaryCircle i).toFun := by
        rw [F.boundary_covers]
        exact x.property
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hclopen : ∀ i, IsClopen (U i) := by
    intro i
    have hcompl : (U i)ᶜ = ⋃ j : {j : Fin n // j ≠ i}, U j.val := by
      ext x
      constructor
      · intro hx
        obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hunion x
        have hji : j ≠ i := by
          intro heq
          exact hx (heq ▸ hj)
        exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
      · intro hx hxi
        obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact Set.disjoint_left.mp (hdisj j.property) hj hxi
    refine ⟨hclosed i, ?_⟩
    apply isClosed_compl_iff.mp
    rw [hcompl]
    exact isClosed_iUnion_of_finite (fun j => hclosed j.val)
  have hconn : ∀ i, IsConnected (U i) := by
    intro i
    rw [← hrange i]
    exact isConnected_range (hc i)
  unfold boundaryCount
  rw [Nat.card_congr
    (ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hunion hconn)]
  simp

theorem spanning_nonempty (E : SmoothExterior T) (F : LinkSpanningSurface.{0} E) :
    Nonempty F.surface := by
  exact ⟨(F.boundaryCircle ⟨0, L.nonempty⟩).toFun 1⟩

theorem same_image_genus (E : SmoothExterior T) (F G : LinkSpanningSurface.{0} E)
    (h : F.image = G.image) : surfaceGenus F.surface = surfaceGenus G.surface := by
  obtain ⟨e, _⟩ := same_image_source_diffeomorph E F G h
  exact surface_genus_diffeomorph F.surface G.surface e

theorem isotopic_image_genus (E : SmoothExterior T) (F G : LinkSpanningSurface.{0} E)
    (h : SmoothAmbientIsotopy.Rel F.image G.image) :
    surfaceGenus F.surface = surfaceGenus G.surface := by
  obtain ⟨H, hH⟩ := h
  let eF := F.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  let eG := G.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  let eH := (H.stage 1).toHomeomorph.image F.image
  let e : F.surface ≃ₜ G.surface :=
    eF.trans (eH.trans ((Homeomorph.setCongr hH).trans eG.symm))
  exact surface_genus_homeomorph F.surface G.surface e

end
noncomputable section

theorem compact_surface_components_finite (S : CompactOrientedSurface.{0}) :
    Finite (ConnectedComponents S) := by
  letI : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) S
  infer_instance

private def coordinateComplex {V : Type} [Fintype V] (K : PreAbstractSimplicialComplex V) :
    Geometry.SimplicialComplex ℝ (V → ℝ) := by
  classical
  exact Geometry.SimplicialComplex.ofAffineIndependent
    (K.map (Pi.basisFun ℝ V)) (by
      refine (Pi.basisFun ℝ V).linearIndependent.affineIndependent ℝ |>.range.mono ?_
      intro x hx
      simp only [Set.mem_iUnion, Finset.mem_coe] at hx
      obtain ⟨_, ⟨s,hs,rfl⟩,hx⟩ := hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      exact Set.mem_range_self _)

private theorem coordinateSimplex_eq {V : Type} [Fintype V]
    (s : Finset V) : convexHull ℝ (↑(s.image (Pi.basisFun ℝ V)) : Set (V → ℝ)) =
      {w | w ∈ stdSimplex ℝ V ∧ ∀ v ∉ s, w v = 0} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ hv
      obtain ⟨v,hvs,rfl⟩ := Finset.mem_image.mp hv
      refine ⟨?_,?_⟩
      · simpa only [Pi.basisFun_apply] using single_mem_stdSimplex ℝ v
      · intro i hi
        simp [Pi.basisFun_apply, Pi.single_apply, ne_of_mem_of_not_mem hvs hi]
    · apply convex_iff_add_mem.mpr
      intro x hx y hy a b ha hb hab
      refine ⟨(convex_stdSimplex ℝ V) hx.1 hy.1 ha hb hab,?_⟩
      intro v hv
      simp [Pi.add_apply, Pi.smul_apply, hx.2 v hv, hy.2 v hv]
  · rintro w ⟨hw,hz⟩
    have hsum : ∑ v ∈ s, w v = 1 := by
      rw [← hw.2]
      exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hz v hv)
    have hwrepr : s.centerMass w (Pi.basisFun ℝ V) = w := by
      rw [Finset.centerMass_eq_of_sum_1 _ _ hsum]
      calc
        ∑ v ∈ s, w v • (Pi.basisFun ℝ V) v = ∑ v, w v • (Pi.basisFun ℝ V) v :=
          Finset.sum_subset (Finset.subset_univ _) (by
            intro v _ hv
            rw [hz v hv, zero_smul])
        _ = w := by
          funext v
          simp [Pi.basisFun_apply, Pi.single_apply, eq_comm]
    rw [← hwrepr]
    exact s.centerMass_mem_convexHull (fun v _ => hw.1 v) (hsum.symm ▸ zero_lt_one)
      (fun v hv => Finset.mem_image.mpr ⟨v,hv,rfl⟩)
private theorem coordinateComplex_finite {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V) : Finite (coordinateComplex K).faces := by
  classical
  change Finite (K.faces.image (fun s => s.image (Pi.basisFun ℝ V)))
  exact (Set.toFinite K.faces).image _ |>.to_subtype

private theorem coordinateComplex_space {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V) :
    (coordinateComplex K).space = {w | w ∈ stdSimplex ℝ V ∧
      ∃ s ∈ K.faces, ∀ v ∉ s, w v = 0} := by
  classical
  ext w
  rw [Geometry.SimplicialComplex.mem_space_iff]
  dsimp only [coordinateComplex, Geometry.SimplicialComplex.ofAffineIndependent, PreAbstractSimplicialComplex.map]
  change (∃ t ∈ K.faces.image (fun s => s.image (Pi.basisFun ℝ V)),
    w ∈ convexHull ℝ (t : Set (V → ℝ))) ↔ _
  constructor
  · rintro ⟨t,⟨s,hs,rfl⟩,hw⟩
    rw [coordinateSimplex_eq] at hw
    exact ⟨hw.1,s,hs,hw.2⟩
  · rintro ⟨hw,s,hs,hz⟩
    exact ⟨s.image (Pi.basisFun ℝ V), ⟨s,hs,rfl⟩,
      (coordinateSimplex_eq s) ▸ ⟨hw,hz⟩⟩

private def fullComplex {X : Type} [TopologicalSpace X]
    (T : LeanEval.Topology.ClassificationOfSurfaces.GeometricTriangulation X) :
    PreAbstractSimplicialComplex T.Vertex where
  faces := {s | s.Nonempty ∧ ∃ t ∈ T.faces, s ⊆ t}
  isRelLowerSet_faces := by
    rintro s ⟨hs,t,ht,hst⟩
    constructor
    · exact hs
    · intro u hus hu
      exact ⟨hu,t,ht,hus.trans hst⟩

private theorem fullComplex_face_card {X : Type} [TopologicalSpace X]
    (T : LeanEval.Topology.ClassificationOfSurfaces.GeometricTriangulation X)
    {s : Finset T.Vertex} (hs : s ∈ (fullComplex T).faces) : s.card ≤ 3 := by
  obtain ⟨_,t,ht,hst⟩ := hs
  exact (Finset.card_le_card hst).trans_eq (T.faces_card t ht)

private theorem fullComplex_space {X : Type} [TopologicalSpace X]
    (T : LeanEval.Topology.ClassificationOfSurfaces.GeometricTriangulation X) :
    (coordinateComplex (fullComplex T)).space =
      LeanEval.Topology.ClassificationOfSurfaces.GeometricRealization T.Vertex T.faces := by
  classical
  ext w
  rw [coordinateComplex_space]
  constructor
  · rintro ⟨hw,s,⟨hs,t,ht,hst⟩,hz⟩
    refine ⟨hw,t,ht,?_⟩
    intro v hvt
    exact hz v (fun hvs => hvt (hst hvs))
  · rintro ⟨hw,t,ht,hz⟩
    exact ⟨hw,t,⟨Finset.card_pos.mp (by rw [T.faces_card t ht]; decide),t,ht,subset_rfl⟩,hz⟩

private theorem fullComplex_finite {X : Type} [TopologicalSpace X]
    (T : LeanEval.Topology.ClassificationOfSurfaces.GeometricTriangulation X) :
    Finite (coordinateComplex (fullComplex T)).faces := by
  letI : Fintype T.Vertex := T.vertexFintype
  exact coordinateComplex_finite (fullComplex T)

private theorem finiteCoordinateHomology {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (n : ℕ) :
    Module.Finite ℚ ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (coordinateComplex K).space))) := by
  letI := coordinateComplex_finite K
  exact (DifferentialGeometry.Topology.SimplicialComplex.finiteHomologyType_geometricSpace
    (coordinateComplex K) ℚ).1 n

private theorem zeroCoordinateHomology {V : Type} [Fintype V]
    (K : PreAbstractSimplicialComplex V) (hK : ∀ s ∈ K.faces, s.card ≤ 3)
    (n : ℕ) (hn : 2 < n) :
    CategoryTheory.Limits.IsZero ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of (coordinateComplex K).space))) := by
  classical
  letI := coordinateComplex_finite K
  letI := linearOrderOfSTO (WellOrderingRel : (V → ℝ) → (V → ℝ) → Prop)
  let A := DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet
    (coordinateComplex K).toPreAbstractSimplicialComplex
  have hcard : ∀ s ∈ (coordinateComplex K).faces, s.card ≤ 3 := by
    intro s hs
    change s ∈ K.faces.image (fun t => t.image (Pi.basisFun ℝ V)) at hs
    obtain ⟨t,ht,rfl⟩ := hs
    exact (Finset.card_image_le).trans (hK t ht)
  letI : A.HasDimensionLT 3 :=
    DifferentialGeometry.Topology.SimplicialComplex.orderedSimplicialSet_hasDimensionLT
      (coordinateComplex K).toPreAbstractSimplicialComplex 3 hcard
  have hz := A.isZero_homology_of_hasDimensionLT (ModuleCat.of ℚ ℚ) n 3 (by omega)
  have hr := hz.of_iso
    (DifferentialGeometry.SSet.realizationHomologyIso (ModuleCat.of ℚ ℚ) A n).symm
  let e := DifferentialGeometry.Topology.SimplicialComplex.geometricRealizationHomeomorphism
    (coordinateComplex K)
  exact hr.of_iso
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) n).obj
      (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo e)).symm)

private def sigmaComplex {J : Type} {V : J → Type}
    (K : ∀ j, PreAbstractSimplicialComplex (V j)) : PreAbstractSimplicialComplex (Σ j, V j) := by
  classical
  exact {
    faces := {s | ∃ j, ∃ t ∈ (K j).faces, t.image (Sigma.mk j) = s}
    isRelLowerSet_faces := by
      rintro s ⟨j,t,ht,rfl⟩
      constructor
      · exact Finset.image_nonempty.mpr ((K j).isRelLowerSet_faces ht).1
      · intro r hrs hr
        obtain ⟨u,hut,rfl⟩ := Finset.subset_image_iff.mp hrs
        exact ⟨j,u,((K j).isRelLowerSet_faces ht).2 hut (Finset.image_nonempty.mp hr),rfl⟩ }

private theorem sigmaComplex_card {J : Type} {V : J → Type}
    (K : ∀ j, PreAbstractSimplicialComplex (V j))
    (hK : ∀ j s, s ∈ (K j).faces → s.card ≤ 3) :
    ∀ s ∈ (sigmaComplex K).faces, s.card ≤ 3 := by
  classical
  rintro s ⟨j,t,ht,rfl⟩
  exact Finset.card_image_le.trans (hK j t ht)

private def sigmaCoordinates {J : Type} {V : J → Type} [Fintype J] [∀ j, Fintype (V j)]
    (j : J) (w : V j → ℝ) : (Σ j, V j) → ℝ :=
  ∑ v, w v • (Pi.basisFun ℝ (Σ j, V j)) ⟨j,v⟩

private theorem sigmaCoordinates_apply_same {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (j : J) (w : V j → ℝ) (v : V j) :
    sigmaCoordinates j w ⟨j,v⟩ = w v := by
  classical
  simp [sigmaCoordinates, Pi.basisFun_apply, Pi.single_apply]

private theorem sigmaCoordinates_apply_other {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (j : J) (w : V j → ℝ)
    (q : Σ j, V j) (hq : q.1 ≠ j) : sigmaCoordinates j w q = 0 := by
  classical
  simp only [sigmaCoordinates, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro v _
  have hne : q ≠ ⟨j,v⟩ := fun h => hq (congrArg Sigma.fst h)
  simp [Pi.basisFun_apply, Pi.single_apply, hne]

private theorem sigmaCoordinates_continuous {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (j : J) : Continuous (sigmaCoordinates (V := V) j) := by
  exact continuous_finsetSum _ (fun v _ => (continuous_apply v).smul continuous_const)

private theorem sigmaCoordinates_image {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (j : J) (s : Finset (V j)) :
    sigmaCoordinates j '' {w | w ∈ stdSimplex ℝ (V j) ∧ ∀ v ∉ s, w v = 0} =
      {w | w ∈ stdSimplex ℝ (Σ j, V j) ∧ ∀ v ∉ s.image (Sigma.mk j), w v = 0} := by
  classical
  ext w
  constructor
  · rintro ⟨x,⟨hx,hz⟩,rfl⟩
    refine ⟨⟨?_,?_⟩,?_⟩
    · rintro ⟨k,v⟩
      by_cases hk : k = j
      · subst k
        rw [sigmaCoordinates_apply_same]
        exact hx.1 v
      · rw [sigmaCoordinates_apply_other j x ⟨k,v⟩ hk]
    · rw [Fintype.sum_sigma]
      have hsum : (∑ k, ∑ v, sigmaCoordinates j x ⟨k,v⟩) =
          ∑ v, sigmaCoordinates j x ⟨j,v⟩ := by
        apply Finset.sum_eq_single j
        · intro k _ hk
          simp only [sigmaCoordinates_apply_other j x ⟨k,_⟩ hk, Finset.sum_const_zero]
        · simp
      rw [hsum]
      simpa only [sigmaCoordinates_apply_same] using hx.2
    · rintro ⟨k,v⟩ hv
      by_cases hk : k = j
      · subst k
        rw [sigmaCoordinates_apply_same]
        exact hz v (by simpa using hv)
      · exact sigmaCoordinates_apply_other j x ⟨k,v⟩ hk
  · rintro ⟨hw,hz⟩
    let x : V j → ℝ := fun v => w ⟨j,v⟩
    have hother (k : J) (v : V k) (hk : k ≠ j) : w ⟨k,v⟩ = 0 := by
      apply hz
      intro hmem
      obtain ⟨u,hu,h⟩ := Finset.mem_image.mp hmem
      exact hk (congrArg Sigma.fst h).symm
    have hsum : ∑ v, x v = 1 := by
      rw [← hw.2, Fintype.sum_sigma]
      symm
      apply Finset.sum_eq_single j
      · intro k _ hk
        simp [hother k _ hk]
      · simp
    refine ⟨x,⟨⟨fun v => hw.1 ⟨j,v⟩,hsum⟩,?_⟩,?_⟩
    · intro v hv
      exact hz ⟨j,v⟩ (by simpa using hv)
    · funext q
      rcases q with ⟨k,v⟩
      by_cases hk : k = j
      · subst k
        exact sigmaCoordinates_apply_same j x v
      · rw [sigmaCoordinates_apply_other j x ⟨k,v⟩ hk, hother k v hk]

private def sigmaSpaceMap {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (K : ∀ j, PreAbstractSimplicialComplex (V j)) :
    (Σ j, (coordinateComplex (K j)).space) → (coordinateComplex (sigmaComplex K)).space := by
  intro p
  refine ⟨sigmaCoordinates p.1 p.2.1,?_⟩
  rw [coordinateComplex_space]
  obtain ⟨hw,s,hs,hz⟩ := (coordinateComplex_space (K p.1)).le p.2.2
  have h := (sigmaCoordinates_image p.1 s).le ⟨p.2.1,⟨hw,hz⟩,rfl⟩
  exact ⟨h.1,s.image (Sigma.mk p.1),⟨p.1,s,hs,rfl⟩,h.2⟩

private theorem sigmaSpaceMap_continuous {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (K : ∀ j, PreAbstractSimplicialComplex (V j)) :
    Continuous (sigmaSpaceMap K) := by
  apply continuous_sigma
  intro j
  exact ((sigmaCoordinates_continuous (V := V) j).comp continuous_subtype_val).subtype_mk _

private theorem sigmaSpaceMap_bijective {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (K : ∀ j, PreAbstractSimplicialComplex (V j)) :
    Function.Bijective (sigmaSpaceMap K) := by
  classical
  constructor
  · rintro ⟨j,x⟩ ⟨k,y⟩ hxy
    have hjk : j = k := by
      by_contra hjk
      have hx : x.1 ∈ stdSimplex ℝ (V j) :=
        ((coordinateComplex_space (K j)).le x.2).1
      have hzero : ∀ v, x.1 v = 0 := by
        intro v
        have h := congrArg (fun z : (coordinateComplex (sigmaComplex K)).space => z.1 ⟨j,v⟩) hxy
        change sigmaCoordinates j x.1 ⟨j,v⟩ = sigmaCoordinates k y.1 ⟨j,v⟩ at h
        rw [sigmaCoordinates_apply_same, sigmaCoordinates_apply_other k y.1 ⟨j,v⟩ hjk] at h
        exact h
      have hsum := hx.2
      simp [hzero] at hsum
    subst k
    congr 1
    apply Subtype.ext
    funext v
    have h := congrArg (fun z : (coordinateComplex (sigmaComplex K)).space => z.1 ⟨j,v⟩) hxy
    change sigmaCoordinates j x.1 ⟨j,v⟩ = sigmaCoordinates j y.1 ⟨j,v⟩ at h
    simpa only [sigmaCoordinates_apply_same] using h
  · rintro ⟨w,hw⟩
    obtain ⟨hw,s,⟨j,t,ht,rfl⟩,hz⟩ := (coordinateComplex_space (sigmaComplex K)).le hw
    obtain ⟨x,hx,hxe⟩ := (sigmaCoordinates_image j t).ge ⟨hw,hz⟩
    refine ⟨⟨j,⟨x,?_⟩⟩,Subtype.ext hxe⟩
    rw [coordinateComplex_space]
    exact ⟨hx.1,t,ht,hx.2⟩

private def sigmaSpaceHomeomorph {J : Type} {V : J → Type}
    [Fintype J] [∀ j, Fintype (V j)] (K : ∀ j, PreAbstractSimplicialComplex (V j)) :
    (Σ j, (coordinateComplex (K j)).space) ≃ₜ (coordinateComplex (sigmaComplex K)).space := by
  letI : ∀ j, Finite (coordinateComplex (K j)).faces := fun j => coordinateComplex_finite (K j)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (sigmaSpaceMap K) (sigmaSpaceMap_bijective K))
    (sigmaSpaceMap_continuous K)

private theorem surface_coordinate_model
    (S : SeifertSurfaces.Foundations.CompactOrientedSurface.{0}) :
    ∃ (V : Type) (_ : Fintype V) (K : PreAbstractSimplicialComplex V),
      (∀ s ∈ K.faces, s.card ≤ 3) ∧ Nonempty ((coordinateComplex K).space ≃ₜ S) := by
  classical
  letI : LocallyConnectedSpace S :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace 2) S
  letI : Finite (ConnectedComponents S) := compact_surface_components_finite S
  letI : Fintype (ConnectedComponents S) := Fintype.ofFinite _
  let U : ConnectedComponents S → TopologicalSpace.Opens S := fun j =>
    ⟨ConnectedComponents.mk ⁻¹' {j},
      ConnectedComponents.continuous_coe.isOpen_preimage _ (isOpen_discrete _)⟩
  have hU (j : ConnectedComponents S) : IsConnected (U j : Set S) := by
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe j
    change IsConnected (ConnectedComponents.mk ⁻¹' {ConnectedComponents.mk x})
    rw [connectedComponents_preimage_singleton]
    exact isConnected_connectedComponent
  letI : ∀ j, ConnectedSpace (U j) := fun j => isConnected_iff_connectedSpace.mp (hU j)
  letI : ∀ j, CompactSpace (U j) := fun j =>
    isCompact_iff_compactSpace.mp ((isClosed_discrete {j}).preimage
      ConnectedComponents.continuous_coe).isCompact
  let T : ∀ j, LeanEval.Topology.ClassificationOfSurfaces.GeometricTriangulation (U j) := fun j =>
    (LeanEval.Topology.ClassificationOfSurfaces.Moise.moise_triangulation_of_boundaries (U j)).some
  let V : ConnectedComponents S → Type := fun j => (T j).Vertex
  letI : ∀ j, Fintype (V j) := fun j => (T j).vertexFintype
  let K : ∀ j, PreAbstractSimplicialComplex (V j) := fun j => fullComplex (T j)
  let E : ∀ j, (coordinateComplex (K j)).space ≃ₜ (U j) := fun j =>
    (Homeomorph.setCongr (fullComplex_space (T j))).trans (T j).homeo
  letI : ∀ j, Finite (coordinateComplex (K j)).faces := fun j => coordinateComplex_finite (K j)
  let e : (Σ j, (coordinateComplex (K j)).space) ≃ S :=
    (Equiv.sigmaCongrRight (fun j => (E j).toEquiv)).trans
      (Equiv.sigmaFiberEquiv (ConnectedComponents.mk (α := S)))
  have he : Continuous e := by
    apply continuous_sigma
    intro j
    exact continuous_subtype_val.comp (E j).continuous
  let H : (coordinateComplex (sigmaComplex K)).space ≃ₜ S :=
    (sigmaSpaceHomeomorph K).symm.trans (Continuous.homeoOfEquivCompactToT2 (f := e) he)
  have hcard : ∀ s ∈ (sigmaComplex K).faces, s.card ≤ 3 :=
    sigmaComplex_card K (fun j t ht => fullComplex_face_card (T j) (s := t) ht)
  exact ⟨Σ j, V j,inferInstance,sigmaComplex K,hcard,⟨H⟩⟩


open LeanEval.Topology.ClassificationOfSurfaces
open LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem chart_core_boundary_preconnected (S : CompactOrientedSurface.{0})
    (c : MoiseChart S) (hc : c.BoundaryFaithful) :
    IsPreconnected (c.core ∩ S.boundary) := by
  by_cases hk : c.kind = ChartKind.disk
  · have he : c.core ∩ S.boundary = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hxcore,hxbd⟩
      exact hc.1 hk x (c.core_subset_domain hxcore) hxbd
    rw [he]
    exact isPreconnected_empty
  · have hk' : c.kind = ChartKind.halfDisk := by
      cases hkind : c.kind with
      | disk => exact False.elim (hk hkind)
      | halfDisk => rfl
    let L : Set Plane := c.kind.modelCore ∩ {p | p 0 = 0}
    have hL : L = Metric.closedBall 0 (1 / 2) ∩ {p | p 0 = 0} := by
      ext p
      simp only [L,hk',ChartKind.modelCore,Set.mem_inter_iff,Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨hp,_⟩,hz⟩; exact ⟨hp,hz⟩
      · rintro ⟨hp,hz⟩; exact ⟨⟨hp,by rw [hz]⟩,hz⟩
    have hconn : IsPreconnected L := by
      rw [hL]
      exact ((convex_closedBall (0 : Plane) (1 / 2)).inter
        (convex_hyperplane (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) 0).toLinearMap.isLinear 0)).isPreconnected
    let Z : Set c.kind.modelRegion := Subtype.val ⁻¹' L
    have hZimage : Subtype.val '' Z = L := by
      apply Set.Subset.antisymm
      · rintro _ ⟨p,hp,rfl⟩; exact hp
      · intro p hp
        exact ⟨⟨p,c.kind.modelCore_subset_modelRegion hp.1⟩,hp,rfl⟩
    have hZ : IsPreconnected Z := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rwa [hZimage]
    let f : c.kind.modelRegion → S := fun p => (c.chart.symm p).1
    have hf : Continuous f := continuous_subtype_val.comp c.chart.symm.continuous
    have heq : c.core ∩ S.boundary = f '' Z := by
      ext x
      constructor
      · rintro ⟨hxcore,hxbd⟩
        obtain ⟨hxdom,hxmodel⟩ := c.mem_core_iff.mp hxcore
        refine ⟨c.chart ⟨x,hxdom⟩,⟨hxmodel,(hc.2 hk' x hxdom).mp hxbd⟩,?_⟩
        exact congrArg Subtype.val (c.chart.symm_apply_apply ⟨x,hxdom⟩)
      · rintro ⟨p,hp,rfl⟩
        have hcore : f p ∈ c.core := c.mem_core_iff.mpr
          ⟨(c.chart.symm p).property,by simpa [f] using hp.1⟩
        refine ⟨hcore,(hc.2 hk' (f p) (c.chart.symm p).property).mpr ?_⟩
        simpa [f] using hp.2
    rw [heq]
    exact hZ.image f hf.continuousOn


theorem compact_surface_boundary_components_finite (S : CompactOrientedSurface.{0}) :
    Finite (ConnectedComponents ↥S.boundary) := by
  classical
  obtain ⟨m,charts,hcover,hbd⟩ := moise_finite_chart_cover S
  let C : Fin m → Set S := fun i => (charts i).core ∩ S.boundary
  let D : Fin m → Set ↥S.boundary := fun i => Subtype.val ⁻¹' C i
  have hD (i : Fin m) : IsPreconnected (D i) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have heq : Subtype.val '' D i = C i := by
      apply Set.Subset.antisymm
      · rintro _ ⟨p,hp,rfl⟩; exact hp
      · intro p hp; exact ⟨⟨p,hp.2⟩,hp,rfl⟩
    rw [heq]
    exact chart_core_boundary_preconnected S (charts i) (hbd i)
  have hDcover : ∀ x : S.boundary, ∃ i, x ∈ D i := by
    intro x
    have hh : (x : S) ∈ ⋃ i, (charts i).core := by rw [hcover]; trivial
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
    exact ⟨i,hi,x.property⟩
  let I := {i : Fin m // (D i).Nonempty}
  let r : I → S.boundary := fun i => i.property.choose
  let f : I → ConnectedComponents ↥S.boundary := fun i => ConnectedComponents.mk (r i)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x,rfl⟩ := ConnectedComponents.surjective_coe q
    obtain ⟨i,hi⟩ := hDcover x
    let ii : I := ⟨i,⟨x,hi⟩⟩
    refine ⟨ii,?_⟩
    apply ConnectedComponents.coe_eq_coe.mpr
    apply connectedComponent_eq
    exact (hD i).subset_connectedComponent (ii.property.choose_spec) hi
  exact Finite.of_surjective f hf

/-- Compact smooth surface triangulation/finite homotopy type is a dependency
of this result, not an assumption restricting the source surfaces. -/
theorem compact_surface_homology_finite (S : CompactOrientedSurface.{0}) (k : ℕ) :
    Module.Finite ℚ (rationalHomology S k) := by
  obtain ⟨V,hV,K,hK,⟨e⟩⟩ := surface_coordinate_model S
  letI := hV
  letI := finiteCoordinateHomology K k
  let q := (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
    (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo
      (X := TopCat.of (coordinateComplex K).space) (Y := TopCat.of S) e)).toLinearEquiv
  exact q.finiteDimensional

theorem compact_surface_higher_homology_zero (S : CompactOrientedSurface.{0})
    (k : ℕ) (hk : 2 < k) : Subsingleton (rationalHomology S k) := by
  obtain ⟨V,hV,K,hK,⟨e⟩⟩ := surface_coordinate_model S
  letI := hV
  have hz := zeroCoordinateHomology K hK k hk
  have hs := hz.of_iso
    ((((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) k).obj
      (ModuleCat.of ℚ ℚ)).mapIso (TopCat.isoOfHomeo
        (X := TopCat.of (coordinateComplex K).space) (Y := TopCat.of S) e)).symm)
  exact ModuleCat.subsingleton_of_isZero hs

theorem surface_betti_zero_components (S : CompactOrientedSurface.{0}) :
    betti S 0 = componentCount S := by
  classical
  letI : LocallyPathConnectedSpace S :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanHalfSpace 2) S
  letI : Fintype (ZerothHomotopy S) := Fintype.ofFinite _
  let e : rationalHomology S 0 ≃ₗ[ℚ] (ZerothHomotopy S → ℚ) :=
    (CategoryTheory.Iso.toLinearEquiv ((TopCat.singularHomology₀Iso (TopCat.of S)
      (ModuleCat.of ℚ ℚ)) ≪≫ ModuleCat.coprodIsoDirectSum
        (fun _ : ZerothHomotopy S => ModuleCat.of ℚ ℚ))).trans
      (DirectSum.linearEquivFunOnFintype ℚ (ZerothHomotopy S) (fun _ => ℚ))
  change Module.finrank ℚ (rationalHomology S 0) = Nat.card (ConnectedComponents S)
  rw [e.finrank_eq, Module.finrank_pi, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (connectedComponentsEquivZerothHomotopy (X := S))).symm


end
end SeifertSurfaces.GenusLinking
