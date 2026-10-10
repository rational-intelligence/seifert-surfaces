import LinkExterior
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Compression-disk bridge and the actual class complex of Definition 4.1

Images, not parametrized embeddings or chosen minimizers, are quotiented by
the genuine smooth ambient-isotopy relation from Section 4.1. Finite faces
require simultaneous representatives; pairwise disjointness of separately
chosen pairs is not sufficient. Genus and area truncations remain deferred
until actual invariant constructions are available.
-/

open scoped Manifold ContDiff
open Set Topology

namespace SeifertSurfaces.Foundations

universe u v
noncomputable section

abbrev ClosedDisk := ↥(Metric.closedBall (0 : Euc 2) 1)

def closedDiskBoundary : Set ClosedDisk := {x | ‖(x : Euc 2)‖ = 1}

/- An actual smooth embedded disk that compresses a surface. A disk is
characterized by a homeomorphism to the closed Euclidean disk, with its genuine
boundary corresponding to the unit circle. Essentiality is non-nullhomotopy of
the embedded boundary loop in the source surface. -/
structure CompressingDisk {S : CompactOrientedSurface.{u}} {M : Type v}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f : NeatEmbedding S M) where
  disk : CompactOrientedSurface.{u}
  disk_homeomorph : disk ≃ₜ ClosedDisk
  disk_boundary : disk_homeomorph '' disk.boundary = closedDiskBoundary
  toFun : disk → M
  smoothEmbedding : Manifold.IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ toFun
  boundaryCircle : disk.OrientedBoundaryCircle
  boundary_covers : Set.range boundaryCircle.toFun = disk.boundary
  surfaceLoop : C(Circle, S)
  surfaceLoop_embedded : IsEmbedding surfaceLoop
  boundary_matches : ∀ z, toFun (boundaryCircle.toFun z) = f.toFun (surfaceLoop z)
  intersection : Set.range toFun ∩ f.image = toFun '' disk.boundary
  interior_ambient : toFun '' (disk.boundary)ᶜ ⊆ (𝓡∂ 3).interior M
  essential : ¬ ∃ x : S,
    ContinuousMap.Homotopic surfaceLoop (ContinuousMap.const Circle x)

/- The introduction's π₁ definition and Section 4.1's compression-disk
definition are compared for an actual oriented spanning surface in the actual
link exterior in S³. Its two-sidedness comes from the oriented surface and
ambient sphere/exterior geometry; producing that bridge and applying the
loop/disk theorem remain proof obligations. No arbitrary ambient manifold or
freely supplied two-sidedness proposition is substituted. -/

/- Smooth isotopy of image surfaces allows an endpoint reparametrization of
the fixed source. This is necessary when comparing an ambient image relation
with normal isotopy of parametrized embeddings. -/
structure ReparametrizedNormalIsotopy (S : CompactOrientedSurface.{u}) (M : Type v)
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (f g : NeatEmbedding S M) where
  stage : Time → NeatEmbedding S M
  smooth_family : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 2)) (𝓡∂ 3) ∞
    (fun p : Time × S => (stage p.1).toFun p.2)
  initial : (stage 0).toFun = f.toFun
  reparametrization : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) S S ∞
  final : (stage 1).toFun = g.toFun ∘ reparametrization


variable {n : ℕ} {L : OrientedLink n} {T : TubularNeighborhood L}

/- Componentwise incompressibility is retained for disconnected link surfaces. -/
abbrev IncompressibleSpanningSurface (E : SmoothExterior T) :=
  {F : LinkSpanningSurface.{u} E // F.Incompressible}

/- Admissible **images** of actual incompressible spanning surfaces. Equality
ignores auxiliary parametrizations, orientations representing the same oriented
ray, boundary-circle choices, and tubular-coordinate witnesses. -/
def SurfaceImage (E : SmoothExterior T) :=
  {A : Set E.Carrier | ∃ F : IncompressibleSpanningSurface.{u} E, F.1.image = A}

def surfaceImageOf (E : SmoothExterior T) (F : IncompressibleSpanningSurface.{u} E) :
    SurfaceImage.{u} E := ⟨F.1.image, ⟨F, rfl⟩⟩

/- Transport of a genuine surface and its π₁ property along an ambient
isotopy is an explicit invariant obligation. -/

/- Equal embedded images have diffeomorphic source surfaces. This supplies
the source-independence bridge needed by any subsequent genus construction. -/
theorem same_image_source_diffeomorph (E : SmoothExterior T)
    (F G : LinkSpanningSurface.{u} E) (h : F.image = G.image) :
    ∃ e : Diffeomorph (𝓡∂ 2) (𝓡∂ 2) F.surface G.surface ∞,
      ∀ x, G.embedding.toFun (e x) = F.embedding.toFun x := by
  let eF := F.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  let eG := G.embedding.smoothEmbedding.isEmbedding.toHomeomorph
  have hr : Set.range F.embedding.toFun = Set.range G.embedding.toFun := h
  let e : F.surface ≃ₜ G.surface := eF.trans ((Homeomorph.setCongr hr).trans eG.symm)
  have he : ∀ x, G.embedding.toFun (e x) = F.embedding.toFun x := by
    intro x
    have hval := congrArg Subtype.val (eG.apply_symm_apply ((Homeomorph.setCongr hr) (eF x)))
    exact hval
  have hei : ∀ y, F.embedding.toFun (e.symm y) = G.embedding.toFun y := by
    intro y
    simpa only [e.apply_symm_apply] using (he (e.symm y)).symm
  have hs : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ e := by
    apply (ContMDiff.iff_comp_isImmersion G.embedding.smoothEmbedding.isImmersion).mpr
    refine ⟨e.continuous, ?_⟩
    have hf : G.embedding.toFun ∘ e = F.embedding.toFun := funext he
    rw [hf]
    exact F.embedding.smoothEmbedding.contMDiff
  have hsi : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ e.symm := by
    apply (ContMDiff.iff_comp_isImmersion F.embedding.smoothEmbedding.isImmersion).mpr
    refine ⟨e.symm.continuous, ?_⟩
    have hf : F.embedding.toFun ∘ e.symm = G.embedding.toFun := funext hei
    rw [hf]
    exact G.embedding.smoothEmbedding.contMDiff
  exact ⟨{ e.toEquiv with contMDiff_toFun := hs, contMDiff_invFun := hsi }, he⟩

def ImageIsotopic (E : SmoothExterior T) (A B : SurfaceImage.{u} E) : Prop :=
  SmoothAmbientIsotopy.Rel A.1 B.1

theorem imageIsotopic_equivalence (E : SmoothExterior T) :
    Equivalence (ImageIsotopic.{u} E) := by
  exact ⟨fun A => SmoothAmbientIsotopy.rel_refl A.1,
    fun h => SmoothAmbientIsotopy.rel_symm _ _ h,
    fun h h' => SmoothAmbientIsotopy.rel_trans _ _ _ h h'⟩

def imageSetoid (E : SmoothExterior T) : Setoid (SurfaceImage.{u} E) :=
  ⟨ImageIsotopic E, imageIsotopic_equivalence E⟩

/- Actual Definition 4.1 vertices for a knot, and the componentwise version
used for links. Connectedness in the knot case is the pending theorem
`LinkSpanningSurface.connected_for_knot`, not a new fake surface property. -/
abbrev Vertex (E : SmoothExterior T) := Quotient (imageSetoid.{u} E)

def classOf (E : SmoothExterior T) (A : SurfaceImage.{u} E) : Vertex.{u} E :=
  Quotient.mk (imageSetoid E) A

theorem classOf_eq_iff (E : SmoothExterior T) (A B : SurfaceImage.{u} E) :
    (classOf E A) = classOf E B ↔ ImageIsotopic E A B := by
  exact Quotient.eq

/- Simultaneous representatives of one fixed finite set of distinct vertices.
Mathlib abstract complexes omit the empty face, so nonemptiness is explicit. -/

/- Simultaneous representatives of one fixed finite set of distinct vertices.
Mathlib abstract complexes omit the empty face, so nonemptiness is explicit. -/
def IsFace (E : SmoothExterior T) (s : Finset (Vertex.{u} E)) : Prop :=
  s.Nonempty ∧
  ∃ representative : {v : Vertex.{u} E // v ∈ s} → SurfaceImage.{u} E,
    (∀ v, classOf E (representative v) = v.1) ∧
    Pairwise (fun v w => Disjoint (representative v).1 (representative w).1)

theorem faces_lower (E : SmoothExterior T) :
    IsRelLowerSet {s | IsFace.{u} E s} Finset.Nonempty := by
  intro s hs
  refine ⟨hs.1, ?_⟩
  intro t hts ht
  rcases hs.2 with ⟨r, hr, hd⟩
  let inc : {v : Vertex.{u} E // v ∈ t} → {v : Vertex.{u} E // v ∈ s} :=
    fun v => ⟨v.1, hts v.2⟩
  refine ⟨ht, r ∘ inc, fun v => hr (inc v), ?_⟩
  intro v w hvw
  apply hd
  intro heq
  apply hvw
  exact Subtype.ext (congrArg (fun z : {v : Vertex.{u} E // v ∈ s} => z.1) heq)

theorem singleton_face (E : SmoothExterior T) (v : Vertex.{u} E) :
    IsFace E {v} := by
  classical
  obtain ⟨A, hA⟩ := Quotient.exists_rep v
  refine ⟨Finset.singleton_nonempty _, (fun _ => A), ?_, ?_⟩
  · intro w
    exact hA.trans (Finset.mem_singleton.mp w.2).symm
  · intro a b hab
    exact (hab (Subtype.ext ((Finset.mem_singleton.mp a.2).trans
      (Finset.mem_singleton.mp b.2).symm))).elim

/- The actual class complex, constructed from simultaneous-disjointness faces.
It is not replaced by the flag complex of its graph; flagness is Lemma 4.3. -/

/- The actual class complex, constructed from simultaneous-disjointness faces.
It is not replaced by the flag complex of its graph; flagness is Lemma 4.3. -/
def IS (E : SmoothExterior T) : AbstractSimplicialComplex (Vertex.{u} E) where
  faces := {s | IsFace E s}
  isRelLowerSet_faces := faces_lower E
  singleton_mem := singleton_face E

/- Definition 4.1 adjacency: distinct classes with disjoint representatives. -/
def Adjacent (E : SmoothExterior T) (v w : Vertex.{u} E) : Prop :=
  v ≠ w ∧ ∃ A B : SurfaceImage.{u} E,
    (classOf E A) = v ∧ classOf E B = w ∧ Disjoint A.1 B.1

theorem adjacent_symmetric (E : SmoothExterior T) :
    ∀ v w : Vertex.{u} E, Adjacent E v w → Adjacent E w v := by
  rintro v w ⟨hne, A, B, hA, hB, hd⟩
  exact ⟨hne.symm, B, A, hB, hA, hd.symm⟩

theorem adjacent_irreflexive (E : SmoothExterior T) :
    ∀ v : Vertex.{u} E, ¬ Adjacent E v v := by
  intro v hv
  exact hv.1 rfl

def oneSkeleton (E : SmoothExterior T) : SimpleGraph (Vertex.{u} E) where
  Adj := Adjacent E
  symm := ⟨adjacent_symmetric E⟩
  loopless := ⟨adjacent_irreflexive E⟩

/- Seifert's algorithm is an existence obligation for actual surface data. -/

/- Existence of an incompressible surface requires compression/termination
and the disk-versus-π₁ bridge; those conclusions are not structure fields. -/


theorem pair_face_iff (E : SmoothExterior T) (v w : Vertex.{u} E) (h : v ≠ w) :
    IsFace E (@insert (Vertex.{u} E) (Finset (Vertex.{u} E))
      (@Finset.instInsert (Vertex.{u} E) (Classical.decEq _)) v {w}) ↔ Adjacent E v w := by
  classical
  letI : DecidableEq (Vertex.{u} E) := Classical.decEq _
  constructor
  · rintro ⟨_, r, hr, hd⟩
    refine ⟨h, r ⟨v, by simp⟩, r ⟨w, by simp⟩, hr _, hr _, ?_⟩
    exact hd (fun heq => h (congrArg Subtype.val heq))
  · rintro ⟨_, A, B, hA, hB, hd⟩
    let r : {x : Vertex.{u} E // x ∈ ({v, w} : Finset (Vertex.{u} E))} → SurfaceImage.{u} E :=
      fun x => if x.1 = v then A else B
    refine ⟨Finset.insert_nonempty _ _, r, ?_, ?_⟩
    · intro x
      rcases Finset.mem_insert.mp x.2 with hv | hw
      · simp [r, hv, hA]
      · have hw' := Finset.mem_singleton.mp hw
        simp [r, hw', h.symm, hB]
    · intro x y hxy
      have hval : x.1 ≠ y.1 := fun heq => hxy (Subtype.ext heq)
      by_cases hx : x.1 = v
      · have hy : y.1 ≠ v := fun hy => hval (hx.trans hy.symm)
        simpa only [r, if_pos hx, if_neg hy] using hd
      · have hxw : x.1 = w := Finset.mem_singleton.mp
          ((Finset.mem_insert.mp x.2).resolve_left hx)
        have hy : y.1 = v := (Finset.mem_insert.mp y.2).resolve_right
          (fun hyw => hval (hxw.trans (Finset.mem_singleton.mp hyw).symm))
        simpa only [r, if_neg hx, if_pos hy] using hd.symm

end
end SeifertSurfaces.Foundations
