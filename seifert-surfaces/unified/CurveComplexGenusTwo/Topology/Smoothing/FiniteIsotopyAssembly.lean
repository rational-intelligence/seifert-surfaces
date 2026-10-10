import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport

namespace CurveComplex
open Set
variable {S : Type*} [TopologicalSpace S]

/-- Composition at each time assembles two ambient moves into one isotopy. -/
def AmbientIsotopy.compose (H K : AmbientIsotopy S) : AmbientIsotopy S where
  map := ⟨fun z => K.map (z.1, H.map z),
    K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
  homeomorphism_at := by
    intro t
    obtain ⟨h, hh⟩ := H.homeomorphism_at t
    obtain ⟨k, hk⟩ := K.homeomorphism_at t
    exact ⟨h.trans k, fun x => by
      change k (h x) = K.map (t, H.map (t, x))
      rw [hh, hk]⟩
  at_zero := by
    intro x
    change K.map (_, H.map (_, x)) = x
    rw [H.at_zero, K.at_zero]

@[simp] theorem AmbientIsotopy.compose_finalMap (H K : AmbientIsotopy S) :
    (H.compose K).finalMap = K.finalMap ∘ H.finalMap := rfl

def AmbientIsotopy.identity (S : Type*) [TopologicalSpace S] : AmbientIsotopy S where
  map := ⟨Prod.snd, continuous_snd⟩
  homeomorphism_at := fun _ => ⟨Homeomorph.refl S, fun _ => rfl⟩
  at_zero := fun _ => rfl

/-- Finite composition retains an explicit common ambient isotopy. -/
def AmbientIsotopy.finiteCompose : List (AmbientIsotopy S) → AmbientIsotopy S
  | [] => AmbientIsotopy.identity S
  | H :: tail => H.compose (AmbientIsotopy.finiteCompose tail)

theorem AmbientIsotopy.finiteCompose_fixes (moves : List (AmbientIsotopy S))
    (P : Set S) (hfix : ∀ H ∈ moves, ∀ t x, x ∈ P → H.map (t, x) = x) :
    ∀ t x, x ∈ P → (AmbientIsotopy.finiteCompose moves).map (t, x) = x := by
  induction moves with
  | nil => intro t x hx; rfl
  | cons H tail ih =>
    intro t x hx
    change (AmbientIsotopy.finiteCompose tail).map (t, H.map (t, x)) = x
    rw [hfix H (by simp) t x hx]
    exact ih (fun K hK => hfix K (by simp [hK])) t x hx

namespace HyperellipticModel
variable {S : Type} [TopologicalSpace S]
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A finite sequence of local moves transports the whole caller's family,
retaining all-time marked fixation, essentiality, endpoints and disjointness. -/
theorem finite_marked_isotopy_family_transport
    (M : HyperellipticModel E S) {ι : Type} (a : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (a i)) (arcInterior M (a j)))
    (moves : List (AmbientIsotopy S))
    (hfix : ∀ H ∈ moves, ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) :
    ∃ b : ι → EssentialMarkedArc M,
      (∀ t x, x ∈ M.cover.branch →
        (AmbientIsotopy.finiteCompose moves).map (t, x) = x) ∧
      (∀ i, (AmbientIsotopy.finiteCompose moves).finalMap '' (a i).val.image =
        (b i).val.image) ∧
      (∀ i, (b i).val.map ⟨0, by norm_num⟩ = (a i).val.map ⟨0, by norm_num⟩) ∧
      (∀ i, (b i).val.map ⟨1, by norm_num⟩ = (a i).val.map ⟨1, by norm_num⟩) ∧
      ∀ i j, i ≠ j → Disjoint (arcInterior M (b i)) (arcInterior M (b j)) := by
  let H := AmbientIsotopy.finiteCompose moves
  have hmarks : ∀ t x, x ∈ M.cover.branch → H.map (t, x) = x :=
    AmbientIsotopy.finiteCompose_fixes moves (M.cover.branch : Set S) hfix
  obtain ⟨g, hg⟩ := H.homeomorphism_at (⟨1, by norm_num⟩ : Interval)
  have hgfix : ∀ x, x ∈ M.cover.branch → g x = x :=
    fun x hx => (hg x).trans (hmarks _ x hx)
  let b : ι → EssentialMarkedArc M := fun i => (a i).transport g hgfix
  refine ⟨b, hmarks, ?_, ?_, ?_, ?_⟩
  · intro i
    change H.finalMap '' (a i).val.image = ((a i).val.transport g hgfix).image
    rw [MarkedArc.transport_image]
    exact congrArg (fun f : S → S => f '' (a i).val.image) (funext hg).symm
  · intro i
    exact hgfix _ (a i).val.start_marked
  · intro i
    exact hgfix _ (a i).val.end_marked
  · intro i j hij
    exact arcInterior_transport_disjoint (a i) (a j) g hgfix (hd i j hij)

#print axioms finite_marked_isotopy_family_transport
end HyperellipticModel
end CurveComplex
