import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition

/-!
# Canonical relative singular-cochain pullbacks

Source: Hatcher, Algebraic Topology, induced maps of pairs p.201.
All complexes and cohomology quotients are the existing genuine singular objects.
The restriction square is proved from functor composition. Mathlib kernel.map
restricts the ordinary pullback to the relative kernels, and quotientMap induces
its map on the actual relative-cohomology quotient. Every definition is implemented.
-/

open CategoryTheory CategoryTheory.Limits Opposite Set

universe u

noncomputable section

namespace HolomorphicAnosov.SingularCochain

variable (R : Type u) [CommRing R]

/-- Hatcher p.201: restriction of a map of pairs to its actual subspaces. -/
def pairSubspaceMap {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (hf : MapsTo f A B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨fun a ↦ ⟨f a, hf a.property⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Hatcher p.201: restriction commutes with pullback, by the actual functor composition law. -/
theorem pairRestrictionSquare {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (hf : MapsTo f A B) :
    pullback R (subspaceInclusion Y B) ≫ pullback R (pairSubspaceMap f hf) =
      pullback R f ≫ pullback R (subspaceInclusion X A) := by
  change (cochainFunctor R).map _ ≫ (cochainFunctor R).map _ =
    (cochainFunctor R).map _ ≫ (cochainFunctor R).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Hatcher p.201: the actual relative-cochain pullback, induced on restriction kernels. -/
def relativePullback {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (hf : MapsTo f A B) :
    relativeComplex R Y B ⟶ relativeComplex R X A :=
  kernel.map (pullback R (subspaceInclusion Y B)) (pullback R (subspaceInclusion X A))
    (pullback R f) (pullback R (pairSubspaceMap f hf)) (pairRestrictionSquare R f hf)

/-- Hatcher p.201: pair pullback on the existing actual relative-cohomology quotient. -/
def relativeCohomologyPullback {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (hf : MapsTo f A B) (k : ℕ) :
    relativeCohomology R Y B k ⟶ relativeCohomology R X A k :=
  quotientMap R (relativePullback R f hf) k

end HolomorphicAnosov.SingularCochain
