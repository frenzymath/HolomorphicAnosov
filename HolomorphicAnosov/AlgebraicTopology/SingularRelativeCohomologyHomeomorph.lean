import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Canonical relative cohomology pullback for a homeomorphism of pairs

Source: Hatcher, Algebraic Topology, pp.199–201, functoriality of relative
cohomology. The map is the literal pullback on relative singular cochains.
-/

open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- A homeomorphism identifying the two distinguished subspaces induces an
isomorphism by the canonical relative cohomology pullback.

Source: Hatcher pp.199–201. The homeomorphism and its subspace restriction are
isomorphisms of topological spaces. The singular cochain functor sends both to
isomorphisms, so the induced map on restriction kernels is an isomorphism.
Applying homology and the canonical kernel/image-quotient identifications gives
the asserted isomorphism in every degree over any commutative ring. -/
theorem relativeCohomologyPullback_isIso_of_homeomorph
    (R : Type u) [CommRing R] {X Y : TopCat.{u}} (A : Set X) (B : Set Y)
    (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    IsIso (relativeCohomologyPullback R (X := X) (Y := Y) (A := A) (B := B) (TopCat.ofHom (e : C(X, Y)))
      (fun x hx ↦ (he x).mp hx) k) := by
  have : IsIso (TopCat.ofHom (e : C(X, Y))) := (TopCat.isoOfHomeo e).isIso_hom
  have hs : pairSubspaceMap (A := A) (B := B) (TopCat.ofHom (e : C(X, Y))) (fun x hx ↦ (he x).mp hx) =
      TopCat.ofHom (e.subtype he : C(A, B)) := rfl
  have : IsIso (pairSubspaceMap (A := A) (B := B) (TopCat.ofHom (e : C(X, Y))) (fun x hx ↦ (he x).mp hx)) := by
    rw [hs]
    exact (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of B) (e.subtype he)).isIso_hom
  have : IsIso (pullback R (TopCat.ofHom (e : C(X, Y)))) := by
    unfold pullback
    infer_instance
  have : IsIso (pullback R (pairSubspaceMap (A := A) (B := B) (TopCat.ofHom (e : C(X, Y))) (fun x hx ↦ (he x).mp hx))) := by
    unfold pullback
    infer_instance
  unfold relativeCohomologyPullback quotientMap relativePullback
  infer_instance

end HolomorphicAnosov.SingularCochain
