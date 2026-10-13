import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Algebra.Homology.Homotopy

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- The original subspace pair `(B, {b : B | b.val ∈ A})`.
Source: Hatcher Theorem 2.20, p. 119; the singular subspace adapter. -/
abbrev singularExcisionSource (X : TopCat.{u}) (A B : Set X) : SSetPair.{u} :=
  singularSubspacePair (TopCat.of B) {b | b.val ∈ A}

/-- The literal pair inclusion from the intersection pair into `(X,A)`.
Source: Hatcher Theorem 2.20, p. 119 and proof p. 124. -/
def singularExcisionInclusion (X : TopCat.{u}) (A B : Set X) :
    singularExcisionSource X A B ⟶ singularSubspacePair X A :=
  singularSubspacePairMap (singularSubspaceInclusion X B)
    {b | b.val ∈ A} A (fun _ hb ↦ hb)

/-- The map of intersection pairs induced by a continuous map preserving both subsets.
Source: Hatcher maps of pairs, p. 118; restriction retains both subspace topologies. -/
def singularExcisionSourceMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (A B : Set X) (A' B' : Set Y) (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    singularExcisionSource X A B ⟶ singularExcisionSource Y A' B' :=
  singularSubspacePairMap (singularSubspaceMap f B B' hB)
    {b | b.val ∈ A} {b | b.val ∈ A'} (fun _ hb ↦ hA hb)

/-- The relative small-chain pair: quotient A-supported chains out of A-or-B chains.
Source: Hatcher proof of excision, p. 124; the subcomplex join records small simplices. -/
def singularExcisionSmallPair (X : TopCat.{u}) (A B : Set X) : SSetPair.{u} :=
  SSetPair.of (SSet.Subcomplex.homOfLE
    (show singularSubspace X A ≤ singularSubspace X A ⊔ singularSubspace X B
      from le_sup_left))

/-- The actual inclusion of the relative small-chain pair into the supported ambient pair.
Source: Hatcher p. 124, the quotient of the small-chain inclusion. -/
def singularExcisionSmallInclusion (X : TopCat.{u}) (A B : Set X) :
    singularExcisionSmallPair X A B ⟶ (singularSubspace X A).pair :=
  SSetPair.homMk (𝟙 _) (singularSubspace X A ⊔ singularSubspace X B).ι (by
    ext n s
    rfl)

/-- The literal intersection-to-small-union pair map used in the quotient isomorphism.
Source: Hatcher p. 124, `C(B)/C(A∩B) → C(A+B)/C(A)`. -/
def singularExcisionQuotientInclusion (X : TopCat.{u}) (A B : Set X) :
    singularIntersectionPair X A B ⟶ singularExcisionSmallPair X A B :=
  SSetPair.homMk (SSet.Subcomplex.homOfLE inf_le_left)
    (SSet.Subcomplex.homOfLE le_sup_right) (by
      ext n s
      rfl)

/-- The homology map obtained by applying a coefficient homomorphism to each summand.
Source: Hatcher arbitrary coefficient groups, p. 153; native relative-chain bifunctor. -/
abbrev singularRelativeCoefficientMap (P : SSetPair.{u})
    {R Q : ModuleCat.{u} ℤ} (φ : R ⟶ Q) (n : ℕ) : P.homology R n ⟶ P.homology Q n :=
  HomologicalComplex.homologyMap
    (((SSetPair.chainComplexFunctor (ModuleCat.{u} ℤ)).map φ).app P) n


end
end HolomorphicAnosov
