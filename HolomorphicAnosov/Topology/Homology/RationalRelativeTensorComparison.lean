import HolomorphicAnosov.Topology.Homology.RationalRelativeScalarProjection
import HolomorphicAnosov.Topology.Homology.NativeRelativeShuffleComparison
import HolomorphicAnosov.Algebra.Homology.FieldTensorHomologyKunneth

/-!
# Rational relative tensor comparison

Source: Bredon VI pp.318–320. This conjugates the native lifted-field relative
shuffle equivalence through the canonical chain comparisons and returns to the
original rational scalar action. The tensor total is exactly the larger-universe
construction used by the field Künneth provider, with no replacement carriers.
DAG node: `topo.rational_relative_tensor_comparison_g1`.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u
namespace HolomorphicAnosov.RationalRelativeTensorComparison
open RationalScalarTransport NativeRelativeShuffleComparison SingularEilenbergZilber

abbrev rationalRelative (X : TopCat.{u}) (B : Set X) :=
  (nativePair X B).chainComplex qCoefficients
abbrev rationalAbsolute (Y : TopCat.{u}) :=
  (TopCat.toSSet.obj Y).chainComplex qCoefficients
abbrev rationalTensor (X Y : TopCat.{u}) (B : Set X) :=
  FieldTensorHomologyKunneth.ArbitraryUniverse.totalComplex.{0,u}
    (rationalRelative X B) (rationalAbsolute Y)

set_option backward.isDefEq.respectTransparency false in
/-- Conjugate the native lifted-rational relative shuffle equivalence by the
canonical chain comparisons, then restrict scalars back to the original ℚ.
All complex carriers and differentials are preserved by this ring equivalence. -/
def transportNativeEquivalence (X Y : TopCat.{u}) (B : Set X)
    (e : HomotopyEquiv
      (HomologicalComplex.tensorObj (relativeComplex X B) (chainFunctor.obj Y))
      (relativeComplex (TopCat.of (X × Y)) (productSupport X Y B))) :
    HomotopyEquiv (rationalTensor X Y B)
      (rationalRelative (TopCat.of (X × Y)) (productSupport X Y B)) := by
  let S := tensorIso (nativeRelativeChainComparison (nativePair X B))
    (nativeChainComparison (TopCat.toSSet.obj Y))
  let T := nativeRelativeChainComparison
    (nativePair (TopCat.of (X × Y)) (productSupport X Y B))
  let E := (HomotopyEquiv.ofIso S).trans (e.trans (HomotopyEquiv.ofIso T.symm))
  exact FieldTensorHomologyKunneth.ArbitraryUniverse.originalScalars.mapHomotopyEquiv E

end HolomorphicAnosov.RationalRelativeTensorComparison

