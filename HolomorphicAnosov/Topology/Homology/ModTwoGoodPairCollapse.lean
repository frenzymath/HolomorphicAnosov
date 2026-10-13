import HolomorphicAnosov.Topology.GoodPairReducedHomologyExactSequence
import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsHomologyNaturality
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

open CategoryTheory CategoryTheory.Limits
open HolomorphicAnosov.GoodPair HolomorphicAnosov.Topology.Homology
namespace HolomorphicAnosov

/-- Collapsing a nonempty closed subspace with a deformation-retract neighborhood
induces an isomorphism on relative singular homology with mod-two coefficients.

Source: Hatcher, Algebraic Topology, Proposition 2.22 p.124 and the coefficient
extension p.153. Apply the proved arbitrary integer-module good-pair comparison
to the underlying abelian group of the mod-two coefficient object. The natural
restriction-of-scalars chain/homology isomorphisms identify this induced map
with restriction of scalars of the original mod-two quotient map. Thus the
latter becomes invertible after forgetting scalars. Restriction of scalars
reflects isomorphisms, giving the stated mod-two isomorphism. Coefficients are
not changed by tensor product, and the map is the original collapse-induced map
in every degree, including zero. -/
theorem modTwoGoodPairCollapse (X : TopCat.{0}) (A V : Set X)
    (hA : A.Nonempty) (hclosed : IsClosed A) (hAV : A ⊆ V)
    (hneighborhood : A ⊆ interior V)
    (d : HolomorphicAnosov.Topology.Homotopy.StrongDeformationRetract A V hAV) (n : ℕ) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    IsIso (SSetPair.homologyMap (collapseSingularPairMap X A) R0 n) := by
  dsimp only
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let f := Int.castRingHom (ZMod 2)
  let F := ModuleCat.restrictScalars.{0} f
  let g := collapseSingularPairMap X A
  have h := collapse_homology_isIso_of_good_pair X A V hA hclosed hAV hneighborhood d
    (F.obj R0) n
  have hn := ssetPairRestrictScalarsHomologyIso_naturality f g R0 n
  have hi : IsIso (F.map (SSetPair.homologyMap g R0 n) ≫
      (ssetPairRestrictScalarsHomologyIso f _ R0 n).hom) := by
    rw [hn]
    infer_instance
  have : IsIso (F.map (SSetPair.homologyMap g R0 n)) :=
    (isIso_comp_right_iff _ (ssetPairRestrictScalarsHomologyIso f _ R0 n).hom).mp hi
  exact isIso_of_reflects_iso (SSetPair.homologyMap g R0 n) F

end HolomorphicAnosov
