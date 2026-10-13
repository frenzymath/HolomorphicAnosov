import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions
import HolomorphicAnosov.Topology.SingularHomologyExcision.PairNaturality

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- Applying the native relative homology functor retains the literal inclusion square.
Source: Hatcher maps of pairs p.118 and excision p.124; no excision assumption is used. -/
theorem excision_homology_naturality
    (X Y : TopCat.{u}) (f : X ⟶ Y) (A B : Set X) (A' B' : Set Y)
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B')
    (R : ModuleCat.{u} ℤ) (n : ℕ) :
    SSetPair.homologyMap (singularExcisionInclusion X A B) R n ≫
        SSetPair.homologyMap (singularSubspacePairMap f A A' hA) R n =
      SSetPair.homologyMap (singularExcisionSourceMap f A B A' B' hA hB) R n ≫
        SSetPair.homologyMap (singularExcisionInclusion Y A' B') R n := by
  rw [← SSetPair.homologyMap_comp, ← SSetPair.homologyMap_comp,
    excision_pair_naturality X Y f A B A' B' hA hB]


end
end HolomorphicAnosov

