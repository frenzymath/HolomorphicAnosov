import HolomorphicAnosov.Topology.SingularHomologyExcision.Definitions

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace HolomorphicAnosov

noncomputable section

/-- The actual inclusion square commutes before taking chains or homology.
Source: Hatcher p.118 maps of pairs and p.124 excision inclusion; both component
maps forget the same subtype witnesses and postcompose by the same continuous map. -/
theorem excision_pair_naturality
    (X Y : TopCat.{u}) (f : X ⟶ Y) (A B : Set X) (A' B' : Set Y)
    (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    singularExcisionInclusion X A B ≫ singularSubspacePairMap f A A' hA =
      singularExcisionSourceMap f A B A' B' hA hB ≫
        singularExcisionInclusion Y A' B' := by
  apply MorphismProperty.Arrow.Hom.ext
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · change TopCat.toSSet.map _ ≫ TopCat.toSSet.map _ =
      TopCat.toSSet.map _ ≫ TopCat.toSSet.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl


end
end HolomorphicAnosov

