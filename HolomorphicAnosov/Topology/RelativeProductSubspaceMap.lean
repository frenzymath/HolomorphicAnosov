import Mathlib.Topology.Category.TopCat.Basic

/-!
# Product maps preserve the relative product subspace

Source: Bredon, *Topology and Geometry*, IV §16.3 p.222. The product of a
map of pairs sends `A × Y ∪ X × B` into `A' × Y' ∪ X' × B'`.
DAG node: `topo.relative_product_subspace_map_g18`.
-/

open CategoryTheory

namespace HolomorphicAnosov.Topology

universe u

/-- The product of maps of pairs maps the union product subspace into the
corresponding union product subspace. -/
theorem relativeProductSubspace_map
    {X Y X' Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y')
    (A : Set X) (B : Set Y) (A' : Set X') (B' : Set Y')
    (hf : Set.MapsTo f A A') (hg : Set.MapsTo g B B') :
    Set.MapsTo (TopCat.ofHom (f.hom.prodMap g.hom))
      (A ×ˢ Set.univ ∪ Set.univ ×ˢ B)
      (A' ×ˢ Set.univ ∪ Set.univ ×ˢ B') := by
  rintro ⟨x, y⟩ (h | h)
  · exact Or.inl ⟨hf h.1, Set.mem_univ _⟩
  · exact Or.inr ⟨Set.mem_univ _, hg h.2⟩

end HolomorphicAnosov.Topology

