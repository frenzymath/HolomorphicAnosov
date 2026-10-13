import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Restriction of a homotopy of topological pair maps

Source: Hatcher, *Algebraic Topology*, p. 201. A homotopy of maps of pairs
restricts to a homotopy on the subspaces, and the inclusion square commutes
with the homotopy cylinder map. DAG node:
`topo.singular_pair_homotopy_restriction_g13`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
universe u
noncomputable section

namespace HolomorphicAnosov.SingularCochain

/-- A homotopy through maps of pairs restricts to the subspace homotopy and
commutes with the two subspace inclusions at the cylinder level. -/
theorem pair_homotopy_restriction {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    {f g : X ⟶ Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) :
    ∃ HA : TopCat.Homotopy (pairSubspaceMap f hf) (pairSubspaceMap g hg),
      (subspaceInclusion X A ▷ TopCat.I) ≫ H.h = HA.h ≫ subspaceInclusion Y B := by
  let HA : TopCat.Homotopy (pairSubspaceMap f hf) (pairSubspaceMap g hg) := {
    toFun := fun z => ⟨H (z.1, z.2.1), hH z.1 z.2.1 z.2.2⟩
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := fun x => Subtype.ext (H.map_zero_left x.1)
    map_one_left := fun x => Subtype.ext (H.map_one_left x.1) }
  exact ⟨HA, rfl⟩


end HolomorphicAnosov.SingularCochain
