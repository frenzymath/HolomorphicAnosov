import HolomorphicAnosov.AlgebraicTopology.SingularPairHomotopyRestriction
import Mathlib.Topology.Homotopy.TopCat.ToSSet

/-!
# Simplicial cylinder square for a homotopy of pairs

Source: Hatcher, *Algebraic Topology*, p. 201, and Mathlib's
`TopCat.Homotopy.toSSet`. The explicit proof uses lax-monoidal naturality.
DAG node: `topo.singular_pair_prism_square_g13`.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Functor.LaxMonoidal
open scoped Simplicial
universe u
noncomputable section

namespace HolomorphicAnosov.SingularCochain

/-- The SSet cylinder square obtained from a homotopy through maps of pairs. -/
theorem singular_pair_prism_square {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    {f g : X ⟶ Y} (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : TopCat.Homotopy f g) (hH : ∀ t x, x ∈ A → H (t, x) ∈ B) :
    ∃ HA : SSet.Homotopy (TopCat.toSSet.map (pairSubspaceMap f hf))
        (TopCat.toSSet.map (pairSubspaceMap g hg)),
      ((TopCat.toSSet.map (subspaceInclusion X A)) ▷ Δ[1]) ≫
          H.toSSet.h =
        HA.h ≫ TopCat.toSSet.map (subspaceInclusion Y B) := by
  obtain ⟨HA, hsq⟩ := pair_homotopy_restriction hf hg H hH
  refine ⟨HA.toSSet, ?_⟩
  dsimp only [TopCat.Homotopy.toSSet]
  rw [← whisker_exchange_assoc, μ_natural_left_assoc,
    ← Functor.map_comp, hsq, Functor.map_comp]
  simp only [Category.assoc]


end HolomorphicAnosov.SingularCochain
