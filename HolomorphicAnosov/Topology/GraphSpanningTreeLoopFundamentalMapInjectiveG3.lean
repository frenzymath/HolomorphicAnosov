import Mathlib.Algebra.Group.Hom.End
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace HolomorphicAnosov.Topology

/-- A left inverse of a based fundamental-group homomorphism makes it
injective. This is the algebraic endpoint of the rooted contraction argument.

Source: Hatcher, *Algebraic Topology*, Proposition 0.17, pp.15--16. The
geometric contraction supplies the left inverse; this theorem discharges the
pure group-theoretic injectivity step without assuming any topological fact.
-/
theorem graph_spanning_tree_loop_fundamental_map_injective_of_left_inverse_g3
    {G H : Type*} [Group G] [Group H]
    (φ : G →* H) (ψ : H →* G)
    (hψ : ψ.comp φ = MonoidHom.id G) :
    Function.Injective φ := by
  intro a b hab
  have hleft : ∀ x : G, ψ (φ x) = x := by
    intro x
    have hx := DFunLike.congr_fun hψ x
    exact hx
  have hm := congrArg ψ hab
  exact (hleft a).symm.trans (hm.trans (hleft b))

end HolomorphicAnosov.Topology
