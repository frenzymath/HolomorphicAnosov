import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
namespace HolomorphicAnosov
open _root_.Topology
/-- A map that is pointwise constant on a based loop sends its class to the
identity. This handles the empty-complement edge case of the quotient-word
argument. -/
theorem graph_spanning_tree_loop_constant_collapse_g3
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (Q : C(X, Y)) (x : X) (γ : Path x x)
    (hconst : ∀ t, Q (γ t) = Q x) :
    FundamentalGroup.map Q x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = 1 := by
  have hmap := FundamentalGroup.mapOfEq_apply Q rfl
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
  have heq : FundamentalGroup.map Q x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((γ.map Q.continuous).cast rfl rfl)) := by
    convert hmap using 1 <;> simp [FundamentalGroup.mapOfEq, ← Path.Homotopic.Quotient.mk_map]
  rw [heq]
  have hp : (γ.map Q.continuous).cast rfl rfl = Path.refl (Q x) := by
    ext t
    exact hconst t
  rw [hp]
  rfl
end HolomorphicAnosov
