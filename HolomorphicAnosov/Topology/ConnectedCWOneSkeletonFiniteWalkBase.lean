import Mathlib.Topology.CWComplex.Classical.Graph

/-!
# The zero-length connected CW one-skeleton walk

This is the reflexive edge case of the finite-walk statement: equal endpoint
vertices are joined by the original zero-cell with no traversed one-cells.
Source: Hatcher, Algebraic Topology, Appendix Proposition A.4, pp.522–523;
the elementary constant-walk case of the original-cell incidence convention.
-/

namespace HolomorphicAnosov

open _root_.Topology

/-- Equal original zero cells admit the length-zero one-skeleton walk.

Source: Hatcher, Algebraic Topology, Appendix Proposition A.4, pp.522–523,
constant-path case. Choose length zero and the constant singleton vertex array.
The edge array has empty domain `Fin 0`, so all incidence conditions are vacuous;
both endpoint equations follow from the supplied equality. -/
theorem connected_cw_one_skeleton_finite_walk_refl
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [CWComplex (Set.univ : Set X)]
    (u v : RelCWComplex.cell (Set.univ : Set X) 0) (huv : u = v) :
    ∃ (n : ℕ) (a : Fin (n + 1) → RelCWComplex.cell (Set.univ : Set X) 0)
      (b : Fin n → RelCWComplex.cell (Set.univ : Set X) 1),
      a 0 = u ∧ a (Fin.last n) = v ∧
        ∀ i : Fin n,
          (CWComplex.OneSkeletonGraph (Set.univ : Set X)).IsLink
            (b i) (a i.castSucc) (a i.succ) := by
  subst v
  refine ⟨0, (fun _ ↦ u), Fin.elim0, rfl, ?_, ?_⟩
  · rfl
  · intro i
    exact Fin.elim0 i

end HolomorphicAnosov
