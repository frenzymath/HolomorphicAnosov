import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Images of rooted edge loops under a collapse

Hatcher, Algebraic Topology, Proposition 1A.2, pp.84–85 identifies the
quotient images of the rooted edge loops with the oriented wedge circles.
The proof below expands the endpoint casts and constant-path cancellations
in that identification. No graph quotient or homotopy equivalence is assumed
constructed by this lemma.
-/

namespace HolomorphicAnosov.Topology

/-- A continuous map constant on both root paths sends the root-edge-root
fundamental-group class to the edge-image loop class. The displayed endpoint
equalities make the result an equality in the original based fundamental group,
without conjugation or reversal of the edge orientation.

Source: Hatcher, Proposition 1A.2, pp.84–85. Map concatenation to concatenation,
identify the two mapped root paths with constant paths (including their endpoint
casts), then use the left and right constant-path homotopies. -/
theorem mapOfEq_rooted_edge_loop_of_constant_root_paths
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (o a b : X) (y : Y)
    (ho : f o = y) (ha : f a = y) (hb : f b = y)
    (qa : Path o a) (qb : Path o b) (edge : Path a b)
    (hqa : ∀ t, f (qa t) = y) (hqb : ∀ t, f (qb t) = y) :
    FundamentalGroup.mapOfEq f ho
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((qa.trans edge).trans qb.symm))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        ((edge.map f.continuous).cast ha.symm hb.symm)) := by
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  apply Path.Homotopic.Quotient.eq.mpr
  let e : Path y y := (edge.map f.continuous).cast ha.symm hb.symm
  have hA : (qa.map f.continuous).cast ho.symm ha.symm = Path.refl y := by
    ext t
    exact hqa t
  have hB : (qb.symm.map f.continuous).cast hb.symm ho.symm = Path.refl y := by
    ext t
    exact hqb (unitInterval.symm t)
  have hL : (((qa.trans edge).trans qb.symm).map f.continuous).cast ho.symm ho.symm =
      ((Path.refl y).trans e).trans (Path.refl y) := by
    rw [Path.map_trans, Path.map_trans]
    change (((qa.map f.continuous).cast ho.symm ha.symm).trans e).trans
      ((qb.symm.map f.continuous).cast hb.symm ho.symm) = _
    rw [hA, hB]
  rw [hL]
  exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans e)

end HolomorphicAnosov.Topology

