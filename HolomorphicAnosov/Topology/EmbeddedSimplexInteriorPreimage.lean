import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# The interior preimage of zero under an embedded simplex

-- This delivery uses the exact Mathlib leaves Convexity.StdSimplex.mem_range_map_iff
-- and Fin.range_succAbove recorded in the accompanying DAG files.

DAG node: `topo.embedded_simplex_interior_preimage_g20`.
This is the elementary geometric step in Hatcher's simplex local-class
comparison (Example 2.23 p.125 and local orientations pp.233–234).
-/

namespace HolomorphicAnosov

/-- A simplex embedding whose image contains zero and whose faces avoid zero
has a unique zero preimage, and every barycentric weight of that point is positive.

Proof: existence follows from image membership and uniqueness from injectivity.
If weight i were zero, the standard-simplex map-range criterion would place the
point in the image of the face omitting i. Face avoidance then contradicts its
value zero. Nonnegativity of every weight upgrades nonzero to strictly positive.
Source: elementary barycentric coordinates, as used in the simplex comparison
of Hatcher, *Algebraic Topology*, Example 2.23 p.125. -/
theorem embeddedSimplex_zero_preimage_positive (n : ℕ)
    (s : C(Convexity.StdSimplex ℝ (Fin (n + 2)), EuclideanSpace ℝ (Fin (n + 1))))
    (hemb : Topology.IsClosedEmbedding s)
    (hzero : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ interior (Set.range s))
    (hfaces : ∀ (i : Fin (n + 2)) (t : Convexity.StdSimplex ℝ (Fin (n + 1))),
      s (Convexity.StdSimplex.map i.succAbove t) ≠ 0) :
    ∃! t : Convexity.StdSimplex ℝ (Fin (n + 2)),
      s t = 0 ∧ ∀ i, 0 < t.weights i := by
  obtain ⟨t, ht⟩ := interior_subset hzero
  refine ⟨t, ⟨ht, ?_⟩, ?_⟩
  · intro i
    apply lt_of_le_of_ne (t.weights_nonneg i)
    intro hi
    have hrange : t ∈ Set.range (Convexity.StdSimplex.map i.succAbove) := by
      apply (Convexity.StdSimplex.mem_range_map_iff _ _).mpr
      intro j hj
      have hji : j = i := by simpa only [Fin.range_succAbove, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_not] using hj
      simpa only [hji] using hi.symm
    obtain ⟨u, hu⟩ := hrange
    exact hfaces i u (hu ▸ ht)
  · intro u hu
    exact hemb.injective (hu.1.trans ht.symm)

end HolomorphicAnosov

